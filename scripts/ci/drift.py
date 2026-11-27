#!/usr/bin/env python3
"""Lists where Pico branches differ from the Pico pinned in extractor/Cargo.toml.

    scripts/ci/drift.py [--repo URL] [--work DIR] [BRANCH ...]     (default branches: dev main)

For each branch it reports:

- per extracted chip and gadget, whether the branch's constraints are the same as the pin's or
  differ: the pinned extractor writes the pin's extraction (`--all`), and a copy of extractor/
  re-pointed at the branch's commit compares its own extraction with it (`--compare`), ignoring
  the first line, which names the commit;
- Pico's two RISC-V chip lists (`RiscvChipType::all_chip_variants`, `mle_riscv_air_refs`) against
  the pin's, and whether each extracted chip is still in them (`--lists`);
- the Plonky3 revisions Pico's Cargo.toml names, against the extractor's;
- the files under vm/src/machine/builder/ changed since the pin.

The pin is not changed: the copy lives in the work directory. It builds into extractor/target,
so only Pico's crates compile again; the next `cargo run` in extractor/ relinks the pinned binary.
The report is printed, and appended to $GITHUB_STEP_SUMMARY when set.

Exits 1 when a branch could not be compared: it was not found, the copy did not build, or a
comparison or list came out empty. A run that compared nothing does not pass.
"""
import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXTRACTOR = ROOT / "extractor"
DEFAULT_REPO = "https://github.com/brevis-network/pico.git"
PICO_DEP = re.compile(r'^(pico-vm|pico-mle-core) = \{ git = "([^"]+)", tag = "([^"]+)" \}$', re.M)
P3_REV = re.compile(r'Plonky3\.git", rev = "([^"]+)"')


class NotCompared(Exception):
    """A branch that could not be compared; the message says why."""


def run(cmd, cwd=None, env=None, check=True):
    proc = subprocess.run(cmd, cwd=cwd, env=env, text=True, capture_output=True)
    if check and proc.returncode != 0:
        raise NotCompared(f"`{' '.join(map(str, cmd))}` failed:\n{tail(proc.stderr)}")
    return proc


def tail(text, lines=15):
    return "\n".join(text.strip().splitlines()[-lines:])


def read_pin():
    manifest = (EXTRACTOR / "Cargo.toml").read_text()
    deps = PICO_DEP.findall(manifest)
    tags = {tag for _, _, tag in deps}
    p3 = set(P3_REV.findall(manifest))
    if len(deps) != 2 or len(tags) != 1 or len(p3) != 1:
        sys.exit(f"cannot read the pin from {EXTRACTOR / 'Cargo.toml'}")
    return tags.pop(), p3.pop()


def parse_lists(text):
    lists = {"chiptype": [], "air": [], "extracted": []}
    for line in text.splitlines():
        kind, _, rest = line.partition(" ")
        lists[kind].append(rest)
    return lists


def extractor_at_pin(work):
    """The pin's extraction directory and chip lists, from the extractor as committed."""
    pin_dir = work / "pin"
    cargo = ["cargo", "run", "--release", "--locked", "--quiet", "--"]
    try:
        run([*cargo, "--all", pin_dir], cwd=EXTRACTOR)
        lists = parse_lists(run([*cargo, "--lists"], cwd=EXTRACTOR).stdout)
    except NotCompared as e:
        publish(f"# Pico drift: not compared\n\nThe extractor at the pin failed:\n\n```\n{e}\n```\n")
        sys.exit(1)
    return pin_dir, lists


def publish(text):
    print(text)
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as f:
            f.write(text)


def extractor_at(branch, commit, repo, p3_rev, work, pin_p3):
    """Builds a copy of extractor/ against `commit` and returns its binary."""
    copy = work / f"extractor-{branch.replace('/', '-')}"
    shutil.rmtree(copy, ignore_errors=True)
    shutil.copytree(EXTRACTOR, copy, ignore=shutil.ignore_patterns("target", "target-*"))
    manifest = copy / "Cargo.toml"
    text = PICO_DEP.sub(lambda m: f'{m[1]} = {{ git = "{repo}", rev = "{commit}" }}',
                        manifest.read_text())
    # The extractor's Plonky3 crates must be the ones Pico builds with, or the AIR types differ.
    text = text.replace(f'rev = "{pin_p3}"', f'rev = "{p3_rev}"')
    manifest.write_text(text)
    env = {**os.environ, "CARGO_TARGET_DIR": str(EXTRACTOR / "target")}
    run(["cargo", "update", "--quiet", "-p", "pico-vm", "-p", "pico-mle-core"], cwd=copy, env=env)
    build = run(["cargo", "build", "--release", "--quiet"], cwd=copy, env=env, check=False)
    if build.returncode != 0:
        raise NotCompared(f"the extractor does not build against {branch} ({commit[:8]}):\n"
                          f"{tail(build.stderr)}")
    return EXTRACTOR / "target" / "release" / "pico-fv-extractor"


def list_changes(name, pin, now):
    added = [x for x in now if x not in pin]
    removed = [x for x in pin if x not in now]
    lines = [f"- `{name}`: {len(now)} entries ({len(pin)} at the pin)"]
    lines += [f"  - added: `{x}`" for x in added]
    lines += [f"  - removed: `{x}`" for x in removed]
    if not added and not removed and pin != now:
        lines.append("  - same entries, order changed")
    return lines


def compare_branch(out, branch, repo, clone, work, pin_tag, pin_p3, pin_dir, pin_lists):
    """Appends the branch's report to `out`; raises NotCompared when it cannot compare."""
    found = run(["git", "rev-parse", "--verify", "--quiet", f"origin/{branch}^{{commit}}"],
                cwd=clone, check=False)
    if found.returncode != 0:
        raise NotCompared(f"branch `{branch}` not found in {repo}")
    commit = found.stdout.strip()
    out += [f"## `{branch}` at `{commit[:8]}`", ""]

    pico_manifest = run(["git", "show", f"{commit}:Cargo.toml"], cwd=clone).stdout
    p3_revs = sorted(set(P3_REV.findall(pico_manifest)))
    if not p3_revs:
        raise NotCompared(f"no Plonky3 revision in Pico's Cargo.toml at {branch}")
    state = "same" if p3_revs == [pin_p3] else "differs"
    out += [f"**Plonky3**: {state}: Pico names {', '.join(f'`{r}`' for r in p3_revs)}, "
            f"the extractor `{pin_p3}`", ""]
    if len(p3_revs) != 1:
        raise NotCompared("Pico names more than one Plonky3 revision")

    builder = run(["git", "diff", "--no-renames", "--name-status", pin_tag, commit, "--",
                   "vm/src/machine/builder/"], cwd=clone).stdout.split("\n")
    builder = [line.replace("\t", " ") for line in builder if line]
    out.append(f"**`vm/src/machine/builder/` since `{pin_tag}`**: "
               + (f"{len(builder)} files" if builder else "no change"))
    out += [f"- `{line}`" for line in builder]
    out.append("")

    binary = extractor_at(branch, commit, repo, p3_revs[0], work, pin_p3)
    rows = run([binary, "--compare", pin_dir]).stdout.split("\n")
    lists = parse_lists(run([binary, "--lists"]).stdout)

    rows = [row.split(" ", 1) for row in rows if row]
    compared = [name for status, name in rows if status in ("same", "differs")]
    if not compared:
        raise NotCompared("the comparison listed no chip")
    counts = {s: sum(1 for status, _ in rows if status == s)
              for s in ("same", "differs", "added", "removed")}
    out.append("**Constraints**: " + ", ".join(f"{n} {s}" for s, n in counts.items() if n))
    for status in counts:
        names = [name for s, name in rows if s == status]
        if names:
            out.append(f"- {status}: " + ", ".join(f"`{name}`" for name in names))
    out.append("")

    if not all(lists.values()):
        empty = [k for k, v in lists.items() if not v]
        raise NotCompared(f"empty chip list: {', '.join(empty)}")
    out.append("**Chip lists**")
    out += list_changes("RiscvChipType::all_chip_variants", pin_lists["chiptype"], lists["chiptype"])
    out += list_changes("mle_riscv_air_refs", pin_lists["air"], lists["air"])
    missing = []
    for entry in lists["extracted"]:
        lean_name, chip_name, air_name = entry.split(" ")
        if chip_name not in lists["chiptype"]:
            missing.append(f"  - `{lean_name}` (`{chip_name}`) is not in `all_chip_variants`")
        if air_name not in lists["air"]:
            missing.append(f"  - `{lean_name}` (`{air_name}`) is not in `mle_riscv_air_refs`")
    out.append(f"- extracted chips: {len(lists['extracted'])}, "
               + ("all in both lists" if not missing else "some missing"))
    out += missing
    out.append("")


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("branches", nargs="*", default=["dev", "main"])
    parser.add_argument("--repo", default=DEFAULT_REPO, help="Pico's git URL (default: %(default)s)")
    parser.add_argument("--work", type=Path, help="work directory, kept (default: a temporary one)")
    args = parser.parse_args()

    pin_tag, pin_p3 = read_pin()
    work = args.work or Path(tempfile.mkdtemp(prefix="pico-drift-"))
    work.mkdir(parents=True, exist_ok=True)

    report = [f"# Pico drift from the pin `{pin_tag}`", "",
              f"Compared against `{args.repo}`. The constraints are compared without the "
              "first line of each file, which names the commit.", ""]
    pin_dir, pin_lists = extractor_at_pin(work)

    clone = work / "pico"
    if not clone.exists():
        run(["git", "clone", "--quiet", "--filter=blob:none", "--no-checkout", args.repo, clone])
    run(["git", "fetch", "--quiet", "--tags", "origin"], cwd=clone)

    failed = []
    for branch in args.branches:
        out = []
        try:
            compare_branch(out, branch, args.repo, clone, work, pin_tag, pin_p3, pin_dir,
                           pin_lists)
        except NotCompared as e:
            failed.append(branch)
            out = out or [f"## `{branch}`", ""]
            out += ["**Not compared**:", "", "```", str(e), "```", ""]
        report += out
    if failed:
        report.append(f"Not compared: {', '.join(failed)}.")
    publish("\n".join(report) + "\n")
    if failed and os.environ.get("GITHUB_ACTIONS"):
        print(f"::error::not compared: {', '.join(failed)} (see the job summary)")
    if not args.work:
        shutil.rmtree(work, ignore_errors=True)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
