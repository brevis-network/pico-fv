#!/usr/bin/env python3
"""Checks every citation of the Pico source in the hand-written files against the pinned Pico.

  check_citations.py [--pico DIR] [--strict] [--show] [--github] [FILE ...]
  check_citations.py --self-test [--pico DIR]

A citation is `path.rs:line`, `path.rs:from-to` (more ranges may follow, `path.rs:3-5, 9`), or a
link to `github.com/brevis-network/pico/blob/<commit>/<path>#L<from>-L<to>`. A path that starts
with `extractor/` names a file of this repository; any other path is matched, by its last
components, against the files of Pico at the commit `extractor/Cargo.lock` pins for the tag in
`extractor/Cargo.toml`. The files read are `PicoFV/` (not `Extraction/`) and `docs/`, or the FILEs
given. A finding is one of:

  NO FILE       the path matches no file
  AMBIGUOUS     the path matches several files: give more of it
  OUT OF RANGE  a cited line is past the end of the file, or a range runs backwards
  OTHER COMMIT  a link names a Pico commit other than the pinned one
  NO TAG        a file cites Pico but does not say which tag it was read at
  STALE TAG     a file says it was read at a tag other than the pinned one

A file says the tag in one line: `Citations read at Pico v3.2.0.` A pin move turns each such file
into STALE TAG until someone re-reads its citations at the new tag and updates the line.

A citation that resolves points at lines that exist; whether they say what the comment claims is
a reader's check. `--show` prints the cited lines next to each citation for that reading.

Pico is read with `git show <commit>:<path>` from DIR (`--pico`), or else from the checkout Cargo
made for the extractor (`$CARGO_HOME/git/checkouts/pico-*/`), or else from `$PICO_SRC`.

Exit status: 0, or 1 with `--strict` when there is a finding; 2 when Pico cannot be read.
`--github` also writes each finding as a workflow warning and the summary to the job summary.
"""
import collections, glob, os, pathlib, re, subprocess, sys, tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
CITE = re.compile(r'(?<![\w./-])((?:[\w.-]+/)*[\w-]+\.rs):(\d+)(?:-(\d+))?((?:,[ \t]*\d+(?:-\d+)?(?![\w.]))*)')
MORE = re.compile(r'(\d+)(?:-(\d+))?')
LINK = re.compile(r'github\.com/brevis-network/pico/blob/([0-9a-f]{7,40})/([\w./-]+\.rs)(?:#L(\d+)(?:-L(\d+))?)?')
MARK = re.compile(r'Citations read at Pico (v\d+\.\d+\.\d+)\.')
KINDS = ['NO FILE', 'AMBIGUOUS', 'OUT OF RANGE', 'OTHER COMMIT', 'NO TAG', 'STALE TAG']


def git(repo, *args):
    r = subprocess.run(['git', '-C', str(repo), *args], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None


def pin(root):
    toml = (root / 'extractor/Cargo.toml').read_text()
    tag = re.search(r'^pico-vm\s*=.*tag\s*=\s*"([^"]+)"', toml, re.M)[1]
    lock = (root / 'extractor/Cargo.lock').read_text()
    rev = re.search(r'name = "pico-vm"\n[^\[]*?source = "git\+[^#]*\?tag=' + re.escape(tag) + r'#([0-9a-f]{40})"', lock)[1]
    return tag, rev


def find_pico(rev, given):
    home = os.environ.get('CARGO_HOME', str(pathlib.Path.home() / '.cargo'))
    cands = [given] if given else (sorted(glob.glob(f'{home}/git/checkouts/pico-*/*'))
                                   + ([os.environ['PICO_SRC']] if os.environ.get('PICO_SRC') else []))
    for c in cands:
        if c and git(c, 'cat-file', '-e', f'{rev}^{{commit}}') is not None:
            return c
    print(f'check_citations: no Pico checkout holding {rev} (tried {", ".join(cands) or "none"}); '
          'pass --pico DIR or run `cargo fetch` in extractor/', file=sys.stderr)
    sys.exit(2)


class Source:
    def __init__(self, root, pico, rev):
        self.root, self.pico, self.rev = root, pico, rev
        self.tree = git(pico, 'ls-tree', '-r', '--name-only', rev).split()
        self.texts = {}

    def resolve(self, path):
        if path.startswith('extractor/'):
            return [path] if (self.root / path).is_file() else []
        return [p for p in self.tree if p == path or p.endswith('/' + path)]

    def lines(self, path):
        if path not in self.texts:
            text = ((self.root / path).read_text() if path.startswith('extractor/')
                    else git(self.pico, 'show', f'{self.rev}:{path}'))
            self.texts[path] = text.splitlines()
        return self.texts[path]


def files(root, given):
    if given:
        return [pathlib.Path(f).resolve() for f in given]
    out = [f for f in sorted((root / 'PicoFV').rglob('*.lean')) if 'Extraction' not in f.relative_to(root).parts]
    return out + sorted((root / 'docs').rglob('*.md'))


def check(root, src, tag, paths):
    """Yields (kind or 'OK', where, citation, detail, cited lines)."""
    for f in paths:
        rel = f.relative_to(root) if f.is_relative_to(root) else f
        text = f.read_text()
        cited = False
        for n, line in enumerate(text.splitlines(), 1):
            where = f'{rel}:{n}'
            for m in LINK.finditer(line):
                cited = True
                commit, path, a = m[1], m[2], int(m[3]) if m[3] else None
                if not src.rev.startswith(commit):
                    yield 'OTHER COMMIT', where, m[0], f'pinned {src.rev[:12]}', None
                    continue
                yield from judge(src, where, m[0], path, [(a, int(m[4] or a))] if a else [])
            for m in CITE.finditer(LINK.sub('', line)):
                cited = True
                ranges = [(int(m[2]), int(m[3] or m[2]))]
                ranges += [(int(x[1]), int(x[2] or x[1])) for x in MORE.finditer(m[4])]
                yield from judge(src, where, m[0], m[1], ranges)
        marks = MARK.findall(text)
        if cited and not marks:
            yield 'NO TAG', str(rel), '', f'add the line `Citations read at Pico {tag}.`', None
        for t in set(marks) - {tag}:
            yield 'STALE TAG', str(rel), t, f're-read the citations at {tag}', None


def judge(src, where, cite, path, ranges):
    hits = src.resolve(path)
    if not hits:
        yield 'NO FILE', where, cite, '', None
    elif len(hits) > 1:
        yield 'AMBIGUOUS', where, cite, f'{len(hits)} files: ' + ', '.join(hits[:4]), None
    else:
        text = src.lines(hits[0])
        bad = [(a, b) for a, b in ranges if not 1 <= a <= b <= len(text)]
        if bad:
            yield 'OUT OF RANGE', where, cite, f'{hits[0]} has {len(text)} lines', None
        else:
            yield 'OK', where, cite, hits[0], [(k, text[k - 1]) for a, b in ranges for k in range(a, b + 1)]


def report(results, tag, rev, strict, show, github):
    count = collections.Counter(r[0] for r in results)
    for kind, where, cite, detail, cited in results:
        if kind == 'OK':
            if show:
                print(f'OK  {where}  {cite}  ->  {detail}')
                for k, t in cited[:12]:
                    print(f'      {k}: {t}')
                if len(cited) > 12:
                    print(f'      ... {len(cited) - 12} more lines')
            continue
        print(f'{kind}  {where}  {cite}  ({detail})' if detail else f'{kind}  {where}  {cite}')
        if github:
            file, _, line = where.partition(':')
            print(f'::warning file={file}{",line=" + line if line else ""},title=citation {kind.lower()}::'
                  f'{cite} {detail}'.rstrip())
    total = sum(count.values()) - count['NO TAG'] - count['STALE TAG']
    found = sum(count[k] for k in KINDS)
    summary = (f'{total} citations at Pico {tag} ({rev[:7]}): {count["OK"]} resolve; '
               + ', '.join(f'{count[k]} {k.lower()}' for k in KINDS))
    print(summary)
    if github and os.environ.get('GITHUB_STEP_SUMMARY'):
        with open(os.environ['GITHUB_STEP_SUMMARY'], 'a') as out:
            out.write(f'### Pico citations\n\n{summary}\n\n')
            for kind, where, cite, detail, _ in results:
                if kind != 'OK':
                    out.write(f'- {kind} `{where}` `{cite}` {detail}\n')
    return 1 if strict and found else 0


def self_test(src, tag):
    """Plants one case of each finding, and one citation that resolves, and checks the report."""
    good = next(p for p in src.tree if p.endswith('vm/src/chips/gadgets/is_zero.rs'))
    planted = {
        'OK': f'`chips/gadgets/is_zero.rs:1-2`',
        'NO FILE': '`vm/src/no_such_file.rs:1`',
        'AMBIGUOUS': '`constraints.rs:1`',
        'OUT OF RANGE': f'`chips/gadgets/is_zero.rs:{len(src.lines(good)) + 1}`',
        'OTHER COMMIT': f'https://github.com/brevis-network/pico/blob/{"0" * 40}/{good}#L1',
    }
    with tempfile.TemporaryDirectory() as tmp:
        tmp = pathlib.Path(tmp)
        lean = tmp / 'Planted.lean'
        lean.write_text(f'/-! Citations read at Pico {tag}. -/\n'
                        + ''.join(f'-- {k}: {v}\n' for k, v in planted.items()))
        (tmp / 'Untagged.lean').write_text('-- `chips/gadgets/is_zero.rs:1`\n')
        (tmp / 'Stale.lean').write_text('-- `chips/gadgets/is_zero.rs:1`\n-- Citations read at Pico v0.0.1.\n')
        got = list(check(tmp, src, tag, sorted(tmp.glob('*.lean'))))
        status = report(got, tag, src.rev, strict=True, show=False, github=False)
    kinds = {(r[0], r[1]) for r in got}
    want = {(k, f'Planted.lean:{i}') for i, k in enumerate(planted, 2)}
    want |= {('NO TAG', 'Untagged.lean'), ('STALE TAG', 'Stale.lean')}
    missing = want - kinds
    extra = {k for k in kinds - want if k[0] != 'OK'}
    ok = not missing and not extra and status == 1
    print('self-test:', 'OK' if ok else f'FAILED (missing {sorted(missing)}, extra {sorted(extra)}, '
                                         f'strict exit {status})')
    return 0 if ok else 1


def main(argv):
    args = [a for a in argv if not a.startswith('--')]
    pico = None
    if '--pico' in argv:
        pico = argv[argv.index('--pico') + 1]
        args.remove(pico)
    tag, rev = pin(ROOT)
    src = Source(ROOT, find_pico(rev, pico), rev)
    if '--self-test' in argv:
        return self_test(src, tag)
    results = list(check(ROOT, src, tag, files(ROOT, args)))
    return report(results, tag, rev, '--strict' in argv, '--show' in argv, '--github' in argv)


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
