#!/usr/bin/env python3
"""Checks every citation of the Pico source in the hand-written files against the pinned Pico.

  check_citations.py [--pico DIR] [--strict] [--show] [--github] [FILE ...]
  check_citations.py --self-test [--pico DIR]

A citation is `path.rs:line`, `path.rs:from-to` (more ranges may follow, `path.rs:3-5, 9`), or a
link into `github.com/brevis-network/pico/` (`blob/<ref>/<path>#L<from>-L<to>`, `tree/<ref>`).
A path that starts with `extractor/` names a file of this repository; any other path is matched,
by its last components, against the files of Pico at the commit `extractor/Cargo.lock` pins for
the `pico-vm` dependency of `extractor/Cargo.toml`. A Markdown link whose text is a citation
(`[alu/lt/constraints.rs:81-82](…#L81-L82)`) counts once, and its text must cite what its link
does. The files read are `PicoFV/` (not `Extraction/`) and `docs/`, or the FILEs given. A finding
is one of:

  NO FILE        the path matches no file
  AMBIGUOUS      the path matches several files: give more of it
  OUT OF RANGE   a cited line is not in the file, or a range runs backwards
  OTHER COMMIT   a link names a Pico ref other than the pinned commit or tag
  LINK MISMATCH  a link's text cites other lines than its link
  NO TAG         a file cites Pico but does not say which tag it was read at
  STALE TAG      a file says it was read at a tag other than the pinned one

A file says the tag in one line: `Citations read at Pico v3.2.0.` A pin move turns each such file
into STALE TAG until someone re-reads its citations at the new tag and updates the line.

A citation that resolves points at lines that exist; whether they say what the comment claims is
a reader's check. `--show` prints the cited lines next to each citation for that reading.

Pico is read with `git show <commit>:<path>` from DIR (`--pico`), or else from the checkout Cargo
made for the extractor (`$CARGO_HOME/git/checkouts/pico-*/`), or else from `$PICO_SRC`.

Exit status: 0, or 1 with `--strict` when there is a finding; 2 when the pin or Pico cannot be
read. `--github` also writes each finding as a workflow warning and the summary to the job summary.
"""
import argparse, collections, glob, os, pathlib, re, subprocess, sys, tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
# A further range counts only when it ends the citation: before a closing mark, a full stop or the
# end of the line, so that `x.rs:3, 2 lines later` cites line 3 alone.
END = r'(?=[`),;\]]|\.(?!\d)|[ \t]*$)'
CITE = re.compile(r'(?<![\w./-])((?:[\w.-]+/)*[\w-]+\.rs):(\d+)(?:-(\d+))?((?:,[ \t]*\d+(?:-\d+)?' + END + r')*)')
MORE = re.compile(r'(\d+)(?:-(\d+))?')
LINK = re.compile(r'github\.com/brevis-network/pico/(?:blob|tree)/([^/\s#)>`]+)(?:/([^\s#)>`]*))?'
                  r'(?:#L(\d+)(?:-L(\d+))?)?')
MDLINK = re.compile(r'\[([^\]]*)\]\((https://' + LINK.pattern + r')\)')
MARK = re.compile(r'Citations read at Pico (\S+?)\.(?:\s|$)')
KINDS = ['NO FILE', 'AMBIGUOUS', 'OUT OF RANGE', 'OTHER COMMIT', 'LINK MISMATCH', 'NO TAG', 'STALE TAG']


def fail(msg):
    print(f'check_citations: {msg}', file=sys.stderr)
    sys.exit(2)


def git(repo, *args):
    r = subprocess.run(['git', '-C', str(repo), *args], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None


def pin(root):
    """The tag (or other ref) `extractor/Cargo.toml` names for pico-vm, and the commit the lock resolves."""
    toml = (root / 'extractor/Cargo.toml').read_text()
    dep = re.search(r'^pico-vm\s*=\s*\{([^}]*)\}', toml, re.M) or \
        re.search(r'^\[dependencies\.pico-vm\]\n((?:[^\[].*\n?)*)', toml, re.M)
    ref = dep and re.search(r'\b(?:tag|rev|branch)\s*=\s*"([^"]+)"', dep[1])
    lock = re.search(r'name = "pico-vm"\n(?:[^\[\n]*\n)*?source = "git\+[^"#]*#([0-9a-f]{40})"',
                     (root / 'extractor/Cargo.lock').read_text())
    if not ref or not lock:
        fail('cannot read the pico-vm pin from extractor/Cargo.toml and extractor/Cargo.lock')
    return ref[1], lock[1]


def find_pico(rev, given):
    home = os.environ.get('CARGO_HOME', str(pathlib.Path.home() / '.cargo'))
    cands = [given] if given else (sorted(glob.glob(f'{home}/git/checkouts/pico-*/*'))
                                   + ([os.environ['PICO_SRC']] if os.environ.get('PICO_SRC') else []))
    for c in cands:
        if c and git(c, 'cat-file', '-e', f'{rev}^{{commit}}') is not None:
            return c
    fail(f'no Pico checkout holding {rev} (tried {", ".join(cands) or "none"}); '
         'pass --pico DIR or run `cargo fetch` in extractor/')


class Source:
    def __init__(self, root, pico, tag, rev):
        self.root, self.pico, self.tag, self.rev = root, pico, tag, rev
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

    def pinned(self, ref):
        return ref == self.tag or (len(ref) >= 7 and self.rev.startswith(ref))


def files(root, given):
    if given:
        return [pathlib.Path(f).resolve() for f in given]
    out = [f for f in sorted((root / 'PicoFV').rglob('*.lean')) if 'Extraction' not in f.relative_to(root).parts]
    return out + sorted((root / 'docs').rglob('*.md'))


def ranges_of(m):
    return [(int(m[2]), int(m[3] or m[2]))] + [(int(x[1]), int(x[2] or x[1])) for x in MORE.finditer(m[4])]


def check(root, src, paths):
    """Yields (kind or 'OK', where, citation, detail, cited lines)."""
    for f in paths:
        rel = f.relative_to(root) if f.is_relative_to(root) else f
        text = f.read_text()
        cited = False
        for n, line in enumerate(text.splitlines(), 1):
            where = f'{rel}:{n}'
            # A Markdown link with a citation as its text: one citation, text and link compared.
            for md in MDLINK.finditer(line):
                inner = CITE.fullmatch(md[1].strip('`'))
                link = LINK.search(md[2])
                if inner and link[2] and link[3]:
                    cited = True
                    said = (inner[1], ranges_of(inner))
                    meant = (link[2], [(int(link[3]), int(link[4] or link[3]))])
                    if not link[2].endswith(said[0]) or said[1] != meant[1]:
                        yield 'LINK MISMATCH', where, md[1], f'link cites {link[2]}#L{link[3]}' + \
                            (f'-L{link[4]}' if link[4] else ''), None
                    else:
                        yield from judge_link(src, where, link)
                    line = line.replace(md[0], '')
            for m in LINK.finditer(line):
                cited = True
                yield from judge_link(src, where, m)
            for m in CITE.finditer(LINK.sub('', line)):
                cited = True
                yield from judge(src, where, m[0], m[1], ranges_of(m))
        marks = MARK.findall(text)
        if cited and not marks:
            yield 'NO TAG', str(rel), '', f'add the line `Citations read at Pico {src.tag}.`', None
        for t in sorted(set(marks) - {src.tag}):
            yield 'STALE TAG', str(rel), t, f're-read the citations at {src.tag}', None


def judge_link(src, where, m):
    ref, path = m[1], m[2]
    if not src.pinned(ref):
        yield 'OTHER COMMIT', where, m[0], f'pinned {src.tag} ({src.rev[:12]})', None
    elif path:
        yield from judge(src, where, m[0], path, [(int(m[3]), int(m[4] or m[3]))] if m[3] is not None else [])


def judge(src, where, cite, path, ranges):
    hits = src.resolve(path)
    if not hits:
        yield 'NO FILE', where, cite, '', None
    elif len(hits) > 1:
        yield 'AMBIGUOUS', where, cite, f'{len(hits)} files: ' + ', '.join(hits[:4]), None
    else:
        text = src.lines(hits[0])
        if any(not 1 <= a <= b <= len(text) for a, b in ranges):
            yield 'OUT OF RANGE', where, cite, f'{hits[0]} has {len(text)} lines', None
        else:
            yield 'OK', where, cite, hits[0], [(k, text[k - 1]) for a, b in ranges for k in range(a, b + 1)]


def report(results, src, strict, show, github):
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
    summary = (f'{total} citations at Pico {src.tag} ({src.rev[:7]}): {count["OK"]} resolve; '
               + ', '.join(f'{count[k]} {k.lower()}' for k in KINDS))
    print(summary)
    if github and os.environ.get('GITHUB_STEP_SUMMARY'):
        with open(os.environ['GITHUB_STEP_SUMMARY'], 'a') as out:
            out.write(f'### Pico citations\n\n{summary}\n\n')
            for kind, where, cite, detail, _ in results:
                if kind != 'OK':
                    out.write(f'- {kind} `{where}` `{cite}` {detail}\n')
    return 1 if strict and found else 0


def self_test(src):
    """Plants one case of each finding, and citations that resolve, and checks the report."""
    rs = [p for p in src.tree if p.startswith('vm/src/') and p.endswith('.rs')]
    names = collections.Counter(p.rsplit('/', 1)[1] for p in rs)
    good = next((p for p in rs if names[p.rsplit('/', 1)[1]] == 1 and len(src.lines(p)) > 2), None)
    twice = next((n for n, k in names.items() if k > 1), None)
    if not good or not twice:
        fail(f'self-test: Pico at {src.rev[:12]} has no .rs file to plant citations on')
    short, size, url = good.split('/', 2)[2], len(src.lines(good)), 'https://github.com/brevis-network/pico'
    planted = {
        'OK': f'`{short}:1-2, {size}`.',
        'NO FILE': '`vm/src/no_such_file.rs:1`',
        'AMBIGUOUS': f'`{twice}:1`',
        'OUT OF RANGE': f'{short}:1, {size + 1}.',
        'OTHER COMMIT': f'{url}/blob/v0.0.1/{good}#L1',
        'LINK MISMATCH': f'[`{short}:1-2`]({url}/blob/{src.rev}/{good}#L2-L3)',
    }
    with tempfile.TemporaryDirectory() as tmp:
        tmp = pathlib.Path(tmp)
        (tmp / 'Planted.lean').write_text(f'/-! Citations read at Pico {src.tag}. -/\n'
                                          + ''.join(f'-- {k}: {v}\n' for k, v in planted.items())
                                          + f'-- OK: `{short}:1, {size + 5} lines later`\n'
                                          + f'-- OK: [`{short}:1-2`]({url}/blob/{src.rev}/{good}#L1-L2)\n'
                                          + f'-- OUT OF RANGE: {url}/blob/{src.rev}/{good}#L0\n')
        (tmp / 'Untagged.lean').write_text(f'-- `{short}:1`\n')
        (tmp / 'Stale.lean').write_text(f'-- `{short}:1`\n-- Citations read at Pico v0.0.1.\n')
        got = list(check(tmp, src, sorted(tmp.glob('*.lean'))))
        status = report(got, src, strict=True, show=False, github=False)
    kinds = {(r[0], r[1]) for r in got}
    want = {(k, f'Planted.lean:{i}') for i, k in enumerate(planted, 2)}
    want |= {('OK', 'Planted.lean:8'), ('OK', 'Planted.lean:9'), ('OUT OF RANGE', 'Planted.lean:10'),
             ('NO TAG', 'Untagged.lean'), ('STALE TAG', 'Stale.lean'),
             ('OK', 'Untagged.lean:1'), ('OK', 'Stale.lean:1')}
    missing, extra = want - kinds, kinds - want
    ok = not missing and not extra and status == 1 and len(got) == len(want)
    print('self-test:', 'OK' if ok else f'FAILED (missing {sorted(missing)}, extra {sorted(extra)}, '
                                         f'{len(got)} results for {len(want)}, strict exit {status})')
    return 0 if ok else 1


def main(argv):
    ap = argparse.ArgumentParser(description='Checks the Pico citations against the pinned Pico.')
    ap.add_argument('files', nargs='*', metavar='FILE')
    ap.add_argument('--pico', metavar='DIR', help='a Pico git checkout holding the pinned commit')
    ap.add_argument('--strict', action='store_true', help='exit 1 when there is a finding')
    ap.add_argument('--show', action='store_true', help='print the cited lines of each citation')
    ap.add_argument('--github', action='store_true', help='workflow warnings and job summary')
    ap.add_argument('--self-test', action='store_true', help='plant one case of each finding')
    a = ap.parse_args(argv)
    tag, rev = pin(ROOT)
    src = Source(ROOT, find_pico(rev, a.pico), tag, rev)
    if a.self_test:
        return self_test(src)
    return report(list(check(ROOT, src, files(ROOT, a.files))), src, a.strict, a.show, a.github)


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
