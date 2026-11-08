"""Fills the generated blocks of SOUNDNESS.md from the repository, so the facts that change
with the code stay true on every commit.

  python3 scripts/fv-check/soundness_facts.py           rewrite the blocks
  python3 scripts/fv-check/soundness_facts.py --check   fail if a block is out of date
"""
import pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
CHECK = ROOT / 'scripts/fv-check'
CORE = {'propext', 'Classical.choice', 'Quot.sound'}
COMPILER = {'Lean.ofReduceBool', 'Lean.trustCompiler'}


def pin():
    rev = re.search(r'PICO_REV: &str = "([0-9a-f]{40})"', (ROOT / 'extractor/src/main.rs').read_text())[1]
    return f'Pico commit [`{rev[:9]}`](https://github.com/brevis-network/pico/commit/{rev}).'


def pending():
    files = [l.strip() for l in (ROOT / 'extractor/pending.txt').read_text().splitlines() if l.strip()]
    if not files:
        return 'Every extraction file is generated from the pinned Pico commit.'
    names = ', '.join(f'`{f}`' for f in files)
    return (f'{len(files)} extraction file(s) still predate the pinned commit and are verified against '
            f'the Pico revision named in their first line: {names}.')


def axioms():
    spec = set((CHECK / 'spec-axioms.txt').read_text().split())
    rows = {}
    for line in (CHECK / 'axioms.txt').read_text().splitlines():
        if not line.strip():
            continue
        name, _, axs = line.partition(' ')
        axs = set(filter(None, axs.split(',')))
        key = ('kernel only' if axs <= CORE else
               'kernel + compiler' if axs <= CORE | COMPILER else
               'kernel + compiler + RISC-V spec axioms' if axs <= CORE | COMPILER | spec else
               'OTHER (check.sh rejects this)')
        rows.setdefault(key, []).append(name)
    out = ['| Axioms the theorem depends on | Theorems |', '|---|---:|']
    out += [f'| {k} | {len(v)} |' for k, v in sorted(rows.items())]
    return '\n'.join(out)


def tactics():
    lines = [l.split() for l in (CHECK / 'tactic-baseline.txt').read_text().splitlines() if l.strip()]
    total = sum(int(n) for n, _ in lines)
    out = [f'{total} uses of `native_decide`, `bv_decide` or `decide +native` in {len(lines)} files:', '']
    out += [f'- `{p}`: {n}' for n, p in lines]
    return '\n'.join(out)


BLOCKS = {'pin': pin, 'pending': pending, 'axioms': axioms, 'tactics': tactics}


def render(text):
    for name, fn in BLOCKS.items():
        pat = re.compile(rf'(<!-- generated: {name} -->\n)(?:(?!<!--).)*?(<!-- end generated -->)', re.S)
        if not pat.search(text):
            sys.exit(f'SOUNDNESS.md has no generated block "{name}"')
        text = pat.sub(lambda m: m[1] + fn() + '\n' + m[2], text)
    return text


if __name__ == '__main__':
    path = ROOT / 'SOUNDNESS.md'
    old = path.read_text()
    new = render(old)
    if '--check' in sys.argv[1:]:
        if new != old:
            sys.exit('SOUNDNESS.md is out of date: run python3 scripts/fv-check/soundness_facts.py')
        print('SOUNDNESS.md facts: OK')
    else:
        path.write_text(new)
