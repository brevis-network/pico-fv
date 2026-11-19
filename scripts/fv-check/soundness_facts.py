"""Fills the generated blocks of SOUNDNESS.md, README.md and the parked-lists README from the
repository, so the facts that change with the code stay true on every commit.

  python3 scripts/fv-check/soundness_facts.py           rewrite the blocks
  python3 scripts/fv-check/soundness_facts.py --check   fail if a block is out of date
"""
import pathlib, re, sys, textwrap

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


def instruction_lists(directory):
    """The instruction-theorem lists in `directory`, as {class file: [opcode, ...]}: the list
    `equivalence-shift-i-op.txt` names the theorems of `Equivalence/ShiftIOp.lean`."""
    out = {}
    for path in sorted(directory.glob('equivalence-*.txt')):
        module = ''.join(part.capitalize() for part in path.stem.removeprefix('equivalence-').split('-'))
        if not (ROOT / f'PicoFV/RV64IM/Equivalence/{module}.lean').exists():
            sys.exit(f'{path.relative_to(ROOT)} names no file Equivalence/{module}.lean')
        out[module] = [l.strip().removeprefix('Equivalence.equivalence_')
                       for l in path.read_text().splitlines() if l.strip()]
    return out


def checked():
    return instruction_lists(CHECK / 'theorems.d')


def parked():
    return instruction_lists(CHECK / 'theorems.d/parked')


def count(lists):
    return sum(len(v) for v in lists.values())


def opcodes(names):
    names = [f'`{n}`' for n in names]
    return names[0] if len(names) == 1 else ', '.join(names[:-1]) + ' and ' + names[-1]


def plural(n, word):
    """`n` with `word` pluralised, so a single parked file does not read "1 files"."""
    return f'{n} {word}' if n == 1 else f'{n} {word}s'


def fill(text, width=80, **kw):
    return textwrap.fill(text, width, break_long_words=False, break_on_hyphens=False, **kw)


def by_file(lists, width):
    return [fill(f'- `{m}.lean`: {opcodes(v)}', width, subsequent_indent='  ') for m, v in lists.items()]


def restored_detail():
    done, rest = checked(), parked()
    # SOUNDNESS.md keeps lines to 100 characters, and the block sits in a list item (2 more).
    width = 98
    out = [fill(f'**{count(done)} of these {count(done) + count(rest)} theorems are checked at the '
                f'moment**, in {plural(len(done), "file")} of `PicoFV/RV64IM/Equivalence/`:', width), '']
    out += by_file(done, width)
    out += ['', fill(f'The other {count(rest)}, in {plural(len(rest), "file")}, are out of the build, with their '
                     'lists parked in `scripts/fv-check/theorems.d/parked/`:', width), '']
    out += by_file(rest, width)
    return '\n'.join(out)


def restored_summary():
    done, rest = checked(), parked()
    names = sorted(n for v in done.values() for n in v)
    text = (f'For now the branch proves {len(names)} of them against the v3.1.1 chip: {opcodes(names)}. '
            f'The other {count(rest)} are out of the build and `check.sh` does not check them (see '
            '[SOUNDNESS.md](SOUNDNESS.md)).')
    return fill(text)


def parked_summary():
    done, rest = checked(), parked()
    verb = 'names' if len(rest) == 1 else 'name'
    text = (f'The {plural(len(rest), "list")} here {verb} {count(rest)} of the '
            f'{count(done) + count(rest)} instruction theorems of `PicoFV/RV64IM/Equivalence/`.')
    return fill(text)


# Each file's generated blocks. A block that appears in a file more than once is filled each time.
FILES = {
    'SOUNDNESS.md': {'restored': restored_detail, 'pin': pin, 'pending': pending, 'axioms': axioms,
                     'tactics': tactics},
    'README.md': {'restored': restored_summary},
    'scripts/fv-check/theorems.d/parked/README.md': {'parked': parked_summary},
}


def render(file, text):
    """Fills each block of `file`, indented as its opening marker is (a block inside a list item
    keeps the item's indentation)."""
    for name, fn in FILES[file].items():
        pat = re.compile(rf'^([ \t]*)(<!-- generated: {name} -->\n)(?:(?!<!--).)*?(<!-- end generated -->)',
                         re.S | re.M)
        if not pat.search(text):
            sys.exit(f'{file} has no generated block "{name}"')
        text = pat.sub(lambda m: m[1] + m[2] + textwrap.indent(fn(), m[1]) + '\n' + m[1] + m[3], text)
    return text


if __name__ == '__main__':
    stale = []
    for file in FILES:
        path = ROOT / file
        old = path.read_text()
        new = render(file, old)
        if new != old:
            stale.append(file)
            if '--check' not in sys.argv[1:]:
                path.write_text(new)
    if '--check' in sys.argv[1:]:
        if stale:
            sys.exit(f'{", ".join(stale)} out of date: run python3 scripts/fv-check/soundness_facts.py')
        print('generated facts: OK')
