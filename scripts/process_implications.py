#! /usr/bin/env python3

from collections import defaultdict
import os
from random import sample
import re
from sys import argv


def transitive_closure(pairs):
    new_pairs = closure = set(pairs)
    while new_pairs:
        new_pairs = {
            (a, d)
            for a, b in new_pairs
            for c, d in pairs
            if b == c
        } - closure
        closure |= new_pairs
    return closure


def get_unknown_implications(universe, known_implies, known_not_implies):
    all_implications = transitive_closure(known_implies)

    fwd_implications = defaultdict(set)
    bwd_implications = defaultdict(set)
    for a, b in all_implications:
        fwd_implications[a].add(b)
        bwd_implications[b].add(a)

    all_negative_implications = set(
        (c, d)
        for a, b in known_not_implies
        for c in fwd_implications[a]
        for d in bwd_implications[b]
    )

    return set((a, b) for a in universe for b in universe) - all_implications - all_negative_implications


THEOREM_ALWAYS = re.compile(
    r'theorem\s+\S+\s+.*\[Magma\s+G\]\s*:\s*(Equation\d+)\s+G\s*:='
)
THEOREM_IMPLIES = re.compile(
    r'theorem\s+\S+\s+.*\[Magma\s+G\]\s*\([^:]*:\s*(Equation\d+)\s+G\)\s*:\s*(Equation\d+)\s+G\s*:='
)
THEOREM_REFUTE = re.compile(
    r'theorem\s+.*:\s*∃.*\(_\s*:\s*Magma\s+G\),\s*(Equation\d+)\s+G\s*∧\s*¬\s*(Equation\d+)\s+G\s*:='
)


def parse_proofs_file(file_name):
    """Read equation defs and implication theorems from a Lean file.

    This still does not check that the proofs are correct; it only reads
    the statement of each theorem. Hypothesis names like `h` or `h1` are
    accepted, not just a single character.
    """
    universe = []
    known_implies, known_not_implies = set(), set()
    with open(file_name, encoding="utf-8") as handle:
        for line in handle:
            if m := re.match(r'def\s+(Equation\d+)\s+', line):
                universe.append(m.group(1))
                known_implies.add((m.group(1), m.group(1)))
            elif m := THEOREM_ALWAYS.match(line):
                for eq in universe:
                    known_implies.add((eq, m.group(1)))
            elif m := THEOREM_IMPLIES.match(line):
                known_implies.add((m.group(1), m.group(2)))
            elif m := THEOREM_REFUTE.match(line):
                known_not_implies.add((m.group(1), m.group(2)))
    return universe, known_implies, known_not_implies


def main(argv=argv):
    try:
        file_name = argv[1]
        assert os.path.exists(file_name)
    except (IndexError, AssertionError):
        print('Usage: python process_implications.py <file_name.lean>')
        return 1

    universe, known_implies, known_not_implies = parse_proofs_file(file_name)

    all_unknown = get_unknown_implications(universe, known_implies, known_not_implies)

    print(f'Found {len(all_unknown)} unknown implications')
    if all_unknown:
        k = min(10, len(all_unknown))
        if k < len(all_unknown):
            print('Sample of', k, 'unknown implications:')
        for a, b in sample(list(all_unknown), k):
            print(f'{a} => {b}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
