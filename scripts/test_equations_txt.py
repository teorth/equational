#!/usr/bin/env python3
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
from generate_eqs_list import format_expr, generate_all_eqs


def generated_formulas():
    return [
        f"{format_expr(lhs)} = {format_expr(rhs)}"
        for lhs, rhs in generate_all_eqs()
    ]


def test_same_length():
    formulas = generated_formulas()
    lines = [ln for ln in Path(__file__).resolve().parent.joinpath("equations.txt").read_text().splitlines() if ln.strip()]
    assert len(formulas) == len(lines) == 4694


if __name__ == "__main__":
    test_same_length()
    print("ok - equations.txt length")
