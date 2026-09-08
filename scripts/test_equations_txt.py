#!/usr/bin/env python3
"""Check scripts/equations.txt against generate_all_eqs numbering."""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from generate_eqs_list import format_expr, generate_all_eqs


def equations_txt():
    return Path(__file__).resolve().parent / "equations.txt"


def generated_formulas():
    return [
        f"{format_expr(lhs)} = {format_expr(rhs)}"
        for lhs, rhs in generate_all_eqs()
    ]


def test_equation1_is_reflexive():
    assert generated_formulas()[0] == "x = x"


def test_same_length():
    formulas = generated_formulas()
    lines = [ln for ln in equations_txt().read_text().splitlines() if ln.strip()]
    assert len(formulas) == len(lines) == 4694


def test_def_headers_are_consecutive():
    lines = equations_txt().read_text().splitlines()
    for i, line in enumerate(lines, 1):
        assert line.startswith(f"def Equation{i} "), i


def test_formulas_appear_in_order():
    formulas = generated_formulas()
    lines = equations_txt().read_text().splitlines()
    for i, formula in enumerate(formulas):
        assert formula in lines[i], (i + 1, formula)


if __name__ == "__main__":
    test_equation1_is_reflexive()
    test_same_length()
    test_def_headers_are_consecutive()
    test_formulas_appear_in_order()
    print("ok - equations.txt")
