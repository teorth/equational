#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1] / "Equational.lean"


def test_imports_basic():
    text = ROOT.read_text()
    assert "import Equational.Basic" in text
    assert "import «Equational».Basic" not in text


if __name__ == "__main__":
    test_imports_basic()
    print("ok - root import")
