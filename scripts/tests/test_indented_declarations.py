import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "process_implications.py"

class IndentedDeclarationsTests(unittest.TestCase):
    def test_namespace_indentation_preserves_implications(self):
        declarations = """import Equational.Basic
namespace Example
  def Equation1 (G: Type*) [Magma G] := ∀ x : G, x = x
  def Equation2 (G: Type*) [Magma G] := ∀ x y : G, x = y
  theorem same [Magma G] (h: Equation2 G) : Equation1 G := by
    intro x
    rfl
end Example
"""
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Example.lean"
            source.write_text(declarations)
            result = subprocess.run([sys.executable, str(SCRIPT), str(source)],
                                    capture_output=True, text=True, check=True)
        self.assertIn("Found 1 unknown implications", result.stdout)
        self.assertIn("Equation1 => Equation2", result.stdout)

if __name__ == "__main__":
    unittest.main()
