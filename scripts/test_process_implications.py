import os
import tempfile
import unittest

from process_implications import parse_proofs_file, get_unknown_implications, transitive_closure


SAMPLE = r'''
def Equation1 (G: Type*) [Magma G] := ∀ x : G, x = x
def Equation2 (G: Type*) [Magma G] := ∀ x y : G, x = y
def Equation4 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ y

theorem Equation11_true (G: Type*) [Magma G] : Equation1 G :=
  fun _ => rfl

theorem Equation1_implies_Equation2 (G: Type*) [Magma G] (h : Equation2 G) : Equation4 G :=
  fun _ _ => h _ _
'''


class ParseTests(unittest.TestCase):
    def test_always_true_and_named_hypothesis(self):
        with tempfile.NamedTemporaryFile('w', suffix='.lean', delete=False) as tmp:
            tmp.write(SAMPLE)
            path = tmp.name
        try:
            universe, implies, refutes = parse_proofs_file(path)
        finally:
            os.unlink(path)
        self.assertEqual(universe, ['Equation1', 'Equation2', 'Equation4'])
        self.assertIn(('Equation2', 'Equation1'), implies)
        self.assertIn(('Equation2', 'Equation4'), implies)
        self.assertEqual(refutes, set())

    def test_transitive_unknown(self):
        unknown = get_unknown_implications(
            ['A', 'B'],
            {('A', 'A'), ('B', 'B'), ('A', 'B')},
            set(),
        )
        self.assertEqual(unknown, {('B', 'A')})

    def test_closure(self):
        self.assertEqual(transitive_closure({('A', 'B'), ('B', 'C')}), {('A', 'B'), ('B', 'C'), ('A', 'C')})


if __name__ == '__main__':
    unittest.main()
