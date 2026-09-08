import unittest

from generate_eqs_list import count_vars, lean_binders, VAR_NAMES, format_expr


class BinderTests(unittest.TestCase):
    def test_count_vars_leaf(self):
        self.assertEqual(count_vars(0), 1)
        self.assertEqual(count_vars(2), 3)

    def test_lean_binders(self):
        self.assertEqual(lean_binders(0, 1), 'x y')

    def test_lean_binders_too_many(self):
        too_many = len(VAR_NAMES)
        with self.assertRaises(ValueError):
            lean_binders(too_many, 0)

    def test_format_expr(self):
        self.assertEqual(format_expr((0, 1)), 'x ∘ y')


if __name__ == '__main__':
    unittest.main()
