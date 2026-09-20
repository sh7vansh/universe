import unittest
from core.atomic_engine import synthesize_element, machine, make_nucleon

class TestAtomBaseline(unittest.TestCase):
    def test_oxygen(self):
        base_p = make_nucleon(True, "base")
        res = synthesize_element("Oxygen-16", 8, 8, 15.994915, quiet=True)
        self.assertLess(res['error'], 1.0)

if __name__ == "__main__":
    unittest.main()
