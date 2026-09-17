import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))
from fractions import Fraction
from unified_categorical_engine import CategoricalMachine, GrothendieckObject

machine = CategoricalMachine()

# Test 1: Unknown prime
print("Test 1: Unknown Prime (e.g. 31)")
obj1 = GrothendieckObject(signature=31, mass=0)
res1 = machine.decoupling_algorithm(obj1)
print(f"Decoupled 31 into: {[str(x) for x in res1]}")

# Test 2: Partial decoupling
print("\nTest 2: Partial Decoupling of Hydrogen (90) to preserve Proton (-45j)")
hydrogen = GrothendieckObject(signature=90, mass=948.7)
res2 = machine.partial_decoupling(hydrogen, [-45j])
print(f"Decoupled 90 (targets=[-45j]) into: {[str(x) for x in res2]}")
