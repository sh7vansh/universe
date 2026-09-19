import sys
sys.path.append('src/hierarchical')
from atomic_engine import synthesize_element, machine, make_nucleon

def test_oxygen():
    base_p = make_nucleon(True, "base")
    machine.calculate_residual_scale(base_p.mass)
    res = synthesize_element("Oxygen-16", 8, 8, 15.994915, quiet=True)
    print(f"Oxygen-16 Pred Mass: {res['mass']:.3f} MeV, Error: {res['error']:.3f} MeV")

test_oxygen()
