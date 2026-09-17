import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))
from particle_discovery import discover_particles
from unified_categorical_engine import CategoricalMachine, GrothendieckObject, SimpleObject

machine = CategoricalMachine()

void_factor = SimpleObject("Void", 0, 0.0, 0.0)
void = GrothendieckObject(signature=0, mass=0.0, factors=[void_factor])

photon_factor = SimpleObject("Photon", 1, 0.0, 1.0)
photon = GrothendieckObject(signature=-1, mass=0.0, factors=[photon_factor])

print(machine.decoupling_algorithm(photon))
print(machine.decoupling_algorithm(void))

