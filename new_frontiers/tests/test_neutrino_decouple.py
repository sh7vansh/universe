import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))
from particle_discovery import discover_particles
from unified_categorical_engine import CategoricalMachine, GrothendieckObject, SimpleObject, ExtensionClass

machine = CategoricalMachine()
electron = machine.get_simple(2)
up = machine.get_simple(3)
anti_down = machine.get_simple(5, is_anti=True)
ext_mass_cancel = ExtensionClass("Neutrino Mass Cancellation", -(electron.mass + up.mass + anti_down.mass))
comp1 = machine.exact_sequence_reconstruction(electron, up)
neutrino = machine.exact_sequence_reconstruction(comp1, anti_down, ext=ext_mass_cancel)

print([str(x) for x in machine.decoupling_algorithm(neutrino)])
