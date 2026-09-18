import sys
import os
import readline

# Ensure we can import the engine from the same directory
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
from unified_categorical_engine import CategoricalMachine

def main():
    print("=========================================")
    print(" Categorical Atom Synthesizer")
    print("=========================================")
    
    machine = CategoricalMachine()
    
    def make_nucleon(is_proton, suffix):
        q1 = machine.get_simple(3, color=f"red_{suffix}")
        q2 = machine.get_simple(3 if is_proton else 5, color=f"blue_{suffix}")
        q3 = machine.get_simple(5 if is_proton else 5, color=f"green_{suffix}")
        return machine.confinement_bind(machine.confinement_bind(q1, q2, "DiQ"), q3, "Nuc")

    PERIODIC_TABLE = {
        "h": {"name": "Hydrogen-1", "Z": 1, "N": 0, "true_u": 1.007825},
        "hydrogen": {"name": "Hydrogen-1", "Z": 1, "N": 0, "true_u": 1.007825},
        "he": {"name": "Helium-4", "Z": 2, "N": 2, "true_u": 4.002603},
        "helium": {"name": "Helium-4", "Z": 2, "N": 2, "true_u": 4.002603},
        "li": {"name": "Lithium-7", "Z": 3, "N": 4, "true_u": 7.016003},
        "lithium": {"name": "Lithium-7", "Z": 3, "N": 4, "true_u": 7.016003},
        "be": {"name": "Beryllium-9", "Z": 4, "N": 5, "true_u": 9.012183},
        "beryllium": {"name": "Beryllium-9", "Z": 4, "N": 5, "true_u": 9.012183},
        "b": {"name": "Boron-11", "Z": 5, "N": 6, "true_u": 11.009305},
        "boron": {"name": "Boron-11", "Z": 5, "N": 6, "true_u": 11.009305},
        "c": {"name": "Carbon-12", "Z": 6, "N": 6, "true_u": 12.0},
        "carbon": {"name": "Carbon-12", "Z": 6, "N": 6, "true_u": 12.0},
        "n": {"name": "Nitrogen-14", "Z": 7, "N": 7, "true_u": 14.003074},
        "nitrogen": {"name": "Nitrogen-14", "Z": 7, "N": 7, "true_u": 14.003074},
        "o": {"name": "Oxygen-16", "Z": 8, "N": 8, "true_u": 15.994915},
        "oxygen": {"name": "Oxygen-16", "Z": 8, "N": 8, "true_u": 15.994915},
        "f": {"name": "Fluorine-19", "Z": 9, "N": 10, "true_u": 18.998403},
        "fluorine": {"name": "Fluorine-19", "Z": 9, "N": 10, "true_u": 18.998403},
        "ne": {"name": "Neon-20", "Z": 10, "N": 10, "true_u": 19.99244},
        "neon": {"name": "Neon-20", "Z": 10, "N": 10, "true_u": 19.99244},
        "na": {"name": "Sodium-23", "Z": 11, "N": 12, "true_u": 22.989769},
        "sodium": {"name": "Sodium-23", "Z": 11, "N": 12, "true_u": 22.989769},
        "mg": {"name": "Magnesium-24", "Z": 12, "N": 12, "true_u": 23.985042},
        "magnesium": {"name": "Magnesium-24", "Z": 12, "N": 12, "true_u": 23.985042},
        "al": {"name": "Aluminum-27", "Z": 13, "N": 14, "true_u": 26.981538},
        "aluminum": {"name": "Aluminum-27", "Z": 13, "N": 14, "true_u": 26.981538},
        "si": {"name": "Silicon-28", "Z": 14, "N": 14, "true_u": 27.976926},
        "silicon": {"name": "Silicon-28", "Z": 14, "N": 14, "true_u": 27.976926},
        "p": {"name": "Phosphorus-31", "Z": 15, "N": 16, "true_u": 30.973761},
        "phosphorus": {"name": "Phosphorus-31", "Z": 15, "N": 16, "true_u": 30.973761},
        "s": {"name": "Sulfur-32", "Z": 16, "N": 16, "true_u": 31.972071},
        "sulfur": {"name": "Sulfur-32", "Z": 16, "N": 16, "true_u": 31.972071},
        "cl": {"name": "Chlorine-35", "Z": 17, "N": 18, "true_u": 34.968852},
        "chlorine": {"name": "Chlorine-35", "Z": 17, "N": 18, "true_u": 34.968852},
        "ar": {"name": "Argon-40", "Z": 18, "N": 22, "true_u": 39.962383},
        "argon": {"name": "Argon-40", "Z": 18, "N": 22, "true_u": 39.962383},
        "k": {"name": "Potassium-39", "Z": 19, "N": 20, "true_u": 38.963706},
        "potassium": {"name": "Potassium-39", "Z": 19, "N": 20, "true_u": 38.963706},
        "ca": {"name": "Calcium-40", "Z": 20, "N": 20, "true_u": 39.96259},
        "calcium": {"name": "Calcium-40", "Z": 20, "N": 20, "true_u": 39.96259},
        "sc": {"name": "Scandium-45", "Z": 21, "N": 24, "true_u": 44.955912},
        "scandium": {"name": "Scandium-45", "Z": 21, "N": 24, "true_u": 44.955912},
        "ti": {"name": "Titanium-48", "Z": 22, "N": 26, "true_u": 47.947946},
        "titanium": {"name": "Titanium-48", "Z": 22, "N": 26, "true_u": 47.947946},
        "v": {"name": "Vanadium-51", "Z": 23, "N": 28, "true_u": 50.943959},
        "vanadium": {"name": "Vanadium-51", "Z": 23, "N": 28, "true_u": 50.943959},
        "cr": {"name": "Chromium-52", "Z": 24, "N": 28, "true_u": 51.940507},
        "chromium": {"name": "Chromium-52", "Z": 24, "N": 28, "true_u": 51.940507},
        "mn": {"name": "Manganese-55", "Z": 25, "N": 30, "true_u": 54.938045},
        "manganese": {"name": "Manganese-55", "Z": 25, "N": 30, "true_u": 54.938045},
        "fe": {"name": "Iron-56", "Z": 26, "N": 30, "true_u": 55.934937},
        "iron": {"name": "Iron-56", "Z": 26, "N": 30, "true_u": 55.934937},
        "co": {"name": "Cobalt-59", "Z": 27, "N": 32, "true_u": 58.933195},
        "cobalt": {"name": "Cobalt-59", "Z": 27, "N": 32, "true_u": 58.933195},
        "ni": {"name": "Nickel-58", "Z": 28, "N": 30, "true_u": 57.935342},
        "nickel": {"name": "Nickel-58", "Z": 28, "N": 30, "true_u": 57.935342},
        "cu": {"name": "Copper-63", "Z": 29, "N": 34, "true_u": 62.929597},
        "copper": {"name": "Copper-63", "Z": 29, "N": 34, "true_u": 62.929597},
        "zn": {"name": "Zinc-64", "Z": 30, "N": 34, "true_u": 63.929142},
        "zinc": {"name": "Zinc-64", "Z": 30, "N": 34, "true_u": 63.929142},
        "ga": {"name": "Gallium-69", "Z": 31, "N": 38, "true_u": 68.925573},
        "gallium": {"name": "Gallium-69", "Z": 31, "N": 38, "true_u": 68.925573},
        "ge": {"name": "Germanium-74", "Z": 32, "N": 42, "true_u": 73.921177},
        "germanium": {"name": "Germanium-74", "Z": 32, "N": 42, "true_u": 73.921177},
        "as": {"name": "Arsenic-75", "Z": 33, "N": 42, "true_u": 74.921596},
        "arsenic": {"name": "Arsenic-75", "Z": 33, "N": 42, "true_u": 74.921596},
        "se": {"name": "Selenium-80", "Z": 34, "N": 46, "true_u": 79.916521},
        "selenium": {"name": "Selenium-80", "Z": 34, "N": 46, "true_u": 79.916521},
        "br": {"name": "Bromine-79", "Z": 35, "N": 44, "true_u": 78.918337},
        "bromine": {"name": "Bromine-79", "Z": 35, "N": 44, "true_u": 78.918337},
        "kr": {"name": "Krypton-84", "Z": 36, "N": 48, "true_u": 83.911507},
        "krypton": {"name": "Krypton-84", "Z": 36, "N": 48, "true_u": 83.911507},
        "rb": {"name": "Rubidium-85", "Z": 37, "N": 48, "true_u": 84.911789},
        "rubidium": {"name": "Rubidium-85", "Z": 37, "N": 48, "true_u": 84.911789},
        "sr": {"name": "Strontium-88", "Z": 38, "N": 50, "true_u": 87.905612},
        "strontium": {"name": "Strontium-88", "Z": 38, "N": 50, "true_u": 87.905612},
        "y": {"name": "Yttrium-89", "Z": 39, "N": 50, "true_u": 88.905848},
        "yttrium": {"name": "Yttrium-89", "Z": 39, "N": 50, "true_u": 88.905848},
        "zr": {"name": "Zirconium-90", "Z": 40, "N": 50, "true_u": 89.904704},
        "zirconium": {"name": "Zirconium-90", "Z": 40, "N": 50, "true_u": 89.904704},
        "nb": {"name": "Niobium-93", "Z": 41, "N": 52, "true_u": 92.906378},
        "niobium": {"name": "Niobium-93", "Z": 41, "N": 52, "true_u": 92.906378},
        "mo": {"name": "Molybdenum-98", "Z": 42, "N": 56, "true_u": 97.905408},
        "molybdenum": {"name": "Molybdenum-98", "Z": 42, "N": 56, "true_u": 97.905408},
        "tc": {"name": "Technetium-98", "Z": 43, "N": 55, "true_u": 97.907212},
        "technetium": {"name": "Technetium-98", "Z": 43, "N": 55, "true_u": 97.907212},
        "ru": {"name": "Ruthenium-102", "Z": 44, "N": 58, "true_u": 101.904349},
        "ruthenium": {"name": "Ruthenium-102", "Z": 44, "N": 58, "true_u": 101.904349},
        "rh": {"name": "Rhodium-103", "Z": 45, "N": 58, "true_u": 102.905504},
        "rhodium": {"name": "Rhodium-103", "Z": 45, "N": 58, "true_u": 102.905504},
        "pd": {"name": "Palladium-106", "Z": 46, "N": 60, "true_u": 105.903486},
        "palladium": {"name": "Palladium-106", "Z": 46, "N": 60, "true_u": 105.903486},
        "ag": {"name": "Silver-107", "Z": 47, "N": 60, "true_u": 106.905097},
        "silver": {"name": "Silver-107", "Z": 47, "N": 60, "true_u": 106.905097},
        "cd": {"name": "Cadmium-114", "Z": 48, "N": 66, "true_u": 113.903365},
        "cadmium": {"name": "Cadmium-114", "Z": 48, "N": 66, "true_u": 113.903365},
        "in": {"name": "Indium-115", "Z": 49, "N": 66, "true_u": 114.903878},
        "indium": {"name": "Indium-115", "Z": 49, "N": 66, "true_u": 114.903878},
        "sn": {"name": "Tin-120", "Z": 50, "N": 70, "true_u": 119.902196},
        "tin": {"name": "Tin-120", "Z": 50, "N": 70, "true_u": 119.902196},
        "sb": {"name": "Antimony-121", "Z": 51, "N": 70, "true_u": 120.903815},
        "antimony": {"name": "Antimony-121", "Z": 51, "N": 70, "true_u": 120.903815},
        "te": {"name": "Tellurium-130", "Z": 52, "N": 78, "true_u": 129.906224},
        "tellurium": {"name": "Tellurium-130", "Z": 52, "N": 78, "true_u": 129.906224},
        "i": {"name": "Iodine-127", "Z": 53, "N": 74, "true_u": 126.904473},
        "iodine": {"name": "Iodine-127", "Z": 53, "N": 74, "true_u": 126.904473},
        "xe": {"name": "Xenon-132", "Z": 54, "N": 78, "true_u": 131.904153},
        "xenon": {"name": "Xenon-132", "Z": 54, "N": 78, "true_u": 131.904153},
        "cs": {"name": "Cesium-133", "Z": 55, "N": 78, "true_u": 132.905451},
        "cesium": {"name": "Cesium-133", "Z": 55, "N": 78, "true_u": 132.905451},
        "ba": {"name": "Barium-138", "Z": 56, "N": 82, "true_u": 137.905247},
        "barium": {"name": "Barium-138", "Z": 56, "N": 82, "true_u": 137.905247},
        "la": {"name": "Lanthanum-139", "Z": 57, "N": 82, "true_u": 138.906353},
        "lanthanum": {"name": "Lanthanum-139", "Z": 57, "N": 82, "true_u": 138.906353},
        "ce": {"name": "Cerium-140", "Z": 58, "N": 82, "true_u": 139.905438},
        "cerium": {"name": "Cerium-140", "Z": 58, "N": 82, "true_u": 139.905438},
        "pr": {"name": "Praseodymium-141", "Z": 59, "N": 82, "true_u": 140.907652},
        "praseodymium": {"name": "Praseodymium-141", "Z": 59, "N": 82, "true_u": 140.907652},
        "nd": {"name": "Neodymium-142", "Z": 60, "N": 82, "true_u": 141.907723},
        "neodymium": {"name": "Neodymium-142", "Z": 60, "N": 82, "true_u": 141.907723},
        "pm": {"name": "Promethium-145", "Z": 61, "N": 84, "true_u": 145},
        "promethium": {"name": "Promethium-145", "Z": 61, "N": 84, "true_u": 145},
        "sm": {"name": "Samarium-150", "Z": 62, "N": 88, "true_u": 150.362},
        "samarium": {"name": "Samarium-150", "Z": 62, "N": 88, "true_u": 150.362},
        "eu": {"name": "Europium-152", "Z": 63, "N": 89, "true_u": 151.9641},
        "europium": {"name": "Europium-152", "Z": 63, "N": 89, "true_u": 151.9641},
        "gd": {"name": "Gadolinium-157", "Z": 64, "N": 93, "true_u": 157.253},
        "gadolinium": {"name": "Gadolinium-157", "Z": 64, "N": 93, "true_u": 157.253},
        "tb": {"name": "Terbium-159", "Z": 65, "N": 94, "true_u": 158.925352},
        "terbium": {"name": "Terbium-159", "Z": 65, "N": 94, "true_u": 158.925352},
        "dy": {"name": "Dysprosium-163", "Z": 66, "N": 97, "true_u": 162.5001},
        "dysprosium": {"name": "Dysprosium-163", "Z": 66, "N": 97, "true_u": 162.5001},
        "ho": {"name": "Holmium-165", "Z": 67, "N": 98, "true_u": 164.930332},
        "holmium": {"name": "Holmium-165", "Z": 67, "N": 98, "true_u": 164.930332},
        "er": {"name": "Erbium-167", "Z": 68, "N": 99, "true_u": 167.2593},
        "erbium": {"name": "Erbium-167", "Z": 68, "N": 99, "true_u": 167.2593},
        "tm": {"name": "Thulium-169", "Z": 69, "N": 100, "true_u": 168.934222},
        "thulium": {"name": "Thulium-169", "Z": 69, "N": 100, "true_u": 168.934222},
        "yb": {"name": "Ytterbium-173", "Z": 70, "N": 103, "true_u": 173.0451},
        "ytterbium": {"name": "Ytterbium-173", "Z": 70, "N": 103, "true_u": 173.0451},
        "lu": {"name": "Lutetium-175", "Z": 71, "N": 104, "true_u": 174.96681},
        "lutetium": {"name": "Lutetium-175", "Z": 71, "N": 104, "true_u": 174.96681},
        "hf": {"name": "Hafnium-178", "Z": 72, "N": 106, "true_u": 178.492},
        "hafnium": {"name": "Hafnium-178", "Z": 72, "N": 106, "true_u": 178.492},
        "ta": {"name": "Tantalum-181", "Z": 73, "N": 108, "true_u": 180.947882},
        "tantalum": {"name": "Tantalum-181", "Z": 73, "N": 108, "true_u": 180.947882},
        "w": {"name": "Tungsten-184", "Z": 74, "N": 110, "true_u": 183.841},
        "tungsten": {"name": "Tungsten-184", "Z": 74, "N": 110, "true_u": 183.841},
        "re": {"name": "Rhenium-186", "Z": 75, "N": 111, "true_u": 186.2071},
        "rhenium": {"name": "Rhenium-186", "Z": 75, "N": 111, "true_u": 186.2071},
        "os": {"name": "Osmium-190", "Z": 76, "N": 114, "true_u": 190.233},
        "osmium": {"name": "Osmium-190", "Z": 76, "N": 114, "true_u": 190.233},
        "ir": {"name": "Iridium-192", "Z": 77, "N": 115, "true_u": 192.2173},
        "iridium": {"name": "Iridium-192", "Z": 77, "N": 115, "true_u": 192.2173},
        "pt": {"name": "Platinum-195", "Z": 78, "N": 117, "true_u": 195.0849},
        "platinum": {"name": "Platinum-195", "Z": 78, "N": 117, "true_u": 195.0849},
        "au": {"name": "Gold-197", "Z": 79, "N": 118, "true_u": 196.9665695},
        "gold": {"name": "Gold-197", "Z": 79, "N": 118, "true_u": 196.9665695},
        "hg": {"name": "Mercury-201", "Z": 80, "N": 121, "true_u": 200.5923},
        "mercury": {"name": "Mercury-201", "Z": 80, "N": 121, "true_u": 200.5923},
        "tl": {"name": "Thallium-204", "Z": 81, "N": 123, "true_u": 204.38},
        "thallium": {"name": "Thallium-204", "Z": 81, "N": 123, "true_u": 204.38},
        "pb": {"name": "Lead-207", "Z": 82, "N": 125, "true_u": 207.21},
        "lead": {"name": "Lead-207", "Z": 82, "N": 125, "true_u": 207.21},
        "bi": {"name": "Bismuth-209", "Z": 83, "N": 126, "true_u": 208.980401},
        "bismuth": {"name": "Bismuth-209", "Z": 83, "N": 126, "true_u": 208.980401},
        "po": {"name": "Polonium-209", "Z": 84, "N": 125, "true_u": 209},
        "polonium": {"name": "Polonium-209", "Z": 84, "N": 125, "true_u": 209},
        "at": {"name": "Astatine-210", "Z": 85, "N": 125, "true_u": 210},
        "astatine": {"name": "Astatine-210", "Z": 85, "N": 125, "true_u": 210},
        "rn": {"name": "Radon-222", "Z": 86, "N": 136, "true_u": 222},
        "radon": {"name": "Radon-222", "Z": 86, "N": 136, "true_u": 222},
        "fr": {"name": "Francium-223", "Z": 87, "N": 136, "true_u": 223},
        "francium": {"name": "Francium-223", "Z": 87, "N": 136, "true_u": 223},
        "ra": {"name": "Radium-226", "Z": 88, "N": 138, "true_u": 226},
        "radium": {"name": "Radium-226", "Z": 88, "N": 138, "true_u": 226},
        "ac": {"name": "Actinium-227", "Z": 89, "N": 138, "true_u": 227},
        "actinium": {"name": "Actinium-227", "Z": 89, "N": 138, "true_u": 227},
        "th": {"name": "Thorium-232", "Z": 90, "N": 142, "true_u": 232.03774},
        "thorium": {"name": "Thorium-232", "Z": 90, "N": 142, "true_u": 232.03774},
        "pa": {"name": "Protactinium-231", "Z": 91, "N": 140, "true_u": 231.035882},
        "protactinium": {"name": "Protactinium-231", "Z": 91, "N": 140, "true_u": 231.035882},
        "u": {"name": "Uranium-238", "Z": 92, "N": 146, "true_u": 238.028913},
        "uranium": {"name": "Uranium-238", "Z": 92, "N": 146, "true_u": 238.028913},
        "np": {"name": "Neptunium-237", "Z": 93, "N": 144, "true_u": 237},
        "neptunium": {"name": "Neptunium-237", "Z": 93, "N": 144, "true_u": 237},
        "pu": {"name": "Plutonium-244", "Z": 94, "N": 150, "true_u": 244},
        "plutonium": {"name": "Plutonium-244", "Z": 94, "N": 150, "true_u": 244},
        "am": {"name": "Americium-243", "Z": 95, "N": 148, "true_u": 243},
        "americium": {"name": "Americium-243", "Z": 95, "N": 148, "true_u": 243},
        "cm": {"name": "Curium-247", "Z": 96, "N": 151, "true_u": 247},
        "curium": {"name": "Curium-247", "Z": 96, "N": 151, "true_u": 247},
        "bk": {"name": "Berkelium-247", "Z": 97, "N": 150, "true_u": 247},
        "berkelium": {"name": "Berkelium-247", "Z": 97, "N": 150, "true_u": 247},
        "cf": {"name": "Californium-251", "Z": 98, "N": 153, "true_u": 251},
        "californium": {"name": "Californium-251", "Z": 98, "N": 153, "true_u": 251},
        "es": {"name": "Einsteinium-252", "Z": 99, "N": 153, "true_u": 252},
        "einsteinium": {"name": "Einsteinium-252", "Z": 99, "N": 153, "true_u": 252},
        "fm": {"name": "Fermium-257", "Z": 100, "N": 157, "true_u": 257},
        "fermium": {"name": "Fermium-257", "Z": 100, "N": 157, "true_u": 257},
        "md": {"name": "Mendelevium-258", "Z": 101, "N": 157, "true_u": 258},
        "mendelevium": {"name": "Mendelevium-258", "Z": 101, "N": 157, "true_u": 258},
        "no": {"name": "Nobelium-259", "Z": 102, "N": 157, "true_u": 259},
        "nobelium": {"name": "Nobelium-259", "Z": 102, "N": 157, "true_u": 259},
        "lr": {"name": "Lawrencium-266", "Z": 103, "N": 163, "true_u": 266},
        "lawrencium": {"name": "Lawrencium-266", "Z": 103, "N": 163, "true_u": 266},
        "rf": {"name": "Rutherfordium-267", "Z": 104, "N": 163, "true_u": 267},
        "rutherfordium": {"name": "Rutherfordium-267", "Z": 104, "N": 163, "true_u": 267},
        "db": {"name": "Dubnium-268", "Z": 105, "N": 163, "true_u": 268},
        "dubnium": {"name": "Dubnium-268", "Z": 105, "N": 163, "true_u": 268},
        "sg": {"name": "Seaborgium-269", "Z": 106, "N": 163, "true_u": 269},
        "seaborgium": {"name": "Seaborgium-269", "Z": 106, "N": 163, "true_u": 269},
        "bh": {"name": "Bohrium-270", "Z": 107, "N": 163, "true_u": 270},
        "bohrium": {"name": "Bohrium-270", "Z": 107, "N": 163, "true_u": 270},
        "hs": {"name": "Hassium-269", "Z": 108, "N": 161, "true_u": 269},
        "hassium": {"name": "Hassium-269", "Z": 108, "N": 161, "true_u": 269},
        "mt": {"name": "Meitnerium-278", "Z": 109, "N": 169, "true_u": 278},
        "meitnerium": {"name": "Meitnerium-278", "Z": 109, "N": 169, "true_u": 278},
        "ds": {"name": "Darmstadtium-281", "Z": 110, "N": 171, "true_u": 281},
        "darmstadtium": {"name": "Darmstadtium-281", "Z": 110, "N": 171, "true_u": 281},
        "rg": {"name": "Roentgenium-282", "Z": 111, "N": 171, "true_u": 282},
        "roentgenium": {"name": "Roentgenium-282", "Z": 111, "N": 171, "true_u": 282},
        "cn": {"name": "Copernicium-285", "Z": 112, "N": 173, "true_u": 285},
        "copernicium": {"name": "Copernicium-285", "Z": 112, "N": 173, "true_u": 285},
        "nh": {"name": "Nihonium-286", "Z": 113, "N": 173, "true_u": 286},
        "nihonium": {"name": "Nihonium-286", "Z": 113, "N": 173, "true_u": 286},
        "fl": {"name": "Flerovium-289", "Z": 114, "N": 175, "true_u": 289},
        "flerovium": {"name": "Flerovium-289", "Z": 114, "N": 175, "true_u": 289},
        "mc": {"name": "Moscovium-289", "Z": 115, "N": 174, "true_u": 289},
        "moscovium": {"name": "Moscovium-289", "Z": 115, "N": 174, "true_u": 289},
        "lv": {"name": "Livermorium-293", "Z": 116, "N": 177, "true_u": 293},
        "livermorium": {"name": "Livermorium-293", "Z": 116, "N": 177, "true_u": 293},
        "ts": {"name": "Tennessine-294", "Z": 117, "N": 177, "true_u": 294},
        "tennessine": {"name": "Tennessine-294", "Z": 117, "N": 177, "true_u": 294},
        "og": {"name": "Oganesson-294", "Z": 118, "N": 176, "true_u": 294},
        "oganesson": {"name": "Oganesson-294", "Z": 118, "N": 176, "true_u": 294},
    }
    
    # Setup autocomplete
    db_keys = list(PERIODIC_TABLE.keys()) + ["custom", "quit", "batch"]
    def completer(text, state):
        options = [k for k in db_keys if k.startswith(text.lower())]
        if state < len(options):
            match = options[state]
            return match.capitalize() if len(match) > 2 else match
        return None

    readline.parse_and_bind("tab: complete")
    readline.set_completer(completer)

    print("Bootstrapping nuclear residual scale...")
    base_p = make_nucleon(True, "base")
    machine.calculate_residual_scale(base_p.mass)

    def synthesize_element(name, Z, N, true_u, quiet=False):
        if not quiet:
            print(f"\n[+] Synthesizing {name} [Z={Z}, N={N}]...")
        
        # 1. Build Nucleus
        nucleus = make_nucleon(True, f"{name}_p0")
        for i in range(1, Z):
            nucleus = machine.nuclear_bind(nucleus, make_nucleon(True, f"{name}_p{i}"), f"{name}_p{i}")
        for i in range(N):
            nucleus = machine.nuclear_bind(nucleus, make_nucleon(False, f"{name}_n{i}"), f"{name}_n{i}")
            
        # 2. Bind Electrons
        atom = nucleus
        for i in range(Z):
            e = machine.get_simple(2, color=f"shell_{i}")
            if i % 2 == 1:
                e.factors[0].spin = -0.5
                e.signature = e.signature.conjugate()
            atom = machine.electroweak_bind(atom, e, f"{name}_e{i}", binding_energy=0.0)
            
        # Calculate masses and composition
        proton_mass = 938.346 
        neutron_mass = 939.635
        electron_mass = 0.511
        parts_mass = (Z * proton_mass) + (N * neutron_mass) + (Z * electron_mass)
        mass_defect = atom.mass - parts_mass
        
        u_quarks = sum(1 for f in atom.factors if f.identifier == 3)
        d_quarks = sum(1 for f in atom.factors if f.identifier == 5)
        electrons = sum(1 for f in atom.factors if f.identifier == 2)
        
        import cmath
        phase = cmath.phase(atom.signature)
        
        error_margin = None
        accuracy = None
        true_mass_mev = None
        
        if true_u is not None:
            true_mass_mev = true_u * 931.4941
            error_margin = abs(atom.mass - true_mass_mev)
            error_pct = 100 * (error_margin / true_mass_mev)
            accuracy = 100 - error_pct
            
        if not quiet:
            print("\n=========================================")
            print(f" Synthesis Complete: {name}")
            print("=========================================")
            print(f" [ Mass Analysis ]")
            print(f"   Theoretical Mass : {atom.mass:,.3f} MeV")
            print(f"   Isolated Parts   : {parts_mass:,.3f} MeV")
            print(f"   Mass Defect (BE) : {mass_defect:,.3f} MeV")
            print(f"   Binding/Nucleon  : {mass_defect / (Z+N):,.3f} MeV")
            
            if true_mass_mev is not None:
                print()
                print(f" [ Accuracy & Error ]")
                print(f"   True Mass        : {true_mass_mev:,.3f} MeV")
                print(f"   Model Error      : {error_margin:,.3f} MeV")
                print(f"   Error Percentage : {error_pct:.4f}%")
                print(f"   Model Accuracy   : {accuracy:.4f}%")
                
            print()
            print(f" [ Categorical Composition ]")
            print(f"   Total Particles  : {len(atom.factors)}")
            print(f"   Up Quarks        : {u_quarks}")
            print(f"   Down Quarks      : {d_quarks}")
            print(f"   Electrons        : {electrons}")
            print()
            print(f" [ Quantum State ]")
            print(f"   Net Spin         : {atom.spin}")
            print(f"   Signature Mag.   : {abs(atom.signature):.3e}")
            print(f"   Signature Phase  : {phase:.3f} rad")
            print("=========================================\n")
            
        return {
            "name": name, "Z": Z, "N": N, "mass": atom.mass, 
            "error": error_margin, "error_pct": error_pct, "accuracy": accuracy
        }

    while True:
        print("\nType an element symbol (e.g. 'Fe'), name ('Iron'), 'custom', or 'batch'. (Tab to autocomplete, 'q' to quit)")
        query = input("> ").strip().lower()
        
        true_u = None
        if query in ('q', 'quit', 'exit'):
            break
            
        if query == 'batch':
            print("\n[+] Running batch synthesis over entire periodic database...\n")
            symbols = sorted([k for k in PERIODIC_TABLE.keys() if len(k) <= 2], key=lambda k: PERIODIC_TABLE[k]["Z"])
            
            print(f"{'Element':<15} | {'Z':<3} | {'N':<3} | {'Pred Mass (MeV)':<16} | {'Error (MeV)':<12} | {'Error %':<9} | {'Accuracy'}")
            print("-" * 88)
            
            total_acc = 0.0
            count = 0
            for sym in symbols:
                data = PERIODIC_TABLE[sym]
                res = synthesize_element(data["name"], data["Z"], data["N"], data.get("true_u"), quiet=True)
                
                acc_str = f"{res['accuracy']:.4f}%" if res['accuracy'] is not None else "N/A"
                err_str = f"{res['error']:.3f}" if res['error'] is not None else "N/A"
                err_pct_str = f"{res['error_pct']:.4f}%" if res['error_pct'] is not None else "N/A"
                print(f"{res['name']:<15} | {res['Z']:<3} | {res['N']:<3} | {res['mass']:<16,.3f} | {err_str:<12} | {err_pct_str:<9} | {acc_str}")
                
                if res['accuracy'] is not None:
                    total_acc += res['accuracy']
                    count += 1
                    
            if count > 0:
                print("-" * 88)
                print(f"Average Accuracy across {count} elements: {total_acc/count:.4f}%\n")
            continue
            
        if query in PERIODIC_TABLE:
            data = PERIODIC_TABLE[query]
            synthesize_element(data["name"], data["Z"], data["N"], data.get("true_u"))
        elif query == 'custom':
            readline.set_completer(None) # disable autocomplete for custom entry
            name = input("Atom Name (e.g. Gold-197): ").strip()
            try:
                Z = int(input("Number of Protons (Z): ").strip())
                N = int(input("Number of Neutrons (N): ").strip())
            except ValueError:
                print("Please enter valid integers for Z and N.")
                readline.set_completer(completer)
                continue
            readline.set_completer(completer)
            
            if Z < 1 or N < 0:
                print("Z must be >= 1 and N >= 0.")
                continue
                
            synthesize_element(name, Z, N, None)
        else:
            matches = [k.capitalize() for k in db_keys if query in k and k not in ('custom', 'quit', 'batch')]
            if matches:
                print(f"Unknown element. Did you mean: {', '.join(matches[:5])}?")
            else:
                print(f"Unknown command '{query}'. Try 'batch', 'custom', or press Tab.")
            continue

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\nExiting...")
        sys.exit(0)
