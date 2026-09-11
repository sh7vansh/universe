import re

with open("MathProject/CategoricalColimits.lean", "r") as f:
    content = f.read()

# Add WellPowered import
content = content.replace(
    "import Mathlib.CategoryTheory.Subobject.Lattice",
    "import Mathlib.CategoryTheory.Subobject.Lattice\nimport Mathlib.CategoryTheory.Subobject.WellPowered"
)

# Add WellPowered to variable A
content = content.replace(
    "variable {A : Type*} [Category A] [Abelian A] [HasColimits A]",
    "variable {A : Type*} [Category A] [Abelian A] [HasColimits A] [WellPowered A]"
)

with open("MathProject/CategoricalColimits.lean", "w") as f:
    f.write(content)
