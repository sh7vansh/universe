import Mathlib

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]
#check Module.rank ℤ (WeierstrassCurve.Projective.Point E)
