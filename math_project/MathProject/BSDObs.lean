import Mathlib

open WeierstrassCurve

-- 1. The Elliptic Curve over ℚ
variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

-- 2. The Mordell-Weil Group E(ℚ)
#check Projective.Point E

-- 3. The Algebraic Rank (free rank of E(ℚ))
#check Module.rank ℤ (Projective.Point E)

-- 4. The L-Series L(E, s)
#check E.LSeries
