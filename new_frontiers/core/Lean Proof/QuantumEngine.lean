/-!
  # QuantumEngine.lean
  Categorical Machine and Quantum State Reconstruction Engine in Lean 4.
  Direct, self-contained computational port of `core/quantum_engine.py`.
-/

namespace QuantumEngine

/-- Complex numbers with 64-bit float components. -/
structure ComplexNum where
  re : Float
  im : Float
  deriving Repr, Inhabited, BEq

namespace ComplexNum

def zero : ComplexNum := ⟨0.0, 0.0⟩
def one : ComplexNum := ⟨1.0, 0.0⟩
def I : ComplexNum := ⟨0.0, 1.0⟩

def add (a b : ComplexNum) : ComplexNum :=
  ⟨a.re + b.re, a.im + b.im⟩

def sub (a b : ComplexNum) : ComplexNum :=
  ⟨a.re - b.re, a.im - b.im⟩

def mul (a b : ComplexNum) : ComplexNum :=
  ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩

def smul (s : Float) (a : ComplexNum) : ComplexNum :=
  ⟨s * a.re, s * a.im⟩

def conj (a : ComplexNum) : ComplexNum :=
  ⟨a.re, -a.im⟩

def absSq (a : ComplexNum) : Float :=
  a.re * a.re + a.im * a.im

def absVal (a : ComplexNum) : Float :=
  Float.sqrt (absSq a)

def phase (a : ComplexNum) : Float :=
  Float.atan2 a.im a.re

def expI (theta : Float) : ComplexNum :=
  ⟨Float.cos theta, Float.sin theta⟩

instance : Add ComplexNum := ⟨add⟩
instance : Sub ComplexNum := ⟨sub⟩
instance : Mul ComplexNum := ⟨mul⟩

def toString (c : ComplexNum) : String :=
  let r := c.re
  let i := c.im
  if Float.abs r < 1e-9 && Float.abs i < 1e-9 then "0"
  else if Float.abs r < 1e-9 then s!"{i}j"
  else if Float.abs i < 1e-9 then s!"{r}"
  else if i > 0.0 then s!"{r}+{i}j"
  else s!"{r}{i}j"

instance : ToString ComplexNum := ⟨toString⟩

end ComplexNum

/-- 2x2 Complex matrix representation for categorical representations. -/
structure Mat2 where
  a00 : ComplexNum
  a01 : ComplexNum
  a10 : ComplexNum
  a11 : ComplexNum
  deriving Repr, Inhabited

namespace Mat2

def id : Mat2 :=
  ⟨ComplexNum.one, ComplexNum.zero, ComplexNum.zero, ComplexNum.one⟩

def mul (m1 m2 : Mat2) : Mat2 :=
  ⟨m1.a00 * m2.a00 + m1.a01 * m2.a10,
   m1.a00 * m2.a01 + m1.a01 * m2.a11,
   m1.a10 * m2.a00 + m1.a11 * m2.a10,
   m1.a10 * m2.a01 + m1.a11 * m2.a11⟩

instance : Mul Mat2 := ⟨mul⟩

end Mat2

def PI : Float := 3.14159265358979323846

structure PhysicsConfig where
  mu0 : Float := 1.0
  alpha : Float := (9.0 / (16.0 * (PI ^ 3.0))) * ((PI / 120.0) ^ 0.25)
  wylerAlpha : Float := (9.0 / (16.0 * (PI ^ 3.0))) * ((PI / 120.0) ^ 0.25)
  alphaInv : Float := 1.0 / ((9.0 / (16.0 * (PI ^ 3.0))) * ((PI / 120.0) ^ 0.25))
  phi : Float := (1.0 + Float.sqrt 5.0) / 2.0
  deriving Repr

def CONFIG : PhysicsConfig := {}

def universalMass (p : Nat) (gaugeFriction : Float) : Float :=
  if p == 0 || p == 1 then 0.0
  else CONFIG.mu0 * (((p.toFloat - 1.0) / 2.0) + gaugeFriction)

def F_E : Float := 1.5 * CONFIG.alpha + CONFIG.alpha ^ 2.0
def F_U : Float := 2.0 / Float.sqrt 3.0
def F_D : Float := 8.0 / 3.0
def F_STRANGE : Float := CONFIG.alphaInv - 45.0
def F_CHARM : Float := (Float.sqrt 3.0) ^ 13.0
def F_BOTTOM : Float := F_STRANGE * (CONFIG.alphaInv / 3.0)
def F_TOP : Float := F_STRANGE ^ F_D

def M_E : Float := universalMass 2 F_E
def M_U : Float := universalMass 3 F_U
def M_D : Float := universalMass 5 F_D
def M_MUON : Float := (M_E * 1.5 * CONFIG.alphaInv) + (CONFIG.mu0 / CONFIG.phi)
def F_MUON : Float := (M_MUON / CONFIG.mu0) - (11.0 - 1.0) / 2.0
def M_TAU : Float := (13.0 * CONFIG.alphaInv * CONFIG.mu0) - M_D
def F_TAU : Float := (M_TAU / CONFIG.mu0) - (17.0 - 1.0) / 2.0

def F_PI : Float := F_STRANGE * CONFIG.mu0
def GEOMETRIC_SCALAR : Float := 0.5 + 1.5 * CONFIG.alpha + CONFIG.alpha ^ 2.0
def VACUUM_DENSITY : Float := 0.5 * PI * Float.log (2.0 * PI) * CONFIG.alphaInv * Float.sqrt (GEOMETRIC_SCALAR * (CONFIG.mu0 ^ 2.0))
def CHIRAL_CONDENSATE : Float := - (VACUUM_DENSITY ^ 3.0)
def M_PI : Float := Float.sqrt (- ((M_U + M_D) * CHIRAL_CONDENSATE) / (F_PI ^ 2.0))

def NUCLEON_CONDENSATE : Float :=
  let noise := Float.log (2.0 * PI)
  let viscosity := 0.5
  (noise ^ 2.0) * (1.0 - (1.0 / (viscosity ^ 2.0)) / Float.sqrt CONFIG.alphaInv)

def KAPPA_RESIDUAL : Float :=
  let viscosity := 0.5
  let res := - (NUCLEON_CONDENSATE * (1.0 / (viscosity ^ 2.0))) * CONFIG.mu0
  res

structure SimpleObject where
  name : String
  identifier : Nat
  mass : Float
  spin : Float
  color : Option String := none
  isAnti : Bool := false
  deriving Repr, Inhabited

def lookupGenerator (p : Nat) : Option SimpleObject :=
  match p with
  | 0 => some ⟨"Void", 0, 0.0, 0.0, none, false⟩
  | 1 => some ⟨"Photon", 1, 0.0, 1.0, none, false⟩
  | 2 => some ⟨"Electron", 2, universalMass 2 F_E, 0.5, none, false⟩
  | 3 => some ⟨"Up Quark", 3, universalMass 3 F_U, 0.5, none, false⟩
  | 5 => some ⟨"Down Quark", 5, universalMass 5 F_D, 0.5, none, false⟩
  | 7 => some ⟨"Strange Quark", 7, universalMass 7 F_STRANGE, 0.5, none, false⟩
  | 11 => some ⟨"Muon", 11, universalMass 11 F_MUON, 0.5, none, false⟩
  | 13 => some ⟨"Charm Quark", 13, universalMass 13 F_CHARM, 0.5, none, false⟩
  | 17 => some ⟨"Tau", 17, universalMass 17 F_TAU, 0.5, none, false⟩
  | 19 => some ⟨"Bottom Quark", 19, universalMass 19 F_BOTTOM, 0.5, none, false⟩
  | 23 => some ⟨"Top Quark", 23, universalMass 23 F_TOP, 0.5, none, false⟩
  | _ => none

structure ExtensionClass where
  name : String
  bindingEnergy : Float
  virtualNodes : List SimpleObject := []
  deriving Repr, Inhabited

structure GrothendieckObject where
  signature : ComplexNum
  mass : Float
  factors : List SimpleObject := []
  extensions : List ExtensionClass := []
  matrix : Mat2 := Mat2.id
  deriving Repr, Inhabited

namespace GrothendieckObject

def spin (obj : GrothendieckObject) : Float :=
  if obj.signature.absVal < 1e-9 then 0.0
  else
    let rawSpin := obj.signature.phase / PI
    let rounded := Float.round (rawSpin * 100000.0) / 100000.0
    if Float.abs rounded < 1e-9 then 0.0 else rounded

def toString (obj : GrothendieckObject) : String :=
  let comp := obj.factors.map SimpleObject.name
  s!"GrothendieckObject(Signature={obj.signature}, Mass={obj.mass}, Spin={obj.spin}, Composition={comp})"

instance : ToString GrothendieckObject := ⟨toString⟩

end GrothendieckObject

def getZN (obj : GrothendieckObject) : Int × Int :=
  if obj.factors.isEmpty then (0, 0)
  else
    let u := (obj.factors.filter (fun f => f.identifier == 3)).length.toFloat
    let d := (obj.factors.filter (fun f => f.identifier == 5)).length.toFloat
    let z := Float.round ((2.0 * u - d) / 3.0)
    let n := Float.round ((2.0 * d - u) / 3.0)
    (z.toInt64.toInt, n.toInt64.toInt)

def isMagic (x : Nat) : Bool :=
  [2, 8, 20, 28, 50, 82, 126].contains x

def geomFriction (Z N : Nat) (nucleonCondensate : Option Float := none) : Float :=
  let Atot := Z + N
  if Atot <= 1 then 0.0
  else
    let wAlpha := CONFIG.wylerAlpha
    let wylerFactor := 1.0 - wAlpha + wAlpha ^ 2.0 - wAlpha ^ 3.0
    if Z == 1 && N == 1 then
      0.25 / wylerFactor
    else
      let dim : Float := (min (Atot - 1) 3).toFloat
      let boundaryExponent := if dim > 0.0 then (dim - 1.0) / dim else 0.0
      let cond := match nucleonCondensate with | some c => c | none => Float.sqrt 5.0
      let AtotF := Atot.toFloat
      let a3Deficit :=
        if Atot > 4 then
          let eNuc := 5.0 * M_PI - (44.0 / 27.0)
          let deltaA3 := 1.0 - Float.sqrt (3.0 / 8.0)
          let effScale := wylerFactor * (cond * 4.0) * CONFIG.mu0
          let a3FrictionPerNuc := (CONFIG.alpha * deltaA3 * (eNuc / 4.0)) / effScale
          AtotF * a3FrictionPerNuc
        else 0.0
      let rank := (6.0 / PI) * AtotF - a3Deficit

      let boundaryDegradation := cond * (AtotF ^ boundaryExponent)
      let topologicalKissingNumber := 12.0
      let ZF := Z.toFloat
      let NF := N.toFloat
      let phaseInterference :=
        if Atot > 0 then (topologicalKissingNumber * CONFIG.alpha) * ZF * (ZF - 1.0) / (AtotF ^ (1.0 / 3.0)) else 0.0

      let complexOrthogonality := 2.0 * Float.sqrt 2.0
      let parityViolation := complexOrthogonality * ((NF - ZF) ^ 2.0) / AtotF
      let su4Wigner := complexOrthogonality * Float.abs (NF - ZF) / AtotF

      let riemannViscosity := 0.5
      let volumetricDampener := 1.0 / (AtotF ^ (1.0 / 3.0))
      let extTowerLimit := PI / 4.0

      let pairingBonus :=
        if Z % 2 == 0 && N % 2 == 0 then riemannViscosity / (AtotF ^ 0.5)
        else if Z % 2 != 0 && N % 2 != 0 then -riemannViscosity / (AtotF ^ 0.5)
        else 0.0

      let alphaClusterBonus :=
        if Z % 2 == 0 && N % 2 == 0 && Z == N && (!isMagic Z || Atot == 4) then
          (riemannViscosity * 2.0) / (AtotF ^ (1.0 / 3.0))
        else 0.0

      let chiralCurrentBonus :=
        if Z % 2 != 0 && N % 2 == 0 then
          (riemannViscosity * CONFIG.alpha) / (AtotF ^ (1.0 / 3.0))
        else 0.0

      let cohomologicalClosure :=
        if Atot == 4 then extTowerLimit * volumetricDampener
        else
          (if isMagic Z then extTowerLimit * volumetricDampener else 0.0) +
          (if isMagic N then extTowerLimit * volumetricDampener else 0.0)

      rank - boundaryDegradation - phaseInterference - parityViolation - su4Wigner +
        pairingBonus + alphaClusterBonus + chiralCurrentBonus + cohomologicalClosure

structure CategoricalMachine where
  mU : Float := M_U
  mD : Float := M_D
  fPi : Float := F_PI
  chiralCondensate : Float := CHIRAL_CONDENSATE
  mPi : Float := M_PI
  kappaSpin : Float := M_PI / 9.0
  kappaEm : Float := 11.0 / 3.0
  kappaConfinement : Float := M_PI
  nucleonCondensate : Float := NUCLEON_CONDENSATE
  kappaResidual : Float := KAPPA_RESIDUAL
  deriving Repr, Inhabited

namespace CategoricalMachine

def defaultMachine : CategoricalMachine := {}

def getSimple (_ : CategoricalMachine) (prime : Nat) (isAnti : Bool := false) (color : Option String := none) : GrothendieckObject :=
  let simp : SimpleObject :=
    match lookupGenerator prime with
    | none => ⟨s!"Unknown Simple ({prime})", prime, 0.0, 0.5, color, isAnti⟩
    | some base =>
      let name :=
        if prime == 0 || prime == 1 then base.name
        else if isAnti then s!"Anti-{base.name}"
        else base.name
      ⟨name, prime, base.mass, base.spin, color, isAnti⟩

  let valF := prime.toFloat * (if isAnti then -1.0 else 1.0)
  let mat : Mat2 :=
    if prime == 0 then Mat2.id
    else
      ⟨⟨valF, 0.0⟩, ⟨0.0, 1.0⟩,
       ⟨0.0, -1.0⟩, ⟨-valF, 0.0⟩⟩
  let mag : Float :=
    if prime == 0 then 0.0
    else if isAnti then 1.0 / prime.toFloat
    else prime.toFloat
  let sig :=
    if mag == 0.0 then ComplexNum.zero
    else (ComplexNum.expI (PI * simp.spin)).smul mag
  ⟨sig, simp.mass, [simp], [], mat⟩

def isColorSinglet (_ : CategoricalMachine) (obj : GrothendieckObject) : Bool :=
  let (red, green, blue) := Id.run do
    let mut r := 0
    let mut g := 0
    let mut b := 0
    for f in obj.factors do
      if let some c := f.color then
        let base := (c.splitOn "_").headD ""
        let val := if f.isAnti then -1 else 1
        if base == "red" then r := r + val
        if base == "green" then g := g + val
        if base == "blue" then b := b + val
    return (r, g, b)
  !obj.factors.isEmpty && red == green && green == blue

def exactSequenceReconstruction (_ : CategoricalMachine) (A B : GrothendieckObject) (ext : Option ExtensionClass := none) : Except String GrothendieckObject := do
  for f1 in A.factors do
    for f2 in B.factors do
      let isFermion := Float.abs (f1.spin - Float.round f1.spin) > 1e-6
      if isFermion && f1.identifier == f2.identifier &&
         Float.abs (f1.spin - f2.spin) < 1e-6 &&
         f1.color == f2.color && f1.isAnti == f2.isAnti then
        throw s!"Pauli Exclusion Principle violation: Identical fermions {f1.name} (color={f1.color}) cannot occupy the same state."

  let sigC := A.signature * B.signature
  let mut massC := A.mass + B.mass
  let mut extList := A.extensions ++ B.extensions
  let matC := A.matrix * B.matrix

  if let some e := ext then
    let vNodes := if e.virtualNodes.isEmpty then A.factors ++ B.factors else e.virtualNodes
    let eCopy : ExtensionClass := { e with virtualNodes := vNodes }
    massC := massC + eCopy.bindingEnergy
    extList := extList ++ [eCopy]

  return ⟨sigC, massC, A.factors ++ B.factors, extList, matC⟩

def exactSequenceReconstruction! (m : CategoricalMachine) (A B : GrothendieckObject) (ext : Option ExtensionClass := none) : GrothendieckObject :=
  match m.exactSequenceReconstruction A B ext with
  | Except.ok res => res
  | Except.error err => panic! err

def calculateFriction (m : CategoricalMachine) (A B : GrothendieckObject) : Float :=
  if m.isColorSinglet A && m.isColorSinglet B then
    let (zA, nA) := getZN A
    let (zB, nB) := getZN B
    let cond := some m.nucleonCondensate
    let zTot := (zA + zB).toNat
    let nTot := (nA + nB).toNat
    geomFriction zTot nTot cond - (geomFriction zA.toNat nA.toNat cond + geomFriction zB.toNat nB.toNat cond)
  else
    let lenA := if m.isColorSinglet A then 1.0 else A.factors.length.toFloat
    let lenB := if m.isColorSinglet B then 1.0 else B.factors.length.toFloat
    let virtA := if m.isColorSinglet A then 0.0 else (A.extensions.map (fun (e : ExtensionClass) => e.virtualNodes.length)).sum.toFloat
    let virtB := if m.isColorSinglet B then 0.0 else (B.extensions.map (fun (e : ExtensionClass) => e.virtualNodes.length)).sum.toFloat
    virtA + virtB + lenA + lenB

def confinementBind (m : CategoricalMachine) (A B : GrothendieckObject) (name : String) : Except String GrothendieckObject := do
  let deltaL := m.calculateFriction A B
  let (parallelScalar, antiScalar) := Id.run do
    let mut pSum := 0.0
    let mut aSum := 0.0
    for f1 in A.factors do
      for f2 in B.factors do
        let p := ComplexNum.expI (PI * f1.spin) * ComplexNum.expI (-PI * f2.spin)
        let a := ComplexNum.expI (PI * f1.spin) * ComplexNum.expI (PI * f2.spin)
        pSum := pSum + p.re
        aSum := aSum + a.re
    return (pSum, aSum)

  let (spinScalar, actualB) :=
    if antiScalar < parallelScalar then
      (antiScalar, { B with signature := B.signature.conj, factors := B.factors.map fun f => { f with spin := -f.spin } })
    else
      (parallelScalar, B)

  let getCharge (f : SimpleObject) : Float :=
    if f.identifier == 3 then (2.0 / 3.0) * (if f.isAnti then -1.0 else 1.0)
    else if f.identifier == 5 then (-1.0 / 3.0) * (if f.isAnti then -1.0 else 1.0)
    else 0.0

  let electrostaticScalar := Id.run do
    let mut es := 0.0
    for f1 in A.factors do
      for f2 in B.factors do
        es := es + getCharge f1 * getCharge f2
    return es

  let combinedFactors := A.factors ++ actualB.factors
  let dummyObj : GrothendieckObject := ⟨ComplexNum.zero, 0.0, combinedFactors, [], Mat2.id⟩
  let singletScreening :=
    if m.isColorSinglet dummyObj then
      - CONFIG.alpha * (1.0 - 1.0 / Float.sqrt 3.0) * m.kappaConfinement
    else 0.0

  let bindingEnergy :=
    (deltaL * m.kappaConfinement) + (m.kappaSpin * spinScalar) + (m.kappaEm * electrostaticScalar) + singletScreening
  let ext : ExtensionClass := ⟨name, bindingEnergy, combinedFactors⟩
  m.exactSequenceReconstruction A actualB (some ext)

def confinementBind! (m : CategoricalMachine) (A B : GrothendieckObject) (name : String) : GrothendieckObject :=
  match m.confinementBind A B name with
  | Except.ok res => res
  | Except.error err => panic! err

def nuclearBind (m : CategoricalMachine) (A B : GrothendieckObject) (name : String) : Except String GrothendieckObject := do
  let totalFriction := m.calculateFriction A B / (1.0 + CONFIG.alpha)
  let bindingEnergy := totalFriction * m.kappaResidual
  let ext : ExtensionClass := ⟨name, bindingEnergy, A.factors ++ B.factors⟩
  m.exactSequenceReconstruction A B (some ext)

def nuclearBind! (m : CategoricalMachine) (A B : GrothendieckObject) (name : String) : GrothendieckObject :=
  match m.nuclearBind A B name with
  | Except.ok res => res
  | Except.error err => panic! err

def electroweakBind (m : CategoricalMachine) (A B : GrothendieckObject) (name : String) (bindingEnergy : Float := -0.0000136) : Except String GrothendieckObject := do
  let ext : ExtensionClass := ⟨name, bindingEnergy, A.factors ++ B.factors⟩
  m.exactSequenceReconstruction A B (some ext)

def electroweakBind! (m : CategoricalMachine) (A B : GrothendieckObject) (name : String) (bindingEnergy : Float := -0.0000136) : GrothendieckObject :=
  match m.electroweakBind A B name bindingEnergy with
  | Except.ok res => res
  | Except.error err => panic! err

end CategoricalMachine

end QuantumEngine

open QuantumEngine

def main : IO Unit := do
  let m := CategoricalMachine.defaultMachine

  IO.println "========================================="
  IO.println "   QUANTUM ENGINE (LEAN 4 SHOWCASE)"
  IO.println "========================================="

  let void := m.getSimple 0
  let photon := m.getSimple 1
  IO.println s!"[+] Vacuum State (Bosons):"
  IO.println s!"    Void: {void}"
  IO.println s!"    Photon: {photon}"

  let electron := m.getSimple 2
  let muon := m.getSimple 11
  let tau := m.getSimple 17
  IO.println s!"
[+] Leptons (Gen 1-3):"
  IO.println s!"    Electron: {electron}"
  IO.println s!"    Muon:     {muon}"
  IO.println s!"    Tau:      {tau}"

  let upRed := m.getSimple 3 false (some "red")
  let downGreen := m.getSimple 5 false (some "green")
  let strange := m.getSimple 7
  let charm := m.getSimple 13
  let bottom := m.getSimple 19
  let top := m.getSimple 23
  IO.println s!"
[+] Quarks (Gen 1-3):"
  IO.println s!"    Up:      {upRed}"
  IO.println s!"    Down:    {downGreen}"
  IO.println s!"    Strange: {strange}"
  IO.println s!"    Charm:   {charm}"
  IO.println s!"    Bottom:  {bottom}"
  IO.println s!"    Top:     {top}"

  -- Neutrinos (Reconstructed via Exact Sequences with Mass Cancellation)
  let antiDown := m.getSimple 5 true (some "green")
  let extCancelE : ExtensionClass := ⟨"Neutrino Mass Cancellation", -(electron.mass + upRed.mass + antiDown.mass), []⟩
  let comp1 ← IO.ofExcept (m.exactSequenceReconstruction electron upRed)
  let eNeutrino ← IO.ofExcept (m.exactSequenceReconstruction comp1 antiDown (some extCancelE))

  let antiStrange := m.getSimple 7 true (some "green")
  let charmRed := m.getSimple 13 false (some "red")
  let extCancelMu : ExtensionClass := ⟨"Muon Neutrino Mass Cancellation", -(muon.mass + charmRed.mass + antiStrange.mass), []⟩
  let comp2 ← IO.ofExcept (m.exactSequenceReconstruction muon charmRed)
  let muNeutrino ← IO.ofExcept (m.exactSequenceReconstruction comp2 antiStrange (some extCancelMu))

  let antiBottom := m.getSimple 19 true (some "green")
  let topRed := m.getSimple 23 false (some "red")
  let extCancelTau : ExtensionClass := ⟨"Tau Neutrino Mass Cancellation", -(tau.mass + topRed.mass + antiBottom.mass), []⟩
  let comp3 ← IO.ofExcept (m.exactSequenceReconstruction tau topRed)
  let tauNeutrino ← IO.ofExcept (m.exactSequenceReconstruction comp3 antiBottom (some extCancelTau))

  IO.println s!"
[+] Neutrinos:"
  IO.println s!"    e_nu:   {eNeutrino}"
  IO.println s!"    mu_nu:  {muNeutrino}"
  IO.println s!"    tau_nu: {tauNeutrino}"

  -- Electroweak & Higgs Bosons
  let sinSqTheta : Float := 2.0 / 9.0
  let cosTheta := Float.sqrt (1.0 - sinSqTheta)
  let mW : Float := 80.377
  let mZ := mW / cosTheta
  let alphaVal := 1.0 / CONFIG.alphaInv
  let gVal := 3.0 * Float.sqrt (2.0 * PI * alphaVal)
  let mH := mW / gVal
  IO.println s!"
[+] Electroweak & Higgs Bosons:"
  IO.println s!"    W Boson Mass:   {mW} GeV"
  IO.println s!"    Z Boson Mass:   {mZ} GeV"
  IO.println s!"    Weak Coupling:  {gVal}"
  IO.println s!"    Higgs Mass:     {mH} GeV"

  -- Nucleons (Color-Singlet Baryons)
  let q1 := m.getSimple 3 false (some "red_p")
  let q2 := m.getSimple 3 false (some "blue_p")
  let q3 := m.getSimple 5 false (some "green_p")
  let diq ← IO.ofExcept (m.confinementBind q1 q2 "DiQ")
  let proton ← IO.ofExcept (m.confinementBind diq q3 "Nuc")

  let qn1 := m.getSimple 3 false (some "red_n")
  let qn2 := m.getSimple 5 false (some "blue_n")
  let qn3 := m.getSimple 5 false (some "green_n")
  let diqn ← IO.ofExcept (m.confinementBind qn1 qn2 "DiQ_n")
  let neutron ← IO.ofExcept (m.confinementBind diqn qn3 "Nuc_n")

  IO.println s!"
[+] Nucleons (Color-Singlet Baryons):"
  IO.println s!"    Proton:  Mass = {proton.mass} MeV, Spin = {proton.spin}"
  IO.println s!"    Neutron: Mass = {neutron.mass} MeV, Spin = {neutron.spin}"

  -- Deuteron Binding
  let deuteron ← IO.ofExcept (m.nuclearBind proton neutron "Deuteron")
  let bindingE := deuteron.mass - (proton.mass + neutron.mass)
  IO.println s!"
[+] Residual Nuclear Binding (Deuteron):"
  IO.println s!"    Deuteron Mass:  {deuteron.mass} MeV"
  IO.println s!"    Binding Energy: {bindingE} MeV"

  -- Pauli Exclusion Principle Check
  let qRedDup1 := m.getSimple 3 false (some "red_state")
  let qRedDup2 := m.getSimple 3 false (some "red_state")
  match m.exactSequenceReconstruction qRedDup1 qRedDup2 with
  | Except.ok _ => IO.println "
[!] Pauli exclusion check: FAILED (forbidden state allowed)"
  | Except.error e => IO.println s!"
[+] Pauli Exclusion Check: PASSED (caught: {e})"

  IO.println "========================================="
