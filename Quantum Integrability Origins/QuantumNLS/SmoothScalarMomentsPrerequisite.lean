import QuantumNLS.SmoothScalarMomentsBinding
import QuantumNLS.ClassicalCharges

/-! The SINGLE permitted missing prerequisite of R-275B7656.
This is a proposition/interface, not an axiom or an asserted theorem. It carries
the printed R-3FEAD88B conclusion, including independent complex variables,
H^S neighbourhoods, uniqueness/holomorphy, differentiated remainders, compact
positive-coupling uniformity and the real restriction. No moment or Cauchy
expansion occurs in this interface. The base coefficient convention is supplied separately by the frozen
RiccatiChargeIdent module; it is NOT a hypothesis in this interface.
Frozen value estimates are proved separately in RiccatiExpansions and are reused.
-/
set_option autoImplicit false
noncomputable section
open Set
namespace QuantumNLS.SmoothScalarMomentsPrerequisite
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE2
open QuantumNLS.RiccatiSobolevE2b QuantumNLS.RiccatiChargeLevels
open QuantumNLS.RiccatiExpansions QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.RiccatiPicardBall QuantumNLS.RiccatiRemainder
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.RiccatiSobolevS
open QuantumNLS.ClassicalCharges

variable (L : ℝ) [Fact (0 < L)]

/-- An algebraic extension of the spatial derivative, proved to exist by
linear algebra. Its existence is not part of the missing prerequisite. -/
def derivativeExtension : Ell2 →ₗ[ℂ] Ell2 :=
  Classical.choose (dmulLin L).exists_extend

omit [Fact (0 < L)] in
lemma derivativeExtension_spec (y : dDom L) :
    derivativeExtension L (y : Ell2) = dmulEll L y := by
  have h := Classical.choose_spec (dmulLin L).exists_extend
  exact congrArg (fun A : dDom L →ₗ[ℂ] Ell2 => A y) h

/-- The independent-field coefficients in the physical normalization κ,
represented in the bottom H^a model. -/
def coeffs (a S κ : ℝ) (hL : 0 < L) (ha : 1 / 2 < a)
    (D : Ell2 →ₗ[ℂ] Ell2) (p : Ell2 × Ell2) (n : ℕ) : Ell2 :=
  wAbs (mulLin hL ha) D (lowT L a S p.2) (lowT L a S p.1) ((κ / L : ℝ) : ℂ) n

def logTrace (a S κ : ℝ) (ha : 1 / 2 < a) (z : ℂ) (p : Ell2 × Ell2) : ℂ :=
  Complex.log (Complex.exp (Complex.I * z * (L : ℂ) / 2) *
    QuantumNLS.ComplexifiedDiscriminant.cxDisc κ
      (fieldMap L a (by linarith) (lowT L a S p.1))
      (fieldMap L a (by linarith) (lowT L a S p.2)) z)

/-- Complete local output of the printed proposition at a smooth real-slice
base. All bounds use one C,R on K × V; a smaller V is allowed by the proposition.
The Banach space Ell2, read at weight S, is exactly the frozen H^S model. -/
structure LocalOutput (f : ℝ → ℂ) (M : ℕ) (a S δ : ℝ) (K : Set ℝ)
    (hL : 0 < L) (ha : 1 / 2 < a) where
  base : Ell2
  base_rep : physRep L a (lowT L a S base) = f
  V : Set (Ell2 × Ell2)
  open_V : IsOpen V
  base_mem : (base, jEll base) ∈ V
  R : ℝ
  R_pos : 0 < R
  C : ℝ
  C_pos : 0 < C
  rf : ℝ → ℂ → (Ell2 × Ell2) → Ell2
  fixed : ∀ κ ∈ K, ∀ z : ℂ, R ≤ ‖z‖ → δ * ‖z‖ ≤ z.im → (hz : 0 < z.im) →
    ∀ p ∈ V, riccatiT hL ha hz (κ / L) (lowT L a S p.1) (lowT L a S p.2) (rf κ z p) = rf κ z p
  small : ∀ κ ∈ K, ∀ z : ℂ, R ≤ ‖z‖ → δ * ‖z‖ ≤ z.im →
    ∀ p ∈ V, ‖rf κ z p‖ ≤ C / z.im
  unique_small : ∀ κ ∈ K, ∀ z : ℂ, R ≤ ‖z‖ → δ * ‖z‖ ≤ z.im → (hz : 0 < z.im) →
    ∀ p ∈ V, ∀ q : Ell2, ‖q‖ ≤ C / z.im →
      riccatiT hL ha hz (κ / L) (lowT L a S p.1) (lowT L a S p.2) q = q → q = rf κ z p
  holomorphic : ∀ κ ∈ K, ∀ z : ℂ, R ≤ ‖z‖ → δ * ‖z‖ ≤ z.im →
    AnalyticOnNhd ℂ (rf κ z) V
  r_remainder_C1 : ∀ κ ∈ K, ∀ z : ℂ, R ≤ ‖z‖ → δ * ‖z‖ ≤ z.im →
    ContDiffOn ℂ 1 (fun p => rf κ z p - rMsum (coeffs L a S κ hL ha (derivativeExtension L) p) (z⁻¹) M) V
  r_remainder : ∀ κ ∈ K, ∀ z : ℂ, R ≤ ‖z‖ → δ * ‖z‖ ≤ z.im → ∀ p ∈ V,
    ‖rf κ z p - rMsum (coeffs L a S κ hL ha (derivativeExtension L) p) (z⁻¹) M‖ ≤ C * (‖z‖ ^ (M + 1))⁻¹ ∧
    ‖fderiv ℂ (fun p => rf κ z p - rMsum (coeffs L a S κ hL ha (derivativeExtension L) p) (z⁻¹) M) p‖
      ≤ C * (‖z‖ ^ (M + 1))⁻¹
  trace_near_one : ∀ κ ∈ K, ∀ z : ℂ, R ≤ ‖z‖ → δ * ‖z‖ ≤ z.im → ∀ p ∈ V,
    ‖Complex.exp (Complex.I * z * (L : ℂ) / 2) *
      QuantumNLS.ComplexifiedDiscriminant.cxDisc κ
        (fieldMap L a (by linarith) (lowT L a S p.1))
        (fieldMap L a (by linarith) (lowT L a S p.2)) z - 1‖ ≤ 1 / 2
  log_remainder_C1 : ∀ κ ∈ K, ∀ z : ℂ, R ≤ ‖z‖ → δ * ‖z‖ ≤ z.im →
    ContDiffOn ℂ 1 (fun p => logTrace L a S κ ha z p - Complex.I * (κ : ℂ) *
      ∑ n ∈ Finset.Icc 1 M, modeCoef L a (lowT L a S p.2) (coeffs L a S κ hL ha (derivativeExtension L) p n) * (z⁻¹) ^ n) V
  log_remainder : ∀ κ ∈ K, ∀ z : ℂ, R ≤ ‖z‖ → δ * ‖z‖ ≤ z.im → ∀ p ∈ V,
    ‖logTrace L a S κ ha z p - Complex.I * (κ : ℂ) *
      ∑ n ∈ Finset.Icc 1 M, modeCoef L a (lowT L a S p.2) (coeffs L a S κ hL ha (derivativeExtension L) p n) * (z⁻¹) ^ n‖
      ≤ C * (‖z‖ ^ (M + 1))⁻¹ ∧
    ‖fderiv ℂ (fun p => logTrace L a S κ ha z p - Complex.I * (κ : ℂ) *
      ∑ n ∈ Finset.Icc 1 M, modeCoef L a (lowT L a S p.2) (coeffs L a S κ hL ha (derivativeExtension L) p n) * (z⁻¹) ^ n) p‖
      ≤ C * (‖z‖ ^ (M + 1))⁻¹
  real_C1 : ∀ κ ∈ K, ∀ z : ℂ, R ≤ ‖z‖ → δ * ‖z‖ ≤ z.im →
    ContDiffOn ℝ 1 (fun q => logTrace L a S κ ha z (q, jEll q)) {q | (q, jEll q) ∈ V}

/-- R-3FEAD88B's entire printed conclusion, carried as ONE named hypothesis
when it has not yet been supplied by the native author. Compact K uniformity
is explicit; S is an integer, with the printed strict regularity inequality. -/
def RiccatiPrintedConclusion (f : ℝ → ℂ) : Prop :=
  ∀ M : ℕ, 1 ≤ M → ∀ a δ : ℝ, (ha : 1 / 2 < a) → 0 < δ → δ ≤ 1 →
    ∀ S : ℕ, a + (M : ℝ) + 2 < (S : ℝ) →
    ∀ K : Set ℝ, IsCompact K → K ⊆ Ioi 0 →
      Nonempty (LocalOutput L f M a S δ K (Fact.out : 0 < L) ha)

end QuantumNLS.SmoothScalarMomentsPrerequisite

#print axioms QuantumNLS.SmoothScalarMomentsPrerequisite.RiccatiPrintedConclusion

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.SmoothScalarMomentsPrerequisite." ||
        n.toString.startsWith "_private.QuantumNLS.SmoothScalarMomentsPrerequisite." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
