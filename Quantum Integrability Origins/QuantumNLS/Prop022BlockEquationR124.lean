import QuantumNLS.Prop022PrintedCoefficientsR124

/-! The original beta block satisfies its physical inhomogeneous equation.
This module neither assumes nor asserts a Hilbert--Schmidt evolution bound. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped InnerProductSpace ComplexConjugate Topology
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal
namespace QuantumNLS.Prop022BlockEquationR124
open TensorCarrier PhysicalTensor BetheCoefficientTransform
open Prop022TensorCompressionR115 Prop022FactorialCoefficientsR115
open Prop022VariationalR123 Prop022PrintedCoefficientsR124 Prop022PairHSR122
open Ext006Blocks Ext006KernelHilbertSchmidt Prop022ActualProfileR117
variable {L : ℝ} [Fact (0 < L)]
local instance : AddCommGroup (L2T L) := (inferInstance : NormedAddCommGroup (L2T L)).toAddCommGroup

lemma conjugation_smul (c : ℂ) (x : L2T L) :
    conjugation (physicalBasis L) (c • x) = conj c • conjugation (physicalBasis L) x := by
  simp only [conjugation_apply, map_smul, star_smul]
  rfl

/-- Complex conjugation of an operator in the fixed original basis. -/
def conjugateOperator (T : L2T L →L[ℂ] L2T L) : L2T L →L[ℂ] L2T L :=
  LinearMap.mkContinuous
    { toFun x := conjugation (physicalBasis L) (T (conjugation (physicalBasis L) x))
      map_add' x y := by simp only [map_add]
      map_smul' c x := by rw [conjugation_smul, map_smul, conjugation_smul, Complex.conj_conj]; rfl }
    ‖T‖ (fun x => by
      change ‖conjugation (physicalBasis L) (T (conjugation (physicalBasis L) x))‖ ≤ _
      simpa only [conjugation_norm] using T.le_opNorm (conjugation (physicalBasis L) x))

lemma conjugateOperator_apply (T : L2T L →L[ℂ] L2T L) (x : L2T L) :
    conjugateOperator T x = conjugation (physicalBasis L) (T (conjugation (physicalBasis L) x)) := rfl

lemma conjugateOperator_norm_le (T : L2T L →L[ℂ] L2T L) : ‖conjugateOperator T‖ ≤ ‖T‖ := by
  exact opNorm_le_bound _ (norm_nonneg _) (fun x => by
    simpa only [conjugateOperator_apply, conjugation_norm] using T.le_opNorm (conjugation (physicalBasis L) x))

variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L))

lemma beta_formula (t s : ℝ) (x : L2T L) :
    betaBlock B M A hA hB hs u₀ t s x = (1/2 : ℂ) •
      (flow B M A hA hB hs u₀ t s (conjugation (physicalBasis L) x) +
        Complex.I • flow B M A hA hB hs u₀ t s (Complex.I • conjugation (physicalBasis L) x)) := by
  change (1/2 : ℝ) • (flow B M A hA hB hs u₀ t s (conjugation (physicalBasis L) x) +
    Complex.I • flow B M A hA hB hs u₀ t s (Complex.I • conjugation (physicalBasis L) x)) = _
  rw [← Complex.coe_smul]
  norm_num

lemma alpha_formula (t s : ℝ) (x : L2T L) :
    alpha B M A hA hB hs u₀ t s x = (1/2 : ℂ) •
      (flow B M A hA hB hs u₀ t s x -
        Complex.I • flow B M A hA hB hs u₀ t s (Complex.I • x)) := by
  change (1/2 : ℝ) • (flow B M A hA hB hs u₀ t s x -
    Complex.I • flow B M A hA hB hs u₀ t s (Complex.I • x)) = _
  rw [← Complex.coe_smul]
  norm_num

lemma beta_self (s : ℝ) : betaBlock B M A hA hB hs u₀ s s = 0 := by
  ext x
  rw [beta_formula, flow_self, flow_self, smul_smul, Complex.I_mul_I, neg_one_smul,
    add_neg_cancel, smul_zero, zero_apply]

lemma flow_derivative (s t : ℝ) (x : L2T L) :
    HasDerivAt (fun r => flow B M A hA hB hs u₀ r s x)
      ((-Complex.I) • (numberOperator B (profile B M A hA hB hs u₀ t)
        (flow B M A hA hB hs u₀ t s x) + pairKernel B (profile B M A hA hB hs u₀ t)
          (conjugation (physicalBasis L) (flow B M A hA hB hs u₀ t s x)))) t := by
  have h := flow_variational B M A hA hB hs u₀ s t x
  rw [(velocity_hasFDerivAt B hs M A hA hB _).fderiv] at h
  change HasDerivAt _ ((-Complex.I) • gradientDerivative B _ _) t at h
  rw [gradientDerivative_eq_coefficients B hs M A hA hB _
    ((profile_spec B M A hA hB hs u₀).2.2.1 t)] at h
  exact h

/-- The forcing is b_t conjugate(alpha(t,s)), in the original basis. -/
def blockForce (t s : ℝ) : L2T L →L[ℂ] L2T L :=
  pairKernel B (profile B M A hA hB hs u₀ t) ∘L
    conjugateOperator (alpha B M A hA hB hs u₀ t s)

/-- The actual block equation, including the physical sign and both time arguments. -/
theorem beta_derivative (s t : ℝ) (x : L2T L) :
    HasDerivAt (fun r => betaBlock B M A hA hB hs u₀ r s x)
      ((-Complex.I) • (numberOperator B (profile B M A hA hB hs u₀ t)
        (betaBlock B M A hA hB hs u₀ t s x) + blockForce B M A hA hB hs u₀ t s x)) t := by
  have h1 := flow_derivative B M A hA hB hs u₀ s t (conjugation (physicalBasis L) x)
  have h2 := flow_derivative B M A hA hB hs u₀ s t (Complex.I • conjugation (physicalBasis L) x)
  have h := (h1.add (h2.const_smul Complex.I)).const_smul (1/2 : ℂ)
  have he : (fun r => betaBlock B M A hA hB hs u₀ r s x) =
      fun r => (1/2 : ℂ) • (flow B M A hA hB hs u₀ r s (conjugation (physicalBasis L) x) +
        Complex.I • flow B M A hA hB hs u₀ r s (Complex.I • conjugation (physicalBasis L) x)) :=
    funext (fun r => beta_formula B M A hA hB hs u₀ r s x)
  rw [he]
  apply h.congr_deriv
  simp only [beta_formula, blockForce, comp_apply, conjugateOperator_apply, alpha_formula,
    map_add, map_sub, map_smul, conjugation_smul, map_mul, map_div₀, map_one, map_ofNat,
    Complex.conj_I, smul_add, smul_sub, smul_smul]
  module

end QuantumNLS.Prop022BlockEquationR124
#print axioms QuantumNLS.Prop022BlockEquationR124.beta_derivative

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022BlockEquationR124." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022BlockEquationR124." then
      pending := pending.push n
  let roots := pending.size
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
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"R124 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
