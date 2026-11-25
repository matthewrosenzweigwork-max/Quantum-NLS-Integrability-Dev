import QuantumNLS.Prop022FlowDifferentialR126

/-! Source positive-rank data on the intended physical carrier. The unused
rank-zero operator is explicitly zero; no rank-zero self-adjointness
hypothesis is imposed. This is a data and classical-flow bridge, not the
full physical quadratic propagator theorem. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology NNReal
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
namespace QuantumNLS.Prop022PositiveDataR126
open PhysicalTensor BetheCoefficientTransform
open Prop022FactorialCoefficientsR115 Prop022ActualProfileR117
open Prop022ClassicalFlowR126 Prop022FlowDifferentialR126 Prop022VariationalR123
variable {L : ℝ} [Fact (0 < L)]
local instance : AddCommGroup (L2T L) := (inferInstance : NormedAddCommGroup (L2T L)).toAddCommGroup

/-- Source rank r=n+1; the extension at rank zero is zero. -/
def positiveExtension (K : ∀ n, HN L (n+1) →L[ℂ] HN L (n+1)) :
    ∀ m, HN L m →L[ℂ] HN L m
  | 0 => 0
  | n+1 => K n

lemma positiveExtension_zero (K : ∀ n, HN L (n+1) →L[ℂ] HN L (n+1)) :
    positiveExtension K 0 = 0 := rfl

lemma positiveExtension_selfAdjoint (K : ∀ n, HN L (n+1) →L[ℂ] HN L (n+1))
    (hs : ∀ n, (K n).adjoint = K n) :
    ∀ m, (positiveExtension K m).adjoint = positiveExtension K m := by
  intro m
  cases m with
  | zero => simp [positiveExtension]
  | succ n => exact hs n

lemma positiveExtension_bound (K : ∀ n, HN L (n+1) →L[ℂ] HN L (n+1))
    (M A : ℝ)
    (hK : ∀ n, ‖K n‖ ≤ M * A^(n+1) / Real.sqrt ((2*(n+1)).factorial : ℝ)) :
    FactorialBound (positiveExtension K) M A := by
  intro m hm
  cases m with
  | zero => omega
  | succ n => exact hK n

/-- Source hypotheses M>=1 and A>0 discharge every weaker analytic
hypothesis. The resulting Phi agrees with the accepted global flow and its
full ambient derivative is the constructed S(t,s), for every signed pair. -/
theorem positive_source_classical_linearization
    (K : ∀ n, HN L (n+1) →L[ℂ] HN L (n+1)) (M A : ℝ)
    (hM : 1 ≤ M) (hA : 0 < A)
    (hK : ∀ n, ‖K n‖ ≤ M * A^(n+1) / Real.sqrt ((2*(n+1)).factorial : ℝ))
    (hs : ∀ n, (K n).adjoint = K n) (u₀ : Prop001.Sphere (L2T L)) :
    let B := positiveExtension K
    let hB := positiveExtension_bound K M A hK
    let hsa := positiveExtension_selfAdjoint K hs
    let Phi := classicalFlow B M A hA.le hB hsa
    let u := profile B M A hA.le hB hsa u₀
    let S := flow B M A hA.le hB hsa u₀
    0 ≤ M ∧ B 0 = 0 ∧
      (∀ t, Phi t u₀.val = u t) ∧
      (∀ s t, Phi (t-s) (u s) = u t) ∧
      (∀ s t, HasFDerivAt (Phi (t-s)) (S t s).toContinuousLinearMap (u s)) ∧
      (∀ s t, (S t s).toContinuousLinearMap = fderiv ℝ (Phi (t-s)) (u s)) := by
  dsimp only
  exact ⟨by linarith, rfl,
    classicalFlow_eq_profile _ M A hA.le _ _ u₀,
    classicalFlow_along_profile _ M A hA.le _ _ u₀,
    classicalFlow_hasFDerivAt _ M A hA.le _ _ u₀,
    flow_eq_fderiv _ M A hA.le _ _ u₀⟩

end QuantumNLS.Prop022PositiveDataR126
#print axioms QuantumNLS.Prop022PositiveDataR126.positiveExtension_bound
#print axioms QuantumNLS.Prop022PositiveDataR126.positive_source_classical_linearization

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022PositiveDataR126." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022PositiveDataR126." then
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
  Lean.logInfo m!"R126 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
