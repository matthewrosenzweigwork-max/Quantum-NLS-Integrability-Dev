import QuantumNLS.Prop022ClassicalFlowR126
import QuantumNLS.Prop022WeylVacuumR124

/-! Identify the constructed variational evolution with the derivative of
the actual classical flow, and transfer the printed P hypothesis. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Metric Filter Topology
open scoped InnerProductSpace NNReal ENNReal
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
namespace QuantumNLS.Prop022FlowDifferentialR126
open PhysicalTensor BetheCoefficientTransform
open Prop022FactorialCoefficientsR115 Prop022FactorialMajorantR115
open Prop022ActualProfileR117 Prop022VariationalR123 Prop022ClassicalFlowR126
open Ext006KernelHilbertSchmidt
variable {L : ℝ} [Fact (0 < L)]
local instance : AddCommGroup (L2T L) := (inferInstance : NormedAddCommGroup (L2T L)).toAddCommGroup
variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L))

lemma classicalFlow_along_profile (s t : ℝ) :
    classicalFlow B M A hA hB hs (t-s) (profile B M A hA hB hs u₀ s) =
      profile B M A hA hB hs u₀ t := by
  have h := ResetMoserFlow.group_law (classicalFlowOn B M A hA hB hs)
    (mem_univ u₀.val) s (t-s)
  rw [add_sub_cancel, classicalFlow_eq_profile, classicalFlow_eq_profile] at h
  exact h.symm

lemma classicalFlow_zero_derivative (x : L2T L) :
    fderiv ℝ (classicalFlow B M A hA hB hs 0) x = ContinuousLinearMap.id ℝ (L2T L) := by
  have he : classicalFlow B M A hA hB hs 0 = id :=
    funext (fun y => (classicalFlow_spec B M A hA hB hs y).1)
  rw [he, fderiv_id]

/-- S(t,s) = D Phi_(t-s)(u_s), on the full ambient real Hilbert space.
The nonlinear trajectory is identified with the accepted PROP-001 flow,
not supplied as a second solution or replaced by a variational definition. -/
theorem flow_eq_fderiv (s t : ℝ) :
    (flow B M A hA hB hs u₀ t s).toContinuousLinearMap =
      fderiv ℝ (classicalFlow B M A hA hB hs (t-s))
        (profile B M A hA hB hs u₀ s) := by
  apply ContinuousLinearMap.ext
  intro x
  let z := profile B M A hA hB hs u₀ s
  let v := fun r => fderiv ℝ (classicalFlow B M A hA hB hs (r-s)) z x
  have hd (r : ℝ) : HasDerivAt v
      (fderiv ℝ (velocity B) (profile B M A hA hB hs u₀ r) (v r)) r := by
    have h := ((classicalFlow_variational B M A hA hB hs z (r-s)).clm_apply
      (hasDerivAt_const (r-s) x)).scomp r ((hasDerivAt_id r).sub_const s)
    simpa only [v, z, comp_apply, one_smul, Function.comp_def, id_eq, map_zero, add_zero,
      classicalFlow_along_profile B M A hA hB hs u₀] using h
  have hi : v s = x := by
    dsimp [v]
    rw [sub_self, classicalFlow_zero_derivative, id_apply]
  exact (flow_unique B M A hA hB hs u₀ s x v hd hi t).symm

/-- The complete real derivative, with the previously constructed S itself. -/
theorem classicalFlow_hasFDerivAt (s t : ℝ) :
    HasFDerivAt (classicalFlow B M A hA hB hs (t-s))
      (flow B M A hA hB hs u₀ t s).toContinuousLinearMap
      (profile B M A hA hB hs u₀ s) := by
  rw [flow_eq_fderiv]
  exact (classicalFlow_differentiable B M A hA hB hs _ _).hasFDerivAt

/-- The stated P assumption on D Phi now applies to the original beta block,
including negative time; no analogous variational bound is added. -/
theorem printed_beta_bound_from_classical (hM : 0 ≤ M) (T P : ℝ) (hP : 1 ≤ P)
    (hPhi : ∀ r q : ℝ, |r| ≤ T → |q| ≤ T →
      ‖fderiv ℝ (classicalFlow B M A hA hB hs (r-q))
        (profile B M A hA hB hs u₀ q)‖ ≤ P)
    (t : ℝ) (ht : |t| ≤ T) :
    TraceClass.hsSq (physicalBasis L) (betaBlock B M A hA hB hs u₀ t 0) ≠ ⊤ ∧
      Real.sqrt ((TraceClass.hsSq (physicalBasis L)
        (betaBlock B M A hA hB hs u₀ t 0)).toReal) ≤ |t| * pairMajorant A * M * P := by
  apply Prop022WeylVacuumR124.printed_beta_bound B M A hM hA hB hs u₀ T P hP
    (fun r q hr hq => ?_) t ht
  rw [flow_eq_fderiv]
  exact hPhi r q hr hq

end QuantumNLS.Prop022FlowDifferentialR126
#print axioms QuantumNLS.Prop022FlowDifferentialR126.flow_eq_fderiv
#print axioms QuantumNLS.Prop022FlowDifferentialR126.classicalFlow_hasFDerivAt
#print axioms QuantumNLS.Prop022FlowDifferentialR126.printed_beta_bound_from_classical

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022FlowDifferentialR126." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022FlowDifferentialR126." then
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
