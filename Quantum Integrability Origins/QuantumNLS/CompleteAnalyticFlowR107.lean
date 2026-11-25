import QuantumNLS.CompleteFlowPhysicalR107
import QuantumNLS.JointAnalyticFlowR107

/-! R-7ED997C1: finite-time analytic dependence and full symplecticity.
The carrier is the actual physical L2T L, with its real Hilbert structure.
The explicit realNS_eq bridge proves compatibility with its existing real
scalar structure. The complete flow solves precisely X_n=-i grad I_n.
All analytic and differential assertions are at each input; no norm-ball
or integer-uniform bound is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open Set Metric
namespace QuantumNLS.CompleteAnalyticFlowR107
open PhysicalTensor (L2T)
open CompleteFlowPhysicalR107
open TerraMultiRound30HessianBridge (Actions)
open ProductTorusGenerator ProductTorusFlow ProductTorusCommute ProductTorusVariational
open RootMassInvolutionR8 (mass)
variable {L κ : ℝ} [Fact (0 < L)]
local instance realNormed : NormedSpace ℝ (L2T L) := realNS
local instance realModule : Module ℝ (L2T L) := (realNS (L := L)).toModule
local instance realSMul : SMul ℝ (L2T L) := (realNS (L := L)).toSMul
local instance additiveGroup : AddCommGroup (L2T L) :=
  (inferInstance : NormedAddCommGroup (L2T L)).toAddCommGroup

theorem analytic_field (hκ : 0 < κ) (n : ℤ) :
    AnalyticOnNhd ℝ (SymplecticBracket.hamField (mass (L := L) hκ n)) univ := by
  rw [← coordinate_field (L := L) hκ n]
  intro u _
  have hh := ((ProductTorusAnalytic.Lgen (e n)).analyticAt
      (fderiv ℝ (Actions (L := L) hκ) u)).comp
    ((analytic_actions (L := L) hκ).fderiv u (mem_univ u))
  simpa only [Function.comp_def, ← ProductTorusAnalytic.X_eq_Lgen] using hh

theorem joint_analytic (hκ : 0 < κ) (n : ℤ) (p : ℝ × L2T L) :
    AnalyticAt ℝ (fun q : ℝ × L2T L => phi (L := L) hκ n q.1 q.2) p :=
  JointAnalyticFlowR107.joint_analytic (analytic_field (L := L) hκ n)
    (fun u => (phi_spec (L := L) hκ n u).2) (fun u => (phi_spec (L := L) hκ n u).1) p

theorem time_analytic (hκ : 0 < κ) (n : ℤ) (t : ℝ) (u : L2T L) :
    AnalyticAt ℝ (phi (L := L) hκ n t) u := by
  have h := (joint_analytic (L := L) hκ n (t,u)).comp
    (analyticAt_const.prod (analyticAt_id : AnalyticAt ℝ (id : L2T L → L2T L) u))
  exact h

/-- The fixed-time analytic diffeomorphism, globally defined on physical L2. -/
def timeHomeomorph (hκ : 0 < κ) (n : ℤ) (t : ℝ) : L2T L ≃ₜ L2T L where
  toFun := phi (L := L) hκ n t
  invFun := phi (L := L) hκ n (-t)
  left_inv u := flow_neg_left (physical_hyp (L := L) hκ) (e n) u t
  right_inv u := flow_neg_right (physical_hyp (L := L) hκ) (e n) u t
  continuous_toFun := continuous_iff_continuousAt.mpr fun u => (time_analytic (L := L) hκ n t u).continuousAt
  continuous_invFun := continuous_iff_continuousAt.mpr fun u => (time_analytic (L := L) hκ n (-t) u).continuousAt

/-- The inverse is the real differential of the negative-time map. -/
theorem inverse_differentials (hκ : 0 < κ) (n : ℤ) (t : ℝ) (u : L2T L) :
    (fderiv ℝ (phi (L := L) hκ n (-t)) (phi (L := L) hκ n t u)).comp (fderiv ℝ (phi (L := L) hκ n t) u) =
        ContinuousLinearMap.id ℝ (L2T L) ∧
    (fderiv ℝ (phi (L := L) hκ n t) u).comp (fderiv ℝ (phi (L := L) hκ n (-t)) (phi (L := L) hκ n t u)) =
        ContinuousLinearMap.id ℝ (L2T L) := by
  refine ⟨fderiv_flow_neg_comp (physical_hyp (L := L) hκ) (e n) t u, ?_⟩
  have h := fderiv_flow_neg_comp (physical_hyp (L := L) hκ) (e n) (-t) (phi (L := L) hκ n t u)
  simpa only [neg_neg,phi,flow_neg_left (physical_hyp (L := L) hκ)] using h

def differentialEquiv (hκ : 0 < κ) (n : ℤ) (t : ℝ) (u : L2T L) : L2T L ≃L[ℝ] L2T L :=
  ContinuousLinearEquiv.equivOfInverse'
    (fderiv ℝ (phi (L := L) hκ n t) u)
    (fderiv ℝ (phi (L := L) hκ n (-t)) (phi (L := L) hκ n t u))
    (inverse_differentials (L := L) hκ n t u).2 (inverse_differentials (L := L) hκ n t u).1

/-- R-7ED997C1, every printed clause in one named theorem, with only L,κ>0
and the integer n. Completeness and the Hamiltonian normalization are included
explicitly to bind the theorem to the actual indexed-mass flow. -/
theorem complete_analytic_flow (hκ : 0 < κ) (n : ℤ) :
    (∀ u : L2T L, phi (L := L) hκ n 0 u = u ∧ ∀ t,
      HasDerivAt (fun s => phi (L := L) hκ n s u)
        (SymplecticBracket.hamField (mass (L := L) hκ n) (phi (L := L) hκ n t u)) t) ∧
    (∀ p : ℝ × L2T L, AnalyticAt ℝ (fun q : ℝ × L2T L => phi (L := L) hκ n q.1 q.2) p) ∧
    (∀ t : ℝ, (∀ u, timeHomeomorph (L := L) hκ n t u = phi (L := L) hκ n t u) ∧
      (∀ u, (timeHomeomorph (L := L) hκ n t).symm u = phi (L := L) hκ n (-t) u) ∧
      AnalyticOnNhd ℝ (timeHomeomorph (L := L) hκ n t) univ ∧
      AnalyticOnNhd ℝ (timeHomeomorph (L := L) hκ n t).symm univ ∧
      ∀ u, (differentialEquiv (L := L) hκ n t u : L2T L →L[ℝ] L2T L) = fderiv ℝ (phi (L := L) hκ n t) u ∧
        ((differentialEquiv (L := L) hκ n t u).symm : L2T L →L[ℝ] L2T L) =
          fderiv ℝ (phi (L := L) hκ n (-t)) (phi (L := L) hκ n t u)) ∧
    (∀ (t : ℝ) (u h k : L2T L),
      SymplecticBracket.omega (fderiv ℝ (phi (L := L) hκ n t) u h) (fderiv ℝ (phi (L := L) hκ n t) u k) =
        SymplecticBracket.omega h k) := by
  refine ⟨phi_spec (L := L) hκ n, joint_analytic (L := L) hκ n, ?_, ?_⟩
  · intro t
    exact ⟨fun _ => rfl,fun _ => rfl,
      fun u _ => time_analytic (L := L) hκ n t u,fun u _ => time_analytic (L := L) hκ n (-t) u,
      fun _ => ⟨rfl,rfl⟩⟩
  · intro t u h k
    exact ProductTorusSymplectic.symplectic (physical_hyp (L := L) hκ) (e n) t u h k

end QuantumNLS.CompleteAnalyticFlowR107
#print axioms QuantumNLS.CompleteAnalyticFlowR107.complete_analytic_flow

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.CompleteAnalyticFlowR107." ||
        n.toString.startsWith "_private.QuantumNLS.CompleteAnalyticFlowR107." then
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
  Lean.logInfo m!"R107 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
