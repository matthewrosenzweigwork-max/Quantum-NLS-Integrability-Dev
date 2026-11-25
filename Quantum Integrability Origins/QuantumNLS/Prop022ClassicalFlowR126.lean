import QuantumNLS.Prop022VariationalR123
import QuantumNLS.ResetMoserFlowGlobal

/-! The ambient classical flow for factorial kernels. Its restriction to the
unit sphere is the accepted PROP-001 trajectory, proved by ODE uniqueness.
Initial-state differentiability is derived from the proved C1 vector field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Metric Filter Topology
open scoped InnerProductSpace NNReal
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
namespace QuantumNLS.Prop022ClassicalFlowR126
open PhysicalTensor BetheCoefficientTransform TensorPlacements TensorCarrier
open Prop022FactorialCoefficientsR115 Prop022FactorialMajorantR115
open Prop022ActualProfileR117 Prop022GradientR118 Prop022VariationalR123
variable {L : ℝ} [Fact (0 < L)]
local instance : AddCommGroup (L2T L) := (inferInstance : NormedAddCommGroup (L2T L)).toAddCommGroup

theorem radius_ball_picard {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {R S : ℝ} (hS : R < S) {M K : ℝ≥0}
    (hM : ∀ x ∈ closedBall (0 : E) S, ‖f x‖ ≤ M)
    (hK : LipschitzOnWith K f (closedBall (0 : E) S)) :
    ∃ δ > (0 : ℝ), ∀ u : E, ‖u‖ ≤ R → ∀ b : ℝ,
      ∃ α : ℝ → E, Continuous α ∧ α b = u ∧
        (∀ t, α t ∈ closedBall (0 : E) S) ∧
        (∀ t ∈ Ioo (b - δ) (b + δ), HasDerivAt α (f (α t)) t) := by
  let r : ℝ≥0 := ⟨S - R, sub_nonneg.mpr hS.le⟩
  let δ : ℝ := (S - R) / ((M : ℝ) + 1)
  have hδ : 0 < δ := div_pos (sub_pos.mpr hS) (by positivity)
  refine ⟨δ, hδ, fun u hu b => ?_⟩
  have hsub : closedBall u (r : ℝ) ⊆ closedBall (0 : E) S := by
    intro x hx
    rw [mem_closedBall_zero_iff]
    have hx' : ‖x - u‖ ≤ S - R := mem_closedBall_iff_norm.mp hx
    have ht := norm_add_le (x - u) u
    rw [sub_add_cancel] at ht
    linarith
  have hPL : IsPicardLindelof (fun _ : ℝ => f)
      (tmin := b - δ) (tmax := b + δ) ⟨b, by constructor <;> linarith⟩ u r 0 M K := by
    refine ⟨fun _ _ => hK.mono hsub, fun _ _ => continuousOn_const,
      fun _ _ x hx => hM x (hsub hx), ?_⟩
    simp only [add_sub_cancel_left, sub_sub_cancel, max_self, NNReal.coe_zero, sub_zero]
    change (M : ℝ) * δ ≤ S - R
    dsimp only [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < (M : ℝ) + 1)).mpr
    nlinarith [sub_pos.mpr hS]
  obtain ⟨α, hc, hb, hm, _, hd⟩ := QuantumNLS.Ext025A2.gp04_differential_existence hPL
    (show u ∈ closedBall u (0 : ℝ≥0) by simp)
  exact ⟨α, hc, hb, fun t => hsub (hm t), fun t ht =>
    (hd t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩

variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)

include M A hA hB hs in
lemma velocity_C1 : ContDiff ℝ 1 (velocity B) := by
  apply contDiff_one_iff_fderiv.mpr
  refine ⟨fun u => (velocity_hasFDerivAt B hs M A hA hB u).differentiableAt, ?_⟩
  have he : fderiv ℝ (velocity B) = velocityDerivative B :=
    funext (fun u => (velocity_hasFDerivAt B hs M A hA hB u).fderiv)
  rw [he]
  exact velocityDerivative_continuous B M A hA hB

include M A hA hB in
/-- All radii are allowed: factorial decay gives the Picard bounds on every
fixed ball, including an open neighborhood of the unit sphere. -/
lemma velocity_ball_bounds (R : ℝ) (hR : 1 ≤ R) :
    ∃ C K : ℝ≥0, (∀ u ∈ closedBall (0 : L2T L) R, ‖velocity B u‖ ≤ C) ∧
      LipschitzOnWith K (velocity B) (closedBall (0 : L2T L) R) := by
  let E := fun n => extendSymKernel (B (n+1))
  have hv : Summable (fun n => ((n+1 : ℕ) : ℝ) * ‖E n‖ * R^(2*n+1)) := by
    apply Summable.of_nonneg_of_le (fun _ => by positivity) _
      (((summable_nat_add_iff 1).mpr (weight_summable 1 (A*R^2) (by positivity))).mul_left M)
    intro n
    calc
      _ ≤ ((n+1 : ℕ) : ℝ) * ‖B (n+1)‖ * R^(2*(n+1)) := by
        gcongr
        · exact norm_extendSymKernel_le _
        · omega
      _ ≤ ((n+1 : ℕ) : ℝ) * (M * A^(n+1) / Real.sqrt ((2*(n+1)).factorial : ℝ)) * R^(2*(n+1)) := by
        gcongr
        exact hB (n+1) (by omega)
      _ = M * weight 1 (A*R^2) (n+1) := by unfold weight; rw [mul_pow, pow_mul]; ring
  have hd : Summable (fun n => ((n+1 : ℕ) : ℝ) * ((2*n+1 : ℕ) : ℝ) * ‖E n‖ * R^(2*n)) := by
    apply Summable.of_nonneg_of_le (fun _ => by positivity) _
      (((summable_nat_add_iff 1).mpr (weight_summable 2 (A*R^2) (by positivity))).mul_left (2*M))
    intro n
    calc
      _ ≤ (2*((n+1 : ℕ) : ℝ)^2) * ‖B (n+1)‖ * R^(2*(n+1)) := by
        have hc : ((n+1 : ℕ) : ℝ) * ((2*n+1 : ℕ) : ℝ) ≤ 2*((n+1 : ℕ) : ℝ)^2 := by
          push_cast; nlinarith
        have hp : R^(2*n) ≤ R^(2*(n+1)) := pow_le_pow_right₀ hR (by omega)
        exact mul_le_mul
          (mul_le_mul hc (norm_extendSymKernel_le _) (norm_nonneg _) (by positivity))
          hp (by positivity) (by positivity)
      _ ≤ (2*((n+1 : ℕ) : ℝ)^2) * (M * A^(n+1) / Real.sqrt ((2*(n+1)).factorial : ℝ)) * R^(2*(n+1)) := by
        gcongr
        exact hB (n+1) (by omega)
      _ = (2*M) * weight 2 (A*R^2) (n+1) := by unfold weight; rw [mul_pow, pow_mul]; ring
  exact Ext025A8.hartreeField_ball_bounds E (by linarith) hv hd

include M A hA hB hs in
/-- Construct global solutions for arbitrary ambient data, preserving their
actual norm. No global ambient solution is a premise. -/
theorem global_exists (x : L2T L) : ∃ γ : ℝ → L2T L,
    γ 0 = x ∧ ∀ t, HasDerivAt γ (velocity B (γ t)) t ∧ ‖γ t‖ = ‖x‖ := by
  let R := ‖x‖ + 1
  obtain ⟨C, K, hC, hK⟩ := velocity_ball_bounds B M A hA hB (R+1) (by dsimp [R]; linarith [norm_nonneg x])
  obtain ⟨δ, hδ, hlocal⟩ := radius_ball_picard (by linarith : R < R+1) hC hK
  let Z : Set (L2T L) := {y | ‖y‖ = ‖x‖}
  have hsub : Z ⊆ closedBall (0 : L2T L) (R+1) := by
    intro y hy
    rw [mem_closedBall_zero_iff, hy]
    dsimp [R]; linarith
  have hlocalZ : ∀ y ∈ Z, ∃ γ : ℝ → L2T L,
      γ 0 = y ∧ Ext025A8.SolOn (velocity B) Z γ (Ioo (-δ) δ) := by
    intro y hy
    obtain ⟨γ, _, hi, hm, hd⟩ := hlocal y (by change ‖y‖ = ‖x‖ at hy; dsimp [R]; linarith) 0
    have hd' : ∀ t ∈ Ioo (-δ) δ, HasDerivAt γ (velocity B (γ t)) t := by
      simpa only [zero_sub, zero_add] using hd
    have hmass := Ext025A8.hartree_mass_on_interval
      (fun n => extendSymKernel (B (n+1)))
      (fun n => Ext025A8.source_kernel_selfAdjoint _ (hs (n+1)))
      (show (0 : ℝ) ∈ Ioo (-δ) δ from ⟨by linarith, hδ⟩) hd'
      (fun t _ => gradient_summable B M A (R+1) hA hB
        (by dsimp [R]; linarith [norm_nonneg x]) (γ t) (mem_closedBall_zero_iff.mp (hm t)))
    refine ⟨γ, hi, fun t ht => ⟨hd' t ht, ?_⟩⟩
    change ‖γ t‖ = ‖x‖
    rw [hmass t ht, hi]; exact hy
  exact Ext025A8.uniform_invariant_global (hK.mono hsub) hδ hlocalZ rfl

/-- The ambient extension uses the identical source vector field. -/
def classicalFlow (t : ℝ) (x : L2T L) : L2T L :=
  (global_exists B M A hA hB hs x).choose t

lemma classicalFlow_spec (x : L2T L) : classicalFlow B M A hA hB hs 0 x = x ∧
    ∀ t, HasDerivAt (fun r => classicalFlow B M A hA hB hs r x)
      (velocity B (classicalFlow B M A hA hB hs t x)) t ∧
      ‖classicalFlow B M A hA hB hs t x‖ = ‖x‖ :=
  (global_exists B M A hA hB hs x).choose_spec

lemma classicalFlowOn : ResetMoserFlow.FlowOn (velocity B)
    (classicalFlow B M A hA hB hs) univ where
  isOpen := isOpen_univ
  cd := (velocity_C1 B M A hA hB hs).contDiffOn
  deriv := fun x _ t => (classicalFlow_spec B M A hA hB hs x).2 t |>.1
  mem := fun _ _ _ => mem_univ _
  zero := fun x _ => (classicalFlow_spec B M A hA hB hs x).1

/-- Equality with the accepted PROP-001/global trajectory on the unit sphere. -/
theorem classicalFlow_eq_profile (u : Prop001.Sphere (L2T L)) (t : ℝ) :
    classicalFlow B M A hA hB hs t u.val = profile B M A hA hB hs u t := by
  have he := (Prop001.trajectory_spec (classicalData B M A hA hB hs) u).2.2.2
    (fun r => classicalFlow B M A hA hB hs r u.val)
    (classicalFlow_spec B M A hA hB hs u.val).1
    (fun r => ⟨((classicalFlow_spec B M A hA hB hs u.val).2 r).2.trans u.property,
      ((classicalFlow_spec B M A hA hB hs u.val).2 r).1⟩)
  exact congrFun he t

/-- Full ambient Frechet differentiability, for every signed time. -/
theorem classicalFlow_differentiable (t : ℝ) (x : L2T L) :
    DifferentiableAt ℝ (classicalFlow B M A hA hB hs t) x :=
  ResetMoserFlow.diffAt (classicalFlowOn B M A hA hB hs) (mem_univ x) t

/-- The nonlinear flow derivative satisfies the genuine variational equation. -/
theorem classicalFlow_variational (x : L2T L) (t : ℝ) :
    HasDerivAt (fun r => fderiv ℝ (classicalFlow B M A hA hB hs r) x)
      ((fderiv ℝ (velocity B) (classicalFlow B M A hA hB hs t x)).comp
        (fderiv ℝ (classicalFlow B M A hA hB hs t) x)) t :=
  ResetMoserFlow.variational (classicalFlowOn B M A hA hB hs) (mem_univ x) t

end QuantumNLS.Prop022ClassicalFlowR126
#print axioms QuantumNLS.Prop022ClassicalFlowR126.global_exists
#print axioms QuantumNLS.Prop022ClassicalFlowR126.classicalFlow_eq_profile
#print axioms QuantumNLS.Prop022ClassicalFlowR126.classicalFlow_differentiable
#print axioms QuantumNLS.Prop022ClassicalFlowR126.classicalFlow_variational

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022ClassicalFlowR126." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022ClassicalFlowR126." then
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
