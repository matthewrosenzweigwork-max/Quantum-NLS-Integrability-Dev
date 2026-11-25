import QuantumNLS.Ext005WeakTestsR36b

/-! Uniform consistency of the actual outer-cutoff force along the
compactness subfilter. No uniform bound on the uncut evolving form vectors
is assumed or substituted for the proved smoothed bound. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology
open ContinuousLinearMap InnerProductSpace Set Filter
namespace QuantumNLS.Ext005NetForceR36b
open Ext005GramResolventR112 Ext005GramConvergenceR112 Ext005WeakTestsR36b
variable {Q H : Type*}
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Time-dependent bounded forces and the actual outer cutoff pass to the
limit UNIFORMLY in scalar tests along any subfilter refining atTop. -/
theorem outer_force_uniform (i : Q →L[ℝ] H) (hi : Function.Injective i)
    (a b : ℝ) (F : ℝ → Q →L[ℝ] Q) (w : ℕ → ℝ → Q) (v : ℝ → Q)
    (L : Filter ℕ) (hL : L ≤ atTop) (M N : ℝ) (hM : 0 ≤ M)
    (hb : ∀ n, ∀ t ∈ Icc a b, ‖w n t‖ ≤ M)
    (hF : ContinuousOn F (Icc a b)) (hFb : ∀ t ∈ Icc a b, ‖F t‖ ≤ N)
    (hf : ∀ z : Q, TendstoUniformlyOn (fun n t => ⟪z, w n t⟫_ℝ)
      (fun t => ⟪z, v t⟫_ℝ) L (Icc a b)) (z : Q) :
    TendstoUniformlyOn (fun n t => ⟪z, C i n (F t (w n t))⟫_ℝ)
      (fun t => ⟪z, F t (v t)⟫_ℝ) L (Icc a b) := by
  let q := fun t => (F t).adjoint z
  have hq : ContinuousOn q (Icc a b) :=
    (ContinuousLinearMap.adjoint.continuous.comp_continuousOn hF).clm_apply continuousOn_const
  have hqt := uniform_continuous_test a b w v L M hM hb hf q hq
  simp only [q, adjoint_inner_left] at hqt
  have he : Tendsto (fun n => N * M * ‖C i n z-z‖) L (𝓝 0) := by
    have h := (tendsto_iff_norm_sub_tendsto_zero.mp (C_tendsto i hi z)).const_mul (N*M)
    simpa only [mul_zero] using h.mono_left hL
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hqt (ε/2) (by linarith),
    he.eventually (gt_mem_nhds (show (0:ℝ) < ε/2 by linarith))] with n hn he t ht
  have hpair : ⟪z, C i n (F t (w n t))⟫_ℝ - ⟪z, F t (w n t)⟫_ℝ =
      ⟪(F t).adjoint (C i n z-z), w n t⟫_ℝ := by
    rw [C, ← cutoff_symm, ← inner_sub_left, adjoint_inner_left]
  have hdist : dist ⟪z, F t (w n t)⟫_ℝ ⟪z, C i n (F t (w n t))⟫_ℝ ≤
      N*M*‖C i n z-z‖ := by
    rw [dist_eq_norm, norm_sub_rev, hpair]
    calc
      _ ≤ ‖(F t).adjoint (C i n z-z)‖ * ‖w n t‖ := norm_inner_le_norm _ _
      _ ≤ (‖F t‖ * ‖C i n z-z‖) * M :=
        mul_le_mul (by simpa only [LinearIsometryEquiv.norm_map] using (F t).adjoint.le_opNorm (C i n z-z))
          (hb n t ht) (norm_nonneg _) (by positivity)
      _ ≤ (N * ‖C i n z-z‖) * M :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hFb t ht) (norm_nonneg _)) hM
      _ = _ := by ring
  exact (dist_triangle _ ⟪z, F t (w n t)⟫_ℝ _).trans_lt
    (by linarith [hn t ht, hdist.trans_lt he])

end QuantumNLS.Ext005NetForceR36b
#print axioms QuantumNLS.Ext005NetForceR36b.outer_force_uniform

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005NetForceR36b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005NetForceR36b." then
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
  Lean.logInfo m!"R36b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
