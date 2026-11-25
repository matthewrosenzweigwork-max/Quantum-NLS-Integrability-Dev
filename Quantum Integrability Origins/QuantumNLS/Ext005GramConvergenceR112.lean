import QuantumNLS.Ext005GramResolventR112

/-! R112: strong convergence of the constructed Gram regularizers.
Only injectivity and density of the form embedding are used. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped InnerProductSpace Topology
open ContinuousLinearMap InnerProductSpace Set Filter
namespace QuantumNLS.Ext005GramConvergenceR112
open Ext005GramResolventR112
variable {Q H : Type*}
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def epsilon (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
lemma epsilon_pos (n : ℕ) : 0 < epsilon n := by unfold epsilon; positivity
lemma epsilon_tendsto : Tendsto epsilon atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

def C (i : Q →L[ℝ] H) (n : ℕ) : Q →L[ℝ] Q := cutoff i (epsilon n) (epsilon_pos n)
def R (i : Q →L[ℝ] H) (n : ℕ) : Q →L[ℝ] H := smooth i (epsilon n) (epsilon_pos n)
def P (i : Q →L[ℝ] H) (n : ℕ) : H →L[ℝ] H := physicalCutoff i (epsilon n) (epsilon_pos n)

lemma gram_dense (i : Q →L[ℝ] H) (hinj : Function.Injective i) :
    DenseRange (gram i) := by
  have ho : (gram i).rangeᗮ = ⊥ := by
    apply le_antisymm
    · intro u hu
      have hz := hu (gram i u) ⟨u, rfl⟩
      rw [gram_pair, real_inner_self_eq_norm_sq] at hz
      have hiu : i u = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
      have hu0 := hinj (hiu.trans (map_zero i).symm)
      simpa only [hu0] using (show (0 : Q) ∈ (⊥ : Submodule ℝ Q) from Submodule.zero_mem _)
    · exact bot_le
  change Dense ((gram i).range : Set Q)
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    ← Submodule.orthogonal_orthogonal_eq_closure, ho]
  exact Submodule.bot_orthogonal_eq_top

/-- Form-norm convergence, proved from the embedding's injectivity. -/
theorem C_tendsto (i : Q →L[ℝ] H) (hinj : Function.Injective i) (u : Q) :
    Tendsto (fun n => C i n u) atTop (𝓝 u) := by
  apply Metric.tendsto_atTop.mpr
  intro d hd
  obtain ⟨v, hv⟩ := (gram_dense i hinj).exists_dist_lt u (show 0 < d / 4 by linarith)
  have ht : Tendsto (fun n => epsilon n * ‖v‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using epsilon_tendsto.mul_const ‖v‖
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (show (0 : ℝ) < d / 2 by linarith)))
  refine ⟨N, fun n hn => ?_⟩
  have h1 : dist (C i n u) (C i n (gram i v)) ≤ dist u (gram i v) := by
    simpa only [dist_eq_norm, ← map_sub, C] using cutoff_norm_le i (epsilon n) (epsilon_pos n) (u - gram i v)
  have h2 : dist (C i n (gram i v)) (gram i v) ≤ epsilon n * ‖v‖ :=
    by simpa only [dist_eq_norm, C] using cutoff_gram_error i (epsilon n) (epsilon_pos n) v
  have h3 := dist_triangle (C i n u) (C i n (gram i v)) (gram i v)
  have h4 := dist_triangle (C i n u) (gram i v) u
  rw [dist_comm (gram i v) u] at h4
  linarith [hN n hn]

/-- H-norm convergence, with density of the form domain as the only new input. -/
theorem P_tendsto (i : Q →L[ℝ] H) (hinj : Function.Injective i)
    (hdense : DenseRange i) (x : H) : Tendsto (fun n => P i n x) atTop (𝓝 x) := by
  apply Metric.tendsto_atTop.mpr
  intro d hd
  obtain ⟨u, hu⟩ := hdense.exists_dist_lt x (show 0 < d / 4 by linarith)
  have ht : Tendsto (fun n => P i n (i u)) atTop (𝓝 (i u)) := by
    have h := i.continuous.tendsto u |>.comp (C_tendsto i hinj u)
    exact h
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht (d / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have h1 : dist (P i n x) (P i n (i u)) ≤ dist x (i u) := by
    simpa only [dist_eq_norm, ← map_sub, P] using physicalCutoff_norm_le i (epsilon n) (epsilon_pos n) (x - i u)
  have h2 := dist_triangle (P i n x) (P i n (i u)) (i u)
  have h3 := dist_triangle (P i n x) (i u) x
  rw [dist_comm (i u) x] at h3
  linarith [hN n hn]

/-- The twice regularized form coordinate converges without an idempotence assumption. -/
theorem CC_tendsto (i : Q →L[ℝ] H) (hinj : Function.Injective i) (u : Q) :
    Tendsto (fun n => C i n (C i n u)) atTop (𝓝 u) := by
  have h := (C_tendsto i hinj u).sub (tendsto_const_nhds (x := u))
  have h0 : Tendsto (fun n => ‖C i n u - u‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using h.norm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) ?_ (by simpa using h0.const_mul 2)
  intro n
  have h1 := norm_add_le (C i n (C i n u) - C i n u) (C i n u - u)
  rw [sub_add_sub_cancel] at h1
  have h2 : ‖C i n (C i n u) - C i n u‖ ≤ ‖C i n u - u‖ := by
    simpa only [← map_sub, C] using cutoff_norm_le i (epsilon n) (epsilon_pos n) (C i n u - u)
  linarith

end QuantumNLS.Ext005GramConvergenceR112
#print axioms QuantumNLS.Ext005GramConvergenceR112.C_tendsto
#print axioms QuantumNLS.Ext005GramConvergenceR112.P_tendsto
#print axioms QuantumNLS.Ext005GramConvergenceR112.CC_tendsto

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005GramConvergenceR112." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005GramConvergenceR112." then
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
  Lean.logInfo m!"R112 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
