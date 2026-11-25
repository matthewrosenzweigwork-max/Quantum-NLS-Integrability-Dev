import QuantumNLS.Ext005RegularizedR33b

/-! Antidual consistency of the constructed regularization. Convergence here
is for fixed or strongly convergent form vectors, not for the unknown
evolving sequence; no limit solution is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology
open ContinuousLinearMap InnerProductSpace Set Filter
namespace QuantumNLS.Ext005ConsistencyR33b
open Ext005GramResolventR112 Ext005GramConvergenceR112 Ext005RegularizedR33b
variable {Q H : Type*}
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma generator_antidual (i : Q →L[ℝ] H) (e : ℝ) (he : 0 < e)
    (F : Q →L[ℝ] Q) (u : Q) :
    gram i (generator i e he F u) = cutoff i e he (F (cutoff i e he u)) := by
  change gram i (inverse i e he (F (cutoff i e he u))) = _
  rw [gram_inverse]

/-- The regularized force is uniformly bounded from Q to Q*, before a
bound for the evolving form vector has been proved. -/
lemma generator_antidual_bound (i : Q →L[ℝ] H) (e : ℝ) (he : 0 < e)
    (F : Q →L[ℝ] Q) (u : Q) :
    ‖gram i (generator i e he F u)‖ ≤ ‖F‖ * ‖u‖ := by
  rw [generator_antidual]
  exact (cutoff_norm_le i e he _).trans ((ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_left (cutoff_norm_le i e he u) (norm_nonneg F)))

lemma cutoff_variable_tendsto (i : Q →L[ℝ] H) (hinj : Function.Injective i)
    (v : ℕ → Q) (w : Q) (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun n => C i n (v n)) atTop (𝓝 w) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h1 : Tendsto (fun n => ‖v n - w‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hv
  have h2 : Tendsto (fun n => ‖C i n w - w‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (C_tendsto i hinj w)
  apply squeeze_zero (fun n => norm_nonneg _) ?_ (by simpa only [add_zero] using h1.add h2)
  intro n
  calc
    ‖C i n (v n) - w‖ ≤ ‖C i n (v n) - C i n w‖ + ‖C i n w - w‖ :=
      by simpa only [dist_eq_norm] using dist_triangle (C i n (v n)) (C i n w) w
    _ ≤ ‖v n - w‖ + ‖C i n w - w‖ := by
      apply add_le_add _ le_rfl
      simpa only [← map_sub, C] using cutoff_norm_le i (epsilon n) (epsilon_pos n) (v n - w)

/-- Correct strong antidual consistency for every fixed bounded form force. -/
theorem generator_consistent (i : Q →L[ℝ] H) (hinj : Function.Injective i)
    (F : Q →L[ℝ] Q) (u : Q) :
    Tendsto (fun n => gram i (generator i (epsilon n) (epsilon_pos n) F u))
      atTop (𝓝 (F u)) := by
  simp only [generator_antidual]
  exact cutoff_variable_tendsto i hinj (fun n => F (C i n u)) (F u)
    (F.continuous.tendsto u |>.comp (C_tendsto i hinj u))

end QuantumNLS.Ext005ConsistencyR33b
#print axioms QuantumNLS.Ext005ConsistencyR33b.generator_antidual_bound
#print axioms QuantumNLS.Ext005ConsistencyR33b.generator_consistent

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005ConsistencyR33b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005ConsistencyR33b." then
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
  Lean.logInfo m!"R33b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
