import QuantumNLS.Ext005ConsistencyR33b

/-! Weak consistency for bounded evolving form vectors.
No strong convergence of the evolving sequence is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology
open ContinuousLinearMap InnerProductSpace Set Filter
namespace QuantumNLS.Ext005WeakConsistencyR34b
open Ext005GramResolventR112 Ext005GramConvergenceR112 Ext005RegularizedR33b
open Ext005ConsistencyR33b
variable {Q H : Type*}
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace Q] in
lemma weak_strong_pair (u v : ℕ → Q) (u₀ v₀ : Q) (M : ℝ)
    (hb : ∀ n, ‖u n‖ ≤ M)
    (hu : ∀ z : Q, Tendsto (fun n => ⟪z, u n⟫_ℝ) atTop (𝓝 ⟪z, u₀⟫_ℝ))
    (hv : Tendsto v atTop (𝓝 v₀)) :
    Tendsto (fun n => ⟪v n, u n⟫_ℝ) atTop (𝓝 ⟪v₀, u₀⟫_ℝ) := by
  have he : Tendsto (fun n => ⟪v n - v₀, u n⟫_ℝ) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_)
      (show Tendsto (fun n => ‖v n - v₀‖ * M) atTop (𝓝 0) by
        simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hv).mul_const M)
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hb n) (norm_nonneg _))
  simpa only [inner_sub_left, sub_add_cancel, zero_add] using he.add (hu v₀)

/-- A strongly converging self-adjoint cutoff may be moved onto the fixed
test vector. Hence a bounded weakly converging sequence suffices. -/
theorem cutoff_weak (i : Q →L[ℝ] H) (hinj : Function.Injective i)
    (u : ℕ → Q) (u₀ : Q) (M : ℝ) (hb : ∀ n, ‖u n‖ ≤ M)
    (hu : ∀ z : Q, Tendsto (fun n => ⟪z, u n⟫_ℝ) atTop (𝓝 ⟪z, u₀⟫_ℝ))
    (z : Q) :
    Tendsto (fun n => ⟪z, C i n (u n)⟫_ℝ) atTop (𝓝 ⟪z, u₀⟫_ℝ) := by
  have h := weak_strong_pair u (fun n => C i n z) u₀ z M hb hu (C_tendsto i hinj z)
  simpa only [C, cutoff_symm] using h

/-- The actual double-cutoff antidual force passes to the weak limit
on a bounded form sequence. This strengthens the fixed/strong R33b result. -/
theorem generator_weak_consistent (i : Q →L[ℝ] H) (hinj : Function.Injective i)
    (F : Q →L[ℝ] Q) (u : ℕ → Q) (u₀ : Q) (M : ℝ) (hb : ∀ n, ‖u n‖ ≤ M)
    (hu : ∀ z : Q, Tendsto (fun n => ⟪z, u n⟫_ℝ) atTop (𝓝 ⟪z, u₀⟫_ℝ))
    (z : Q) :
    Tendsto (fun n => ⟪z, gram i (generator i (epsilon n) (epsilon_pos n) F (u n))⟫_ℝ)
      atTop (𝓝 ⟪z, F u₀⟫_ℝ) := by
  have hc := generator_consistent i hinj F.adjoint z
  rw [show ⟪z, F u₀⟫_ℝ = ⟪F.adjoint z, u₀⟫_ℝ from
    (F.adjoint_inner_left u₀ z).symm]
  have h := weak_strong_pair u
    (fun n => gram i (generator i (epsilon n) (epsilon_pos n) F.adjoint z))
    u₀ (F.adjoint z) M hb hu hc
  convert h using 1
  ext n
  rw [generator_antidual, generator_antidual]
  rw [cutoff_symm, F.adjoint_inner_left, cutoff_symm]

/-- If the smoothed evolving sequence has a weak form limit, the outer
cutoff force converges without requiring an uncut uniform form bound. -/
theorem outer_cutoff_weak_consistent (i : Q →L[ℝ] H) (hinj : Function.Injective i)
    (F : Q →L[ℝ] Q) (w : ℕ → Q) (w₀ : Q) (M : ℝ) (hb : ∀ n, ‖w n‖ ≤ M)
    (hw : ∀ z : Q, Tendsto (fun n => ⟪z, w n⟫_ℝ) atTop (𝓝 ⟪z, w₀⟫_ℝ))
    (z : Q) :
    Tendsto (fun n => ⟪z, C i n (F (w n))⟫_ℝ) atTop (𝓝 ⟪z, F w₀⟫_ℝ) := by
  have h := weak_strong_pair w (fun n => F.adjoint (C i n z))
    w₀ (F.adjoint z) M hb hw
    (F.adjoint.continuous.tendsto z |>.comp (C_tendsto i hinj z))
  simpa only [C, cutoff_symm, F.adjoint_inner_left] using h

end QuantumNLS.Ext005WeakConsistencyR34b
#print axioms QuantumNLS.Ext005WeakConsistencyR34b.generator_weak_consistent
#print axioms QuantumNLS.Ext005WeakConsistencyR34b.outer_cutoff_weak_consistent

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005WeakConsistencyR34b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005WeakConsistencyR34b." then
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
  Lean.logInfo m!"R34b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
