import QuantumNLS.Ext005WeakStarR36b
import QuantumNLS.Ext005SourceBoundsR36b

/-! Actual extraction of uniformly bounded form representatives, their
ambient norm continuity, and their initial trace. This module does not
identify a weak equation; no original evolution is a premise. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology
open ContinuousLinearMap InnerProductSpace Set Filter
namespace QuantumNLS.Ext005WeakSubfilterR36b
open Ext005WeakStarR36b Ext005LimitRegularityR35b
open Ext005GramResolventR112 Ext005GramConvergenceR112
variable {Q H : Type*}
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace Q] in
lemma weak_norm_bound_filter {ι : Type*} (L : Filter ι) [NeBot L]
    (u : ι → Q) (v : Q) (M : ℝ) (hb : ∀ n, ‖u n‖ ≤ M)
    (hw : ∀ z : Q, Tendsto (fun n => ⟪z, u n⟫_ℝ) L (𝓝 ⟪z, v⟫_ℝ)) : ‖v‖ ≤ M := by
  have h := le_of_tendsto (hw v) (Eventually.of_forall fun n =>
    (real_inner_le_norm v (u n)).trans (mul_le_mul_of_nonneg_left (hb n) (norm_nonneg v)))
  rw [real_inner_self_eq_norm_sq] at h
  have hM : 0 ≤ M := by
    obtain ⟨n, hn⟩ := (Eventually.of_forall hb : ∀ᶠ n in L, ‖u n‖ ≤ M).exists
    exact (norm_nonneg _).trans hn
  nlinarith [norm_nonneg v]

/-- Antidual time bounds pass to an extracted weak subfilter. -/
theorem gram_time_bound_filter (i : Q →L[ℝ] H) (U : Set ℝ)
    (w : ℕ → ℝ → Q) (v : ℝ → Q) (L : Filter ℕ) [NeBot L] (K : ℝ)
    (hb : ∀ n, ∀ s ∈ U, ∀ t ∈ U,
      ‖gram i (w n t) - gram i (w n s)‖ ≤ K * ‖t-s‖)
    (hw : ∀ t ∈ U, ∀ z : Q,
      Tendsto (fun n => ⟪z, w n t⟫_ℝ) L (𝓝 ⟪z, v t⟫_ℝ)) :
    ∀ s ∈ U, ∀ t ∈ U, ‖gram i (v t) - gram i (v s)‖ ≤ K * ‖t-s‖ := by
  intro s hs t ht
  apply weak_norm_bound_filter L (fun n => gram i (w n t) - gram i (w n s))
    (gram i (v t) - gram i (v s)) (K * ‖t-s‖) (fun n => hb n s hs t ht)
  intro z
  simpa only [inner_sub_right, gram_symm] using
    (hw t ht (gram i z)).sub (hw s hs (gram i z))

/-- Extraction, the uniform form bound, ambient continuity and the initial
trace are conclusions. This theorem supplies the limit missing in R35b. -/
theorem extract_bounded_continuous_limit (i : Q →L[ℝ] H) (hi : Function.Injective i)
    (a b : ℝ) (hab : a ≤ b) (w : ℕ → ℝ → Q) (u₀ : Q) (M K : ℝ)
    (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hb : ∀ n, ∀ t ∈ Icc a b, ‖w n t‖ ≤ M)
    (hl : ∀ n, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      ‖gram i (w n t) - gram i (w n s)‖ ≤ K * ‖t-s‖)
    (hinit : ∀ n, w n a = C i n u₀) :
    ∃ L : Filter ℕ, NeBot L ∧ L ≤ atTop ∧ ∃ v : ℝ → Q,
      (∀ t ∈ Icc a b, ‖v t‖ ≤ M) ∧ ContinuousOn (fun t => i (v t)) (Icc a b) ∧
      v a = u₀ ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        ‖gram i (v t) - gram i (v s)‖ ≤ K * ‖t-s‖) ∧
      ∀ t ∈ Icc a b, ∀ z : Q,
        Tendsto (fun n => ⟪z, w n t⟫_ℝ) L (𝓝 ⟪z, v t⟫_ℝ) := by
  obtain ⟨L, hL, hLa, v, hv, hw⟩ := bounded_pointwise_subfilter atTop
    (fun n (t : Icc a b) => w n t) M (fun n t => hb n t t.property)
  let : NeBot L := hL
  let V : ℝ → Q := fun t => if ht : t ∈ Icc a b then v ⟨t, ht⟩ else 0
  have hV (t : ℝ) (ht : t ∈ Icc a b) : V t = v ⟨t, ht⟩ := dite_eq_left ht
  have hW (t : ℝ) (ht : t ∈ Icc a b) (z : Q) :
      Tendsto (fun n => ⟪z, w n t⟫_ℝ) L (𝓝 ⟪z, V t⟫_ℝ) := by
    rw [hV t ht]
    exact hw ⟨t, ht⟩ z
  have hB (t : ℝ) (ht : t ∈ Icc a b) : ‖V t‖ ≤ M := by rw [hV t ht]; exact hv _
  have hG := gram_time_bound_filter i (Icc a b) w V L K hl hW
  have hC : ContinuousOn (fun t => i (V t)) (Icc a b) := by
    apply embedded_continuous_of_gram i (Icc a b) V M hM hB
    have hli : LipschitzOnWith ⟨K, hK⟩ (fun t => gram i (V t)) (Icc a b) :=
      lipschitzOnWith_iff_norm_sub_le.mpr (fun t ht s hs => hG s hs t ht)
    exact hli.continuousOn
  have hI : V a = u₀ := by
    apply ext_inner_left ℝ
    intro z
    have h := hW a ⟨le_rfl, hab⟩ z
    simp only [hinit] at h
    exact tendsto_nhds_unique h
      ((tendsto_const_nhds.inner (C_tendsto i hi u₀)).mono_left hLa)
  exact ⟨L, hL, hLa, V, hB, hC, hI, hG, hW⟩

end QuantumNLS.Ext005WeakSubfilterR36b
#print axioms QuantumNLS.Ext005WeakSubfilterR36b.extract_bounded_continuous_limit

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005WeakSubfilterR36b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005WeakSubfilterR36b." then
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
