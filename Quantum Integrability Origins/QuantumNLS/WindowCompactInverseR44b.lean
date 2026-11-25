import Mathlib

open scoped NNReal
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 50000

/-! R-E59628C9, final paragraph: the set of straight segments joining
points of a fixed compact torus is compact, even in infinite dimension.
A C¹ ambient inverse therefore has one Lipschitz constant for all pairs.
This does not use compactness of an infinite-dimensional closed ball. -/
noncomputable section
set_option autoImplicit false
open Set Metric
namespace QuantumNLS.WindowCompactInverseR44b
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def segmentUnion (K : Set E) : Set E :=
  (fun p : ℝ × (E × E) => (1-p.1) • p.2.1 + p.1 • p.2.2) ''
    (Icc (0 : ℝ) 1 ×ˢ (K ×ˢ K))

theorem isCompact_segmentUnion {K : Set E} (hK : IsCompact K) : IsCompact (segmentUnion K) := by
  apply (isCompact_Icc.prod (hK.prod hK)).image
  fun_prop

theorem segment_subset_segmentUnion {K : Set E} {x y : E} (hx : x ∈ K) (hy : y ∈ K) :
    segment ℝ x y ⊆ segmentUnion K := by
  rw [segment_eq_image]
  rintro z ⟨t, ht, rfl⟩
  exact ⟨(t,x,y), ⟨ht,hx,hy⟩, rfl⟩

/-- One common Lipschitz bound for an ambient C¹ function on a compact set.
The derivative is bounded on the compact union of joining segments. -/
theorem compact_lipschitz {K : Set E} (hK : IsCompact K) (f : E → G)
    (hf : ContDiff ℝ 1 f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, ∀ y ∈ K, ‖f x - f y‖ ≤ M * ‖x-y‖ := by
  have hc : Continuous (fun x => ‖fderiv ℝ f x‖) :=
    (hf.continuous_fderiv (by norm_num)).norm
  obtain ⟨B,hB⟩ := (isCompact_segmentUnion hK).bddAbove_image hc.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro x hx y hy
  have hs := segment_subset_segmentUnion hy hx
  apply (convex_segment y x).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hf.differentiable (by norm_num) z)
    (fun z hz => (hB ⟨z,hs hz,rfl⟩).trans (le_max_left _ _))
    (left_mem_segment ℝ y x) (right_mem_segment ℝ y x)

/-- Multiplying an already proved sequence-space rate by the common inverse
Lipschitz constant preserves the exponent and cutoff independence. -/
theorem transfer_rate {K : Set E} (hK : IsCompact K) (f : E → G)
    (hf : ContDiff ℝ 1 f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {a C : ℝ}, 0 ≤ C → ∀ x ∈ K, ∀ y ∈ K,
      ‖x-y‖ ≤ C*a^(-(1/4 : ℝ)) →
      ‖f x-f y‖ ≤ (M*C)*a^(-(1/4 : ℝ)) := by
  obtain ⟨M,hM,hbound⟩ := compact_lipschitz hK f hf
  refine ⟨M,hM,?_⟩
  intro a C _ x hx y hy hxy
  calc ‖f x-f y‖ ≤ M*‖x-y‖ := hbound x hx y hy
    _ ≤ M*(C*a^(-(1/4 : ℝ))) := mul_le_mul_of_nonneg_left hxy hM
    _ = _ := by ring

end QuantumNLS.WindowCompactInverseR44b

#print axioms QuantumNLS.WindowCompactInverseR44b.isCompact_segmentUnion
#print axioms QuantumNLS.WindowCompactInverseR44b.compact_lipschitz
#print axioms QuantumNLS.WindowCompactInverseR44b.transfer_rate

-- Recursive type/value audit of every own declaration, including generated declarations.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.WindowCompactInverseR44b." ||
        n.toString.startsWith "_private.QuantumNLS.WindowCompactInverseR44b." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {n}"
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
  Lean.logInfo m!"R44b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
