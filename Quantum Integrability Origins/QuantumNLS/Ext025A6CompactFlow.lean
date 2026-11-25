import QuantumNLS.Ext025A2ODE

/-! GP-04 compact-trajectory local existence. A finite cover of an actual
compact set yields common positive time and initial radii for local solutions
of an autonomous C1 field. Analytic dependence, derivative bounds of the flow,
and gluing/subdivision remain separate obligations. -/
set_option autoImplicit false
noncomputable section
open Set Metric
namespace QuantumNLS.Ext025A6
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The finite cover and both common positive radii are constructed from C1
regularity at the compact set. Solutions for all nearby initial points are
conclusions, rather than supplied local maps. -/
theorem compact_common_local_solutions {f : E → E} {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty)
    (hf : ∀ x ∈ K, ContDiffAt ℝ 1 f x) (b : ℝ) :
    ∃ r > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x ∈ K, ∀ y ∈ closedBall x r,
      ∃ α : ℝ → E, α b = y ∧
        ∀ t ∈ Ioo (b - δ) (b + δ), HasDerivAt α (f (α t)) t := by
  classical
  have H (x : K) :=
    (hf x x.property).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt b
  choose r hr δ hδ hsol using H
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => ball (x : E) (r x / 2))
    (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (half_pos (hr ⟨x, hx⟩))⟩)
  have hsne : s.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨i, hi, _⟩ := mem_iUnion₂.mp (hs hx)
    exact ⟨i, hi⟩
  let r₀ := s.inf' hsne (fun i => r i / 2)
  let δ₀ := s.inf' hsne δ
  have hr₀ : 0 < r₀ := by
    dsimp only [r₀]
    rw [Finset.lt_inf'_iff]
    exact fun i _ => half_pos (hr i)
  have hδ₀ : 0 < δ₀ := by
    dsimp only [δ₀]
    rw [Finset.lt_inf'_iff]
    exact fun i _ => hδ i
  refine ⟨r₀, hr₀, δ₀, hδ₀, ?_⟩
  intro x hx y hy
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
  have hri : r₀ ≤ r i / 2 := Finset.inf'_le _ hi
  have hδi : δ₀ ≤ δ i := Finset.inf'_le _ hi
  have hyi : y ∈ closedBall (i : E) (r i) := by
    rw [mem_closedBall] at hy ⊢
    rw [mem_ball] at hxi
    calc
      dist y (i : E) ≤ dist y x + dist x (i : E) := dist_triangle _ _ _
      _ ≤ r₀ + r i / 2 := add_le_add hy hxi.le
      _ ≤ r i := by linarith
  obtain ⟨α, hα, hdα⟩ := hsol i y hyi
  refine ⟨α, hα, fun t ht => hdα t ?_⟩
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
end QuantumNLS.Ext025A6

#print axioms QuantumNLS.Ext025A6.compact_common_local_solutions
