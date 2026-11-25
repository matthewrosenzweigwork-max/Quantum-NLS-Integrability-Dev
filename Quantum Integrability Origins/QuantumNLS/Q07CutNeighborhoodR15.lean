import QuantumNLS.Q07RealCutsR15

/-! Stability of the compact real-cut checkpoint on one fixed interval-L1
neighborhood. The transfer error on the neighborhood is proved from the
original Volterra stability bound. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Filter Topology Metric
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
local instance : TopologicalSpace.PseudoMetrizableSpace QuantumNLS.SpatialTransfer.Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))
local instance : ENormedAddMonoid QuantumNLS.SpatialTransfer.Mat2 := NormedAddGroup.toENormedAddMonoid
namespace QuantumNLS.Q07CutNeighborhoodR15
open Q07RealCutsR15
variable {L κ : ℝ}

theorem uniform_interaction_near (hL : 0 ≤ L) {K : Set (Profile L)} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ t : ℝ in cocompact ℝ,
      ∀ u ∈ K, ∀ v : Profile L, ‖v-u‖ < η → ‖interaction κ v t - 1‖ < ε := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (f := fun u : Profile L => u) continuousOn_id
  let C := Real.sqrt κ *
    (Real.exp (Real.sqrt κ * (B+1)) * Real.exp (Real.sqrt κ * B))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let η := min 1 (ε / (2*(C+1)))
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨η, hη, ?_⟩
  filter_upwards [uniform_interaction (κ := κ) hL hK (half_pos hε)] with t ht u hu v hv
  have hv1 : ‖v-u‖ < 1 := hv.trans_le (min_le_left _ _)
  have hvB : ‖v‖ ≤ B+1 := by
    have hh := norm_add_le (v-u) u
    rw [sub_add_cancel] at hh
    linarith [hB u hu]
  have hst : ‖interaction κ v t - interaction κ u t‖ ≤ C * ‖v-u‖ := by
    refine (interaction_sub_le hL v u t).trans ?_
    have he1 := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hvB (Real.sqrt_nonneg κ))
    have he2 := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hB u hu) (Real.sqrt_nonneg κ))
    calc
      _ ≤ Real.sqrt κ * ‖v-u‖ *
          (Real.exp (Real.sqrt κ * (B+1)) * Real.exp (Real.sqrt κ * B)) := by gcongr
      _ = C * ‖v-u‖ := by dsimp [C]; ring
  have hsmall : C * ‖v-u‖ < ε / 2 := by
    have h1 : ‖v-u‖ < ε / (2*(C+1)) := hv.trans_le (min_le_right _ _)
    have h2 : C * (ε / (2*(C+1))) < ε / 2 := by
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < 2*(C+1))]
      nlinarith
    exact (mul_le_mul_of_nonneg_left h1.le hC).trans_lt h2
  have htri := norm_add_le (interaction κ v t - interaction κ u t) (interaction κ u t - 1)
  rw [sub_add_sub_cancel] at htri
  exact htri.trans_lt (by linarith [ht u hu])

theorem uniform_real_asymptotic_near (hL : 0 < L) {K : Set (Profile L)} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ t : ℝ in cocompact ℝ,
      ∀ u ∈ K, ∀ v : Profile L, ‖v-u‖ < η →
        |discriminant κ v t - 2 * Real.cos (t*L/2)| < ε := by
  obtain ⟨η, hη, hh⟩ := uniform_interaction_near (κ := κ) hL.le hK (half_pos hε)
  refine ⟨η, hη, ?_⟩
  filter_upwards [hh] with t ht u hu v hv
  exact (discriminant_error_le hL v t).trans_lt (by linarith [ht u hu v hv])

open QuantumNLS.PROP017UniformN (cutSeq)
open QuantumNLS.RootSpectralInputsDischarge (cos_cut_bound)

/-- Both signed cut intervals stay strictly in the open bands on one fixed
neighborhood, uniformly over the compact class. -/
theorem uniform_real_cuts_near (hL : 0 < L) {K : Set (Profile L)} (hK : IsCompact K) :
    ∃ η : ℝ, 0 < η ∧ ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l → ∀ u ∈ K,
      ∀ v : Profile L, ‖v-u‖ < η → ∀ a : ℝ,
      (a = cutSeq L l ∨ a = -cutSeq L l) →
      (∀ s : ℝ, |s| < 1 / L → |discriminant κ v (a + s)| < 3 / 2) ∧
        |discriminant κ v a| ≤ 1 / 2 := by
  let : Fact (0 < L) := ⟨hL⟩
  obtain ⟨η, hη, h1⟩ := uniform_real_asymptotic_near (κ := κ) hL hK (ε := 1/2) (by norm_num)
  refine ⟨η, hη, ?_⟩
  rw [cocompact_eq_atBot_atTop, Filter.eventually_sup, Filter.eventually_atBot, Filter.eventually_atTop] at h1
  obtain ⟨⟨T2, hT2⟩, ⟨T1, hT1⟩⟩ := h1
  have hT : ∀ t : ℝ, max T1 (-T2) ≤ |t| → ∀ u ∈ K, ∀ v : Profile L, ‖v-u‖ < η → |discriminant κ v t - 2 * Real.cos (t * L / 2)| < 1 / 2 := by
    intro t ht u hu v hv
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h] at ht
      have := hT1 t (le_trans (le_max_left _ _) ht)
      simpa [Real.dist_eq] using this u hu v hv
    · rw [abs_of_nonpos h] at ht
      have : t ≤ T2 := by have := le_trans (le_max_right _ _) ht; linarith
      have := hT2 t this
      simpa [Real.dist_eq] using this u hu v hv
  obtain ⟨l0, hl0⟩ := exists_nat_gt ((max T1 (-T2) + 1 / L) * L)
  refine ⟨l0, fun l hl u hu v hv a ha => ?_⟩
  have hapos : max T1 (-T2) + 1 / L < |a| := by
    have habs : |a| = cutSeq L l := by
      rcases ha with ha | ha
      · rw [ha]; unfold cutSeq; exact abs_of_nonneg (by positivity)
      · rw [ha, abs_neg]; unfold cutSeq; exact abs_of_nonneg (by positivity)
    rw [habs]
    unfold cutSeq
    rw [lt_div_iff₀ hL]
    have hlle : (l0 : ℝ) ≤ l := by exact_mod_cast hl
    have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hl0' : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    nlinarith
  have key : ∀ s : ℝ, |s| < 1 / L → |discriminant κ v (a + s)| < 3 / 2 := by
    intro s hs
    have hsL : |s| * L < 1 := by
      have := (lt_div_iff₀ hL).1 hs
      exact this
    have habs : max T1 (-T2) ≤ |a + s| := by
      have := abs_sub_abs_le_abs_sub a (a + s)
      rw [show a - (a + s) = -s by ring, abs_neg] at this
      linarith
    have hd := hT (a + s) habs u hu v hv
    obtain ⟨-, hc⟩ := cos_cut_bound hL l ha s
    have hc2 : |2 * Real.cos ((a + s) * L / 2)| ≤ |s| * L := by
      rw [abs_mul]; norm_num; linarith
    have := abs_sub_abs_le_abs_sub (discriminant κ v (a + s)) (2 * Real.cos ((a + s) * L / 2))
    linarith
  refine ⟨key, ?_⟩
  have hd := hT (a + 0) (by
    rw [add_zero]
    exact le_of_lt (lt_of_le_of_lt (le_add_of_nonneg_right (by positivity)) hapos))
  have hd := hd u hu v hv
  obtain ⟨hc0, -⟩ := cos_cut_bound hL l ha 0
  rw [add_zero, hc0] at hd
  simp at hd
  linarith [hd]

end QuantumNLS.Q07CutNeighborhoodR15
