import NlsGge.GK38.IsolatingGeometryBounds

/-! Consequences of the exact quantitative geometry and the approved finite
fit lemma: OPEN tail discs fit, strict CLOSED fit is only for fixed exceptions. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem isolating_geometry_disjoint38 (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (h : IsolatingGeometry38 C R c N) :
    Pairwise (fun m n => Disjoint (ball (C m) (R m)) (ball (C n) (R n))) := by
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro z hzm hzn
  have hc : 0 < c := lt_of_lt_of_le (by norm_num) h.2.2.1
  have hD : 0 < |((m - n : ℤ) : ℝ)| := abs_pos.mpr (by exact_mod_cast sub_ne_zero.mpr hmn)
  have hp : 0 < c⁻¹ * |((m - n : ℤ) : ℝ)| := mul_pos (inv_pos.mpr hc) hD
  have hl := (h.2.2.2.1 m n hmn).1
  have hu := ballDistance38_le_pair (C m) (C n) (R m) (R n) hzm hzn
  rw [dist_self] at hu
  linarith

theorem isolating_geometry_closure_separated38 (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (h : IsolatingGeometry38 C R c N) (m n : ℤ) (hmn : m ≠ n) :
    R m + R n < dist (C m) (C n) := by
  have hc : 0 < c := lt_of_lt_of_le (by norm_num) h.2.2.1
  have hD : 0 < |((m - n : ℤ) : ℝ)| := abs_pos.mpr (by exact_mod_cast sub_ne_zero.mpr hmn)
  have hp := (mul_pos (inv_pos.mpr hc) hD).trans_le (h.2.2.2.1 m n hmn).1
  rw [ballDistance38_eq _ _ (h.1 m).1 (h.1 n).1] at hp
  rcases lt_max_iff.mp hp with hf | hh
  · exact False.elim (lt_irrefl 0 hf)
  · linarith

theorem central_finite_fit38 (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (h : IsolatingGeometry38 C R c N) : ∃ L : ℕ, N ≤ L ∧ ∀ M : ℕ, L ≤ M →
      (∀ n : ℤ, |n| ≤ (M : ℤ) → ball (C n) (R n) ⊆ ball (0 : ℂ) (countingRadius38 M)) ∧
      (∀ n : ℤ, |n| ≤ (N : ℤ) → closedBall (C n) (R n) ⊆ ball (0 : ℂ) (countingRadius38 M)) := by
  have hTail : ∀ n : ℤ, (N : ℤ) < |n| → C n = countingCenter38 n ∧ R n = Real.pi / 4 :=
    fun n hn => ⟨(h.2.2.2.2 n hn).1, (h.2.2.2.2 n hn).2.1⟩
  obtain ⟨K, _, hdev⟩ := isolating_deviation_bound38 C R N hTail
  obtain ⟨J, hJ⟩ := exists_nat_gt ((K + (N : ℝ) * Real.pi) / Real.pi)
  let L : ℕ := max N J
  have hJL : (J : ℝ) ≤ (L : ℝ) := by exact_mod_cast le_max_right N J
  have hbound : K + (N : ℝ) * Real.pi < (L : ℝ) * Real.pi := by
    have hh := (div_lt_iff₀ Real.pi_pos).mp hJ
    nlinarith [Real.pi_pos]
  have hfinite : ∀ M : ℕ, L ≤ M → ∀ n : ℤ, |n| ≤ (N : ℤ) →
      closedBall (C n) (R n) ⊆ ball (0 : ℂ) (countingRadius38 M) := by
    intro M hLM n hn z hz
    have hML : (L : ℝ) ≤ (M : ℝ) := by exact_mod_cast hLM
    have hc := countingCenter_low_norm38 hn
    have ht : ‖C n‖ ≤ ‖C n - countingCenter38 n‖ + ‖countingCenter38 n‖ := by
      simpa only [sub_add_cancel] using norm_add_le (C n - countingCenter38 n) (countingCenter38 n)
    have hzC : ‖z - C n‖ ≤ R n := mem_closedBall_iff_norm.mp hz
    have htz : ‖z‖ ≤ ‖z - C n‖ + ‖C n‖ := by
      simpa only [sub_add_cancel] using norm_add_le (z - C n) (C n)
    rw [mem_ball_zero_iff]
    unfold countingRadius38
    nlinarith [hdev n, Real.pi_pos]
  refine ⟨L, le_max_left _ _, fun M hLM => ⟨?_, hfinite M hLM⟩⟩
  intro n hn
  by_cases hsmall : |n| ≤ (N : ℤ)
  · exact ball_subset_closedBall.trans (hfinite M hLM n hsmall)
  · obtain ⟨hc, hr⟩ := hTail n (lt_of_not_ge hsmall)
    rw [hc, hr]
    exact counting_small_subset_central38 hn

theorem isolating_horizontal_order38 (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (h : IsolatingGeometry38 C R c N) {m n : ℤ} (hmn : m < n) {z w : ℂ}
    (hz : z ∈ ball (C m) (R m)) (hw : w ∈ ball (C n) (R n)) : z.re < w.re := by
  have hsep := isolating_geometry_closure_separated38 C R c N h m n (ne_of_lt hmn)
  have hc := h.2.1 hmn
  rw [dist_eq_norm, realType_norm_sub_real38 _ _ (h.1 m).2 (h.1 n).2,
    abs_of_neg (sub_neg.mpr hc)] at hsep
  have hz' : |z.re - (C m).re| < R m :=
    (Complex.abs_re_le_norm (z - C m)).trans_lt (mem_ball_iff_norm.mp hz)
  have hw' : |w.re - (C n).re| < R n :=
    (Complex.abs_re_le_norm (w - C n)).trans_lt (mem_ball_iff_norm.mp hw)
  have hza := (abs_lt.mp hz').2
  have hwb := (abs_lt.mp hw').1
  linarith

end
end NlsGge.GK38
