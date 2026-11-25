import NlsGge.GK38.DirichletL2
import NlsGge.GK38.Lib.EntireProducts

/-! # D1: symmetric entire product, including zero factors

Book Lemma 5.4. Genuine convergence and circle nonvanishing precede all
product identities and divisions. The prefactor is exactly minus one. -/
set_option autoImplicit false
open Filter Topology SummationFilter Set Metric
namespace NlsGge.GK38
noncomputable section

/-- Convergence is proved at every spectral parameter, including any root. -/
theorem dirichletChar_multipliable (φ : PotPair) (z : ℂ) :
    Multipliable (fun m : ℤ => (muSeq φ m - z) / (πn m : ℂ)) (symmetricIcc ℤ) :=
  (Lib.product_entire (muSeq φ) (muSeq_summable38 φ)).1 z

def normalizedDirichletProduct38 (φ : PotPair) (z : ℂ) : ℂ :=
  -∏'[symmetricIcc ℤ] m : ℤ, (muSeq φ m - z) / (πn m : ℂ)

theorem differentiable_normalizedDirichletProduct38 (φ : PotPair) :
    Differentiable ℂ (normalizedDirichletProduct38 φ) :=
  (Lib.product_entire (muSeq φ) (muSeq_summable38 φ)).2.1.neg

theorem order_normalizedDirichletProduct38 (φ : PotPair) (w : ℂ) :
    analyticOrderAt (normalizedDirichletProduct38 φ) w = analyticOrderAt (dirichletChar φ) w := by
  change analyticOrderAt (-(fun z : ℂ => ∏'[symmetricIcc ℤ] m : ℤ,
    (muSeq φ m - z) / (πn m : ℂ))) w = _
  rw [analyticOrderAt_neg, (Lib.product_entire (muSeq φ) (muSeq_summable38 φ)).2.2 w]
  exact (muSeq_occurrence38 φ w).2

/-- Fixed-potential strict circle ratio, with sine and denominator nonzero first. -/
theorem dirichlet_ratio_circle38 (φ : PotPair) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ,
      ‖z‖ = (n : ℝ) * Real.pi + Real.pi / 2 →
      Complex.sin z ≠ 0 ∧ normalizedDirichletProduct38 φ z ≠ 0 ∧
        ‖dirichletChar φ z / normalizedDirichletProduct38 φ z - 1‖ < ε := by
  let δ : ℝ := min (ε / 8) (1 / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδquarter : δ ≤ 1 / 4 := min_le_right _ _
  have hδeps : δ ≤ ε / 8 := min_le_left _ _
  obtain ⟨Np, hp⟩ := Lib.product_growth (muSeq φ) (muSeq_summable38 φ) δ hδ
  obtain ⟨U, hU, R, hR⟩ := dirichletChar_asymp φ (δ / sineOffDiscsConstant38)
    (div_pos hδ sineOffDiscsConstant38_pos)
  obtain ⟨Nr, hNr⟩ := exists_nat_ge (R / Real.pi)
  have hNrR : R ≤ (Nr : ℝ) * Real.pi + Real.pi / 2 := by
    have hh := (div_le_iff₀ Real.pi_pos).mp hNr
    linarith [Real.pi_pos]
  refine ⟨max Np Nr, fun n hn z hz => ?_⟩
  have hnp : Np ≤ n := (le_max_left _ _).trans hn
  have hnr : (Nr : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_max_right Np Nr).trans hn
  have hzR : R ≤ ‖z‖ := by
    rw [hz]
    nlinarith [Real.pi_pos]
  have hsep : ∀ m : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 m‖ := by
    intro m
    have hh := Lib.pi_mul_dd_le hz m
    have hd := Lib.half_le_circDist n m
    rw [norm_sub_rev] at hh
    change Real.pi * Lib.circDist n m ≤ ‖z - countingCenter38 m‖ at hh
    nlinarith [Real.pi_pos]
  have hsin : Complex.sin z ≠ 0 := counting_sin_ne_zero38 hsep
  have hspos : 0 < ‖Complex.sin z‖ := norm_pos_iff.mpr hsin
  have hprod : ‖normalizedDirichletProduct38 φ z - Complex.sin z‖ ≤ δ * ‖Complex.sin z‖ := by
    have hh := hp n hnp z hz
    have he : normalizedDirichletProduct38 φ z - Complex.sin z =
        -((∏'[symmetricIcc ℤ] m : ℤ, (muSeq φ m - z) / (πn m : ℂ)) + Complex.sin z) := by
      dsimp [normalizedDirichletProduct38]
      ring
    rw [he, norm_neg]
    exact hh
  have hchar : ‖dirichletChar φ z - Complex.sin z‖ ≤ δ * ‖Complex.sin z‖ := by
    have hh := hR φ (mem_of_mem_nhds hU) z hzR
    have hbound := sine_off_discs_lower_bound38 z hsep
    have hle := mul_le_mul_of_nonneg_left hbound (div_pos hδ sineOffDiscsConstant38_pos).le
    have he : δ / sineOffDiscsConstant38 * (sineOffDiscsConstant38 * ‖Complex.sin z‖) =
        δ * ‖Complex.sin z‖ := by
      field_simp [sineOffDiscsConstant38_pos.ne']
    exact hh.trans (by simpa only [he] using hle)
  have hlower : ‖Complex.sin z‖ / 2 ≤ ‖normalizedDirichletProduct38 φ z‖ := by
    have hh := norm_sub_norm_le (Complex.sin z) (normalizedDirichletProduct38 φ z)
    rw [norm_sub_rev] at hh
    nlinarith
  have hnz : normalizedDirichletProduct38 φ z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hlower)
  have hnum : ‖dirichletChar φ z - normalizedDirichletProduct38 φ z‖ ≤ 2 * δ * ‖Complex.sin z‖ := by
    have hh := norm_sub_le (dirichletChar φ z - Complex.sin z)
      (normalizedDirichletProduct38 φ z - Complex.sin z)
    have he : dirichletChar φ z - Complex.sin z -
        (normalizedDirichletProduct38 φ z - Complex.sin z) =
        dirichletChar φ z - normalizedDirichletProduct38 φ z := by ring
    rw [he] at hh
    linarith
  refine ⟨hsin, hnz, ?_⟩
  rw [div_sub_one hnz, norm_div]
  have hle : ‖dirichletChar φ z - normalizedDirichletProduct38 φ z‖ /
      ‖normalizedDirichletProduct38 φ z‖ ≤ 4 * δ := by
    apply (div_le_iff₀ (norm_pos_iff.mpr hnz)).mpr
    have hh := mul_le_mul_of_nonneg_left hlower (show 0 ≤ 4 * δ by positivity)
    nlinarith
  exact hle.trans_lt (by linarith)

/-- The full Dirichlet characteristic, including its roots, is the normalized symmetric product. -/
theorem dirichletChar_product (φ : PotPair) (z : ℂ) :
    dirichletChar φ z = -∏'[symmetricIcc ℤ] m : ℤ, (muSeq φ m - z) / (πn m : ℂ) := by
  have he := Lib.entire_eq_of_ratio_tendsto_one
    (fun w => (analyticOnNhd_dirichletChar_z φ w (mem_univ _)).differentiableAt)
    (differentiable_normalizedDirichletProduct38 φ)
    (fun w => (order_normalizedDirichletProduct38 φ w).le)
    (fun ε hε => by
      obtain ⟨N, hN⟩ := dirichlet_ratio_circle38 φ ε hε
      exact ⟨N, fun n hn w hw => (hN n hn w hw).2.2⟩)
  exact congrFun he z

end
end NlsGge.GK38
