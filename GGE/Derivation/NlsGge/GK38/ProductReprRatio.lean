import NlsGge.GK38.ProductReprGrowth

/-! # S4: comparison of the actual and constructed entire functions on circles

Source anchors: GK book Lemmas 6.5/6.8. Denominator lower bounds precede
quotient estimates; F5's neighborhood estimates are instantiated at the fixed potential.
-/
set_option autoImplicit false
open Filter Topology SummationFilter Set Metric
namespace NlsGge.GK38
noncomputable section

/-- Two small relative errors against one nonzero comparison imply a small ratio error. -/
theorem productRepr_relative_ratio38 (f g t : ℂ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) (ht : t ≠ 0)
    (hf : ‖f - t‖ ≤ δ * ‖t‖) (hg : ‖g - t‖ ≤ δ * ‖t‖) :
    g ≠ 0 ∧ ‖f / g - 1‖ ≤ 4 * δ := by
  obtain ⟨hgne, hglower⟩ := productRepr_relative_denominator38 g t δ hδhalf ht hg
  have htp : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hgp : 0 < ‖g‖ := norm_pos_iff.mpr hgne
  have hdiff : ‖f - g‖ ≤ 2 * δ * ‖t‖ := by
    calc ‖f - g‖ = ‖(f - t) - (g - t)‖ := by congr 1; ring
      _ ≤ ‖f - t‖ + ‖g - t‖ := norm_sub_le _ _
      _ ≤ δ * ‖t‖ + δ * ‖t‖ := add_le_add hf hg
      _ = _ := by ring
  have he : f / g - 1 = (f - g) / g := by field_simp
  refine ⟨hgne, ?_⟩
  rw [he, norm_div]
  apply (div_le_iff₀ hgp).mpr
  nlinarith

/-- F5's periodic and derivative errors against the same sine comparisons as the products. -/
theorem productRepr_actual_circle_growth38 (φ : PotPair) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ,
      ‖z‖ = (n : ℝ) * Real.pi + Real.pi / 2 →
      ‖perChar φ z - (-4 * Complex.sin z ^ 2)‖ ≤ ε * ‖(-4 : ℂ) * Complex.sin z ^ 2‖ ∧
      ‖deriv (discrim φ) z - (-2 * Complex.sin z)‖ ≤ ε * ‖(-2 : ℂ) * Complex.sin z‖ := by
  obtain ⟨C, hC, hsin⟩ := exists_sine_off_discs_lower_bound38
  obtain ⟨Up, hUp, Rp, hp⟩ := perChar_asymp φ (4 * ε) (by positivity)
  obtain ⟨Ud, hUd, Rd, hd⟩ := discrimDeriv_asymp φ (2 * ε / C) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_ge (max Rp Rd / Real.pi)
  refine ⟨N, fun n hn z hz => ?_⟩
  have hR : max Rp Rd ≤ ‖z‖ := by
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hbase : max Rp Rd ≤ (N : ℝ) * Real.pi :=
      (div_le_iff₀ Real.pi_pos).mp hN
    rw [hz]
    nlinarith [Real.pi_pos]
  have hsep := productRepr_circle_separation38 hz
  constructor
  · have h := hp φ (mem_of_mem_nhds hUp) z ((le_max_left _ _).trans hR) hsep
    simpa only [norm_mul, norm_neg, Complex.norm_ofNat, norm_pow, mul_assoc, mul_comm,
      mul_left_comm] using h
  · have h := hd φ (mem_of_mem_nhds hUd) z ((le_max_right _ _).trans hR)
    have hl := hsin z hsep
    calc ‖deriv (discrim φ) z - (-2 * Complex.sin z)‖
        ≤ (2 * ε / C) * Real.exp |z.im| := h
      _ ≤ (2 * ε / C) * (C * ‖Complex.sin z‖) := by gcongr
      _ = ε * ‖(-2 : ℂ) * Complex.sin z‖ := by
        rw [norm_mul, norm_neg, Complex.norm_ofNat]
        field_simp

/-- The strict circle ratio estimates used by the accepted entire-ratio theorem. -/
theorem productRepr_circle_ratio38 (φ : PotPair) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ,
      ‖z‖ = (n : ℝ) * Real.pi + Real.pi / 2 →
      periodicProduct38 φ z ≠ 0 ∧ criticalProduct38 φ z ≠ 0 ∧
      ‖perChar φ z / periodicProduct38 φ z - 1‖ < ε ∧
      ‖deriv (discrim φ) z / criticalProduct38 φ z - 1‖ < ε := by
  let δ := min (1 / 4) (ε / 8)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδhalf : δ ≤ 1 / 2 := (min_le_left _ _).trans (by norm_num)
  have hδε : 4 * δ < ε := by
    have h := min_le_right (1 / 4 : ℝ) (ε / 8)
    change δ ≤ ε / 8 at h
    linarith
  obtain ⟨Np, hp⟩ := productRepr_normalized_growth38 φ δ hδ
  obtain ⟨Na, ha⟩ := productRepr_actual_circle_growth38 φ δ hδ
  refine ⟨max Np Na, fun n hn z hz => ?_⟩
  obtain ⟨hgp, hgd⟩ := hp n ((le_max_left _ _).trans hn) z hz
  obtain ⟨hfp, hfd⟩ := ha n ((le_max_right _ _).trans hn) z hz
  have hs := productRepr_circle_sin_ne_zero38 hz
  have htP : (-4 : ℂ) * Complex.sin z ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hs)
  have htD : (-2 : ℂ) * Complex.sin z ≠ 0 := mul_ne_zero (by norm_num) hs
  obtain ⟨hneP, hrP⟩ := productRepr_relative_ratio38 _ _ _ δ hδ.le hδhalf htP hfp hgp
  obtain ⟨hneD, hrD⟩ := productRepr_relative_ratio38 _ _ _ δ hδ.le hδhalf htD hfd hgd
  exact ⟨hneP, hneD, hrP.trans_lt hδε, hrD.trans_lt hδε⟩

end
end NlsGge.GK38
