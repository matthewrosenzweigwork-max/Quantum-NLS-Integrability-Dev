import NlsGge.GK38.ProductReprConstruction

/-! # S4: fixed-potential circle growth and explicit denominator separation

Source anchors: GK book Lemmas 6.5/6.8 and Appendix C, Lemma C.5.
Every cutoff here is chosen for one fixed potential.
-/
set_option autoImplicit false
open Filter Topology SummationFilter Set Metric
namespace NlsGge.GK38
noncomputable section

theorem productRepr_circle_separation38 {n : ℕ} {z : ℂ}
    (hz : ‖z‖ = (n : ℝ) * Real.pi + Real.pi / 2) (m : ℤ) :
    Real.pi / 4 ≤ ‖z - (m : ℂ) * (Real.pi : ℂ)‖ := by
  have h := Lib.pi_mul_dd_le hz m
  have hh := Lib.half_le_circDist n m
  rw [norm_sub_rev] at h
  nlinarith [Real.pi_pos]

theorem productRepr_circle_sin_ne_zero38 {n : ℕ} {z : ℂ}
    (hz : ‖z‖ = (n : ℝ) * Real.pi + Real.pi / 2) : Complex.sin z ≠ 0 := by
  intro hzero
  obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.mp hzero
  have h := productRepr_circle_separation38 hz m
  rw [hm, sub_self, norm_zero] at h
  linarith [Real.pi_pos]

/-- Two comparisons with `-sin` give the paired comparison with `sin²`. -/
theorem productRepr_pair_error38 (a b s : ℂ) (η : ℝ) (hη : 0 ≤ η)
    (ha : ‖a + s‖ ≤ η * ‖s‖) (hb : ‖b + s‖ ≤ η * ‖s‖) :
    ‖a * b - s ^ 2‖ ≤ (2 * η + η ^ 2) * ‖s‖ ^ 2 := by
  have hna : ‖a‖ ≤ (1 + η) * ‖s‖ := by
    calc ‖a‖ = ‖(a + s) - s‖ := by congr 1; ring
      _ ≤ ‖a + s‖ + ‖s‖ := norm_sub_le _ _
      _ ≤ η * ‖s‖ + ‖s‖ := add_le_add ha le_rfl
      _ = _ := by ring
  have he : a * b - s ^ 2 = a * (b + s) - s * (a + s) := by ring
  rw [he]
  calc ‖a * (b + s) - s * (a + s)‖
      ≤ ‖a * (b + s)‖ + ‖s * (a + s)‖ := norm_sub_le _ _
    _ = ‖a‖ * ‖b + s‖ + ‖s‖ * ‖a + s‖ := by rw [norm_mul, norm_mul]
    _ ≤ ((1 + η) * ‖s‖) * (η * ‖s‖) + ‖s‖ * (η * ‖s‖) := by
      gcongr
    _ = _ := by ring

theorem productRepr_circle_growth38 (φ : PotPair) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ,
      ‖z‖ = (n : ℝ) * Real.pi + Real.pi / 2 →
      ‖pairedProduct38 φ z - Complex.sin z ^ 2‖ ≤ ε * ‖Complex.sin z‖ ^ 2 ∧
      ‖singleProduct38 (lamDot φ) z + Complex.sin z‖ ≤ ε * ‖Complex.sin z‖ := by
  let η := min 1 (ε / 3)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : η ≤ ε / 3 := min_le_right _ _
  have hcoeff : 2 * η + η ^ 2 ≤ ε := by nlinarith
  obtain ⟨Np, hp⟩ := Lib.product_growth (lamPlus φ) (periodic_plus_summable38 φ) η hη
  obtain ⟨Nm, hm⟩ := Lib.product_growth (lamMinus φ) (periodic_minus_summable38 φ) η hη
  obtain ⟨Nd, hd⟩ := Lib.product_growth (lamDot φ) (critical_summable38 φ) ε hε
  refine ⟨max (max Np Nm) Nd, ?_⟩
  intro n hn z hz
  constructor
  · rw [pairedProduct_eq_mul38]
    exact (productRepr_pair_error38 _ _ _ η hη.le
      (hp n (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn) z hz)
      (hm n (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn) z hz)).trans
      (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _))
  · exact hd n (le_trans (le_max_right _ _) hn) z hz

/-- Product errors are normalized against the same nonzero sine expressions as F5. -/
theorem productRepr_normalized_growth38 (φ : PotPair) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ,
      ‖z‖ = (n : ℝ) * Real.pi + Real.pi / 2 →
      ‖periodicProduct38 φ z - (-4 * Complex.sin z ^ 2)‖ ≤
        ε * ‖(-4 : ℂ) * Complex.sin z ^ 2‖ ∧
      ‖criticalProduct38 φ z - (-2 * Complex.sin z)‖ ≤
        ε * ‖(-2 : ℂ) * Complex.sin z‖ := by
  obtain ⟨N, hN⟩ := productRepr_circle_growth38 φ ε hε
  refine ⟨N, fun n hn z hz => ?_⟩
  obtain ⟨hp, hd⟩ := hN n hn z hz
  have heP : periodicProduct38 φ z - (-4 * Complex.sin z ^ 2) =
      (-4 : ℂ) * (pairedProduct38 φ z - Complex.sin z ^ 2) := by
    unfold periodicProduct38; ring
  have heD : criticalProduct38 φ z - (-2 * Complex.sin z) =
      (2 : ℂ) * (singleProduct38 (lamDot φ) z + Complex.sin z) := by
    unfold criticalProduct38; ring
  constructor
  · rw [heP, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat, norm_pow]
    nlinarith
  · rw [heD, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat]
    nlinarith

/-- A relative error at most one half gives a positive denominator lower bound. -/
theorem productRepr_relative_denominator38 (g t : ℂ) (δ : ℝ)
    (hδ : δ ≤ 1 / 2) (ht : t ≠ 0) (hg : ‖g - t‖ ≤ δ * ‖t‖) :
    g ≠ 0 ∧ ‖t‖ / 2 ≤ ‖g‖ := by
  have hpos : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have htriangle : ‖t‖ ≤ ‖g - t‖ + ‖g‖ := by
    calc ‖t‖ = ‖g - (g - t)‖ := by congr 1; ring
      _ ≤ ‖g‖ + ‖g - t‖ := norm_sub_le _ _
      _ = _ := by ring
  have hhalf : ‖t‖ / 2 ≤ ‖g‖ := by nlinarith
  refine ⟨?_, hhalf⟩
  intro hzero
  rw [hzero, norm_zero] at hhalf
  linarith

theorem productRepr_circle_denominators38 (φ : PotPair) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ,
      ‖z‖ = (n : ℝ) * Real.pi + Real.pi / 2 →
      Complex.sin z ≠ 0 ∧ periodicProduct38 φ z ≠ 0 ∧ criticalProduct38 φ z ≠ 0 := by
  obtain ⟨N, hN⟩ := productRepr_normalized_growth38 φ (1 / 2) (by norm_num)
  refine ⟨N, fun n hn z hz => ?_⟩
  have hs := productRepr_circle_sin_ne_zero38 hz
  obtain ⟨hp, hd⟩ := hN n hn z hz
  have htP : (-4 : ℂ) * Complex.sin z ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hs)
  have htD : (-2 : ℂ) * Complex.sin z ≠ 0 := mul_ne_zero (by norm_num) hs
  exact ⟨hs, (productRepr_relative_denominator38 _ _ _ le_rfl htP hp).1,
    (productRepr_relative_denominator38 _ _ _ le_rfl htD hd).1⟩

end
end NlsGge.GK38
