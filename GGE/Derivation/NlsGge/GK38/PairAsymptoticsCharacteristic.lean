import NlsGge.GK38.PairAsymptoticsDerivative
import NlsGge.GK38.PairAsymptoticsSine

/-! # F5: relative periodic-characteristic asymptotics off the lattice discs (GK Lemma 6.2) -/

set_option autoImplicit false

open Filter Topology MeasureTheory Set Metric

namespace NlsGge.GK38

noncomputable section

/-- Explicit separation is exactly the complement of the union of the open lattice discs. -/
theorem outside_lattice_discs_iff38 (z : ℂ) :
    (z ∉ ⋃ n : ℤ, ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4)) ↔
      (∀ n : ℤ, Real.pi / 4 ≤ ‖z - (n : ℂ) * (Real.pi : ℂ)‖) := by
  simp only [mem_iUnion, mem_ball_iff_norm, not_exists, not_lt]

theorem norm_cos_le_exp_im38 (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have h1 : ‖Complex.exp (z * Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa [Complex.mul_re] using neg_le_abs z.im
  have h2 : ‖Complex.exp (-z * Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa [Complex.mul_re] using le_abs_self z.im
  rw [Complex.cos, norm_div, Complex.norm_ofNat]
  calc ‖Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)‖ / 2
      ≤ (‖Complex.exp (z * Complex.I)‖ + ‖Complex.exp (-z * Complex.I)‖) / 2 :=
        div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ ≤ (Real.exp |z.im| + Real.exp |z.im|) / 2 := by gcongr
    _ = _ := by ring

theorem perChar_asymp (φ₀ : PotPair) : ∀ ε > 0, ∃ U ∈ 𝓝 φ₀, ∃ R : ℝ,
    ∀ φ ∈ U, ∀ z : ℂ, R ≤ ‖z‖ →
      (∀ n : ℤ, Real.pi / 4 ≤ ‖z - (n : ℂ) * (Real.pi : ℂ)‖) →
        ‖perChar φ z - (-4 * Complex.sin z ^ 2)‖ ≤ ε * ‖Complex.sin z‖ ^ 2 := by
  intro ε hε
  obtain ⟨C, hC, hsin⟩ := exists_sine_off_discs_lower_bound38
  let δ : ℝ := min 1 (ε / (5 * C ^ 2))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hcoeff : δ * (δ + 4) * C ^ 2 ≤ ε := by
    have hp : δ * (δ + 4) ≤ 5 * δ := by nlinarith
    have h := (le_div_iff₀ (by positivity : 0 < 5 * C ^ 2)).mp
      (show δ ≤ ε / (5 * C ^ 2) from min_le_right _ _)
    calc δ * (δ + 4) * C ^ 2 ≤ (5 * δ) * C ^ 2 :=
          mul_le_mul_of_nonneg_right hp (sq_nonneg _)
      _ ≤ ε := by nlinarith [h]
  obtain ⟨U, hU, R, hR⟩ := discrim_asymp φ₀ δ hδ
  refine ⟨U, hU, R, fun φ hφ z hz hsep => ?_⟩
  have he : ‖discrim φ z - 2 * Complex.cos z‖ ≤ δ * Real.exp |z.im| := hR φ hφ z hz
  have hplus : ‖discrim φ z + 2 * Complex.cos z‖ ≤ (δ + 4) * Real.exp |z.im| := by
    have heq : discrim φ z + 2 * Complex.cos z =
        (discrim φ z - 2 * Complex.cos z) + 4 * Complex.cos z := by ring
    rw [heq]
    calc ‖(discrim φ z - 2 * Complex.cos z) + 4 * Complex.cos z‖
        ≤ ‖discrim φ z - 2 * Complex.cos z‖ + ‖4 * Complex.cos z‖ := norm_add_le _ _
      _ ≤ δ * Real.exp |z.im| + 4 * Real.exp |z.im| := by
        rw [norm_mul, Complex.norm_ofNat]
        exact add_le_add he (mul_le_mul_of_nonneg_left (norm_cos_le_exp_im38 z) (by norm_num))
      _ = _ := by ring
  have halg : perChar φ z - (-4 * Complex.sin z ^ 2) =
      (discrim φ z - 2 * Complex.cos z) * (discrim φ z + 2 * Complex.cos z) := by
    rw [perChar_eq]
    have htrig := Complex.sin_sq_add_cos_sq z
    linear_combination 4 * htrig
  rw [halg, norm_mul]
  calc ‖discrim φ z - 2 * Complex.cos z‖ * ‖discrim φ z + 2 * Complex.cos z‖
      ≤ (δ * Real.exp |z.im|) * ((δ + 4) * Real.exp |z.im|) :=
        mul_le_mul he hplus (norm_nonneg _) (by positivity)
    _ = δ * (δ + 4) * (Real.exp |z.im|) ^ 2 := by ring
    _ ≤ δ * (δ + 4) * (C * ‖Complex.sin z‖) ^ 2 := by
      gcongr
      exact hsin z hsep
    _ = (δ * (δ + 4) * C ^ 2) * ‖Complex.sin z‖ ^ 2 := by ring
    _ ≤ ε * ‖Complex.sin z‖ ^ 2 := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)

end

end NlsGge.GK38
