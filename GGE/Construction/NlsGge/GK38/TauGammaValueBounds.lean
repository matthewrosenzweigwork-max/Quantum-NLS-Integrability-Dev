import NlsGge.GK38.TauGammaContourGlue

/-! Value bounds use the accepted paired square summability, without uniform-tail claims. -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem norm_add_square_le_twice38 (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h := pow_le_pow_left₀ (norm_nonneg (a + b)) (norm_add_le a b) 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem pair_value_square_bounds38 (a b z : ℂ) :
    ‖(a + b) / 2 - z‖ ^ 2 ≤ 2 * (‖b - z‖ ^ 2 + ‖a - z‖ ^ 2) ∧
    ‖a - b‖ ^ 2 ≤ 2 * (‖b - z‖ ^ 2 + ‖a - z‖ ^ 2) := by
  have hmean : (a + b) / 2 - z = ((a - z) + (b - z)) / 2 := by ring
  have hdiff : a - b = (a - z) + -(b - z) := by ring
  constructor
  · rw [hmean, norm_div, Complex.norm_ofNat]
    have h := norm_add_square_le_twice38 (a - z) (b - z)
    nlinarith [sq_nonneg ‖(a - z) + (b - z)‖, sq_nonneg ‖a - z‖, sq_nonneg ‖b - z‖]
  · rw [hdiff]
    simpa only [norm_neg, add_comm] using norm_add_square_le_twice38 (a - z) (-(b - z))

theorem tauGamma_common_value_bound38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ V ⊆ gkW ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ φ ∈ V,
      Summable (fun n : ℤ => ‖tauN38 C R φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ∧
      Summable (fun n : ℤ => ‖lamPlus φ n - lamMinus φ n‖ ^ 2) ∧
      Summable (fun n : ℤ => ‖gamma2N38 C R φ n‖) ∧
      (∑' n : ℤ, ‖tauN38 C R φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ≤ B ∧
      (∑' n : ℤ, ‖lamPlus φ n - lamMinus φ n‖ ^ 2) ≤ B ∧
      (∑' n : ℤ, ‖gamma2N38 C R φ n‖) ≤ B := by
  obtain ⟨U, hU, B, hB, h⟩ := periodic_l2_summable38 φ₀
  refine ⟨U ∩ gkW, inter_mem hU (isOpen_gkW.mem_nhds hφ₀), inter_subset_right, 2 * B,
    by positivity, ?_⟩
  intro φ hφ
  obtain ⟨hs, hb⟩ := h φ hφ.1
  have hdom := hs.mul_left (2 : ℝ)
  have hp (n : ℤ) := pair_value_square_bounds38 (lamPlus φ n) (lamMinus φ n)
    ((n : ℂ) * (Real.pi : ℂ))
  have hm (n : ℤ) : ‖tauN38 C R φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 ≤
      2 * (‖lamMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 +
        ‖lamPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) := by
    rw [tau_pair_mean38 C R hsel φ hφ.2 n]
    exact (hp n).1
  have hsMean := hdom.of_nonneg_of_le (fun n => sq_nonneg _) hm
  have hsGap := hdom.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => (hp n).2)
  have hgamma : (fun n : ℤ => ‖gamma2N38 C R φ n‖) =
      (fun n : ℤ => ‖lamPlus φ n - lamMinus φ n‖ ^ 2) := by
    funext n
    rw [gamma2_pair_gap38 C R hsel φ hφ.2 n, norm_pow]
  have hdomBound : (∑' n : ℤ, 2 * (‖lamMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2 +
      ‖lamPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2)) ≤ 2 * B := by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have hmeanBound := (Summable.tsum_le_tsum hm hsMean hdom).trans hdomBound
  have hgapBound := (Summable.tsum_le_tsum (fun n => (hp n).2) hsGap hdom).trans hdomBound
  refine ⟨hsMean, hsGap, ?_, hmeanBound, hgapBound, ?_⟩
  · rw [hgamma]
    exact hsGap
  · rw [hgamma]
    exact hgapBound

theorem tauGamma_l2_38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    IsLocUnifL2Seq (fun φ n => tauN38 C R φ n - (n : ℂ) * (Real.pi : ℂ)) φ₀ ∧
      IsLocUnifL2Seq (fun φ n => (gapMagnitude38 C R φ n : ℂ)) φ₀ := by
  obtain ⟨V, hV, hVW, B, _, h⟩ := tauGamma_common_value_bound38 C R hsel φ₀ hφ₀
  refine ⟨⟨V, hV, B, fun φ hφ => ⟨(h φ hφ).1, (h φ hφ).2.2.2.1⟩⟩,
    ⟨V, hV, B, fun φ hφ => ?_⟩⟩
  have he : (fun n : ℤ => ‖(gapMagnitude38 C R φ n : ℂ)‖ ^ 2) =
      (fun n : ℤ => ‖lamPlus φ n - lamMinus φ n‖ ^ 2) := by
    funext n
    rw [gapMagnitude_pair_norm38 C R hsel φ (hVW hφ) n, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [he]
  exact ⟨(h φ hφ).2.1, (h φ hφ).2.2.2.2.1⟩

end
end NlsGge.GK38
