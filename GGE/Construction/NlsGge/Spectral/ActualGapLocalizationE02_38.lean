import NlsGge.Spectral.ActualGapActionAllNE02_38
import NlsGge.Spectral.ActualQuasimomentumBoundaryFunctionE02_38
import NlsGge.Spectral.ActualGapLabelsAgreeE02_38
import NlsGge.Spectral.ActualBoxWindowUniformE02_38
import NlsGge.Schur.ActualSchurF03Package38V1
set_option autoImplicit false
noncomputable section
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # E03 (campaign 38): uniform localization of labelled gaps, `|λ - nπ| ≤ K_B/⟨n⟩` -/

/-- Low-index bound: an exterior bound `|k(x+i0) - x| ≤ 1/4` for `|x| ≥ X` confines every point of
the level-set gap `g_n` to `|λ - nπ| ≤ X + 2|nπ| + 1`. -/
theorem gapLocalization_of_exterior_E02_38 (u : PhysicalL2) (X : ℝ) (hX : 0 ≤ X)
    (hext : ∀ x : ℝ, X ≤ |x| → ‖actualQuasimomentumBoundaryE02_38 u x - x‖ ≤ 1/4) (n : ℤ) :
    ∀ l ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
      |l - (n:ℝ)*Real.pi| ≤ X + 2*|(n:ℝ)*Real.pi| + 1 := by
  intro l hl
  have hlev : actualQuasimomentumRealPartE02_38 u l = (n:ℝ)*Real.pi := by
    have := (actualGapLevelSet_eq_Icc_E02_38 u n).2
    rw [← this] at hl; exact hl
  have hre : ∀ x : ℝ, X ≤ |x| → |actualQuasimomentumRealPartE02_38 u x - x| ≤ 1/4 := by
    intro x hx
    have h := hext x hx
    have := Complex.abs_re_le_norm (actualQuasimomentumBoundaryE02_38 u x - x)
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    exact this.trans h
  have hbound : |l| ≤ X + |(n:ℝ)*Real.pi| + 1 := by
    by_contra hc
    push Not at hc
    have hx : X ≤ |l| := by linarith [abs_nonneg ((n:ℝ)*Real.pi)]
    have h := abs_le.mp (hre l hx)
    rw [hlev] at h
    rcases le_or_gt 0 l with h0 | h0
    · rw [abs_of_nonneg h0] at hc; linarith [h.1, le_abs_self ((n:ℝ)*Real.pi)]
    · rw [abs_of_neg h0] at hc; linarith [h.2, neg_abs_le ((n:ℝ)*Real.pi)]
  calc |l - (n:ℝ)*Real.pi| ≤ |l| + |(n:ℝ)*Real.pi| := abs_sub _ _
    _ ≤ X + 2*|(n:ℝ)*Real.pi| + 1 := by linarith


theorem div_abs_le_sqrt_two_div_bracket_E02_38 (c : ℝ) (hc : 0 ≤ c) (n : ℤ) (hn : 1 ≤ |(n:ℝ)|) :
    c / |(n:ℝ)| ≤ Real.sqrt 2 * c / japaneseBracket n := by
  have hb : 0 < japaneseBracket n := Real.sqrt_pos.mpr (by positivity)
  have hnpos : 0 < |(n:ℝ)| := by linarith
  have hbr : japaneseBracket n ≤ Real.sqrt 2 * |(n:ℝ)| := by
    unfold japaneseBracket
    rw [show Real.sqrt 2 * |(n:ℝ)| = Real.sqrt (2 * |(n:ℝ)|^2) by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (abs_nonneg _)]]
    apply Real.sqrt_le_sqrt
    rw [sq_abs]; nlinarith [sq_abs (n:ℝ)]
  rw [div_le_div_iff₀ hnpos hb]
  calc c * japaneseBracket n ≤ c * (Real.sqrt 2 * |(n:ℝ)|) := mul_le_mul_of_nonneg_left hbr hc
    _ = Real.sqrt 2 * c * |(n:ℝ)| := by ring

/-- E03 (v2 A:eq:localization), conditional only on the uniform exterior estimate `hext`
(worker W-E03a): for each `B ≥ 1` there is `K` with `|λ - nπ| ≤ K/⟨n⟩` for every point `λ` of the
closed labelled gap `g_n` of every field `‖w‖_{H¹} ≤ B`, every `n ∈ ℤ`. -/
theorem actualGapLocalization_of_exterior_E02_38
    (hext : ∀ B : ℝ, 1 ≤ B → ∃ X : ℝ, 0 < X ∧ ∀ (u : PhysicalL2)
      (hu : SobolevSquareSummable 1 (physicalFourier u)), ‖physicalSobolevL2 1 u hu‖ ≤ B →
      ∀ x : ℝ, X ≤ |x| → ‖actualQuasimomentumBoundaryE02_38 u x - x‖ ≤ 1/4) :
    ∀ B : ℝ, 1 ≤ B → ∃ K : ℝ, 0 < K ∧
      ∀ w : WeightedHilbert (sobolevModeWeight (1 : ℝ)), ‖w‖ ≤ B → ∀ n : ℤ,
        ∀ l ∈ Set.Icc (actualGapLowerAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n)
          (actualGapUpperAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n),
          |l - (n:ℝ)*Real.pi| ≤ K / japaneseBracket n := by
  intro B hB
  obtain ⟨X, hX, hXb⟩ := hext B hB
  obtain ⟨Kp, hKp, hpack⟩ := actualSchurF03Package38V1
  obtain ⟨K1, C1, hK1, hC1, hbw⟩ := actualBoxWindow_uniform_E02_38
  set N : ℝ := max (max (Kp * B^3) (K1 * B^2)) 1
  set L : ℝ := X + 2 * (Real.pi * N) + 1
  set Cs := actualSchurGapLocalConstant38
  refine ⟨max (Real.sqrt 2 * (|Cs| * B^3)) (L * Real.sqrt (1 + N^2)) + 1, by positivity, ?_⟩
  intro w hw n l hl
  set u := physicalH1ComplexCarrierToL2Actual22 w
  have hu := physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable w
  have hnorm : ‖physicalSobolevL2 1 u hu‖ ≤ B := by rw [physicalSobolevL2_norm_h1Carrier38]; exact hw
  have hb : 0 < japaneseBracket n := Real.sqrt_pos.mpr (by positivity)
  rcases le_or_gt N |(n:ℝ)| with hn | hn
  · -- high index
    have hn1 : 1 ≤ |(n:ℝ)| := le_trans (le_max_right _ _) hn
    have hnp : Kp * B^3 ≤ |((-n:ℤ):ℝ)| := by
      rw [Int.cast_neg, abs_neg]; exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hnw : K1 * B^2 ≤ |(n:ℝ)| := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    obtain ⟨⟨lp, lm, hlp, hlm⟩, hall⟩ := hpack B hB (-n) hnp w hw
    obtain ⟨-, -, ⟨hc1, hc2⟩, -⟩ := hall lp lm hlp.1 hlp.2 hlm.1 hlm.2
    simp only [neg_neg, Int.cast_neg, abs_neg] at hc1 hc2
    obtain ⟨hbox, hδ, hwin⟩ := hbw B hB u hu hnorm n hnw
    obtain ⟨hlo, hup, -⟩ := actualGapLabels_agree_E02_38 u n _ (by positivity) hδ hbox hwin
    rw [hlo] at hc1; rw [hup] at hc2
    have hc1' : |actualGapLowerAllE02_38 u n - (n:ℝ)*Real.pi| ≤ Cs * B^3 / |(n:ℝ)| := by
      rw [show actualGapLowerAllE02_38 u n - (n:ℝ)*Real.pi =
        actualGapLowerAllE02_38 u n + -(n:ℝ) * Real.pi by ring]; exact hc1
    have hc2' : |actualGapUpperAllE02_38 u n - (n:ℝ)*Real.pi| ≤ Cs * B^3 / |(n:ℝ)| := by
      rw [show actualGapUpperAllE02_38 u n - (n:ℝ)*Real.pi =
        actualGapUpperAllE02_38 u n + -(n:ℝ) * Real.pi by ring]; exact hc2
    have hl' : |l - (n:ℝ)*Real.pi| ≤ Cs * B^3 / |(n:ℝ)| := by
      rw [abs_le] at hc1' hc2' ⊢
      constructor <;> linarith [hl.1, hl.2, hc1'.1, hc2'.2]
    have hCs : Cs * B^3 ≤ |Cs| * B^3 := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    calc |l - (n:ℝ)*Real.pi| ≤ |Cs| * B^3 / |(n:ℝ)| :=
          hl'.trans (div_le_div_of_nonneg_right hCs (by positivity))
      _ ≤ Real.sqrt 2 * (|Cs| * B^3) / japaneseBracket n := by
          exact div_abs_le_sqrt_two_div_bracket_E02_38 (|Cs| * B^3) (by positivity) n hn1
      _ ≤ _ := by
          apply div_le_div_of_nonneg_right _ hb.le
          have := le_max_left (Real.sqrt 2 * (|Cs| * B^3)) (L * Real.sqrt (1 + N^2)); linarith
  · -- low index
    have h := gapLocalization_of_exterior_E02_38 u X hX.le (hXb u hu hnorm) n l hl
    have hnπ : |(n:ℝ)*Real.pi| ≤ Real.pi * N := by
      rw [abs_mul, abs_of_pos Real.pi_pos]; nlinarith [Real.pi_pos]
    have hL : |l - (n:ℝ)*Real.pi| ≤ L := by simp only [L]; linarith
    have hbr : japaneseBracket n ≤ Real.sqrt (1 + N^2) := by
      unfold japaneseBracket; apply Real.sqrt_le_sqrt
      have : (n:ℝ)^2 ≤ N^2 := by
        rw [← sq_abs (n:ℝ)]; exact pow_le_pow_left₀ (abs_nonneg _) hn.le 2
      linarith
    have hL0 : 0 ≤ L := by
      simp only [L]; have : 0 ≤ Real.pi * N := by positivity
      linarith
    rw [le_div_iff₀ hb]
    calc |l - (n:ℝ)*Real.pi| * japaneseBracket n ≤ L * Real.sqrt (1 + N^2) :=
          mul_le_mul hL hbr hb.le hL0
      _ ≤ _ := by
          have := le_max_right (Real.sqrt 2 * (|Cs| * B^3)) (L * Real.sqrt (1 + N^2)); linarith

end NlsGge.SpectralFoundations
end
