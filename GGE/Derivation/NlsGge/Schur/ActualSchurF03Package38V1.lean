import NlsGge.Schur.ActualSchurE02Identification38V1
import NlsGge.Spectral.ActualCouplingSobolevUniformBox38
import NlsGge.Spectral.ActualQuasimomentumWindowUniformE02_38

/-!
# NEW-F03: unconditional package (uniform window discharged)

* `actualQuasimomentumWindow_uniform38`: E02's Window hypothesis holds uniformly on H¹ balls,
  `|n| ≥ K R^2`, from the coupled normalized strip estimate
  (`actualHalfTrace_uniformHalfStrip_coupling38`) and E02's
  `actualQuasimomentumWindow_of_normalizedStrip_E02_38` (ε ≤ 1/20000).
* `actualSchurF03Package38V1`: `actualSchurE02Identification38V1` with the window premise removed.
-/

set_option autoImplicit false
noncomputable section
open NlsGge.Analysis NlsGge.Pilot NlsGge.SpectralFoundations

namespace NlsGge.Schur

theorem actualQuasimomentumWindow_uniform38 :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 1 ≤ R →
      ∀ (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)),
        ‖physicalSobolevL2 1 u hu‖ ≤ R → ∀ n : ℤ, K * R ^ 2 ≤ |(n : ℝ)| →
          ActualQuasimomentumWindowE02_38 u n := by
  obtain ⟨K, C, hK, hC, h⟩ := actualHalfTrace_uniformHalfStrip_coupling38
  refine ⟨K + 20000 * C, by positivity, ?_⟩
  intro R hR u hu huR n hn
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  have hnK : K * R ^ 2 ≤ |(n : ℝ)| := by nlinarith
  have hNpos : 0 < |(n : ℝ)| := lt_of_lt_of_le (by positivity) hnK
  have hε : C * R ^ 2 / |(n : ℝ)| ≤ 1 / 20000 := by
    rw [div_le_div_iff₀ hNpos (by norm_num)]
    nlinarith
  exact actualQuasimomentumWindow_of_normalizedStrip_E02_38 u n _ (by positivity) hε
    (fun τ hτ z hz hz0 => h R hR u hu huR τ hτ n hnK z hz hz0)

/-- NEW-F03 package, unconditional: for an absolute `K`, `‖w‖_{H¹} ≤ R`, `|n| ≥ K R^3`, the
conclusions (a)–(d) of `actualSchurE02Identification38V1` hold with no window premise. -/
theorem actualSchurF03Package38V1 :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 1 ≤ R → ∀ n : ℤ, K * R ^ 3 ≤ |(n : ℝ)| →
      ∀ w : WeightedHilbert (sobolevModeWeight (1 : ℝ)), ‖w‖ ≤ R →
      (∃ lp lm : ℝ,
        (lp ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) ∧
          actualSchurShiftedF38 n (w, actualH1Conj38 w) lp -
            actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lp = 0) ∧
        (lm ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) ∧
          actualSchurShiftedF38 n (w, actualH1Conj38 w) lm +
            actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lm = 0)) ∧
      ∀ lp lm : ℝ,
        lp ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) →
        actualSchurShiftedF38 n (w, actualH1Conj38 w) lp -
          actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lp = 0 →
        lm ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) →
        actualSchurShiftedF38 n (w, actualH1Conj38 w) lm +
          actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lm = 0 →
        (lp = -actualGapLowerE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) ∧
          lm = -actualGapUpperE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n)) ∧
        (lp - lm = actualGapUpperE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) -
            actualGapLowerE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) ∧
          2 * ‖actualSchurQn38 R n (w, actualH1Conj38 w)‖ /
              (1 + 2 * actualSchurGapParameter38 R n) ≤
            actualGapUpperE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) -
              actualGapLowerE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n)) ∧
        (|actualGapLowerE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) + n * Real.pi| ≤
            actualSchurGapLocalConstant38 * R ^ 3 / |(n : ℝ)| ∧
          |actualGapUpperE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) + n * Real.pi| ≤
            actualSchurGapLocalConstant38 * R ^ 3 / |(n : ℝ)|) ∧
        Real.exp (-4 * actualSchurGapParameter38 R n) *
            ‖actualSchurQn38 R n (w, actualH1Conj38 w)‖ ^ 2 ≤
          actualGapActionE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) := by
  obtain ⟨K1, hK1, h1⟩ := actualSchurE02Identification38V1
  obtain ⟨Kw, hKw, hw⟩ := actualQuasimomentumWindow_uniform38
  refine ⟨K1 + Kw, by positivity, ?_⟩
  intro R hR n hn w hwR
  have hR3 : R ^ 2 ≤ R ^ 3 := pow_le_pow_right₀ hR (by norm_num)
  have hR2 : 0 ≤ R ^ 2 := by positivity
  have hn1 : K1 * R ^ 3 ≤ |(n : ℝ)| := by nlinarith
  have hnw : Kw * R ^ 2 ≤ |((-n : ℤ) : ℝ)| := by
    rw [Int.cast_neg, abs_neg]; nlinarith
  have hwin := hw R hR (physicalH1ComplexCarrierToL2Actual22 w)
    (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable w)
    (by rw [physicalSobolevL2_norm_h1Carrier38]; exact hwR) (-n) hnw
  exact h1 R hR n hn1 w hwR hwin

end NlsGge.Schur
