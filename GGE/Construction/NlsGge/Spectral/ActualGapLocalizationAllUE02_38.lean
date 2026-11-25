import NlsGge.Spectral.ActualGapLocalizationFinalE02_38
set_option autoImplicit false
noncomputable section
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- Surjectivity of the complex `H¹` carrier onto `{u ∈ L² : Σ⟨n⟩²|û_n|² < ∞}`, norm-exact. -/
theorem physicalH1Carrier_surjective_E02_38 :
    ∀ (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)),
      ∃ w : WeightedHilbert (sobolevModeWeight (1 : ℝ)),
        physicalH1ComplexCarrierToL2Actual22 w = u ∧
          ‖w‖ = ‖physicalSobolevL2 1 u hu‖ := by
  intro u hu
  let w : WeightedHilbert (sobolevModeWeight (1 : ℝ)) :=
    ⟨physicalFourier u,
      (weightedCoordinates_mem_l2_iff (sobolevModeWeight (1 : ℝ))
        (fun n => (Real.rpow_pos_of_pos (japaneseBracket_pos n) _).le)
        (physicalFourier u)).2 hu⟩
  have hw : (w : ℤ → ℂ) = physicalFourier u := rfl
  have hc : physicalH1ComplexCarrierToL2Actual22 w = u := by
    apply physicalFourierL2.injective
    apply lp.ext
    funext n
    rw [physicalFourierL2_apply, physicalFourierL2_apply,
      physicalH1ComplexCarrierToL2Actual22_fourier, hw]
  refine ⟨w, hc, ?_⟩
  have h := physicalSobolevL2_norm_h1Carrier38 w
  have hu' : physicalSobolevL2 1 (physicalH1ComplexCarrierToL2Actual22 w)
      (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable w) =
      physicalSobolevL2 1 u hu := by
    have key : ∀ v : PhysicalL2, v = u → ∀ hv : SobolevSquareSummable 1 (physicalFourier v),
        physicalSobolevL2 1 v hv = physicalSobolevL2 1 u hu := by
      rintro v rfl hv
      rfl
    exact key _ hc _
  rw [← h, hu']

/-- E03 for every `H¹` potential `u : PhysicalL2`. -/
theorem actualGapLocalization_allU_E02_38 :
    ∀ B : ℝ, 1 ≤ B → ∃ K : ℝ, 0 < K ∧
      ∀ (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)),
        ‖physicalSobolevL2 1 u hu‖ ≤ B → ∀ n : ℤ,
          ∀ l ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
            |l - (n:ℝ)*Real.pi| ≤ K / japaneseBracket n := by
  intro B hB
  obtain ⟨K, hK, h⟩ := actualGapLocalization_E02_38 B hB
  refine ⟨K, hK, fun u hu hn n l hl => ?_⟩
  obtain ⟨w, hwu, hwn⟩ := physicalH1Carrier_surjective_E02_38 u hu
  subst hwu
  exact h w (hwn ▸ hn) n l hl

end NlsGge.SpectralFoundations
end
