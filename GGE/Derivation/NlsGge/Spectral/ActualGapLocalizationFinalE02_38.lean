import NlsGge.Spectral.ActualGapLocalizationE02_38
import NlsGge.Spectral.ActualQuasimomentumUniformExteriorE02_38
set_option autoImplicit false
noncomputable section
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- E03 (v2 A:eq:localization): for every `B ≥ 1` there is `K_B` such that every field with
`‖w‖_{H¹} ≤ B` has `|λ - πn| ≤ K_B/⟨n⟩` for all `λ ∈ \overline{g_n}` and all `n ∈ ℤ`. -/
theorem actualGapLocalization_E02_38 :
    ∀ B : ℝ, 1 ≤ B → ∃ K : ℝ, 0 < K ∧
      ∀ w : WeightedHilbert (sobolevModeWeight (1 : ℝ)), ‖w‖ ≤ B → ∀ n : ℤ,
        ∀ l ∈ Set.Icc (actualGapLowerAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n)
          (actualGapUpperAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n),
          |l - (n:ℝ)*Real.pi| ≤ K / japaneseBracket n :=
  actualGapLocalization_of_exterior_E02_38 actualQuasimomentumBoundary_uniformExterior_E02_38

end NlsGge.SpectralFoundations
end
