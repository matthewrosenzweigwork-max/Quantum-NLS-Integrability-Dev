import NlsGge.Birkhoff.F05Identity38k
open MeasureTheory NlsGge.HierarchyRiccati.Core NlsGge.Pilot NlsGge.AblowitzLadik

/-! F05 / L06.08(b) bridges (review REVIEW_F05 finding F1): the D4 clause stated for the defined
object `gammaFM38`, and the finite-gap partition functions converging to `alQ4Z2_38`. -/

namespace NlsGge.Birkhoff

/-- `γ₂^F` (the defined `gammaFM38`) realized in `H^s` is the `m = 2` Gaussian realization. -/
theorem gammaFM38_two_realization {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 < β₁) (h2 : 0 < β₂) (s : ℝ) :
    (gammaFM38 2 (alQ4Beta38 β₀ β₁ β₂)).map (reSob38 ((2 - 1 : ℕ) : ℝ) s) =
      (gammaM38 2 (alQ4Beta38 β₀ β₁ β₂)).map (seqRealization38 (sobolevModeWeight s)) := by
  have hβ := hβ_alQ4Beta38 h0 h1 h2
  rw [gammaFM38_eq_realization, Measure.map_map (measurable_reSob38 _ s) measurable_gaussianRealization38]
  have hae := ae_summable38 (m := 2) (β := alQ4Beta38 β₀ β₁ β₂) le_rfl (fun j hj => (hβ j hj).le)
    (hβ 0 (Nat.zero_le _)) (hβ 2 le_rfl)
  refine Measure.map_congr ?_
  filter_upwards [hae] with z hz
  exact reSob38_realization _ s z (by exact hz)

/-- `Z_{2,Λ_N} → alQ4Z2_38` (finite-gap partition functions, `m = 2`). -/
theorem tendsto_ZΛM38_two_alQ4 {β₀ β₁ β₂ : ℝ} (B : NlsGge.Birkhoff.BirkhoffInput38) (O : NlsGge.Birkhoff.OneSmoothingInput38 B)
    (h0 : 0 < β₀) (h1 : 0 < β₁) (h2 : 0 < β₂) :
    Filter.Tendsto (fun N : ℕ => ZΛM38 B 2 (alQ4Beta38 β₀ β₁ β₂) (stdExh38 N)) Filter.atTop
      (nhds (alQ4Z2_38 β₀ β₁ β₂)) := by
  have hβ := hβ_alQ4Beta38 h0 h1 h2
  have := (L06_08b_38 B O h0 h1 h2 0).2.2.1
  rw [← this]
  exact tendsto_ZΛM38 B 2 _ le_rfl hβ

theorem isProbabilityMeasure_gammaFM38_two {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 < β₁) (h2 : 0 < β₂) :
   IsProbabilityMeasure (gammaFM38 2 (alQ4Beta38 β₀ β₁ β₂)) :=
  isProbabilityMeasure_gammaFM38 le_rfl (hβ_alQ4Beta38 h0 h1 h2)

end NlsGge.Birkhoff
