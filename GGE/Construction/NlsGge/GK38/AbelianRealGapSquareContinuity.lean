import NlsGge.GK38.AbelianGammaTraceContinuity
import NlsGge.GK38.AbelianNonnegativeSeriesContinuity
import NlsGge.GK38.EigenvalueCompactnessStrong

/-! Uncompiled ACTUAL realization of the nonnegative-series bridge. Every
premise of Scheffé is discharged by actual gamma2 and endpoint theorems. -/
set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

def p5RealGapSquare38 (u : PhysicalL2) (m : ℤ) : ℝ :=
  (actualGapUpperAllE02_38 u m-actualGapLowerAllE02_38 u m)^2

theorem p5RealGapSquare_eq_norm_gamma38 (u : PhysicalL2) (m : ℤ) :
    p5RealGapSquare38 u m = ‖gamma2 (realSlice u) m‖ := by
  rw [(tauGamma_real38 u m).2,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  rfl

theorem p5RealGapSquare_summable38 (u : PhysicalL2) : Summable (p5RealGapSquare38 u) := by
  obtain ⟨V,hV,_hVW,B,_hB,h⟩ := tauGamma_common_value_bound38 discC discR
    isolating_selectors_admissible38 (realSlice u) (realSlice_mem_gkW u)
  exact ((h (realSlice u) (mem_of_mem_nhds hV)).2.2.1).congr
    (fun m => (p5RealGapSquare_eq_norm_gamma38 u m).symm)

theorem p5RealGapSquare_mass_eq_trace38 (u : PhysicalL2) :
    (∑' m : ℤ, p5RealGapSquare38 u m) = (∑' m : ℤ, gamma2 (realSlice u) m).re := by
  have _hs := p5RealGapSquare_summable38 u
  have hc : Complex.ofReal (∑' m : ℤ, p5RealGapSquare38 u m) =
      ∑' m : ℤ, gamma2 (realSlice u) m := by
    rw [Complex.ofReal_tsum]
    congr 1
    funext m
    exact (tauGamma_real38 u m).2.symm
  simpa only [Complex.ofReal_re] using congrArg Complex.re hc

theorem p5RealGapSquare_mass_continuous38 :
    Continuous (fun u : PhysicalL2 => ∑' m : ℤ, p5RealGapSquare38 u m) := by
  apply continuous_iff_continuousAt.mpr
  intro u₀
  have ht := (p5Gamma_trace_continuousAt38 (realSlice u₀) (realSlice_mem_gkW u₀)).comp
    continuous_realSlice.continuousAt
  have hh := Complex.continuous_re.continuousAt.comp ht
  change ContinuousAt (fun u : PhysicalL2 => (∑' m : ℤ, gamma2 (realSlice u) m).re) u₀ at hh
  simpa only [← p5RealGapSquare_mass_eq_trace38] using hh

theorem p5RealGapSquare_strong_tendsto38 (u₀ : PhysicalL2) :
    Tendsto (fun u : PhysicalL2 => ∑' m : ℤ,
      |p5RealGapSquare38 u m-p5RealGapSquare38 u₀ m|) (𝓝 u₀) (𝓝 (0 : ℝ)) := by
  apply p5Nonnegative_series_strong_tendsto38 (𝓝 u₀) p5RealGapSquare38
    (p5RealGapSquare38 u₀) (fun _ _ => sq_nonneg _) (fun _ => sq_nonneg _)
    p5RealGapSquare_summable38 (p5RealGapSquare_summable38 u₀)
  · intro m
    exact (((gapEndpoints_L2_continuous38 m).2.sub
      (gapEndpoints_L2_continuous38 m).1).pow 2).continuousAt
  · exact p5RealGapSquare_mass_continuous38.continuousAt

end
end NlsGge.GK38
