import NlsGge.GK38.GradFundamentalSpectralGauge

/-! # K1: actual spectral derivative of the independent diagonal resolvent.
GK Chapter I, Proposition3.1. Accepted invertibility, the true shifted equation
and F3 continuity prove the concrete little-o remainder without inverse differentiation.
-/
set_option autoImplicit false
open Filter Topology MeasureTheory Asymptotics
namespace NlsGge.GK38
noncomputable section

/-- Independent variation from the bounded diagonal forcing operator. -/
def fundSpectralResolvent38 (φ : PotPair) (z : ℂ) : PairCont38 :=
  Ring.inverse (1 - volterraP φ z) (spectralForcingCLM38 z (fundContP φ z))

theorem fundSpectralResolvent38_source (φ : PotPair) (z : ℂ) :
    fundSpectralResolvent38 φ z - volterraP φ z (fundSpectralResolvent38 φ z) =
      spectralForcingCLM38 z (fundContP φ z) :=
  resolvent_source38 φ z _

theorem fundSpectral_remainder_eq38 (φ : PotPair) (z w : ℂ) :
    fundContP φ (z + w) - fundContP φ z - w • fundSpectralResolvent38 φ z =
      w • Ring.inverse (1 - volterraP φ z)
        (spectralForcingCLM38 z (fundContP φ (z + w) - fundContP φ z)) := by
  apply volterra_inhomogeneous_unique38 φ z
    (F := w • spectralForcingCLM38 z (fundContP φ (z + w) - fundContP φ z))
  · have hm := fundContP_shiftedVolterra38 φ z w
    have hm0 := fundCont_eq_add φ z
    have hw := congrArg (fun N : PairCont38 => w • N) (fundSpectralResolvent38_source φ z)
    simp only [smul_sub] at hw
    simp only [map_sub, map_smul, smul_sub]
    linear_combination hm - hm0 - hw
  · have hr := congrArg (fun N : PairCont38 => w • N)
      (resolvent_source38 φ z
        (spectralForcingCLM38 z (fundContP φ (z + w) - fundContP φ z)))
    simpa only [smul_sub, map_smul] using hr

theorem norm_fundSpectral_remainder_le38 (φ : PotPair) (z w : ℂ) :
    ‖fundContP φ (z + w) - fundContP φ z - w • fundSpectralResolvent38 φ z‖ ≤
      (‖Ring.inverse (1 - volterraP φ z)‖ * ‖spectralForcingCLM38 z‖) * ‖w‖ *
        ‖fundContP φ (z + w) - fundContP φ z‖ := by
  rw [fundSpectral_remainder_eq38, norm_smul]
  have ht := (spectralForcingCLM38 z).le_opNorm (fundContP φ (z + w) - fundContP φ z)
  have ha := (Ring.inverse (1 - volterraP φ z)).le_opNorm
    (spectralForcingCLM38 z (fundContP φ (z + w) - fundContP φ z))
  calc
    _ ≤ ‖w‖ * (‖Ring.inverse (1 - volterraP φ z)‖ *
        (‖spectralForcingCLM38 z‖ * ‖fundContP φ (z + w) - fundContP φ z‖)) :=
      mul_le_mul_of_nonneg_left (ha.trans (mul_le_mul_of_nonneg_left ht (norm_nonneg _)))
        (norm_nonneg w)
    _ = _ := by ring

theorem fundSpectral_difference_tendsto_zero38 (φ : PotPair) (z : ℂ) :
    Tendsto (fun w : ℂ => ‖fundContP φ (z + w) - fundContP φ z‖) (𝓝 0) (𝓝 0) := by
  have hJ : Continuous (fun p : PotPair × ℂ => fundContP p.1 p.2) :=
    continuousOn_univ.mp analyticOnNhd_fundContP.continuousOn
  have hA : Continuous (fun w : ℂ => (φ, z + w)) :=
    (continuous_const : Continuous (fun _ : ℂ => φ)).prodMk
      ((continuous_const : Continuous (fun _ : ℂ => z)).add continuous_id)
  have hcomp := hJ.comp hA
  have hc : Continuous (fun w : ℂ => fundContP φ (z + w)) := by
    simpa only [Function.comp_def] using hcomp
  have ht : Tendsto (fun w : ℂ => fundContP φ (z + w)) (𝓝 0) (𝓝 (fundContP φ z)) := by
    simpa only [add_zero] using hc.tendsto 0
  have hs : Tendsto (fun w : ℂ => fundContP φ (z + w) - fundContP φ z) (𝓝 0) (𝓝 0) := by
    simpa only [sub_self] using ht.sub (show Tendsto (fun _ : ℂ => fundContP φ z) (𝓝 0)
      (𝓝 (fundContP φ z)) from tendsto_const_nhds)
  simpa only [norm_zero] using hs.norm

theorem isLittleO_fundSpectral_remainder38 (φ : PotPair) (z : ℂ) :
    (fun w : ℂ => fundContP φ (z + w) - fundContP φ z - w • fundSpectralResolvent38 φ z)
      =o[𝓝 0] (fun w : ℂ => w) := by
  apply k1LittleO_norm_factor38
    (q := fun w : ℂ => ‖fundContP φ (z + w) - fundContP φ z‖)
    (K := ‖Ring.inverse (1 - volterraP φ z)‖ * ‖spectralForcingCLM38 z‖)
  · positivity
  · intro w; exact norm_nonneg _
  · exact fundSpectral_difference_tendsto_zero38 φ z
  · intro w; exact norm_fundSpectral_remainder_le38 φ z w

/-- Generic scalar remainder criterion, isolated before the concrete application. -/
theorem k1HasDerivAt_of_remainder38 {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (f : 𝕜 → F) (D : F) (x : 𝕜)
    (hr : (fun h : 𝕜 => f (x + h) - f x - h • D) =o[𝓝 0] (fun h : 𝕜 => h)) :
    HasDerivAt f D x := hasDerivAt_iff_isLittleO_nhds_zero.mpr hr

theorem hasDerivAt_fundSpectralResolvent38 (φ : PotPair) (z : ℂ) :
    HasDerivAt (fundContP φ) (fundSpectralResolvent38 φ z) z :=
  k1HasDerivAt_of_remainder38 (𝕜 := ℂ) (F := PairCont38) (fundContP φ)
    (fundSpectralResolvent38 φ z) z (isLittleO_fundSpectral_remainder38 φ z)

end
end NlsGge.GK38
