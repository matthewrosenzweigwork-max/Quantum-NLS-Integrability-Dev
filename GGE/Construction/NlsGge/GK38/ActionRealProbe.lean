import NlsGge.GK38.ActionReal
import NlsGge.GK38.RealTypeSpectrumConstant

set_option autoImplicit false
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.AblowitzLadik
namespace NlsGge.GK38.ActionRealProbe
noncomputable section

/-- Actual nonzero negative-amplitude field: active negative action9 and a distinct closed gap. -/
theorem nonfree_signed_plane :
    let u := planeL2 2 (planeWaveCoeff38 2 (2 : ℤ) (-3))
    u ≠ 0 ∧ gkActionC38 (realSlice u) (-2) = 9 ∧
      gkActionC38 (realSlice u) 2 = 0 := by
  dsimp only
  have ha := NlsGge.GK38.plane_wave_contour_probe38 2 (2 : ℤ) (by decide) (-3) (-2)
  have hz := NlsGge.GK38.plane_wave_contour_probe38 2 (2 : ℤ) (by decide) (-3) 2
  norm_num at ha hz
  refine ⟨?_, ha, hz⟩
  intro hu
  have hf : gkActionC38 (realSlice (0 : PhysicalL2)) (-2) = 0 := by
    simpa only [realSlice_zero] using free_action38 (-2)
  have he := congrArg (fun v : PhysicalL2 => gkActionC38 (realSlice v) (-2)) hu
  have hbad : (0 : ℂ) = 9 := hf.symm.trans (he.symm.trans ha)
  norm_num at hbad

/-- A genuinely nonfree constant field has a collapsed negative gap and zero actual contour action. -/
theorem nonfree_constant_closed_gap :
    gkActionC38 (realSlice (constL2 1)) (-1) = 0 ∧
      ∀ n : ℤ, gkActionC38 (realSlice (constL2 1)) n =
        (actualGapActionAllE02_38 (constL2 1) n : ℂ) := by
  have hlabels := realType_const_negative_labels38
  have hc := hlabels.1.trans hlabels.2.symm
  rw [(lamPlus_real (constL2 1) (-1)).2, (lamPlus_real (constL2 1) (-1)).1] at hc
  have hclosed : actualGapLowerAllE02_38 (constL2 1) (-1) =
      actualGapUpperAllE02_38 (constL2 1) (-1) := Complex.ofReal_inj.mp hc
  have hz := (actionZeroIffClosed38 (constL2 1) (-1)).mpr hclosed
  exact ⟨by rw [NlsGge.GK38.ActionRealBridge.action_real_bridge, hz]; rfl,
    NlsGge.GK38.ActionRealBridge.action_real_bridge (constL2 1)⟩

/-- Zero amplitude at negative frequency retains the reflected positive label. -/
theorem zero_amplitude_negative_frequency :
    gkActionC38 (realSlice (planeL2 2 (planeWaveCoeff38 2 (-2 : ℤ) 0))) 2 = 0 := by
  simpa using NlsGge.GK38.plane_wave_contour_probe38 2 (-2 : ℤ) (by decide) 0 2

end
end NlsGge.GK38.ActionRealProbe
