import NlsGge.GK38.DirichletRealSign
import NlsGge.GK38.DirichletRealContinuityProbe
import NlsGge.GK38.DirichletCharProbe
import NlsGge.GK38.RealTypeSpectrumProbe

/-! Same-gap regressions for all free indices and actual nonfree constant roots. -/
set_option autoImplicit false
open Set
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem dirichlet_free_labels_probe38 (n : ℤ) :
    gkMu 0 n = (n : ℝ) * Real.pi ∧ deltaMu 0 n = 0 := by
  refine ⟨gkMu_free38 n, ?_⟩
  rw [deltaMu, realSlice_zero, antiDiscrim, monodromyPair_zero_potential]
  simp [freeE]

theorem dirichlet_real_constant_labels_probe38 :
    gkMu (constL2 1) 0 = 1 ∧ deltaMu (constL2 1) 0 = 0 ∧
      gkMu (constL2 1) (-1) = -Real.sqrt (Real.pi ^ 2 + 1) := by
  have hmem : (1 : ℝ) ∈ Icc (actualGapLowerAllE02_38 (constL2 1) 0)
      (actualGapUpperAllE02_38 (constL2 1) 0) := by
    rw [realType_probe_nonfree_constant38.2.2.1, realType_probe_nonfree_constant38.2.2.2.1]
    norm_num
  have hμ : gkMu (constL2 1) 0 = 1 :=
    ((gkMu_spec (constL2 1) 0).2.2 1 hmem dirichlet_nonfree_constant_root38).symm
  have hδ := deltaMu_squared38 (constL2 1) 0
  have hend := (actualGapEndpoint_halfTrace_all_E02_38 (constL2 1) 0).2
  rw [realType_probe_nonfree_constant38.2.2.2.1] at hend
  rw [hμ, discrim_realSlice, hend] at hδ
  have hneg := gkMu_mem_gap38 (constL2 1) (-1)
  rw [realType_probe_nonfree_negative38.2.1, realType_probe_nonfree_negative38.2.2.1] at hneg
  refine ⟨hμ, ?_, le_antisymm hneg.2 hneg.1⟩
  norm_num [Complex.mul_re] at hδ
  nlinarith

end
end NlsGge.GK38
