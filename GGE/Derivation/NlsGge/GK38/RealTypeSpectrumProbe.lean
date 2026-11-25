import NlsGge.GK38.RealTypeSpectrum
import NlsGge.GK38.RealTypeSpectrumConstant
import NlsGge.GK38.MolnarLocalizationProbe
import NlsGge.GK38.PairRealBridgeProbe

/-! # S5: exact free, negative-index and nonfree real constant regressions -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem realType_probe_free_negative38 :
    actualGapLowerAllE02_38 (0 : PhysicalL2) (-1) = -Real.pi ∧
    actualGapUpperAllE02_38 (0 : PhysicalL2) (-1) = -Real.pi ∧
    lamMinus (realSlice (0 : PhysicalL2)) (-1) = -(Real.pi : ℂ) ∧
    lamPlus (realSlice (0 : PhysicalL2)) (-1) = -(Real.pi : ℂ) ∧
    actualGapUpperAllE02_38 (0 : PhysicalL2) (-1) < actualGapLowerAllE02_38 (0 : PhysicalL2) 0 := by
  refine ⟨?_, ?_, ?_, ?_, gap_interlace 0 (-1)⟩
  · simpa using (gap_zero38 (-1)).1
  · simpa using (gap_zero38 (-1)).2
  · rw [realSlice_zero, lamMinus_zero38]; simp [countingCenter38]
  · rw [realSlice_zero, lamPlus_zero38]; simp [countingCenter38]

theorem realType_probe_free_zero38 :
    actualGapLowerAllE02_38 (0 : PhysicalL2) 0 = 0 ∧
    actualGapUpperAllE02_38 (0 : PhysicalL2) 0 = 0 ∧
    lamMinus (realSlice (0 : PhysicalL2)) 0 = 0 ∧ lamPlus (realSlice (0 : PhysicalL2)) 0 = 0 := by
  rw [(gap_zero38 0).1, (gap_zero38 0).2, realSlice_zero, lamMinus_zero38, lamPlus_zero38]
  simp [countingCenter38]

theorem realType_probe_nonfree_central_roots38 :
    perChar (realSlice (constL2 1)) (1 : ℂ) = 0 ∧ perChar (realSlice (constL2 1)) (-1 : ℂ) = 0 := by
  constructor
  · exact perChar_realSlice_const_double 1 1 (by norm_num)
  · exact perChar_realSlice_const_double 1 (-1) (by norm_num)

theorem realType_probe_nonfree_negative_root38 :
    perChar (realSlice (constL2 1)) ((-Real.sqrt (Real.pi ^ 2 + 1) : ℝ) : ℂ) = 0 := by
  let r : ℝ := -Real.sqrt (Real.pi ^ 2 + 1)
  have hr : r ^ 2 = Real.pi ^ 2 + 1 := by
    dsimp [r]
    rw [neg_sq, Real.sq_sqrt (by positivity)]
  have hκ : (Real.pi : ℂ) ^ 2 = (r : ℂ) ^ 2 - 1 * star (1 : ℂ) := by
    norm_num
    exact_mod_cast (show Real.pi ^ 2 = r ^ 2 - 1 by linarith)
  have h := perChar_realSlice_const 1 (r : ℂ) (Real.pi : ℂ)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hκ
  simpa only [Complex.sin_pi, zero_pow (by decide : 2 ≠ 0), mul_zero] using h

theorem realType_probe_nonfree_zero_ne38 : perChar (realSlice (constL2 1)) 0 ≠ 0 := by
  have h := perChar_realSlice_const 1 0 Complex.I Complex.I_ne_zero (by simp)
  rw [h]
  have hs : Complex.sin Complex.I ≠ 0 := by
    intro hz
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hz
    have hi := congrArg Complex.im hk
    norm_num [Complex.mul_im] at hi
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ hs)

theorem realType_probe_nonfree_constant38 :
    perChar (realSlice (constL2 1)) (1 : ℂ) = 0 ∧
    perChar (realSlice (constL2 1)) (-1 : ℂ) = 0 ∧
    actualGapLowerAllE02_38 (constL2 1) 0 = -1 ∧ actualGapUpperAllE02_38 (constL2 1) 0 = 1 ∧
    lamMinus (realSlice (constL2 1)) 0 = -1 ∧ lamPlus (realSlice (constL2 1)) 0 = 1 := by
  have hl : actualGapLowerAllE02_38 (constL2 1) 0 = -1 := by
    have h := (lamPlus_real (constL2 1) 0).2.symm.trans realType_const_central_labels38.1
    exact_mod_cast h
  have hu : actualGapUpperAllE02_38 (constL2 1) 0 = 1 := by
    have h := (lamPlus_real (constL2 1) 0).1.symm.trans realType_const_central_labels38.2
    exact_mod_cast h
  exact ⟨realType_probe_nonfree_central_roots38.1, realType_probe_nonfree_central_roots38.2,
    hl, hu, realType_const_central_labels38⟩

theorem realType_probe_nonfree_negative38 :
    let r : ℝ := -Real.sqrt (Real.pi ^ 2 + 1)
    perChar (realSlice (constL2 1)) (r : ℂ) = 0 ∧
    actualGapLowerAllE02_38 (constL2 1) (-1) = r ∧ actualGapUpperAllE02_38 (constL2 1) (-1) = r ∧
    lamMinus (realSlice (constL2 1)) (-1) = (r : ℂ) ∧ lamPlus (realSlice (constL2 1)) (-1) = (r : ℂ) := by
  let r : ℝ := -Real.sqrt (Real.pi ^ 2 + 1)
  have hl : actualGapLowerAllE02_38 (constL2 1) (-1) = r := by
    have h := (lamPlus_real (constL2 1) (-1)).2.symm.trans realType_const_negative_labels38.1
    exact_mod_cast h
  have hu : actualGapUpperAllE02_38 (constL2 1) (-1) = r := by
    have h := (lamPlus_real (constL2 1) (-1)).1.symm.trans realType_const_negative_labels38.2
    exact_mod_cast h
  exact ⟨realType_probe_nonfree_negative_root38, hl, hu, realType_const_negative_labels38⟩

theorem realType_probe_nonfree_open_gap38 :
    actualGapLowerAllE02_38 (constL2 1) 0 < actualGapUpperAllE02_38 (constL2 1) 0 := by
  rw [realType_probe_nonfree_constant38.2.2.1, realType_probe_nonfree_constant38.2.2.2.1]
  norm_num

end
end NlsGge.GK38
