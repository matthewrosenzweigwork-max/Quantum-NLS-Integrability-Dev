import NlsGge.GK38.EigenvalueCompactnessPhaseRealization
import NlsGge.GK38.PairVolterraProbe
import NlsGge.GK38.DirichletNilpotentProbe

/-! # S7: actual free closed directions and nonfree Jordan endpoint phase

The zero representative is used only through its proved AE equality.
-/
set_option autoImplicit false
open Filter Topology Set Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem periodicPhase_free_one38 (x : ℝ) (a : ℂ) (ha : ‖a‖ = 1) :
    periodicPhase38 0 x a 1 = x := by
  have _hi := periodicPhase_intervalIntegrable38 0 x a ha ⟨1, zero_le_one, le_rfl⟩
  have he : (∫ r in (0 : ℝ)..1, (e02Pot38 0 r *
      (actualPhysicalFloquetState33 0 (x : ℂ) (realInitial38 a) r 1 /
        actualPhysicalFloquetState33 0 (x : ℂ) (realInitial38 a) r 0)).re) = ∫ _r in (0 : ℝ)..1, (0 : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [coverRep38_zero_ae] with r hr
    intro _
    change e02Pot38 0 r = 0 at hr
    rw [hr, zero_mul, Complex.zero_re]
  simp only [periodicPhase38, mul_one, he, intervalIntegral.integral_zero, sub_zero]

theorem periodicPhase_free_closed_negative38 (a : ℂ) (ha : ‖a‖ = 1) :
    periodicPhase38 0 (-Real.pi) a 1 = -Real.pi := periodicPhase_free_one38 _ _ ha

theorem periodicState_nilpotent38 (t : Time38) :
    periodicState38 (constL2 1) 1 1 t = realInitial38 1 := by
  change (actualComplexZsDysonTsum (e02Pot38 (constL2 1)) (1 : ℂ) t).mulVec (realInitial38 1) = _
  rw [← fundPair_realSlice, fundPair_dirichlet_nilpotent38]
  ext i
  fin_cases i <;> norm_num [dirichletNilpotentFund38, realInitial38, zsCoefficientComplex,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]

theorem periodicPhase_nonfree_jordan38 : periodicPhase38 (constL2 1) 1 1 1 = 0 := by
  have _hi := periodicPhase_intervalIntegrable38 (constL2 1) 1 1 (by norm_num) ⟨1, zero_le_one, le_rfl⟩
  have he : (∫ r in (0 : ℝ)..1, (e02Pot38 (constL2 1) r *
      (actualPhysicalFloquetState33 (constL2 1) (1 : ℂ) (realInitial38 1) r 1 /
        actualPhysicalFloquetState33 (constL2 1) (1 : ℂ) (realInitial38 1) r 0)).re) = ∫ _r in (0 : ℝ)..1, (1 : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [coverRep38_const_ae (1 : ℂ)] with r hr
    intro hmem
    have ht : r ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le zero_le_one] at hmem
      exact ⟨hmem.1.le, hmem.2⟩
    have hs := periodicState_nilpotent38 ⟨r, ht⟩
    change actualPhysicalFloquetState33 (constL2 1) (1 : ℂ) (realInitial38 1) r = realInitial38 1 at hs
    change e02Pot38 (constL2 1) r = 1 at hr
    rw [hr, hs]
    norm_num [realInitial38]
  simp only [periodicPhase38, Complex.ofReal_one]
  rw [he]
  norm_num

end
end NlsGge.GK38
