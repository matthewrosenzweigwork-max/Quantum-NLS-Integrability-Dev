import NlsGge.GK38.GradEigenStateL2
import NlsGge.GK38.DirichletRealBridge
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem real_state_symmetry (u : PhysicalL2) (x : ℝ) (a : PairVec38)
    (ha : a 1 = star (a 0)) : realSymmetric (state (realSlice u) (x : ℂ) a) := by
  intro t
  simp only [state_eq_mulVec,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
    star_add,star_mul,fundPair_real_entry_star38,ha,star_star]
  change fundPair (realSlice u) (x : ℂ) t 1 0 * a 0 +
      fundPair (realSlice u) (x : ℂ) t 1 1 * star (a 0) =
    star (a 0) * fundPair (realSlice u) (x : ℂ) t 1 1 +
      a 0 * fundPair (realSlice u) (x : ℂ) t 1 0
  ring

theorem dirState_real_symmetry (u : PhysicalL2) (n : ℤ) : realSymmetric (dirState u n) :=
  real_state_symmetry u (gkMu u n) ![1,1] (by simp)

theorem neuState_real_symmetry (u : PhysicalL2) (n : ℤ) : realSymmetric (neuState u n) :=
  real_state_symmetry u (nu u n) ![Complex.I,-Complex.I] (by simp)

theorem dirState_energy_positive (u : PhysicalL2) (n : ℤ) : 0 < energy (dirState u n) := by
  apply state_energy_positive
  intro h
  have hz := congrFun h 0
  norm_num at hz

theorem neuState_energy_positive (u : PhysicalL2) (n : ℤ) : 0 < energy (neuState u n) := by
  apply state_energy_positive
  intro h
  have hz := congrFun h 0
  simp only [Matrix.cons_val_zero,Pi.zero_apply] at hz
  exact Complex.I_ne_zero hz

theorem bilinear_real_energy (w : PairKernelCont38) (hw : realSymmetric w)
    (h : PhysicalL2) :
    (bilinearGradient w (realSlice h)).re = realEnergyGradient w h := by
  rw [bilinearGradient,real_denominator w hw]
  change (((energy w : ℂ)⁻¹) * integralPairCLM38 (square w) t1 (realSlice h)).re =
    (energy w)⁻¹ * (integralPairCLM38 (square w) t1 (realSlice h)).re
  rw [← Complex.ofReal_inv]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

end
end NlsGge.GK38.GradEigen38
