import NlsGge.GK38.GradEigenCharacteristic
import NlsGge.GK38.DirichletRealContinuityProbe

/-! Concrete K2 prerequisite regressions. The general eigenvalue derivative,
closed-monodromy and codimension-two targets remain later obligations. -/
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

def constKernel (a : PairVec38) : PairKernelCont38 := ⟨fun _ => a, continuous_const⟩

theorem constKernel_ext (a : PairVec38) (s : ℝ) : pairKernelExt38 (constKernel a) s = a := by
  simp [pairKernelExt38, constKernel, Set.IccExtend]

theorem probe_const_seed_energy :
    Q (constKernel ![1, 1]) = 2 ∧ energy (constKernel ![1, 1]) = 2 ∧
      Q (Complex.I • constKernel ![1, 1]) = -2 := by
  have _hi := kernel_integrability (constKernel ![1, 1])
  refine ⟨?_, ?_, ?_⟩
  · simp [Q, constKernel_ext]
  · norm_num [energy, constKernel_ext]
  · rw [Q_smul]
    simp [Q, constKernel_ext]

theorem probe_free_state (z : ℂ) (a : PairVec38) (t : Time) :
    state 0 z a t =
      ![Complex.exp (-Complex.I * z * (t : ℝ)) * a 0,
        Complex.exp (Complex.I * z * (t : ℝ)) * a 1] := by
  rw [state_eq_mulVec, fundPair_zero_potential]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem probe_free_dirichlet (n : ℤ) (t : Time) :
    dirState 0 n t =
      ![Complex.exp (-Complex.I * ((n : ℝ) * Real.pi : ℂ) * (t : ℝ)),
        Complex.exp (Complex.I * ((n : ℝ) * Real.pi : ℂ) * (t : ℝ))] := by
  unfold dirState
  rw [realSlice_zero, gkMu_free38, probe_free_state]
  simp

theorem probe_distinct_complex_seed :
    state 0 0 ![1, Complex.I] t0 = ![1, Complex.I] ∧
      state 0 0 ![Complex.I, 1] t1 = ![Complex.I, 1] ∧
      starProd38 (![1, Complex.I] : PairVec38) ![1, Complex.I] = ![-1, 1] := by
  refine ⟨state_initial _ _ _, ?_, ?_⟩
  · rw [probe_free_state]
    simp
  · simp [starProd38]

theorem probe_negative_free_state :
    dirState 0 (-1) t0 = ![1, 1] ∧ dirState 0 (-1) t1 = ![-1, -1] := by
  constructor
  · exact state_initial _ _ _
  · rw [probe_free_dirichlet]
    ext i
    fin_cases i <;> norm_num [t1, mul_comm Complex.I (Real.pi : ℂ),
      Complex.exp_pi_mul_I, Complex.exp_neg_pi_mul_I]

end
end NlsGge.GK38.GradEigen38
