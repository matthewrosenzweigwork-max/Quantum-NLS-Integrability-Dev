import NlsGge.GK38.EigenvalueCompactnessEndpointPhase
import NlsGge.GK38.DirichletRealPhaseInteger

/-! # S7: actual periodic half-turn integers and their parity -/
set_option autoImplicit false
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem clockwise_exp_real38 (r : ℝ) :
    (Complex.exp (-Complex.I * (r : ℂ))).re = Real.cos r := by
  simp only [Complex.exp_re, Complex.neg_re, Complex.neg_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, neg_zero, Real.exp_zero, one_mul, zero_add,
    neg_one_mul, Real.cos_neg]

theorem periodicPhase_discrete38 (u : PhysicalL2) (x : ℝ) (n : ℤ) (a : ℂ)
    (ha : EigenDirectionAt38 u x n a) : ∃ m : ℤ,
    periodicPhase38 u x a 1 = (m : ℝ) * Real.pi ∧
      Real.cos ((m : ℝ) * Real.pi) = Real.cos ((n : ℝ) * Real.pi) := by
  have he := eigenDirection_phase_exp38 u x n a ha
  have him : (Complex.exp (-Complex.I * (periodicPhase38 u x a 1 : ℂ))).im = 0 := by
    rw [he]
    exact Complex.ofReal_im _
  obtain ⟨m, hm⟩ := dirichlet_clockwise_phase_integer38 _ him
  refine ⟨m, hm, ?_⟩
  have hre := congrArg Complex.re he
  rw [clockwise_exp_real38, hm, Complex.ofReal_re] at hre
  exact hre


end
end NlsGge.GK38
