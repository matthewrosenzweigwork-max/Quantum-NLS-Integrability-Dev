import Mathlib
import NlsGge.Ramer.FiniteGaussian
import NlsGge.Ramer.FiniteDivergenceGrowth

                                                                                                                       
                                                                                 
                                                                                                            
                                                                                                         
set_option autoImplicit false

open MeasureTheory Filter Real
open scoped Topology

namespace NlsGge.ThirdConsultation.R
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- `e^{‖x‖²/4}` is integrable against the finite standard Gaussian. -/
theorem integrable_exp_quarter_sq_norm_finiteStd :
    Integrable (fun x : V => Real.exp (‖x‖ ^ 2 / 4)) (NlsGge.Ramer.finiteStdGaussian V) := by
  have hdens : Measurable (fun x : V => ENNReal.ofReal (NlsGge.Ramer.finiteGaussianDensity V x)) :=
    (NlsGge.Ramer.continuous_finiteGaussianDensity (V := V)).measurable.ennreal_ofReal
  rw [NlsGge.Ramer.finiteStdGaussian, integrable_withDensity_iff_integrable_smul' hdens
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  refine ((NlsGge.Ramer.integrable_rexp_neg_quarter_sq_norm (V := V)).const_mul
    ((2 * π) ^ (-(Module.finrank ℝ V : ℝ) / 2))).congr (Filter.Eventually.of_forall fun x => ?_)
  have e : Real.exp (-(‖x‖ ^ 2) / 2) * Real.exp (‖x‖ ^ 2 / 4) =
      Real.exp (-(1 / 4 : ℝ) * ‖x‖ ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  dsimp only
  rw [ENNReal.toReal_ofReal (NlsGge.Ramer.finiteGaussianDensity_pos x).le, smul_eq_mul]
  unfold NlsGge.Ramer.finiteGaussianDensity
  rw [mul_assoc, e]

/-- Pointwise bound: `(1+t)^m e^{a t} <= e^{(m+a)^2} e^{t^2/4}` for `t >= 0`. -/
theorem pow_one_add_mul_exp_le_quarter (m : ℕ) (a t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ m * Real.exp (a * t) ≤ Real.exp ((m + a) ^ 2) * Real.exp (t ^ 2 / 4) := by
  have h1 : (1 + t) ^ m ≤ Real.exp (m * t) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp t]) m
  have h2 : Real.exp (m * t) * Real.exp (a * t) ≤
      Real.exp ((m + a) ^ 2) * Real.exp (t ^ 2 / 4) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (t / 2 - (m + a))]
  calc (1 + t) ^ m * Real.exp (a * t) ≤ Real.exp (m * t) * Real.exp (a * t) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ ≤ Real.exp ((m + a) ^ 2) * Real.exp (t ^ 2 / 4) := h2

/-- Integrability of `(1+‖x‖)^m e^{a‖x‖}` under the finite standard Gaussian. -/
theorem integrable_pow_mul_exp_norm_finiteStd (m : ℕ) (a : ℝ) :
    Integrable (fun x : V => (1 + ‖x‖) ^ m * Real.exp (a * ‖x‖))
      (NlsGge.Ramer.finiteStdGaussian V) := by
  refine Integrable.mono' ((integrable_exp_quarter_sq_norm_finiteStd (V := V)).const_mul
    (Real.exp ((m + a) ^ 2))) ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (by fun_prop : Continuous fun x : V => (1 + ‖x‖) ^ m * Real.exp (a * ‖x‖)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_one_add_mul_exp_le_quarter m a ‖x‖ (norm_nonneg x)

/-- Integrability from a pointwise bound by `K (1+‖x‖)^m e^{a‖x‖}`. -/
theorem integrable_of_norm_le_pow_mul_exp_finiteStd {g : V → ℝ}
    (hg : AEStronglyMeasurable g (NlsGge.Ramer.finiteStdGaussian V)) (K a : ℝ) (m : ℕ)
    (h : ∀ x, ‖g x‖ ≤ K * ((1 + ‖x‖) ^ m * Real.exp (a * ‖x‖))) :
    Integrable g (NlsGge.Ramer.finiteStdGaussian V) :=
  Integrable.mono' ((integrable_pow_mul_exp_norm_finiteStd m a).const_mul K) hg
    (Filter.Eventually.of_forall h)

end
end NlsGge.ThirdConsultation.R
