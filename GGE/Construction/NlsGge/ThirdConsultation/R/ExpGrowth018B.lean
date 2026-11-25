import Mathlib
import NlsGge.Ramer.FiniteDivergenceGrowth
import NlsGge.Ramer.FiniteDivergenceL2
import NlsGge.ThirdConsultation.R.ExpGrowth018A

                                                                                                                 
                                                                                                            
                                                                                                 
                                                                                                                  
set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Filter Real
open scoped Topology RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section

/-! ### Elementary squares of exponentials -/

theorem sq_le_sq_mul_of_le {y K w : ℝ} (hy : 0 ≤ y) (h : y ≤ K * w) : y ^ 2 ≤ K ^ 2 * w ^ 2 := by
  have := pow_le_pow_left₀ hy h 2
  rwa [mul_pow] at this

theorem sq_le_sq_mul_of_abs_le {y K w : ℝ} (h : |y| ≤ K * w) : y ^ 2 ≤ K ^ 2 * w ^ 2 := by
  have := sq_le_sq_mul_of_le (abs_nonneg y) h
  rwa [sq_abs] at this

theorem sq_mul_exp_eq (a t : ℝ) : (Real.exp (a * t)) ^ 2 = Real.exp ((2 * a) * t) := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Dominated convergence with an exponential dominator -/

/-- Dominated convergence with the integrable exponential dominator `K (1+‖x‖)^m e^{a‖x‖}`
(the exponential analogue of `NlsGge.Ramer.tendsto_integral_of_poly_bound`). -/
theorem tendsto_integral_of_exp_bound_finiteStd {g : ℕ → V → ℝ} {g0 : V → ℝ}
    (hmeas : ∀ n, AEStronglyMeasurable (g n) (NlsGge.Ramer.finiteStdGaussian V))
    (K a : ℝ) (m : ℕ) (hb : ∀ n x, ‖g n x‖ ≤ K * ((1 + ‖x‖) ^ m * Real.exp (a * ‖x‖)))
    (hev : ∀ x, ∃ N : ℕ, ∀ n ≥ N, g n x = g0 x) :
    Tendsto (fun n => ∫ x, g n x ∂(NlsGge.Ramer.finiteStdGaussian V)) atTop
      (𝓝 (∫ x, g0 x ∂(NlsGge.Ramer.finiteStdGaussian V))) := by
  refine tendsto_integral_of_dominated_convergence
    (fun x => K * ((1 + ‖x‖) ^ m * Real.exp (a * ‖x‖))) hmeas
    ((integrable_pow_mul_exp_norm_finiteStd m a).const_mul K)
    (fun n => Filter.Eventually.of_forall (hb n)) (Filter.Eventually.of_forall fun x => ?_)
  obtain ⟨N, hN⟩ := hev x
  exact tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨N, fun n hn => (hN n hn).symm⟩)

/-! ### Exponential pointwise bounds for the divergence and the signed trace -/

/-- `|δF(x)| <= (A + d B) (1+‖x‖) e^{a‖x‖}` when `‖F x‖ <= A e^{a‖x‖}` and `‖DF x‖ <= B e^{a‖x‖}`
(`d = finrank V`); the exponential analogue of `NlsGge.Ramer.abs_finiteGaussianDivergence_le_poly`. -/
theorem abs_finiteGaussianDivergence_le_exp {F : V → V} {A B a : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (x : V) (hF : ‖F x‖ ≤ A * Real.exp (a * ‖x‖))
    (hD : ‖fderiv ℝ F x‖ ≤ B * Real.exp (a * ‖x‖)) :
    |NlsGge.Ramer.finiteGaussianDivergence F x| ≤
      (A + (Module.finrank ℝ V : ℝ) * B) * ((1 + ‖x‖) * Real.exp (a * ‖x‖)) := by
  have hd : |NlsGge.Ramer.finiteGaussianDivergence F x| ≤
      ‖x‖ * ‖F x‖ + (Module.finrank ℝ V : ℝ) * ‖fderiv ℝ F x‖ := by
    rw [NlsGge.Ramer.finiteGaussianDivergence_eq_traceCLM]
    refine (abs_sub _ _).trans (add_le_add ?_ (NlsGge.Ramer.abs_traceCLM_le _))
    exact abs_real_inner_le_norm _ _
  have he : 0 ≤ Real.exp (a * ‖x‖) := (Real.exp_pos _).le
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have hfd : (0 : ℝ) ≤ Module.finrank ℝ V := Nat.cast_nonneg _
  have hAe : 0 ≤ A * Real.exp (a * ‖x‖) := mul_nonneg hA he
  have h1x : Real.exp (a * ‖x‖) ≤ (1 + ‖x‖) * Real.exp (a * ‖x‖) :=
    le_mul_of_one_le_left he (by linarith)
  calc |NlsGge.Ramer.finiteGaussianDivergence F x|
      ≤ ‖x‖ * ‖F x‖ + (Module.finrank ℝ V : ℝ) * ‖fderiv ℝ F x‖ := hd
    _ ≤ ‖x‖ * (A * Real.exp (a * ‖x‖)) +
          (Module.finrank ℝ V : ℝ) * (B * Real.exp (a * ‖x‖)) :=
        add_le_add (mul_le_mul_of_nonneg_left hF hx) (mul_le_mul_of_nonneg_left hD hfd)
    _ ≤ (1 + ‖x‖) * (A * Real.exp (a * ‖x‖)) +
          (Module.finrank ℝ V : ℝ) * (B * ((1 + ‖x‖) * Real.exp (a * ‖x‖))) :=
        add_le_add (mul_le_mul_of_nonneg_right (by linarith) hAe)
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1x hB) hfd)
    _ = (A + (Module.finrank ℝ V : ℝ) * B) * ((1 + ‖x‖) * Real.exp (a * ‖x‖)) := by ring

/-- `|tr(DF∘DF)| <= d B^2 e^{2a‖x‖}` when `‖DF x‖ <= B e^{a‖x‖}`, `B >= 0`. -/
theorem abs_traceCLM_comp_self_le_exp {D : V →L[ℝ] V} {B a : ℝ} (x : V)
    (hD : ‖D‖ ≤ B * Real.exp (a * ‖x‖)) (hB : 0 ≤ B) :
    |NlsGge.Ramer.traceCLM V (D.comp D)| ≤
      (Module.finrank ℝ V : ℝ) * (B ^ 2 * Real.exp ((2 * a) * ‖x‖)) := by
  have hop : ‖D.comp D‖ ≤ ‖D‖ * ‖D‖ := ContinuousLinearMap.opNorm_comp_le D D
  have hsq : ‖D‖ * ‖D‖ ≤ (B * Real.exp (a * ‖x‖)) * (B * Real.exp (a * ‖x‖)) :=
    mul_le_mul hD hD (norm_nonneg _) (mul_nonneg hB (Real.exp_pos _).le)
  have hexp : (B * Real.exp (a * ‖x‖)) * (B * Real.exp (a * ‖x‖)) =
      B ^ 2 * Real.exp ((2 * a) * ‖x‖) := by
    rw [← sq_mul_exp_eq]
    ring
  calc |NlsGge.Ramer.traceCLM V (D.comp D)|
      ≤ (Module.finrank ℝ V : ℝ) * ‖D.comp D‖ := NlsGge.Ramer.abs_traceCLM_le _
    _ ≤ (Module.finrank ℝ V : ℝ) * (B ^ 2 * Real.exp ((2 * a) * ‖x‖)) :=
        mul_le_mul_of_nonneg_left (hop.trans (hsq.trans_eq hexp)) (Nat.cast_nonneg _)

end
end NlsGge.ThirdConsultation.R
