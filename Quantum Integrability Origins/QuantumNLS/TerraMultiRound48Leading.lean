import QuantumNLS.TerraMultiRound48TreeFubini
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Fixed-field degree-zero dominated convergence for finite path-shifted
Sobolev correlations. This is one contribution to the scalar expansion. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
namespace QuantumNLS.TerraMultiRound48Leading
open QuantumNLS.TranslatedCorrelation QuantumNLS.Sobolev QuantumNLS.Fourier
open QuantumNLS.TerraMultiRound48Orthant QuantumNLS.TerraMultiRound48TreeFubini

variable {L : ℝ} [Fact (0 < L)]

def scaledShift {n q : ℕ} (paths : Fin q → Finset (Fin n))
    (z : ℝ) (t : Fin n → ℝ) (j : Fin q) : ℝ :=
  -(∑ i ∈ paths j, t i) * z

theorem scaledShift_continuous_t {n q : ℕ} (paths : Fin q → Finset (Fin n)) (z : ℝ) :
    Continuous (scaledShift paths z) := by
  apply continuous_pi
  intro j
  exact ((continuous_finsetSum _ (fun i _ => continuous_apply i)).neg).mul_const z

theorem scaledShift_tendsto_zero {n q : ℕ} (paths : Fin q → Finset (Fin n)) (t : Fin n → ℝ) :
    Tendsto (fun z : ℝ => scaledShift paths z t) (𝓝 0) (𝓝 0) := by
  apply tendsto_pi_nhds.mpr
  intro j
  have h : Continuous (fun z : ℝ => -(∑ i ∈ paths j, t i) * z) := continuous_const.mul continuous_id
  simpa only [scaledShift, mul_zero, Pi.zero_apply] using h.tendsto 0

/-- The finite product exponential density has total integral one. -/
theorem orthant_exp_integral (n : ℕ) :
    (∫ t : Fin n → ℝ, ∏ i, Real.exp (-t i) ∂
      (Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ))))) = 1 := by
  have h := integral_fintype_prod_eq_pow (ι := Fin n)
    (μ := volume.restrict (Ioi (0 : ℝ))) (fun x : ℝ => Real.exp (-x))
  simpa only [integral_exp_neg_Ioi_zero, one_pow] using h

/-- The leading correlation contribution converges to the unshifted
correlation for each fixed Sobolev field and every finite family of paths. -/
theorem correlation_leading {n q k : ℕ} (hk : 1 ≤ k) (f : Fin q → Hk L k)
    (paths : Fin q → Finset (Fin n)) :
    Tendsto (fun z : ℝ => ∫ t : Fin n → ℝ,
      ((∏ i, Real.exp (-t i) : ℝ) : ℂ) * Cfun f (scaledShift paths z t) ∂
      (Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ)))))
      (𝓝 0) (𝓝 (Cfun f 0)) := by
  let B : ℝ := L * cL L ^ q * ∏ j, ‖f j‖
  let μ := Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ)))
  let F : ℝ → (Fin n → ℝ) → ℂ := fun z t =>
    ((∏ i, Real.exp (-t i) : ℝ) : ℂ) * Cfun f (scaledShift paths z t)
  have hD : Tendsto (fun z => ∫ t, F z t ∂μ) (𝓝 0)
      (𝓝 (∫ t : Fin n → ℝ, ((∏ i, Real.exp (-t i) : ℝ) : ℂ) * Cfun f 0 ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun t : Fin n → ℝ => B * ∏ i, Real.exp (-t i))
    · filter_upwards with z
      exact (orthant_bounded_integrable n (fun t => Cfun f (scaledShift paths z t)) B
        ((Cfun_continuous hk f).comp (scaledShift_continuous_t paths z))
        (fun t => norm_Cfun_le hk f _)).aestronglyMeasurable
    · filter_upwards with z
      filter_upwards with t
      have hp : 0 ≤ ∏ i : Fin n, Real.exp (-t i) := Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le)
      dsimp [F]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hp]
      calc
        _ ≤ (∏ i : Fin n, Real.exp (-t i)) * B := mul_le_mul_of_nonneg_left (norm_Cfun_le hk f _) hp
        _ = _ := mul_comm _ _
    · exact (orthant_exp_integrable n).const_mul B
    · filter_upwards with t
      have ht := ((Cfun_continuous hk f).tendsto 0).comp (scaledShift_tendsto_zero paths t)
      exact tendsto_const_nhds.mul ht
  have hIntegral : (∫ t : Fin n → ℝ, ((∏ i, Real.exp (-t i) : ℝ) : ℂ) * Cfun f 0 ∂μ) = Cfun f 0 := by
    rw [integral_mul_const]
    have he : (∫ t : Fin n → ℝ, ((∏ i, Real.exp (-t i) : ℝ) : ℂ) ∂μ) = 1 := by
      rw [integral_complex_ofReal]
      rw [orthant_exp_integral]
      norm_num
    rw [he, one_mul]
  rw [hIntegral] at hD
  exact hD

#print axioms scaledShift_continuous_t
#print axioms scaledShift_tendsto_zero
#print axioms orthant_exp_integral
#print axioms correlation_leading
end QuantumNLS.TerraMultiRound48Leading
