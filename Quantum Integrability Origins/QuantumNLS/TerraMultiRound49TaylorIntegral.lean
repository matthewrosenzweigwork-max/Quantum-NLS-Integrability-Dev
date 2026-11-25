import QuantumNLS.TerraMultiRound49TaylorBound
import QuantumNLS.TerraMultiRound48OrthantMoment

/-! Dominated convergence for the normalized positive-degree Taylor
remainder of an actual translated Sobolev correlation. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Asymptotics
namespace QuantumNLS.TerraMultiRound49TaylorIntegral
open QuantumNLS.TranslatedCorrelation QuantumNLS.Sobolev QuantumNLS.CorrelationTaylor
open QuantumNLS.TerraMultiRound48Leading QuantumNLS.TerraMultiRound48OrthantMoment
open QuantumNLS.TerraMultiRound49TaylorBound

variable {L : ℝ} [Fact (0 < L)]

theorem taylorPoly_continuous {q : ℕ} (C : (Fin q → ℝ) → ℂ) (d : ℕ) :
    Continuous (taylorPoly C d) := by
  unfold taylorPoly
  apply continuous_finsetSum
  intro j hj
  exact (continuous_const : Continuous (fun _ : Fin q → ℝ => ((Nat.factorial j : ℝ)⁻¹))).smul ((iteratedFDeriv ℝ j C 0).cont.comp
    (continuous_pi (fun _ => continuous_id)))

theorem remainder_continuous_t {n m k : ℕ} (hk : 1 ≤ k)
    (f : Fin (m + 2) → Hk L k) (d : ℕ)
    (paths : Fin (m + 2) → Finset (Fin n)) (z : ℝ) :
    Continuous (remainder f d paths z) := by
  unfold remainder
  exact (continuous_const : Continuous (fun _ : Fin n → ℝ => (z ^ (d + 1))⁻¹)).smul (((Cfun_continuous hk f).comp (scaledShift_continuous_t paths z)).sub
    ((taylorPoly_continuous (Cfun f) (d + 1)).comp (scaledShift_continuous_t paths z)))

/-- For every fixed family of Sobolev factors and finite paths, the
exponentially weighted normalized Taylor remainder tends to zero. -/
theorem integrated_remainder_tendsto {n m k d : ℕ} (hk : 1 ≤ k)
    (f : Fin (m + 2) → Hk L k) (hd : d + 1 ≤ 2 * k)
    (paths : Fin (m + 2) → Finset (Fin n)) :
    Tendsto (fun z : ℝ => ∫ t : Fin n → ℝ,
      ((∏ i, Real.exp (-t i) : ℝ) : ℂ) * remainder f d paths z t ∂
      (Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ)))))
      (𝓝 0) (𝓝 0) := by
  let μ := Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ)))
  let F : ℝ → (Fin n → ℝ) → ℂ := fun z t =>
    ((∏ i, Real.exp (-t i) : ℝ) : ℂ) * remainder f d paths z t
  have hD : Tendsto (fun z => ∫ t, F z t ∂μ) (𝓝 0)
      (𝓝 (∫ _t : Fin n → ℝ, (0 : ℂ) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun t : Fin n → ℝ => majorantConstant f d *
        ((∏ i, Real.exp (-t i)) * (∑ i, |t i|) ^ (d + 1)))
    · filter_upwards with z
      apply Continuous.aestronglyMeasurable
      apply Continuous.mul
      · apply Complex.continuous_ofReal.comp
        exact continuous_finsetProd _ (fun i _ => Real.continuous_exp.comp ((continuous_apply i).neg))
      · exact remainder_continuous_t hk f d paths z
    · filter_upwards with z
      filter_upwards with t
      have hp : 0 ≤ ∏ i : Fin n, Real.exp (-t i) :=
        Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le)
      dsimp [F]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hp]
      calc
        _ ≤ (∏ i : Fin n, Real.exp (-t i)) *
            (majorantConstant f d * (∑ i, |t i|) ^ (d + 1)) :=
          mul_le_mul_of_nonneg_left (remainder_bound hk f hd paths z t) hp
        _ = _ := by ring
    · exact (orthant_sum_moment n (d + 1)).const_mul _
    · filter_upwards with t
      simpa only [mul_zero] using tendsto_const_nhds.mul
        (remainder_pointwise_tendsto hk f hd paths t)
  simpa only [integral_zero] using hD

#print axioms taylorPoly_continuous
#print axioms remainder_continuous_t
#print axioms integrated_remainder_tendsto
end QuantumNLS.TerraMultiRound49TaylorIntegral
