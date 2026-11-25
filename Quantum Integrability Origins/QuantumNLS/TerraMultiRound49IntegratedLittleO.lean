import QuantumNLS.TerraMultiRound49TaylorIntegral

/-! The path-integrated positive-degree Taylor remainder is little-oh of
its scale power. The identification with physical Riccati trees is separate. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Asymptotics
namespace QuantumNLS.TerraMultiRound49IntegratedLittleO
open QuantumNLS.TranslatedCorrelation QuantumNLS.Sobolev QuantumNLS.CorrelationTaylor
open QuantumNLS.TerraMultiRound48Leading QuantumNLS.TerraMultiRound49TaylorBound
open QuantumNLS.TerraMultiRound49TaylorIntegral

variable {L : ℝ} [Fact (0 < L)]

def integratedResidual {n m k : ℕ} (f : Fin (m + 2) → Hk L k) (d : ℕ)
    (paths : Fin (m + 2) → Finset (Fin n)) (z : ℝ) : ℂ :=
  ∫ t : Fin n → ℝ, ((∏ i, Real.exp (-t i) : ℝ) : ℂ) *
    (Cfun f (scaledShift paths z t) - taylorPoly (Cfun f) (d + 1) (scaledShift paths z t)) ∂
    (Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ))))

theorem normalized_integral_eq {n m k : ℕ} (f : Fin (m + 2) → Hk L k) (d : ℕ)
    (paths : Fin (m + 2) → Finset (Fin n)) (z : ℝ) :
    (z ^ (d + 1))⁻¹ • integratedResidual f d paths z =
    ∫ t : Fin n → ℝ, ((∏ i, Real.exp (-t i) : ℝ) : ℂ) * remainder f d paths z t ∂
      (Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ)))) := by
  rw [integratedResidual, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [remainder, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow]
  ring

theorem integratedResidual_zero {n m k d : ℕ} (hk : 1 ≤ k)
    (f : Fin (m + 2) → Hk L k) (hd : d + 1 ≤ 2 * k)
    (paths : Fin (m + 2) → Finset (Fin n)) : integratedResidual f d paths 0 = 0 := by
  have hr : Cfun f 0 - taylorPoly (Cfun f) (d + 1) 0 = 0 := by
    have hb := taylor_remainder_bound hk f hd 0
    have he : eucl (0 : Fin (m + 2) → ℝ) = 0 := by simp [eucl]
    rw [he] at hb
    simp only [zero_pow (Nat.succ_ne_zero d), mul_zero] at hb
    exact norm_le_zero_iff.mp hb
  unfold integratedResidual
  have hs : ∀ t, scaledShift paths 0 t = 0 := by intro t; ext j; simp [scaledShift]
  simp only [hs, hr, mul_zero, integral_zero]

/-- The correlation Taylor remainder integrated against the orthant density
is little-oh of the scale to any positive allowed Taylor degree. -/
theorem integratedResidual_isLittleO {n m k d : ℕ} (hk : 1 ≤ k)
    (f : Fin (m + 2) → Hk L k) (hd : d + 1 ≤ 2 * k)
    (paths : Fin (m + 2) → Finset (Fin n)) :
    (integratedResidual f d paths) =o[𝓝 0] (fun z : ℝ => z ^ (d + 1)) := by
  apply IsLittleO.of_norm_norm
  apply isLittleO_of_tendsto
  · intro z hz
    have hz' : z = 0 := eq_zero_of_pow_eq_zero (norm_eq_zero.mp hz)
    subst z
    simp [integratedResidual_zero hk f hd paths]
  · have h := (integrated_remainder_tendsto hk f hd paths).norm
    have heq : (fun z : ℝ => ‖integratedResidual f d paths z‖ / ‖z ^ (d + 1)‖) =
        (fun z => ‖(z ^ (d + 1))⁻¹ • integratedResidual f d paths z‖) := by
      funext z
      rw [norm_smul, norm_inv, div_eq_mul_inv, mul_comm]
    rw [heq]
    simpa only [← normalized_integral_eq, norm_zero] using h

#print axioms normalized_integral_eq
#print axioms integratedResidual_zero
#print axioms integratedResidual_isLittleO
end QuantumNLS.TerraMultiRound49IntegratedLittleO
