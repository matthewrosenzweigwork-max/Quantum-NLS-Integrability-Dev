import QuantumNLS.TerraMultiRound67DensityRule
import QuantumNLS.TerraMultiRound67Correction
import QuantumNLS.TerraMultiRound67RealDensity

/-! Smooth evaluations of the three continuous correction terms. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open QuantumNLS.ClassicalCharges QuantumNLS.RelativeEnergy QuantumNLS.TranslatedCorrelation
open QuantumNLS.Fourier QuantumNLS.TerraMultiRound66WeakMap
open QuantumNLS.RiccatiPointwiseDisc QuantumNLS.TerraMultiRound59SobolevCoordinates
open QuantumNLS.TerraMultiRound67SmoothWeak QuantumNLS.TerraMultiRound67Quartic
open QuantumNLS.TerraMultiRound67DensityCandidate QuantumNLS.TerraMultiRound67Sextic
open QuantumNLS.TerraMultiRound67RealDensity QuantumNLS.RootH1RatioOperator
namespace QuantumNLS.TerraMultiRound67SmoothNorms
variable {L : ℝ} [Fact (0 < L)]

theorem smooth_weighted_norm (u : Hk L 1)
    (hf : SmoothPeriodic L (physRep L 1 (coordinates (L := L) 1 u))) :
    ‖weightedDerivative u‖^2 =
      ∫ x in (0 : ℝ)..L, ‖physRep L 1 (coordinates (L := L) 1 u) x‖^2 *
        ‖deriv (physRep L 1 (coordinates (L := L) 1 u)) x‖^2 := by
  rw [quartic_eq]
  calc
    _ = ∫ x : AddCircle L, ‖lift hf x‖^2 * ‖lift (sp_deriv hf) x‖^2 := by
      apply integral_congr_ae
      have hw := smooth_weakD_eq u hf
      filter_upwards [(memLp_of_continuous (continuous_lift (sp_deriv hf))).coeFn_toLp] with x hx
      rw [contRep_eq_lift u hf, hw, hx]
    _ = _ := by
      rw [← AddCircle.intervalIntegral_preimage L 0, zero_add]
      apply intervalIntegral.integral_congr
      intro x hx
      simp only [lift_coe]

theorem smooth_density_norm (u : Hk L 1)
    (hf : SmoothPeriodic L (physRep L 1 (coordinates (L := L) 1 u))) :
    ‖densityCandidate u‖^2 = ∫ x in (0 : ℝ)..L,
      ‖deriv (fun y => ‖physRep L 1 (coordinates (L := L) 1 u) y‖^2) x‖^2 := by
  let f := physRep L 1 (coordinates (L := L) 1 u)
  rw [← integral_norm_sq (densityCandidate u)]
  calc
    _ = ∫ x : AddCircle L,
      ‖conj (lift hf x) * lift (sp_deriv hf) x + conj (lift (sp_deriv hf) x) * lift hf x‖^2 := by
      apply integral_congr_ae
      have hw := smooth_weakD_eq u hf
      filter_upwards [densityCandidate_ae u, (memLp_of_continuous (continuous_lift (sp_deriv hf))).coeFn_toLp] with x hx hy
      rw [hx, contRep_eq_lift u hf, hw, hy]
    _ = _ := by
      rw [← AddCircle.intervalIntegral_preimage L 0, zero_add]
      apply intervalIntegral.integral_congr
      intro x hx
      simp only [lift_coe]
      have h := density_embedded_deriv ((contDiff_infty_iff_deriv.mp hf.smooth).1 x)
      rw [(QuantumNLS.TerraMultiRound65DensityDerivative.density_hasDerivAt
        ((contDiff_infty_iff_deriv.mp hf.smooth).1 x).hasDerivAt).deriv] at h
      rw [add_comm, h, Complex.norm_real, Real.norm_eq_abs]

theorem smooth_sextic (u : Hk L 1)
    (hf : SmoothPeriodic L (physRep L 1 (coordinates (L := L) 1 u))) :
    sexticIntegral u = ∫ x in (0 : ℝ)..L,
      ‖physRep L 1 (coordinates (L := L) 1 u) x‖^6 := by
  rw [sexticIntegral_eq, contRep_eq_lift u hf, ← AddCircle.intervalIntegral_preimage L 0, zero_add]
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [lift_coe]

#print axioms smooth_weighted_norm
#print axioms smooth_density_norm
#print axioms smooth_sextic
end QuantumNLS.TerraMultiRound67SmoothNorms
