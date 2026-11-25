import QuantumNLS.TerraMultiRound67SmoothWeak
import QuantumNLS.TerraMultiRound67DensityExtension
import QuantumNLS.TerraMultiRound65DensityDerivative

/-! The H¹ weak product rule for the squared density. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open QuantumNLS.ClassicalCharges QuantumNLS.RelativeEnergy QuantumNLS.TranslatedCorrelation
open QuantumNLS.Fourier QuantumNLS.WeakDerivatives QuantumNLS.TerraMultiRound66WeakMap
open QuantumNLS.RiccatiPointwiseDisc QuantumNLS.TerraMultiRound59SobolevCoordinates
open QuantumNLS.TerraMultiRound67SmoothWeak QuantumNLS.TerraMultiRound67DensityExtension
open QuantumNLS.TerraMultiRound67DensityCandidate QuantumNLS.TerraMultiRound67SmoothDense
open QuantumNLS.TerraMultiRound65DensityDerivative
namespace QuantumNLS.TerraMultiRound67DensityRule
variable {L : ℝ} [Fact (0 < L)]

theorem density_smooth_product_rule (u : Hk L 1) (hu : u ∈ smoothFields (L := L)) :
    HasWeakDeriv (densityClass u) (densityCandidate u) := by
  let f := physRep L 1 (coordinates (L := L) 1 u)
  have hf : SmoothPeriodic L f := hu
  let d : ℝ → ℂ := fun x => ((‖f x‖^2 : ℝ) : ℂ)
  have hd : SmoothPeriodic L d := by
    constructor
    · have h : d = fun x => conj (f x) * f x := by
        funext x
        dsimp [d]
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      rw [h]
      exact (Complex.conjCLE.contDiff.comp hf.smooth).mul hf.smooth
    · intro x
      dsimp [d]
      rw [hf.periodic x]
  have hrepr := contRep_eq_lift u hf
  have hfield : densityClass u = (memLp_of_continuous (continuous_lift hd)).toLp (lift hd) := by
    apply Lp.ext
    filter_upwards [densityClass_ae u, (memLp_of_continuous (continuous_lift hd)).coeFn_toLp] with x hx hy
    rw [hx, hy, hrepr]
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
    simp only [lift_coe, d]
    rfl
  have hderiv : densityCandidate u =
      (memLp_of_continuous (continuous_lift (sp_deriv hd))).toLp (lift (sp_deriv hd)) := by
    apply Lp.ext
    have hw := smooth_weakD_eq u hf
    filter_upwards [densityCandidate_ae u,
      (memLp_of_continuous (continuous_lift (sp_deriv hf))).coeFn_toLp,
      (memLp_of_continuous (continuous_lift (sp_deriv hd))).coeFn_toLp] with x hx hw' hy
    rw [hx, hy, hrepr, hw] 
    rw [hw']
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
    simp only [lift_coe]
    simpa only [f, d, add_comm] using
      ((density_hasDerivAt ((contDiff_infty_iff_deriv.mp hf.smooth).1 x).hasDerivAt).deriv).symm
  rw [hfield, hderiv]
  exact smooth_lift_weak d hd

theorem density_product_rule (u : Hk L 1) : HasWeakDeriv (densityClass u) (densityCandidate u) :=
  density_product_rule_extension density_smooth_product_rule u

#print axioms density_smooth_product_rule
#print axioms density_product_rule
end QuantumNLS.TerraMultiRound67DensityRule
