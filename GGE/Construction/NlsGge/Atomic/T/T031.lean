                                                                                                                                                                                                                                                                                                                                                     
                                                                                                     
                                                                                                           
                                                                                                          
                                                                                                           
                                                                                                              
                                                                                        
import Mathlib
import NlsGge.Birkhoff.W12Tilt38b

set_option autoImplicit false

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Birkhoff
open scoped ENNReal
namespace NlsGge.ThirdConsultation.T
noncomputable section

def Ddelta {lo up : ℝ}
    (c : BoundedCoefficients lo up) (δ : ℝ) : ℝ :=
  Dtilt38 c.val δ

def gammaRates (a : ℤ → ℝ) : Measure (ℤ → ℂ) :=
  NlsGge.Measure.countableComplexGaussian a

def lowerTiltEnergy {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (z : ℤ → ℂ) : ℝ≥0∞ :=
  ∑' n : ℤ, ENNReal.ofReal (bRate38 c.val n * ‖z n‖ ^ 2)

def lowerTiltDensity {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (δ : ℝ) (z : ℤ → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Ddelta c δ * Real.exp (δ * (lowerTiltEnergy c z).toReal))

private theorem t031_Ddelta_zero {lo up : ℝ} (c : BoundedCoefficients lo up) :
    Ddelta c 0 = 1 := by
  unfold Ddelta Dtilt38 tiltRatio38
  simp

private theorem t031_density_eq {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ * upper < lower) :
    fullWeightSequenceGaussian (tiltCoef38 c.val δ) =
      (fullWeightSequenceGaussian c.val).withDensity
        (fun z => ENNReal.ofReal (Ddelta c δ * Real.exp (δ * bEnergy38 c.val z))) := by
  rcases hδ0.eq_or_lt with h0 | hpos
  · subst h0
    have hT : tiltCoef38 c.val 0 = c.val := funext fun j => by simp [tiltCoef38]
    have hf : (fun z : ℤ → ℂ =>
        ENNReal.ofReal (Ddelta c 0 * Real.exp (0 * bEnergy38 c.val z))) = fun _ => 1 := by
      funext z
      simp [t031_Ddelta_zero]
    rw [hT, hf]
    exact withDensity_one.symm
  · exact gaussian_tilt_density38 c hpos hδ

theorem lowerWeightTilt_gaussian_density
    (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ * upper < lower) :
    0 < Ddelta c δ ∧
    (∀ᵐ z ∂fullWeightSequenceGaussian c.val,
      Summable (fun n : ℤ => bRate38 c.val n * ‖z n‖ ^ 2) ∧
      lowerTiltEnergy c z ≠ ⊤) ∧
    Integrable
      (fun z => Ddelta c δ * Real.exp (δ * (lowerTiltEnergy c z).toReal))
      (fullWeightSequenceGaussian c.val) ∧
    (∫ z, Ddelta c δ * Real.exp (δ * (lowerTiltEnergy c z).toReal)
      ∂fullWeightSequenceGaussian c.val) = 1 ∧
    gammaRates (fun n => fullWeightRate c.val n - δ * bRate38 c.val n) =
      (fullWeightSequenceGaussian c.val).withDensity
        (lowerTiltDensity c δ) ∧
    (∀ Λ : Finset ℤ,
      (gammaRates (fun n =>
        fullWeightRate c.val n - δ * bRate38 c.val n)).map
          (fun z : ℤ → ℂ => fun i : Λ => z i) =
        Measure.pi (fun i : Λ =>
          complexGaussian (fullWeightRate c.val i - δ * bRate38 c.val i))) := by
  have hDpos : 0 < Ddelta c δ := by
    rcases hδ0.eq_or_lt with h0 | hpos
    · subst h0
      rw [t031_Ddelta_zero]
      exact one_pos
    · exact (hasProd_tilt38 c hpos hδ).1
  have hdens := t031_density_eq c hδ0 hδ
  have hmeasE : Measurable (fun z : ℤ → ℂ => Real.exp (δ * bEnergy38 c.val z)) :=
    Real.measurable_exp.comp ((measurable_bEnergy38 c.val).const_mul δ)
  have hmeas : Measurable (fun z : ℤ → ℂ =>
      ENNReal.ofReal (Ddelta c δ * Real.exp (δ * bEnergy38 c.val z))) :=
    ENNReal.measurable_ofReal.comp (hmeasE.const_mul (Ddelta c δ))
  have hlin : ∫⁻ z, ENNReal.ofReal (Ddelta c δ * Real.exp (δ * bEnergy38 c.val z))
      ∂fullWeightSequenceGaussian c.val = 1 := by
    have h1 : (fullWeightSequenceGaussian c.val).withDensity
        (fun z => ENNReal.ofReal (Ddelta c δ * Real.exp (δ * bEnergy38 c.val z))) Set.univ =
        ∫⁻ z, ENNReal.ofReal (Ddelta c δ * Real.exp (δ * bEnergy38 c.val z))
          ∂fullWeightSequenceGaussian c.val := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← h1, ← hdens, measure_univ]
  have hnonneg : ∀ z : ℤ → ℂ, 0 ≤ Ddelta c δ * Real.exp (δ * bEnergy38 c.val z) :=
    fun z => mul_nonneg hDpos.le (Real.exp_pos _).le
  have hae : (fun z : ℤ → ℂ => (ENNReal.ofReal (Ddelta c δ * Real.exp (δ * bEnergy38 c.val z))).toReal)
      =ᵐ[fullWeightSequenceGaussian c.val]
      (fun z : ℤ → ℂ => Ddelta c δ * Real.exp (δ * bEnergy38 c.val z)) :=
    Filter.Eventually.of_forall fun z => ENNReal.toReal_ofReal (hnonneg z)
  have hint : Integrable (fun z : ℤ → ℂ => Ddelta c δ * Real.exp (δ * bEnergy38 c.val z))
      (fullWeightSequenceGaussian c.val) :=
    (integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable
      (by rw [hlin]; exact ENNReal.one_ne_top)).congr hae
  refine ⟨hDpos, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ae_summable_bRate38 c).mono fun z hz => ⟨hz, hz.tsum_ofReal_ne_top⟩
  · exact hint
  · have hI : ∫ z, Ddelta c δ * Real.exp (δ * (lowerTiltEnergy c z).toReal)
        ∂fullWeightSequenceGaussian c.val =
        ∫ z, (ENNReal.ofReal (Ddelta c δ * Real.exp (δ * bEnergy38 c.val z))).toReal
          ∂fullWeightSequenceGaussian c.val :=
      (integral_congr_ae hae).symm
    rw [hI, integral_toReal hmeas.aemeasurable
      (Filter.Eventually.of_forall fun z => ENNReal.ofReal_lt_top), hlin, ENNReal.toReal_one]
  · have hrates : (fun n : ℤ => fullWeightRate c.val n - δ * bRate38 c.val n) =
        fullWeightRate (tiltCoef38 c.val δ) :=
      funext fun n => (fullWeightRate_tilt38 c δ n).symm
    unfold gammaRates
    rw [hrates]
    exact hdens
  · intro Λ
    unfold gammaRates countableComplexGaussian
    exact Measure.infinitePi_map_restrict _

end
end NlsGge.ThirdConsultation.T
