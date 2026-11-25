import NlsGge.Measure.FiniteFourierGaussianTranslation
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NlsGge.Measure

/-- The real-valued output-side likelihood for the actual finite full-rate
Fourier Gaussian, with every signed mode including zero. -/
def fullWeightFourierLikelihoodReal (c : ℕ → ℝ) (N : ℕ)
    (h z : NlsGge.Pilot.FourierPlane N) : ℝ :=
  Real.exp (∑ i : Fin (2 * N + 1),
    (2 * fullWeightRate c (NlsGge.Pilot.modeIndex N i) *
        (star (h i) * z i).re -
      fullWeightRate c (NlsGge.Pilot.modeIndex N i) * ‖h i‖ ^ 2))

/-- The finite squared Cameron--Martin energy for the actual source rates. -/
def fullWeightFourierLikelihoodEnergy (c : ℕ → ℝ) (N : ℕ)
    (h : NlsGge.Pilot.FourierPlane N) : ℝ :=
  ∑ i : Fin (2 * N + 1),
    2 * fullWeightRate c (NlsGge.Pilot.modeIndex N i) * ‖h i‖ ^ 2

lemma fullWeightFourierLikelihoodReal_sq_eq_expEnergy_mul_double
    (c : ℕ → ℝ) (N : ℕ)
    (h z : NlsGge.Pilot.FourierPlane N) :
    (fullWeightFourierLikelihoodReal c N h z) ^ 2 =
      Real.exp (fullWeightFourierLikelihoodEnergy c N h) *
        fullWeightFourierLikelihoodReal c N (fun i => (2 : ℂ) * h i) z := by
  unfold fullWeightFourierLikelihoodReal fullWeightFourierLikelihoodEnergy
  rw [pow_two, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hstar : star ((2 : ℂ) * h i) = (2 : ℂ) * star (h i) := by simp
  have hnorm : ‖(2 : ℂ) * h i‖ ^ 2 = 4 * ‖h i‖ ^ 2 := by
    rw [norm_mul]
    norm_num
    <;> ring
  have hre : (star ((2 : ℂ) * h i) * z i).re =
      2 * (star (h i) * z i).re := by
    rw [hstar]
    have hmul : (2 : ℂ) * star (h i) * z i =
        (2 : ℂ) * (star (h i) * z i) := by ring
    rw [hmul]
    norm_num [Complex.mul_re]
  rw [hnorm, hre]
  ring

theorem integrable_and_integral_fullWeightFourierLikelihoodReal
    (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (N : ℕ)
    (h : NlsGge.Pilot.FourierPlane N) :
    Integrable (fun z : NlsGge.Pilot.FourierPlane N =>
      fullWeightFourierLikelihoodReal c N h z)
      (fullWeightFourierGaussian N c) ∧
    (∫ z : NlsGge.Pilot.FourierPlane N,
      fullWeightFourierLikelihoodReal c N h z ∂fullWeightFourierGaussian N c) = 1 := by
  let μ := fullWeightFourierGaussian N c
  let ρ : NlsGge.Pilot.FourierPlane N → ℝ :=
    fullWeightFourierLikelihoodReal c N h
  have hRN : μ.map (fun z i => z i + h i) =
      μ.withDensity (fun z => ENNReal.ofReal (ρ z)) := by
    simpa [μ, ρ, fullWeightFourierLikelihoodReal] using
      fullWeightFourierGaussian_map_add_withDensity_afterNormalization
        lower upper c hlower hbound hupper N h
  have hρ_meas : Measurable ρ := by
    dsimp [ρ, fullWeightFourierLikelihoodReal]
    apply Real.measurable_exp.comp
    refine Finset.measurable_sum Finset.univ ?_
    intro i hi
    fun_prop
  have hρ_nonneg : 0 ≤ᵐ[μ] ρ :=
    Filter.Eventually.of_forall (fun z => (Real.exp_pos _).le)
  have hshift_meas : Measurable (fun z : NlsGge.Pilot.FourierPlane N =>
      fun i => z i + h i) := by
    fun_prop
  have hmass : (μ.withDensity (fun z => ENNReal.ofReal (ρ z))) Set.univ = 1 := by
    rw [← hRN]
    rw [Measure.map_apply hshift_meas MeasurableSet.univ]
    simp [μ]
  have hlintegral : (∫⁻ z, ENNReal.ofReal (ρ z) ∂μ) = 1 := by
    calc
      (∫⁻ z, ENNReal.ofReal (ρ z) ∂μ) =
          ∫⁻ z in Set.univ, ENNReal.ofReal (ρ z) ∂μ := by
        rw [setLIntegral_univ]
      _ = (μ.withDensity (fun z => ENNReal.ofReal (ρ z))) Set.univ := by
        exact (withDensity_apply _ MeasurableSet.univ).symm
      _ = 1 := hmass
  have hρ_integrable : Integrable ρ μ :=
    (lintegral_ofReal_ne_top_iff_integrable
      hρ_meas.aestronglyMeasurable hρ_nonneg).mp (by rw [hlintegral]; simp)
  have hconvert := ofReal_integral_eq_lintegral_ofReal hρ_integrable hρ_nonneg
  rw [hlintegral] at hconvert
  have hreal_eq : ENNReal.ofReal (∫ z, ρ z ∂μ) = ENNReal.ofReal (1 : ℝ) := by
    simpa using hconvert
  have hint_nonneg : 0 ≤ ∫ z, ρ z ∂μ := integral_nonneg_of_ae hρ_nonneg
  refine ⟨hρ_integrable, ?_⟩
  exact (ENNReal.ofReal_eq_ofReal_iff hint_nonneg (by norm_num)).mp hreal_eq

theorem integrable_and_integral_sq_fullWeightFourierLikelihoodReal
    (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (N : ℕ)
    (h : NlsGge.Pilot.FourierPlane N) :
    Integrable (fun z : NlsGge.Pilot.FourierPlane N =>
      (fullWeightFourierLikelihoodReal c N h z) ^ 2)
      (fullWeightFourierGaussian N c) ∧
    (∫ z : NlsGge.Pilot.FourierPlane N,
      (fullWeightFourierLikelihoodReal c N h z) ^ 2
        ∂fullWeightFourierGaussian N c) =
      Real.exp (fullWeightFourierLikelihoodEnergy c N h) := by
  let μ := fullWeightFourierGaussian N c
  obtain ⟨hdouble_integrable, hdouble_integral⟩ :=
    integrable_and_integral_fullWeightFourierLikelihoodReal lower upper c
      hlower hbound hupper N (fun i => (2 : ℂ) * h i)
  have hpointwise (z : NlsGge.Pilot.FourierPlane N) :
      (fullWeightFourierLikelihoodReal c N h z) ^ 2 =
        Real.exp (fullWeightFourierLikelihoodEnergy c N h) *
          fullWeightFourierLikelihoodReal c N (fun i => (2 : ℂ) * h i) z :=
    fullWeightFourierLikelihoodReal_sq_eq_expEnergy_mul_double c N h z
  have hproduct_integrable : Integrable
      (fun z : NlsGge.Pilot.FourierPlane N =>
        Real.exp (fullWeightFourierLikelihoodEnergy c N h) *
          fullWeightFourierLikelihoodReal c N (fun i => (2 : ℂ) * h i) z) μ := by
    exact hdouble_integrable.const_mul _
  have hsquare_integrable : Integrable
      (fun z : NlsGge.Pilot.FourierPlane N =>
        (fullWeightFourierLikelihoodReal c N h z) ^ 2) μ := by
    exact hproduct_integrable.congr
      (Filter.Eventually.of_forall (fun z => (hpointwise z).symm))
  refine ⟨hsquare_integrable, ?_⟩
  calc
    (∫ z : NlsGge.Pilot.FourierPlane N,
        (fullWeightFourierLikelihoodReal c N h z) ^ 2 ∂μ) =
      ∫ z : NlsGge.Pilot.FourierPlane N,
        Real.exp (fullWeightFourierLikelihoodEnergy c N h) *
          fullWeightFourierLikelihoodReal c N (fun i => (2 : ℂ) * h i) z ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpointwise
    _ = Real.exp (fullWeightFourierLikelihoodEnergy c N h) *
        ∫ z : NlsGge.Pilot.FourierPlane N,
          fullWeightFourierLikelihoodReal c N (fun i => (2 : ℂ) * h i) z ∂μ := by
        rw [integral_const_mul]
    _ = Real.exp (fullWeightFourierLikelihoodEnergy c N h) := by
        rw [hdouble_integral]
        ring

end NlsGge.Measure
