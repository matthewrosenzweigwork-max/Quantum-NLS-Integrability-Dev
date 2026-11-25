import Mathlib
import NlsGge.Birkhoff.F08Bare38e

                                                                                                 
                                                                                           
                                                                                            
                                                                                                     
                                                                                                 
                                                                                                          
                                                                                                        
                                                                                              
                                                                                                
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.F010Aux

variable {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)
include hm hβ

theorem dens_pos_le (y : Hm1 m) :
    0 < Real.exp (-Rm38 m β y) ∧ Real.exp (-Rm38 m β y) ≤ 1 :=
  ⟨Real.exp_pos _, Real.exp_le_one_iff.2 (neg_nonpos.2 (Rm38_nonneg hm hβ y))⟩

theorem measurable_dens {g : (ℤ → ℂ) → Hm1 m} (hg : Measurable g) :
    Measurable (fun z => Real.exp (-Rm38 m β (g z))) :=
  Real.measurable_exp.comp ((continuous_Rm38 hm hβ).measurable.comp hg).neg

theorem integrable_dens {g : (ℤ → ℂ) → Hm1 m} (hg : Measurable g) :
    Integrable (fun z => Real.exp (-Rm38 m β (g z))) (gammaM38 m β) :=
  Integrable.of_bound (measurable_dens hm hβ hg).aestronglyMeasurable 1
    (Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact (dens_pos_le hm hβ (g z)).2)

theorem normalizer_pos_le {g : (ℤ → ℂ) → Hm1 m} (hg : Measurable g) :
    0 < ∫ z, Real.exp (-Rm38 m β (g z)) ∂gammaM38 m β ∧
      ∫ z, Real.exp (-Rm38 m β (g z)) ∂gammaM38 m β ≤ 1 := by
  refine ⟨integral_exp_pos (f := fun z => -Rm38 m β (g z)) (integrable_dens hm hβ hg), ?_⟩
  calc ∫ z, Real.exp (-Rm38 m β (g z)) ∂gammaM38 m β
      ≤ ∫ _z, (1 : ℝ) ∂gammaM38 m β :=
        integral_mono (integrable_dens hm hβ hg) (integrable_const _)
          (fun z => (dens_pos_le hm hβ (g z)).2)
    _ = 1 := by simp

theorem isProbability_law {g : (ℤ → ℂ) → Hm1 m} (hg : Measurable g) :
    IsProbabilityMeasure
      (((ENNReal.ofReal (∫ z, Real.exp (-Rm38 m β (g z)) ∂gammaM38 m β))⁻¹ •
        (gammaM38 m β).withDensity
          (fun z => ENNReal.ofReal (Real.exp (-Rm38 m β (g z))))).map g) := by
  have hZ := (normalizer_pos_le hm hβ hg).1
  have hint : ∫⁻ z, ENNReal.ofReal (Real.exp (-Rm38 m β (g z))) ∂gammaM38 m β =
      ENNReal.ofReal (∫ z, Real.exp (-Rm38 m β (g z)) ∂gammaM38 m β) :=
    (ofReal_integral_eq_lintegral_ofReal (integrable_dens hm hβ hg)
      (Eventually.of_forall fun z => (Real.exp_pos _).le)).symm
  have h1 : IsProbabilityMeasure
      ((ENNReal.ofReal (∫ z, Real.exp (-Rm38 m β (g z)) ∂gammaM38 m β))⁻¹ •
        (gammaM38 m β).withDensity
          (fun z => ENNReal.ofReal (Real.exp (-Rm38 m β (g z))))) := by
    constructor
    rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hint,
      smul_eq_mul]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hZ).ne' ENNReal.ofReal_ne_top
  infer_instance

theorem integral_law {g : (ℤ → ℂ) → Hm1 m} (hg : Measurable g) (F : Hm1 m → ℝ)
    (hF : Continuous F) :
    ∫ u, F u ∂(((ENNReal.ofReal (∫ z, Real.exp (-Rm38 m β (g z)) ∂gammaM38 m β))⁻¹ •
        (gammaM38 m β).withDensity
          (fun z => ENNReal.ofReal (Real.exp (-Rm38 m β (g z))))).map g) =
      (∫ z, Real.exp (-Rm38 m β (g z)) ∂gammaM38 m β)⁻¹ *
        ∫ z, Real.exp (-Rm38 m β (g z)) * F (g z) ∂gammaM38 m β := by
  have hZ := (normalizer_pos_le hm hβ hg).1
  rw [integral_map hg.aemeasurable hF.measurable.aestronglyMeasurable, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul (measurable_dens hm hβ hg).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have e : (fun z => (ENNReal.ofReal (Real.exp (-Rm38 m β (g z)))).toReal • F (g z)) =
      fun z => Real.exp (-Rm38 m β (g z)) * F (g z) :=
    funext fun z => by rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  rw [e, ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le, smul_eq_mul]

theorem ae_tendsto (I : Hm1 m → Hm1 m) (hI : Continuous I) :
    ∀ᵐ z ∂gammaM38 m β, Tendsto (fun N => I (PN38 m N z)) atTop
      (𝓝 (I (gaussianRealization38 m z))) := by
  filter_upwards [F08_ae_PN_tendsto38 hm hβ] with z hz
  exact (hI.tendsto _).comp hz

theorem normalizer_tendsto (I : Hm1 m → Hm1 m) (hI : Continuous I) :
    Tendsto (fun N => ∫ z, Real.exp (-Rm38 m β (I (PN38 m N z))) ∂gammaM38 m β) atTop
      (𝓝 (∫ z, Real.exp (-Rm38 m β (I (gaussianRealization38 m z))) ∂gammaM38 m β)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun N => (measurable_dens hm hβ (hI.measurable.comp (measurable_PN38 m N))).aestronglyMeasurable)
    (integrable_const 1) (fun N => Eventually.of_forall fun z => ?_) ?_
  · rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact (dens_pos_le hm hβ _).2
  · filter_upwards [ae_tendsto hm hβ I hI] with z hz
    exact ((Real.continuous_exp.comp (continuous_Rm38 hm hβ).neg).tendsto _).comp hz

theorem test_tendsto (I : Hm1 m → Hm1 m) (hI : Continuous I) (F : BoundedContinuousFunction (Hm1 m) ℝ) :
    Tendsto (fun N => ∫ z, Real.exp (-Rm38 m β (I (PN38 m N z))) * F (I (PN38 m N z))
      ∂gammaM38 m β) atTop
      (𝓝 (∫ z, Real.exp (-Rm38 m β (I (gaussianRealization38 m z))) *
        F (I (gaussianRealization38 m z)) ∂gammaM38 m β)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
    (fun N => ((measurable_dens hm hβ (hI.measurable.comp (measurable_PN38 m N))).mul
      (F.continuous.measurable.comp (hI.measurable.comp (measurable_PN38 m N)))).aestronglyMeasurable)
    (integrable_const _) (fun N => Eventually.of_forall fun z => ?_) ?_
  · rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc Real.exp (-Rm38 m β (I (PN38 m N z))) * ‖F (I (PN38 m N z))‖ ≤ 1 * ‖F‖ :=
          mul_le_mul (dens_pos_le hm hβ _).2 (F.norm_coe_le_norm _) (norm_nonneg _) zero_le_one
      _ = ‖F‖ := one_mul _
  · filter_upwards [ae_tendsto hm hβ I hI] with z hz
    exact (((Real.continuous_exp.comp (continuous_Rm38 hm hβ).neg).tendsto _).comp hz).mul
      ((F.continuous.tendsto _).comp hz)

/-- Assembled generic core, in the order of the F-010 head (the clauses needing the G6 map are separate). -/
theorem core (I : Hm1 m → Hm1 m) (hI : Continuous I) :
    (∀ z : ℤ → ℂ, 0 < Real.exp (-Rm38 m β (I (gaussianRealization38 m z))) ∧
      Real.exp (-Rm38 m β (I (gaussianRealization38 m z))) ≤ 1) ∧
    Integrable (fun z => Real.exp (-Rm38 m β (I (gaussianRealization38 m z)))) (gammaM38 m β) ∧
    0 < ∫ z, Real.exp (-Rm38 m β (I (gaussianRealization38 m z))) ∂gammaM38 m β ∧
    ∫ z, Real.exp (-Rm38 m β (I (gaussianRealization38 m z))) ∂gammaM38 m β ≤ 1 ∧
    IsProbabilityMeasure
      (((ENNReal.ofReal (∫ z, Real.exp (-Rm38 m β (I (gaussianRealization38 m z))) ∂gammaM38 m β))⁻¹ •
        (gammaM38 m β).withDensity
          (fun z => ENNReal.ofReal (Real.exp (-Rm38 m β (I (gaussianRealization38 m z)))))).map
            (fun z => I (gaussianRealization38 m z))) ∧
    (∀ N : ℕ,
      0 < ∫ z, Real.exp (-Rm38 m β (I (PN38 m N z))) ∂gammaM38 m β ∧
      ∫ z, Real.exp (-Rm38 m β (I (PN38 m N z))) ∂gammaM38 m β ≤ 1 ∧
      IsProbabilityMeasure
        (((ENNReal.ofReal (∫ z, Real.exp (-Rm38 m β (I (PN38 m N z))) ∂gammaM38 m β))⁻¹ •
          (gammaM38 m β).withDensity
            (fun z => ENNReal.ofReal (Real.exp (-Rm38 m β (I (PN38 m N z)))))).map
              (fun z => I (PN38 m N z)))) ∧
    (∀ᵐ z ∂gammaM38 m β, Tendsto (fun N => I (PN38 m N z)) atTop
      (𝓝 (I (gaussianRealization38 m z)))) ∧
    Tendsto (fun N => ∫ z, Real.exp (-Rm38 m β (I (PN38 m N z))) ∂gammaM38 m β) atTop
      (𝓝 (∫ z, Real.exp (-Rm38 m β (I (gaussianRealization38 m z))) ∂gammaM38 m β)) ∧
    ∀ F : BoundedContinuousFunction (Hm1 m) ℝ,
      Tendsto (fun N => ∫ u, F u ∂(((ENNReal.ofReal
          (∫ z, Real.exp (-Rm38 m β (I (PN38 m N z))) ∂gammaM38 m β))⁻¹ •
          (gammaM38 m β).withDensity
            (fun z => ENNReal.ofReal (Real.exp (-Rm38 m β (I (PN38 m N z)))))).map
              (fun z => I (PN38 m N z)))) atTop
        (𝓝 (∫ u, F u ∂(((ENNReal.ofReal
          (∫ z, Real.exp (-Rm38 m β (I (gaussianRealization38 m z))) ∂gammaM38 m β))⁻¹ •
          (gammaM38 m β).withDensity
            (fun z => ENNReal.ofReal (Real.exp (-Rm38 m β (I (gaussianRealization38 m z)))))).map
              (fun z => I (gaussianRealization38 m z))))) := by
  have hgI : Measurable (fun z => I (gaussianRealization38 m z)) :=
    hI.measurable.comp measurable_gaussianRealization38
  have hgN : ∀ N : ℕ, Measurable (fun z => I (PN38 m N z)) :=
    fun N => hI.measurable.comp (measurable_PN38 m N)
  obtain ⟨hZ, hZ1⟩ := normalizer_pos_le hm hβ hgI
  refine ⟨fun z => dens_pos_le hm hβ _, integrable_dens hm hβ hgI, hZ, hZ1,
    isProbability_law hm hβ hgI, fun N => ⟨(normalizer_pos_le hm hβ (hgN N)).1,
      (normalizer_pos_le hm hβ (hgN N)).2, isProbability_law hm hβ (hgN N)⟩,
    ae_tendsto hm hβ I hI, normalizer_tendsto hm hβ I hI, fun F => ?_⟩
  have e : (fun N => ∫ u, F u ∂(((ENNReal.ofReal
          (∫ z, Real.exp (-Rm38 m β (I (PN38 m N z))) ∂gammaM38 m β))⁻¹ •
          (gammaM38 m β).withDensity
            (fun z => ENNReal.ofReal (Real.exp (-Rm38 m β (I (PN38 m N z)))))).map
              (fun z => I (PN38 m N z)))) = fun N =>
      (∫ z, Real.exp (-Rm38 m β (I (PN38 m N z))) ∂gammaM38 m β)⁻¹ *
        ∫ z, Real.exp (-Rm38 m β (I (PN38 m N z))) * F (I (PN38 m N z)) ∂gammaM38 m β :=
    funext fun N => integral_law hm hβ (hgN N) F F.continuous
  rw [e, integral_law hm hβ hgI F F.continuous]
  exact ((normalizer_tendsto hm hβ I hI).inv₀ hZ.ne').mul (test_tendsto hm hβ I hI F)

end NlsGge.ThirdConsultation.F010Aux
