import Mathlib
import NlsGge.Measure.FiniteGaussian
import NlsGge.Ramer.ActualHeadLawBridge

                                                                                                                  
                                         
                                                                                                                         
                                                                                                                                 
                                                           
                                                                                                                        
                                                                             
                                                                                                               
                                                                                                                      

set_option autoImplicit false
open MeasureTheory ProbabilityTheory NlsGge.Measure NlsGge.Ramer NlsGge.Pilot

namespace NlsGge.Atomic.R010

theorem map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (f : α → ENNReal) :
    (μ.withDensity f).map e = (μ.map e).withDensity (f ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, Measure.restrict_map e.measurable hs, lintegral_map_equiv]
  simp [Function.comp]

theorem R010_main : ((
  (∀ a : ℝ, 0 < a →
    variance (fun z : ℂ => z.re) (complexGaussian a) = 1 / (2 * a) ∧
    variance (fun z : ℂ => z.im) (complexGaussian a) = 1 / (2 * a) ∧
    IndepFun (fun z : ℂ => z.re) (fun z : ℂ => z.im) (complexGaussian a) ∧
    complexGaussian a = volume.withDensity (fun z : ℂ => ENNReal.ofReal (a / Real.pi * Real.exp (-a * ‖z‖ ^ 2)))) ∧
  (∀ (ι : Type) [Fintype ι] (a : ι → ℝ), finiteComplexGaussian a = Measure.pi (fun i => complexGaussian (a i))) ∧
  (∀ (lower upper : ℝ) (c : BoundedCoefficients lower upper) (N : ℕ) (v : actualCMHead c N),
    ‖v‖ ^ 2 = ∑ i, 2 * sourceRate c (modeIndex N i) * ‖actualCMHeadCoord c N v i‖ ^ 2)
  : Prop)) := by
  refine ⟨fun a ha => ⟨?_, ?_, ?_, ?_⟩, fun ι _ a => rfl, fun lower upper c N v => actualCMHead_norm_sq c N v⟩
  · -- clause 1: variance of the real part
    unfold complexGaussian
    rw [variance_map (by fun_prop) (by fun_prop)]
    have h1 : ((fun z : ℂ => z.re) ∘ ⇑Complex.measurableEquivRealProd.symm) = (fun x : ℝ => x) ∘ Prod.fst := by
      funext p; simp
    rw [h1, ← variance_map (X := fun x : ℝ => x) (Y := (Prod.fst : ℝ × ℝ → ℝ))
      measurable_id.aemeasurable measurable_fst.aemeasurable, Measure.map_fst_prod]
    simp [variance_fun_id_gaussianReal, componentVariance_coe a ha]
  · -- clause 2: variance of the imaginary part
    unfold complexGaussian
    rw [variance_map (by fun_prop) (by fun_prop)]
    have h2 : ((fun z : ℂ => z.im) ∘ ⇑Complex.measurableEquivRealProd.symm) = (fun x : ℝ => x) ∘ Prod.snd := by
      funext p; simp
    rw [h2, ← variance_map (X := fun x : ℝ => x) (Y := (Prod.snd : ℝ × ℝ → ℝ))
      measurable_id.aemeasurable measurable_snd.aemeasurable, Measure.map_snd_prod]
    simp [variance_fun_id_gaussianReal, componentVariance_coe a ha]
  · -- clause 3: independence of the real and imaginary parts
    have e1 : ((fun ω : ℂ => (ω.re, ω.im)) ∘ ⇑Complex.measurableEquivRealProd.symm) = id := by
      funext p; simp
    have e2 : ((fun z : ℂ => z.re) ∘ ⇑Complex.measurableEquivRealProd.symm) = Prod.fst := by
      funext p; simp
    have e3 : ((fun z : ℂ => z.im) ∘ ⇑Complex.measurableEquivRealProd.symm) = Prod.snd := by
      funext p; simp
    rw [indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)]
    unfold complexGaussian
    rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    rw [e1, Measure.map_id, e2, e3]
    simp
  · -- clause 4: density of complexGaussian a
    have hv : componentVariance a ≠ 0 := by
      intro h
      have h1 := componentVariance_coe a ha
      rw [h] at h1
      have : (0:ℝ) < 1 / (2 * a) := by positivity
      simp at h1
      linarith
    have hvR : ((componentVariance a : NNReal) : ℝ) = 1 / (2 * a) := componentVariance_coe a ha
    unfold complexGaussian
    rw [gaussianReal_of_var_ne_zero 0 hv]
    rw [prod_withDensity (by fun_prop) (by fun_prop)]
    rw [map_withDensity_equiv Complex.measurableEquivRealProd.symm]
    have hmap : Measure.map (⇑Complex.measurableEquivRealProd.symm)
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) = (volume : Measure ℂ) :=
      Complex.volume_preserving_equiv_real_prod.symm.map_eq
    rw [hmap]
    congr 1
    funext z
    simp only [Function.comp, gaussianPDF, gaussianPDFReal]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hx : (0 : ℝ) < 2 * Real.pi * (componentVariance a : ℝ) := by
      rw [hvR]; positivity
    have hsq : Real.sqrt (2 * Real.pi * (componentVariance a : ℝ)) *
        Real.sqrt (2 * Real.pi * (componentVariance a : ℝ)) = 2 * Real.pi * (componentVariance a : ℝ) :=
      Real.mul_self_sqrt hx.le
    have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have e1 : (Complex.measurableEquivRealProd.symm.symm z).1 = z.re := rfl
    have e2 : (Complex.measurableEquivRealProd.symm.symm z).2 = z.im := rfl
    rw [e1, e2, hn]
    have key : (Real.sqrt (2 * Real.pi * (componentVariance a : ℝ)))⁻¹ *
        (Real.sqrt (2 * Real.pi * (componentVariance a : ℝ)))⁻¹ = a / Real.pi := by
      rw [← mul_inv, hsq, hvR]
      field_simp
    calc (Real.sqrt (2 * Real.pi * (componentVariance a : ℝ)))⁻¹ *
          Real.exp (-(z.re - 0) ^ 2 / (2 * (componentVariance a : ℝ))) *
        ((Real.sqrt (2 * Real.pi * (componentVariance a : ℝ)))⁻¹ *
          Real.exp (-(z.im - 0) ^ 2 / (2 * (componentVariance a : ℝ))))
        = ((Real.sqrt (2 * Real.pi * (componentVariance a : ℝ)))⁻¹ *
          (Real.sqrt (2 * Real.pi * (componentVariance a : ℝ)))⁻¹) *
          (Real.exp (-(z.re - 0) ^ 2 / (2 * (componentVariance a : ℝ))) *
          Real.exp (-(z.im - 0) ^ 2 / (2 * (componentVariance a : ℝ)))) := by ring
      _ = a / Real.pi * Real.exp (-a * (z.re ^ 2 + z.im ^ 2)) := by
          rw [key, ← Real.exp_add]
          congr 2
          rw [hvR]
          field_simp
          ring

end NlsGge.Atomic.R010
