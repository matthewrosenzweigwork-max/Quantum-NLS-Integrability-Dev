import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS012Support3

                                                                                                                    
                                                                          
                                                                                                                       
                                                                                                                      
                                                                                      
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Matrix
open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation.KSPSVolterra

namespace NlsGge.ThirdConsultation.KSPSWKB

theorem E_00 (lam : ℂ) (x : ℝ) : E lam x 0 0 = Complex.exp (-(Complex.I * lam * (x : ℂ))) := by simp [E]
theorem E_01 (lam : ℂ) (x : ℝ) : E lam x 0 1 = 0 := by simp [E]
theorem E_10 (lam : ℂ) (x : ℝ) : E lam x 1 0 = 0 := by simp [E]
theorem E_11 (lam : ℂ) (x : ℝ) : E lam x 1 1 = Complex.exp (Complex.I * lam * (x : ℂ)) := by simp [E]
theorem R_00 : (R : Mat) 0 0 = Complex.I := by simp [R]
theorem R_01 : (R : Mat) 0 1 = 0 := by simp [R]
theorem R_10 : (R : Mat) 1 0 = 0 := by simp [R]
theorem R_11 : (R : Mat) 1 1 = -Complex.I := by simp [R]
theorem fv_0 (f : PotPair) (t : ℝ) : forcingValue f t 0 = potRepFst38 f t := by simp [forcingValue]
theorem fv_1 (f : PotPair) (t : ℝ) : forcingValue f t 1 = potRepSnd38 f t := by simp [forcingValue]

theorem lower_diag_component (φ : SobolevC 1) (lam : ℂ) (hlam : lam ≠ 0) (f : PotPair)
    (F : ℝ → ℂ) (hF : IntervalIntegrable F volume 0 1)
    (hf : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ![potRepFst38 f t, potRepSnd38 f t] = ![0, Complex.exp (-(Complex.I * lam * (t : ℂ))) * F t]) :
    (forcingLeading φ lam f 1 + forcingFirstCorrection φ lam f 1) 0 =
      -Complex.exp (-(2 * Complex.I * lam)) *
        endpointOsc lam (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * lam * (s : ℂ)) * potRepFst38 (toPair φ) s) * F t) := by
  have hu : IntervalIntegrable (potRepFst38 (toPair φ)) volume 0 1 :=
    intervalIntegrable_coverRep38_one _
  have hae := ae_uIoc_of_restrict hf
  have hfst : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) 1 → potRepFst38 f t = 0 := by
    filter_upwards [hae] with t ht htI
    have := congrFun (ht htI) 0
    simpa using this
  have hsnd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) 1 →
      potRepSnd38 f t = Complex.exp (-(Complex.I * lam * (t : ℂ))) * F t := by
    filter_upwards [hae] with t ht htI
    have := congrFun (ht htI) 1
    simpa using this
  have hLead : forcingLeading φ lam f 1 0 = 0 := by
    unfold forcingLeading
    simp only [Pi.neg_apply]
    show -∫ t in (0 : ℝ)..1, (R *ᵥ (E lam (1 - t) *ᵥ forcingValue f t)) 0 = 0
    have : ∫ t in (0 : ℝ)..1, (R *ᵥ (E lam (1 - t) *ᵥ forcingValue f t)) 0 =
        ∫ t in (0 : ℝ)..1, (0 : ℂ) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hfst] with t ht htI
      rw [mulVec_comp0, mulVec_comp0, mulVec_comp1, R_00, R_01, E_00, E_01, E_10, E_11, fv_0, fv_1,
        ht htI]
      ring
    rw [this]; simp
  have hB2 : forcingB2 φ lam f 1 0 = 0 := by
    unfold forcingB2
    rw [mulVec_comp0, integratedQuadratic_apply01, zero_mul, add_zero]
    have : integrateVector 0 1 (fun t => E lam (1 - t) *ᵥ forcingValue f t) 0 = 0 := by
      show ∫ t in (0 : ℝ)..1, (E lam (1 - t) *ᵥ forcingValue f t) 0 = 0
      have : ∫ t in (0 : ℝ)..1, (E lam (1 - t) *ᵥ forcingValue f t) 0 = ∫ t in (0 : ℝ)..1, (0 : ℂ) := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards [hfst] with t ht htI
        rw [mulVec_comp0, E_00, E_01, fv_0, fv_1, ht htI]
        ring
      rw [this]; simp
    rw [this, mul_zero]
  have hB4 : forcingB4 φ lam f 1 0 = 0 := by
    unfold forcingB4
    simp only [Pi.neg_apply]
    show -∫ t in (0 : ℝ)..1, (E lam (1 - t) *ᵥ (integratedQuadratic φ t *ᵥ forcingValue f t)) 0 = 0
    have : ∫ t in (0 : ℝ)..1, (E lam (1 - t) *ᵥ (integratedQuadratic φ t *ᵥ forcingValue f t)) 0 =
        ∫ t in (0 : ℝ)..1, (0 : ℂ) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hfst] with t ht htI
      rw [mulVec_comp0, E_00, E_01, mulVec_comp0, mulVec_comp1, integratedQuadratic_apply01, fv_0,
        fv_1, ht htI]
      ring
    rw [this]; simp
  have hw0 : integrateVector 0 1 (fun t => E lam (-t) *ᵥ forcingValue f t) 0 = 0 := by
    show ∫ t in (0 : ℝ)..1, (E lam (-t) *ᵥ forcingValue f t) 0 = 0
    have : ∫ t in (0 : ℝ)..1, (E lam (-t) *ᵥ forcingValue f t) 0 = ∫ t in (0 : ℝ)..1, (0 : ℂ) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hfst] with t ht htI
      rw [mulVec_comp0, E_00, E_01, fv_0, fv_1, ht htI]
      ring
    rw [this]; simp
  have hw1 : integrateVector 0 1 (fun t => E lam (-t) *ᵥ forcingValue f t) 1 =
      ∫ t in (0 : ℝ)..1, Complex.exp (-(2 * Complex.I * lam * (t : ℂ))) * F t := by
    show ∫ t in (0 : ℝ)..1, (E lam (-t) *ᵥ forcingValue f t) 1 = _
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hsnd] with t ht htI
    have e : Complex.exp (Complex.I * lam * ((-t : ℝ) : ℂ)) *
        Complex.exp (-(Complex.I * lam * (t : ℂ))) = Complex.exp (-(2 * Complex.I * lam * (t : ℂ))) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [mulVec_comp1, E_10, E_11, fv_0, fv_1, ht htI, ← e]
    ring
  have hB1 : forcingB1 φ lam f 1 0 = -(2 * lam) *
      ((Complex.I * Complex.exp (-(Complex.I * lam * ((1 : ℝ) : ℂ))) *
          ∫ t in (0 : ℝ)..1, Complex.exp (2 * Complex.I * lam * (t : ℂ)) * potRepFst38 (toPair φ) t) *
        (-Complex.I * ∫ t in (0 : ℝ)..1, Complex.exp (-(2 * Complex.I * lam * (t : ℂ))) * F t)) := by
    unfold forcingB1
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mulVec_comp0, term_one_diag011, zero_mul, zero_add, mulVec_comp1, hw0, hw1, R_10, R_11,
      term1_01]
    ring
  have hV0 : integrateVector 0 1 (fun t => (2 * lam) • (term 1 t lam (toPair φ) *ᵥ
      (R *ᵥ forcingValue f t))) 0 = (2 * lam) *
        ∫ t in (0 : ℝ)..1, (Complex.I * Complex.exp (-(Complex.I * lam * (t : ℂ))) *
            ∫ s in (0 : ℝ)..t, Complex.exp (2 * Complex.I * lam * (s : ℂ)) * potRepFst38 (toPair φ) s) *
          (-Complex.I * (Complex.exp (-(Complex.I * lam * (t : ℂ))) * F t)) := by
    show ∫ t in (0 : ℝ)..1, ((2 * lam) • (term 1 t lam (toPair φ) *ᵥ (R *ᵥ forcingValue f t))) 0 = _
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hfst, hsnd] with t h1 h2 htI
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mulVec_comp0, term_one_diag011, zero_mul, zero_add, mulVec_comp1, R_10, R_11, fv_0, fv_1,
      term1_01, h1 htI, h2 htI]
    ring
  have hB3 : forcingB3 φ lam f 1 0 = Complex.exp (-(Complex.I * lam * ((1 : ℝ) : ℂ))) * (2 * lam) *
        ∫ t in (0 : ℝ)..1, (Complex.I * Complex.exp (-(Complex.I * lam * (t : ℂ))) *
            ∫ s in (0 : ℝ)..t, Complex.exp (2 * Complex.I * lam * (s : ℂ)) * potRepFst38 (toPair φ) s) *
          (-Complex.I * (Complex.exp (-(Complex.I * lam * (t : ℂ))) * F t)) := by
    unfold forcingB3
    rw [mulVec_comp0, E_00, E_01, zero_mul, add_zero, hV0]
    ring
  have hS := scalar_diag_identity hlam hu hF
  rw [← hS, Pi.add_apply, hLead]
  unfold forcingFirstCorrection
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hB1, hB2, hB3, hB4]
  ring

theorem upper_diag_component (φ : SobolevC 1) (lam : ℂ) (hlam : lam ≠ 0) (f : PotPair)
    (F : ℝ → ℂ) (hF : IntervalIntegrable F volume 0 1)
    (hf : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ![potRepFst38 f t, potRepSnd38 f t] = ![Complex.exp (Complex.I * lam * (t : ℂ)) * F t, 0]) :
    (forcingLeading φ lam f 1 + forcingFirstCorrection φ lam f 1) 1 =
      -Complex.exp (-(2 * Complex.I * (-lam))) *
        endpointOsc (-lam) (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * (-lam) * (s : ℂ)) * potRepSnd38 (toPair φ) s) *
            F t) := by
  have hu : IntervalIntegrable (potRepSnd38 (toPair φ)) volume 0 1 :=
    intervalIntegrable_coverRep38_one _
  have hae := ae_uIoc_of_restrict hf
  have hsnd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) 1 → potRepSnd38 f t = 0 := by
    filter_upwards [hae] with t ht htI
    have := congrFun (ht htI) 1
    simpa using this
  have hfst : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) 1 →
      potRepFst38 f t = Complex.exp (Complex.I * lam * (t : ℂ)) * F t := by
    filter_upwards [hae] with t ht htI
    have := congrFun (ht htI) 0
    simpa using this
  have hLead : forcingLeading φ lam f 1 1 = 0 := by
    unfold forcingLeading
    simp only [Pi.neg_apply]
    show -∫ t in (0 : ℝ)..1, (R *ᵥ (E lam (1 - t) *ᵥ forcingValue f t)) 1 = 0
    have : ∫ t in (0 : ℝ)..1, (R *ᵥ (E lam (1 - t) *ᵥ forcingValue f t)) 1 =
        ∫ t in (0 : ℝ)..1, (0 : ℂ) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hsnd] with t ht htI
      rw [mulVec_comp1, mulVec_comp0, mulVec_comp1, R_10, R_11, E_10, E_11, fv_0, fv_1, ht htI]
      ring
    rw [this]; simp
  have hB2 : forcingB2 φ lam f 1 1 = 0 := by
    unfold forcingB2
    rw [mulVec_comp1, integratedQuadratic_apply10, zero_mul, zero_add]
    have : integrateVector 0 1 (fun t => E lam (1 - t) *ᵥ forcingValue f t) 1 = 0 := by
      show ∫ t in (0 : ℝ)..1, (E lam (1 - t) *ᵥ forcingValue f t) 1 = 0
      have : ∫ t in (0 : ℝ)..1, (E lam (1 - t) *ᵥ forcingValue f t) 1 = ∫ t in (0 : ℝ)..1, (0 : ℂ) := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards [hsnd] with t ht htI
        rw [mulVec_comp1, E_10, E_11, fv_0, fv_1, ht htI]
        ring
      rw [this]; simp
    rw [this, mul_zero]
  have hB4 : forcingB4 φ lam f 1 1 = 0 := by
    unfold forcingB4
    simp only [Pi.neg_apply]
    show -∫ t in (0 : ℝ)..1, (E lam (1 - t) *ᵥ (integratedQuadratic φ t *ᵥ forcingValue f t)) 1 = 0
    have : ∫ t in (0 : ℝ)..1, (E lam (1 - t) *ᵥ (integratedQuadratic φ t *ᵥ forcingValue f t)) 1 =
        ∫ t in (0 : ℝ)..1, (0 : ℂ) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hsnd] with t ht htI
      rw [mulVec_comp1, E_10, E_11, mulVec_comp1, integratedQuadratic_apply10, fv_1, ht htI]
      ring
    rw [this]; simp
  have hw1 : integrateVector 0 1 (fun t => E lam (-t) *ᵥ forcingValue f t) 1 = 0 := by
    show ∫ t in (0 : ℝ)..1, (E lam (-t) *ᵥ forcingValue f t) 1 = 0
    have : ∫ t in (0 : ℝ)..1, (E lam (-t) *ᵥ forcingValue f t) 1 = ∫ t in (0 : ℝ)..1, (0 : ℂ) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hsnd] with t ht htI
      rw [mulVec_comp1, E_10, E_11, fv_0, fv_1, ht htI]
      ring
    rw [this]; simp
  have hw0 : integrateVector 0 1 (fun t => E lam (-t) *ᵥ forcingValue f t) 0 =
      ∫ t in (0 : ℝ)..1, Complex.exp (-(2 * Complex.I * (-lam) * (t : ℂ))) * F t := by
    show ∫ t in (0 : ℝ)..1, (E lam (-t) *ᵥ forcingValue f t) 0 = _
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hfst] with t ht htI
    have e : Complex.exp (-(Complex.I * lam * ((-t : ℝ) : ℂ))) *
        Complex.exp (Complex.I * lam * (t : ℂ)) = Complex.exp (-(2 * Complex.I * (-lam) * (t : ℂ))) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [mulVec_comp0, E_00, E_01, fv_0, fv_1, ht htI, ← e]
    ring
  have e1 : Complex.exp (Complex.I * lam * ((1 : ℝ) : ℂ)) =
      Complex.exp (-(Complex.I * (-lam) * ((1 : ℝ) : ℂ))) := by congr 1 <;> ring
  have e2 : ∀ t : ℝ, ∫ s in (0 : ℝ)..t, Complex.exp (-(2 * Complex.I * lam * (s : ℂ))) *
        potRepSnd38 (toPair φ) s =
      ∫ s in (0 : ℝ)..t, Complex.exp (2 * Complex.I * (-lam) * (s : ℂ)) * potRepSnd38 (toPair φ) s := by
    intro t
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    beta_reduce
    congr 2; ring
  have e3 : ∀ t : ℝ, Complex.exp (Complex.I * lam * (t : ℂ)) =
      Complex.exp (-(Complex.I * (-lam) * (t : ℂ))) := fun t => by congr 1 <;> ring
  have hB1 : forcingB1 φ lam f 1 1 = (2 * (-lam)) *
      ((Complex.I * Complex.exp (-(Complex.I * (-lam) * ((1 : ℝ) : ℂ))) *
          ∫ t in (0 : ℝ)..1, Complex.exp (2 * Complex.I * (-lam) * (t : ℂ)) * potRepSnd38 (toPair φ) t) *
        (-Complex.I * ∫ t in (0 : ℝ)..1, Complex.exp (-(2 * Complex.I * (-lam) * (t : ℂ))) * F t)) := by
    unfold forcingB1
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mulVec_comp1, term_one_diag011, zero_mul, add_zero, mulVec_comp0, hw0, hw1, R_00, R_01,
      term1_10]
    rw [e1, e2 1]
    ring
  have hV1 : integrateVector 0 1 (fun t => (2 * lam) • (term 1 t lam (toPair φ) *ᵥ
      (R *ᵥ forcingValue f t))) 1 = (2 * lam) *
        ∫ t in (0 : ℝ)..1, (Complex.I * Complex.exp (-(Complex.I * (-lam) * (t : ℂ))) *
            ∫ s in (0 : ℝ)..t, Complex.exp (2 * Complex.I * (-lam) * (s : ℂ)) * potRepSnd38 (toPair φ) s) *
          (-Complex.I * (Complex.exp (-(Complex.I * (-lam) * (t : ℂ))) * F t)) := by
    show ∫ t in (0 : ℝ)..1, ((2 * lam) • (term 1 t lam (toPair φ) *ᵥ (R *ᵥ forcingValue f t))) 1 = _
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hsnd, hfst] with t h1 h2 htI
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mulVec_comp1, term_one_diag011, zero_mul, add_zero, mulVec_comp0, R_00, R_01, fv_0, fv_1,
      term1_10, h1 htI, h2 htI, e3 t, e2 t]
    ring
  have hB3 : forcingB3 φ lam f 1 1 = Complex.exp (-(Complex.I * (-lam) * ((1 : ℝ) : ℂ))) * (2 * lam) *
        ∫ t in (0 : ℝ)..1, (Complex.I * Complex.exp (-(Complex.I * (-lam) * (t : ℂ))) *
            ∫ s in (0 : ℝ)..t, Complex.exp (2 * Complex.I * (-lam) * (s : ℂ)) * potRepSnd38 (toPair φ) s) *
          (-Complex.I * (Complex.exp (-(Complex.I * (-lam) * (t : ℂ))) * F t)) := by
    unfold forcingB3
    rw [mulVec_comp1, E_10, E_11, zero_mul, zero_add, hV1, e1]
    ring
  have hS := scalar_diag_identity (neg_ne_zero.mpr hlam) hu hF
  rw [← hS, Pi.add_apply, hLead]
  unfold forcingFirstCorrection
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hB1, hB2, hB3, hB4]
  have h2 : (2 * lam) ≠ 0 := mul_ne_zero two_ne_zero hlam
  field_simp
  ring

end NlsGge.ThirdConsultation.KSPSWKB
