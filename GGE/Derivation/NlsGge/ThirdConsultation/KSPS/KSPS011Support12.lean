import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS007Host
import NlsGge.ThirdConsultation.KSPS.KSPS011Support9

/- KSPS-011 SUPPORT12 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS011Support12.lean. Component algebra (M4a/M4b): when the forcing vector is
   (0, e^{-i lam t} F) a.e. on [0,1], component 1 of forcingLeading + forcingFirstCorrection at x = 1 is
   I * osc lam F + (2 lam)^-1 (q(1) osc lam F - osc lam (q F)), q t = integratedQuadratic phi' t 0 0; the B1 and B3
   terms vanish (term 1 has zero diagonal). Upper analogue: forcing (e^{i lam t} F, 0), component 0,
   -I * osc (-lam) F + (2 lam)^-1 (q(1) osc (-lam) F - osc (-lam) (q F)). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Matrix
open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation.KSPSVolterra

namespace NlsGge.ThirdConsultation.KSPSWKB

theorem mulVec_comp0 (A : Mat) (v : Vec) : (A *ᵥ v) 0 = A 0 0 * v 0 + A 0 1 * v 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem mulVec_comp1 (A : Mat) (v : Vec) : (A *ᵥ v) 1 = A 1 0 * v 0 + A 1 1 * v 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem term_one_diag011 (x : ℝ) (lam : ℂ) (p : PotPair) (i : Fin 2) : term 1 x lam p i i = 0 := by
  show integrateMatrix 0 x (fun t => E lam (x - t) * R * phi p t * term 0 t lam p) i i = 0
  unfold integrateMatrix
  have : ∀ t : ℝ, (E lam (x - t) * R * phi p t * term 0 t lam p) i i = 0 := by
    intro t
    fin_cases i <;> simp [E, R, phi, term, Matrix.mul_apply, Fin.sum_univ_two]
  simp [this]

theorem ae_uIoc_of_restrict {P : ℝ → Prop}
    (h : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), P t) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) 1 → P t := by
  have := (ae_restrict_iff' measurableSet_Icc).1 h
  filter_upwards [this] with t ht htI
  rw [Set.uIoc_of_le zero_le_one] at htI
  exact ht ⟨htI.1.le, htI.2⟩

theorem integratedQuadratic_apply00 (φ : SobolevC 1) (x : ℝ) :
    integratedQuadratic φ x 0 0 = ∫ t in (0 : ℝ)..x, potRepFst38 (toPair φ) t * potRepSnd38 (toPair φ) t := by
  simp [integratedQuadratic]

theorem integratedQuadratic_apply11 (φ : SobolevC 1) (x : ℝ) :
    integratedQuadratic φ x 1 1 = integratedQuadratic φ x 0 0 := by
  simp [integratedQuadratic]

theorem integratedQuadratic_apply01 (φ : SobolevC 1) (x : ℝ) :
    integratedQuadratic φ x 0 1 = 0 := by
  simp [integratedQuadratic]

theorem integratedQuadratic_apply10 (φ : SobolevC 1) (x : ℝ) :
    integratedQuadratic φ x 1 0 = 0 := by
  simp [integratedQuadratic]

theorem lower_component (φ : SobolevC 1) (lam : ℂ) (f : PotPair) (F : ℝ → ℂ)
    (hf : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ![potRepFst38 f t, potRepSnd38 f t] = ![0, Complex.exp (-(Complex.I * lam * (t : ℂ))) * F t]) :
    (forcingLeading φ lam f 1 + forcingFirstCorrection φ lam f 1) 1 =
      Complex.I * endpointOsc lam F + (2 * lam)⁻¹ *
        (integratedQuadratic φ 1 0 0 * endpointOsc lam F -
          endpointOsc lam (fun t => integratedQuadratic φ t 0 0 * F t)) := by
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
  -- key rewriting of the weighted integrals
  have key : ∀ h : ℝ → ℂ, ∫ t in (0 : ℝ)..1, Complex.exp (Complex.I * lam * ((1 - t : ℝ) : ℂ)) *
      (h t * potRepSnd38 f t) = endpointOsc lam (fun t => h t * F t) := by
    intro h
    unfold endpointOsc
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hsnd] with t ht htI
    rw [ht htI]
    have e : Complex.exp (Complex.I * lam * ((1 - 2 * t : ℝ) : ℂ)) =
        Complex.exp (Complex.I * lam * ((1 - t : ℝ) : ℂ)) * Complex.exp (-(Complex.I * lam * (t : ℂ))) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [e]; ring
  have zero_int : ∀ g : ℝ → ℂ, ∫ t in (0 : ℝ)..1, g t * potRepFst38 f t = 0 := by
    intro g
    have : ∫ t in (0 : ℝ)..1, g t * potRepFst38 f t = ∫ t in (0 : ℝ)..1, (0 : ℂ) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hfst] with t ht htI
      rw [ht htI, mul_zero]
    simpa using this
  -- the pieces at x = 1, component 1
  have hLead : forcingLeading φ lam f 1 1 = Complex.I * endpointOsc lam F := by
    have h1 := key (fun _ => 1)
    simp only [one_mul] at h1
    unfold forcingLeading integrateVector
    simp only [Pi.neg_apply]
    have : ∀ t : ℝ, (R *ᵥ (E lam (1 - t) *ᵥ forcingValue f t)) 1 =
        -Complex.I * (Complex.exp (Complex.I * lam * ((1 - t : ℝ) : ℂ)) * potRepSnd38 f t) := by
      intro t
      rw [mulVec_comp1, mulVec_comp1]
      simp [R, E, forcingValue]
    simp_rw [this]
    rw [intervalIntegral.integral_const_mul, h1]
    ring
  have hB1 : forcingB1 φ lam f 1 1 = 0 := by
    unfold forcingB1
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    rw [mulVec_comp1, term_one_diag011, zero_mul, add_zero, mulVec_comp0]
    have hw0 : integrateVector 0 1 (fun t => E lam (-t) *ᵥ forcingValue f t) 0 = 0 := by
      unfold integrateVector
      have := zero_int (fun t => Complex.exp (-(Complex.I * lam * ((-t : ℝ) : ℂ))))
      rw [← this]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      beta_reduce
      rw [mulVec_comp0]
      simp [E, forcingValue]
    rw [hw0]
    simp [R]
  have hB3 : forcingB3 φ lam f 1 1 = 0 := by
    unfold forcingB3
    rw [mulVec_comp1]
    have hz : integrateVector 0 1 (fun t => (2 * lam) • (term 1 t lam (toPair φ) *ᵥ (R *ᵥ forcingValue f t))) 1 = 0 := by
      unfold integrateVector
      have : ∫ t in (0 : ℝ)..1, (0 : ℂ) = 0 := by simp
      rw [← this]
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hfst] with t ht htI
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [mulVec_comp1, term_one_diag011, zero_mul, add_zero, mulVec_comp0]
      simp [R, forcingValue, ht htI]
    rw [hz, mul_zero]
    simp [E]
  have hB2 : forcingB2 φ lam f 1 1 = integratedQuadratic φ 1 0 0 * endpointOsc lam F := by
    unfold forcingB2
    rw [mulVec_comp1, integratedQuadratic_apply10, zero_mul, zero_add, integratedQuadratic_apply11]
    have h1 := key (fun _ => 1)
    simp only [one_mul] at h1
    congr 1
    unfold integrateVector
    rw [← h1]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    beta_reduce
    rw [mulVec_comp1]
    simp [E, forcingValue]
  have hB4 : forcingB4 φ lam f 1 1 = -endpointOsc lam (fun t => integratedQuadratic φ t 0 0 * F t) := by
    unfold forcingB4 integrateVector
    simp only [Pi.neg_apply]
    rw [← key (fun t => integratedQuadratic φ t 0 0), ← intervalIntegral.integral_neg,
      ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    beta_reduce
    rw [mulVec_comp1, mulVec_comp1, integratedQuadratic_apply10, integratedQuadratic_apply11]
    simp [E, forcingValue]
  unfold forcingFirstCorrection
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hLead, hB1, hB2, hB3, hB4]
  ring

theorem upper_component (φ : SobolevC 1) (lam : ℂ) (f : PotPair) (F : ℝ → ℂ)
    (hf : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ![potRepFst38 f t, potRepSnd38 f t] = ![Complex.exp (Complex.I * lam * (t : ℂ)) * F t, 0]) :
    (forcingLeading φ lam f 1 + forcingFirstCorrection φ lam f 1) 0 =
      -Complex.I * endpointOsc (-lam) F + (2 * lam)⁻¹ *
        (integratedQuadratic φ 1 0 0 * endpointOsc (-lam) F -
          endpointOsc (-lam) (fun t => integratedQuadratic φ t 0 0 * F t)) := by
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
  have key : ∀ h : ℝ → ℂ, ∫ t in (0 : ℝ)..1, Complex.exp (-(Complex.I * lam * ((1 - t : ℝ) : ℂ))) *
      (h t * potRepFst38 f t) = endpointOsc (-lam) (fun t => h t * F t) := by
    intro h
    unfold endpointOsc
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hfst] with t ht htI
    rw [ht htI]
    have e : Complex.exp (Complex.I * (-lam) * ((1 - 2 * t : ℝ) : ℂ)) =
        Complex.exp (-(Complex.I * lam * ((1 - t : ℝ) : ℂ))) * Complex.exp (Complex.I * lam * (t : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [e]; ring
  have zero_int : ∀ g : ℝ → ℂ, ∫ t in (0 : ℝ)..1, g t * potRepSnd38 f t = 0 := by
    intro g
    have : ∫ t in (0 : ℝ)..1, g t * potRepSnd38 f t = ∫ t in (0 : ℝ)..1, (0 : ℂ) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hsnd] with t ht htI
      rw [ht htI, mul_zero]
    simpa using this
  have hLead : forcingLeading φ lam f 1 0 = -Complex.I * endpointOsc (-lam) F := by
    have h1 := key (fun _ => 1)
    simp only [one_mul] at h1
    unfold forcingLeading integrateVector
    simp only [Pi.neg_apply]
    have : ∀ t : ℝ, (R *ᵥ (E lam (1 - t) *ᵥ forcingValue f t)) 0 =
        Complex.I * (Complex.exp (-(Complex.I * lam * ((1 - t : ℝ) : ℂ))) * potRepFst38 f t) := by
      intro t
      rw [mulVec_comp0, mulVec_comp0]
      simp [R, E, forcingValue]
    simp_rw [this]
    rw [intervalIntegral.integral_const_mul, h1]
    ring
  have hB1 : forcingB1 φ lam f 1 0 = 0 := by
    unfold forcingB1
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    rw [mulVec_comp0, term_one_diag011, zero_mul, zero_add, mulVec_comp1]
    have hw1 : integrateVector 0 1 (fun t => E lam (-t) *ᵥ forcingValue f t) 1 = 0 := by
      unfold integrateVector
      have := zero_int (fun t => Complex.exp (Complex.I * lam * ((-t : ℝ) : ℂ)))
      rw [← this]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      beta_reduce
      rw [mulVec_comp1]
      simp [E, forcingValue]
    rw [hw1]
    simp [R]
  have hB3 : forcingB3 φ lam f 1 0 = 0 := by
    unfold forcingB3
    rw [mulVec_comp0]
    have hz : integrateVector 0 1 (fun t => (2 * lam) • (term 1 t lam (toPair φ) *ᵥ (R *ᵥ forcingValue f t))) 0 = 0 := by
      unfold integrateVector
      have : ∫ t in (0 : ℝ)..1, (0 : ℂ) = 0 := by simp
      rw [← this]
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hsnd] with t ht htI
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [mulVec_comp0, term_one_diag011, zero_mul, zero_add, mulVec_comp1]
      simp [R, forcingValue, ht htI]
    rw [hz, mul_zero]
    simp [E]
  have hB2 : forcingB2 φ lam f 1 0 = integratedQuadratic φ 1 0 0 * endpointOsc (-lam) F := by
    unfold forcingB2
    rw [mulVec_comp0, integratedQuadratic_apply01, zero_mul, add_zero]
    have h1 := key (fun _ => 1)
    simp only [one_mul] at h1
    congr 1
    unfold integrateVector
    rw [← h1]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    beta_reduce
    rw [mulVec_comp0]
    simp [E, forcingValue]
  have hB4 : forcingB4 φ lam f 1 0 = -endpointOsc (-lam) (fun t => integratedQuadratic φ t 0 0 * F t) := by
    unfold forcingB4 integrateVector
    simp only [Pi.neg_apply]
    rw [← key (fun t => integratedQuadratic φ t 0 0), ← intervalIntegral.integral_neg,
      ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    beta_reduce
    rw [mulVec_comp0, mulVec_comp0, integratedQuadratic_apply01]
    simp [E, forcingValue]
  unfold forcingFirstCorrection
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hLead, hB1, hB2, hB3, hB4]
  ring

end NlsGge.ThirdConsultation.KSPSWKB
