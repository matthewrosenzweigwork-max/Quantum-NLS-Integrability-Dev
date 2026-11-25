import Mathlib
import NlsGge.ThirdConsultation.KSPSInversePhaseHost
import NlsGge.ThirdConsultation.KSPS.KSPS023Host
import NlsGge.Atomic.LIB.LIB019

                                                                                 
                                                                                           
                                                                                                                 
                                                                                                                      
                                                                                                                  
                                                                                                                          
                                                                                                                     
                                    
                                                                               
                                                                                    
                                                                                                          
                                                                                                                  
                          
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.Common

namespace NlsGge.ThirdConsultation.KSPS025U2
noncomputable section
open NlsGge.ThirdConsultation.KSPS

theorem iteratedDeriv_eq_of_sub_eq_pow_mul {f h g : ℂ → ℂ} {k : ℕ} (hf : AnalyticAt ℂ f 0)
    (hh : AnalyticAt ℂ h 0) (hg : AnalyticAt ℂ g 0)
    (hfg : ∀ᶠ z : ℂ in 𝓝 0, f z - h z = z ^ (k + 1) * g z) :
    iteratedDeriv k f 0 = iteratedDeriv k h 0 := by
  have han : AnalyticAt ℂ (fun z => f z - h z) 0 := hf.sub hh
  have hle : ((k + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (fun z => f z - h z) 0 :=
    (natCast_le_analyticOrderAt han).2 ⟨g, hg, by
      filter_upwards [hfg] with z hz
      simpa using hz⟩
  have h0 := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero han).1 hle k
    (Nat.lt_succ_self k)
  rw [iteratedDeriv_fun_sub hf.contDiffAt hh.contDiffAt] at h0
  exact sub_eq_zero.1 h0

theorem inversePhaseIterate_one_eq {N : ℕ} (φ : SobolevC N) :
    NlsGge.ThirdConsultation.KSPSRiccati.inversePhaseIterate φ 1 =
      fun z => -((2 * (Real.pi : ℂ))⁻¹ * integralRiccatiLeft φ 1) * z := by
  have hπ : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  funext z
  show -NlsGge.ThirdConsultation.KSPSRiccati.phasePolynomial φ 1 (z / ((Real.pi : ℂ) + z * 0)) = _
  simp only [NlsGge.ThirdConsultation.KSPSRiccati.phasePolynomial, Finset.Icc_self,
    Finset.sum_singleton, pow_one, mul_zero, add_zero]
  field_simp

theorem spectralCoefficient_one_eq {N : ℕ} (φ : SobolevC N) :
    NlsGge.ThirdConsultation.KSPSRiccati.spectralCoefficient φ 1 = massCoefficient φ := by
  unfold NlsGge.ThirdConsultation.KSPSRiccati.spectralCoefficient massCoefficient
  rw [inversePhaseIterate_one_eq]
  simp [iteratedDeriv_one]

theorem spectralCoefficient_two_eq_integral {N : ℕ} (φ : SobolevC N) :
    NlsGge.ThirdConsultation.KSPSRiccati.spectralCoefficient φ 2 =
      Complex.I * (4 * (Real.pi : ℂ) ^ 2)⁻¹ * integralRiccatiLeft φ 2 := by
  have hπ : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : (2 * Complex.I) ^ 2 = -4 := by rw [mul_pow, Complex.I_sq]; norm_num
  obtain ⟨α, hα⟩ : ∃ α : ℂ, α = (2 * (Real.pi : ℂ))⁻¹ * integralRiccatiLeft φ 1 := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A2 : ℂ, A2 = integralRiccatiLeft φ 2 := ⟨_, rfl⟩
  obtain ⟨a1, ha1⟩ : ∃ a1 : ℂ, a1 = -(Complex.I * (((2 * Complex.I) ^ 1)⁻¹ *
      integralRiccatiLeft φ 1)) := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ a2 : ℂ, a2 = Complex.I * (4 : ℂ)⁻¹ * A2 := ⟨_, rfl⟩
  have hpoly : ∀ z : ℂ, NlsGge.ThirdConsultation.KSPSRiccati.inversePhaseIterate φ 2 z =
      a1 * (z / ((Real.pi : ℂ) - α * z ^ 2)) + a2 * (z / ((Real.pi : ℂ) - α * z ^ 2)) ^ 2 := by
    intro z
    have e : NlsGge.ThirdConsultation.KSPSRiccati.inversePhaseIterate φ 2 z =
        -NlsGge.ThirdConsultation.KSPSRiccati.phasePolynomial φ 2
        (z / ((Real.pi : ℂ) + z * NlsGge.ThirdConsultation.KSPSRiccati.inversePhaseIterate φ 1 z)) := rfl
    rw [e, inversePhaseIterate_one_eq, ← hα]
    unfold NlsGge.ThirdConsultation.KSPSRiccati.phasePolynomial
    rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.sum_pair (by norm_num), hI, ← hA2, ha1, ha2]
    have e3 : (Real.pi : ℂ) + z * (-α * z) = (Real.pi : ℂ) - α * z ^ 2 := by ring
    rw [e3]
    ring
  have hDa : AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ) - α * z ^ 2) 0 := by fun_prop
  have hD0 : (fun z : ℂ => (Real.pi : ℂ) - α * z ^ 2) 0 ≠ 0 := by simpa using hπ
  have hIa : AnalyticAt ℂ (NlsGge.ThirdConsultation.KSPSRiccati.inversePhaseIterate φ 2) 0 := by
    have : NlsGge.ThirdConsultation.KSPSRiccati.inversePhaseIterate φ 2 = fun z : ℂ =>
        a1 * (z / ((Real.pi : ℂ) - α * z ^ 2)) + a2 * (z / ((Real.pi : ℂ) - α * z ^ 2)) ^ 2 :=
      funext hpoly
    rw [this]
    have hq : AnalyticAt ℂ (fun z : ℂ => z / ((Real.pi : ℂ) - α * z ^ 2)) 0 :=
      analyticAt_id.div hDa hD0
    exact (analyticAt_const.mul hq).add (analyticAt_const.mul (hq.pow 2))
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, ∀ z, g z =
      α / ((Real.pi : ℂ) * ((Real.pi : ℂ) - α * z ^ 2)) := ⟨_, fun _ => rfl⟩
  have hD : ∀ᶠ z : ℂ in 𝓝 0, (Real.pi : ℂ) - α * z ^ 2 ≠ 0 := by
    have hca : ContinuousAt (fun z : ℂ => (Real.pi : ℂ) - α * z ^ 2) 0 := by fun_prop
    exact hca.eventually_ne (by simpa using hπ)
  have hga : AnalyticAt ℂ g 0 := by
    have : g = fun z : ℂ => α / ((Real.pi : ℂ) * ((Real.pi : ℂ) - α * z ^ 2)) := funext hg
    rw [this]
    exact analyticAt_const.div (analyticAt_const.mul hDa) (mul_ne_zero hπ hD0)
  have hHa : AnalyticAt ℂ (fun z : ℂ => a1 * g z + a2 * (2 * z * g z / (Real.pi : ℂ) +
      z ^ 3 * g z ^ 2)) 0 := by fun_prop
  have hpolya : AnalyticAt ℂ (fun z : ℂ => a1 / (Real.pi : ℂ) * z +
      a2 / (Real.pi : ℂ) ^ 2 * z ^ 2) 0 := by fun_prop
  have hdiv : ∀ᶠ z : ℂ in 𝓝 0, NlsGge.ThirdConsultation.KSPSRiccati.inversePhaseIterate φ 2 z -
      (a1 / (Real.pi : ℂ) * z + a2 / (Real.pi : ℂ) ^ 2 * z ^ 2) =
      z ^ (2 + 1) * (a1 * g z + a2 * (2 * z * g z / (Real.pi : ℂ) + z ^ 3 * g z ^ 2)) := by
    filter_upwards [hD] with z hz
    have hu : z / ((Real.pi : ℂ) - α * z ^ 2) = z / (Real.pi : ℂ) + z ^ 3 * g z := by
      rw [hg z]
      generalize hDe : (Real.pi : ℂ) - α * z ^ 2 = D at hz ⊢
      have hrel : α * z ^ 2 = Real.pi - D := by rw [← hDe]; ring
      symm
      rw [show z / (Real.pi : ℂ) + z ^ 3 * (α / ((Real.pi : ℂ) * D)) =
        (z * D + z * (α * z ^ 2)) / ((Real.pi : ℂ) * D) by field_simp, hrel]
      field_simp
      try ring
    rw [hpoly, hu]
    ring
  have h2 := iteratedDeriv_eq_of_sub_eq_pow_mul (k := 2) hIa hpolya hHa hdiv
  have hd : deriv (fun z : ℂ => a1 / (Real.pi : ℂ) * z + a2 / (Real.pi : ℂ) ^ 2 * z ^ 2) =
      fun z => a1 / (Real.pi : ℂ) + 2 * (a2 / (Real.pi : ℂ) ^ 2) * z := by
    funext z
    have h1 : HasDerivAt (fun x : ℂ => a1 / (Real.pi : ℂ) * x + a2 / (Real.pi : ℂ) ^ 2 * x ^ 2)
        (a1 / (Real.pi : ℂ) * 1 + a2 / (Real.pi : ℂ) ^ 2 * (((2 : ℕ) : ℂ) * z ^ (2 - 1))) z :=
      ((hasDerivAt_id' z).const_mul (a1 / (Real.pi : ℂ))).add
        ((hasDerivAt_pow 2 z).const_mul (a2 / (Real.pi : ℂ) ^ 2))
    rw [h1.deriv]
    norm_num
    ring
  have h3 : iteratedDeriv 2 (fun z : ℂ => a1 / (Real.pi : ℂ) * z +
      a2 / (Real.pi : ℂ) ^ 2 * z ^ 2) 0 = 2 * (a2 / (Real.pi : ℂ) ^ 2) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hd]
    simp
  unfold NlsGge.ThirdConsultation.KSPSRiccati.spectralCoefficient
  rw [h2, h3, ha2, hA2]
  simp [Nat.factorial]
  field_simp

theorem weakDerivative_neg_eq (u : PhysicalL2) :
    weakDerivative (-u) = -weakDerivative u := by
  have hd : (fun n : ℤ => (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
        reflectedFourierL2 (-u) n) =
      fun n : ℤ => -((-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * reflectedFourierL2 u n) := by
    funext n; simp
  unfold weakDerivative
  dsimp only
  by_cases h : Memℓp (fun n : ℤ => (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
      reflectedFourierL2 u n) 2
  · have h1 : Memℓp (fun n : ℤ => (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
        reflectedFourierL2 (-u) n) 2 := by
      rw [hd]; exact h.neg
    rw [dif_pos h, dif_pos h1, ← map_neg]
    congr 1
    exact Subtype.ext (funext fun n => congrFun hd n)
  · have h1 : ¬ Memℓp (fun n : ℤ => (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
        reflectedFourierL2 (-u) n) 2 := fun hh => by
      rw [hd] at hh
      exact h ((Memℓp.neg_iff (f := fun n : ℤ => (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
        reflectedFourierL2 u n)).1 hh)
    rw [dif_neg h, dif_neg h1]
    simp

theorem physicalProduct_zero_right (u : PhysicalL2) : physicalProduct u 0 = 0 := by
  unfold physicalProduct
  split_ifs with h
  · apply Lp.eq_zero_iff_ae_eq_zero.2
    filter_upwards [h.coeFn_toLp, Lp.coeFn_zero ℂ 2 spatialMeasure] with x hx hz
    rw [hx, hz]
    simp
  · rfl

theorem riccatiLeft_two_eq {N : ℕ} (φ : SobolevC N) :
    riccatiLeft φ 2 = -weakDerivative (toPotPair φ).2 := by
  unfold riccatiLeft NlsGge.ThirdConsultation.KSPSRiccati.left
    NlsGge.ThirdConsultation.KSPSRiccati.coefficient wkbR
  simp [wkbList, weakDerivative_neg_eq, physicalProduct_zero_right]

theorem integralRiccatiLeft_two_eq {N : ℕ} (φ : SobolevC N) :
    integralRiccatiLeft φ 2 = -NlsGge.ThirdConsultation.KSPSRiccati.momentumIntegral φ := by
  unfold integralRiccatiLeft NlsGge.ThirdConsultation.KSPSRiccati.momentumIntegral
  rw [riccatiLeft_two_eq, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr_ae ?_
  have h1 := coverRep38_ae_phys (toPotPair φ).1
  have h2 := coverRep38_ae_phys (-weakDerivative (toPotPair φ).2)
  have h3 : ∀ᵐ t : ℝ, coverRep38 (-weakDerivative (toPotPair φ).2) t =
      -coverRep38 (weakDerivative (toPotPair φ).2) t := by
    simpa only [neg_one_smul, neg_one_mul] using
      coverRep38_smul_ae (-1) (weakDerivative (toPotPair φ).2)
  filter_upwards [h1, h2, h3] with x e1 e2 e3 _
  rw [← e1, ← e2, e3]
  ring

theorem spectralCoefficient_two_eq {N : ℕ} (φ : SobolevC N) :
    NlsGge.ThirdConsultation.KSPSRiccati.spectralCoefficient φ 2 = -momentumCoefficient φ := by
  rw [spectralCoefficient_two_eq_integral, integralRiccatiLeft_two_eq]
  unfold momentumCoefficient
  ring

theorem spectralPolynomial_one_eq (φ : SobolevC 1) (n : ℤ) :
    spectralPolynomial φ n =
      (n : ℂ) * Real.pi + massCoefficient φ / (n : ℂ) - momentumCoefficient φ / (n : ℂ) ^ 2 := by
  unfold spectralPolynomial
  rw [show Finset.Icc 1 (1 + 1) = {1, 2} by decide, Finset.sum_pair (by norm_num),
    spectralCoefficient_one_eq, spectralCoefficient_two_eq, pow_one]
  ring

end
end NlsGge.ThirdConsultation.KSPS025U2
