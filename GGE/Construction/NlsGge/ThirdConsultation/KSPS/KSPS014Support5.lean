import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS014Support1
import NlsGge.ThirdConsultation.KSPS.KSPS014Support4

                                                                                                                    
                                                                                                                 
                                                                                                
                                                                                                  
                                                                                                                  
set_option autoImplicit false
open MeasureTheory Matrix
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS014W
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.KSPS

theorem remainder_eq {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : {z : ℂ // z ≠ 0})
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (i : Fin 2) :
    (((2 * Complex.I * lam.1) ^ N)⁻¹ • KSPSWKB.sourceRemainderVector φ b lam x) i =
      -(fundExt (toPotPair φ) lam.1 x i 0 *
          (∫ t in (0 : ℝ)..x, (NlsGge.ThirdConsultation.KSPSVolterra.adjugate2
            (fundExt (toPotPair φ) lam.1 t) *ᵥ forcingTerm φ b lam t) 0) +
        fundExt (toPotPair φ) lam.1 x i 1 *
          (∫ t in (0 : ℝ)..x, (NlsGge.ThirdConsultation.KSPSVolterra.adjugate2
            (fundExt (toPotPair φ) lam.1 t) *ᵥ forcingTerm φ b lam t) 1)) := by
  have hint : ∀ j : Fin 2, IntervalIntegrable (fun t => (NlsGge.ThirdConsultation.KSPSVolterra.adjugate2
      (fundExt (toPotPair φ) lam.1 t) *ᵥ forcingTerm φ b lam t) j) volume 0 x :=
    fun j => ii_sub (adj_ii (toPotPair φ) lam.1 _ (forcingTerm_ii φ b lam) j) hx
  have hcongr : ∫ t in (0 : ℝ)..x,
      ((KSPSWKB.sourceFundamental φ x lam.1 *
        NlsGge.ThirdConsultation.KSPSVolterra.adjugate2 (KSPSWKB.sourceFundamental φ t lam.1)) *ᵥ
        (NlsGge.ThirdConsultation.KSPSVolterra.R *ᵥ KSPSWKB.sourceForcingVector φ b lam t)) i =
      ∫ t in (0 : ℝ)..x, ((fundExt (toPotPair φ) lam.1 x *
        NlsGge.ThirdConsultation.KSPSVolterra.adjugate2 (fundExt (toPotPair φ) lam.1 t)) *ᵥ
        (NlsGge.ThirdConsultation.KSPSVolterra.R *ᵥ KSPSWKB.sourceForcingVector φ b lam t)) i := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le hx.1] at ht
    have ht1 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, le_trans ht.2 hx.2⟩
    try dsimp only
    rw [sourceFundamental_eq_fundPair N φ lam.1 x hx, sourceFundamental_eq_fundPair N φ lam.1 t ht1,
      ← fundExt_of_mem (toPotPair φ) lam.1 hx, ← fundExt_of_mem (toPotPair φ) lam.1 ht1]
  have hsplit : ∀ t : ℝ, ((2 * Complex.I * lam.1) ^ N)⁻¹ * ((fundExt (toPotPair φ) lam.1 x *
        NlsGge.ThirdConsultation.KSPSVolterra.adjugate2 (fundExt (toPotPair φ) lam.1 t)) *ᵥ
        (NlsGge.ThirdConsultation.KSPSVolterra.R *ᵥ KSPSWKB.sourceForcingVector φ b lam t)) i =
      fundExt (toPotPair φ) lam.1 x i 0 * (NlsGge.ThirdConsultation.KSPSVolterra.adjugate2
          (fundExt (toPotPair φ) lam.1 t) *ᵥ forcingTerm φ b lam t) 0 +
        fundExt (toPotPair φ) lam.1 x i 1 * (NlsGge.ThirdConsultation.KSPSVolterra.adjugate2
          (fundExt (toPotPair φ) lam.1 t) *ᵥ forcingTerm φ b lam t) 1 := by
    intro t
    rw [← Matrix.mulVec_mulVec]
    simp only [forcingTerm, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  simp only [KSPSWKB.sourceRemainderVector, NlsGge.ThirdConsultation.KSPSVolterra.integrateVector,
    Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  rw [hcongr, mul_neg, ← intervalIntegral.integral_const_mul]
  simp only [hsplit]
  rw [intervalIntegral.integral_add ((hint 0).const_mul _) ((hint 1).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem column_eq {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : {z : ℂ // z ≠ 0})
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (i : Fin 2) :
    KSPSWKB.wkbColumn φ b lam x i =
      fundExt (toPotPair φ) lam.1 x i 0 * KSPSWKB.wkbColumn φ b lam 0 0 +
        fundExt (toPotPair φ) lam.1 x i 1 * KSPSWKB.wkbColumn φ b lam 0 1 := by
  have hV := voc (toPotPair φ) lam.1 (explicitColumn φ b lam) (forcingTerm φ b lam) (explicitColumn_ac φ b lam)
    (forcingTerm_ii φ b lam) (explicitColumn_deriv φ b lam) x hx
  have F0 := hV 0
  have F1 := hV 1
  rw [(adjugate2_mulVec _ _).1] at F0
  rw [(adjugate2_mulVec _ _).2] at F1
  have hD := fundExt_det (toPotPair φ) lam.1 x
  rw [Matrix.det_fin_two] at hD
  have h0 : KSPSWKB.wkbColumn φ b lam 0 = explicitColumn φ b lam 0 := by
    rw [wkbColumn_eq, KSPSWKB.sourceRemainderVector_at_zero, smul_zero, add_zero]
  rw [h0, wkbColumn_eq, Pi.add_apply, remainder_eq φ b lam x hx i]
  fin_cases i
  · try simp only [Fin.zero_eta, Fin.isValue]
    linear_combination (fundExt (toPotPair φ) lam.1 x 0 0) * F0 + (fundExt (toPotPair φ) lam.1 x 0 1) * F1 -
      explicitColumn φ b lam x 0 * hD
  · try simp only [Fin.mk_one, Fin.isValue]
    linear_combination (fundExt (toPotPair φ) lam.1 x 1 0) * F0 + (fundExt (toPotPair φ) lam.1 x 1 1) * F1 -
      explicitColumn φ b lam x 1 * hD

end
end NlsGge.ThirdConsultation.KSPS014W

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section
open NlsGge.Pilot NlsGge.GK38

theorem wkbColumns_eq_fundPair_mul
    (N : ℕ) (φ : SobolevC N) (lam : {z : ℂ // z ≠ 0})
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    KSPSWKB.wkbColumns φ lam x =
      fundPair (toPotPair φ) lam.1 ⟨x, hx⟩ *
        KSPSWKB.initialColumns φ lam.1 := by
  rw [← KSPSWKB.wkbColumns_zero N φ lam, ← KSPS014W.fundExt_of_mem (toPotPair φ) lam.1 hx]
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases j
  · simp only [KSPSWKB.wkbColumns, Fin.zero_eta, Fin.isValue, ↓reduceIte]
    exact KSPS014W.column_eq φ false lam x hx i
  · simp only [KSPSWKB.wkbColumns, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
    exact KSPS014W.column_eq φ true lam x hx i

end
end NlsGge.ThirdConsultation.KSPS
