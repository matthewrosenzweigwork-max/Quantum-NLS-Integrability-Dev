import Mathlib
import NlsGge.Atomic.M.M016ChartFinalHead
import NlsGge.Atomic.M.M016HalfNodeHead
import NlsGge.Atomic.M.M016DiscIdentity
import NlsGge.Atomic.M.M016FirstCoeff
import NlsGge.Atomic.M.M016MassAssembly
import NlsGge.Atomic.M.M053
import NlsGge.ThirdConsultation.KSPS.KSPS031SharpLaurent
import NlsGge.ThirdConsultation.M.M016Host

                                                                                                    
                                                                                        
                                                                                                                  
                                                                                                                    
                                                   
                                                                                        
                                                                                                     
                                                                                                                      
                                                  
                                                                                                                  
                                                                                                                    

set_option autoImplicit false
open Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M

theorem finitegap_primitive_laurent
    (N : ℕ) (φ : KSPS.SobolevC N)
    (hW : KSPS.toPotPair φ ∈ gkW)
    (hfg : finiteGapPair (KSPS.toPotPair φ)) :
    ∃ R : ℝ, ∃ F : ℂ → ℂ,
      ExteriorPrimitiveRepresentative (KSPS.toPotPair φ) R F ∧
      MPrimitive.ExteriorHolomorphic F ∧
      PrimitiveLaurentCoefficients N φ F := by
  obtain ⟨R, F, hrep, hhol, hinf, hzero⟩ :=
    finitegap_pair_primitive_meromorphic_infinity (KSPS.toPotPair φ) hW hfg
  refine ⟨R, F, hrep, hhol, ?_⟩
  have hcosh : ∀ z : ℂ, R < ‖z‖ →
      2 * Complex.cosh (F z) = NlsGge.GK38.discrim (KSPS.toPotPair φ) z := by
    intro z hz
    obtain ⟨hz', e⟩ := hrep.2 z hz
    rw [e]
    exact primitive_discriminant_identity _ hz'.1 z hz'.2
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    intro K hK1 hK
    obtain rfl : K = 1 := le_antisymm hK hK1
    obtain ⟨C, R', hC, hR', hb⟩ := M016ChartAux.first_coeff_generic F
      (NlsGge.GK38.discrim (KSPS.toPotPair φ)) R _ hinf hcosh
      (discriminant_imaginary_bilinear_mass (KSPS.toPotPair φ))
    refine ⟨C, R', hC, hR', fun z hz => ?_⟩
    have hH : hierarchyCharge φ ⟨1, le_rfl, Nat.succ_le_succ (Nat.zero_le 0)⟩ =
        ∫ x in (0 : ℝ)..1, coverRep38 (KSPS.toPotPair φ).1 x * coverRep38 (KSPS.toPotPair φ).2 x := by
      have h1 := WKB_hierarchy_coefficients_complex_one 0 φ le_rfl (Nat.succ_le_succ (Nat.zero_le 0))
      rw [integralRiccatiCoefficient_one] at h1
      exact (neg_inj.1 h1).symm
    rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty, sub_zero, hH]
    exact hb z hz
  · intro K hK1 hK
    obtain ⟨C, R', hC, hR', hb⟩ := KSPS031SL.sharp_littleO_along_halfNodes N hN φ F hinf
      (exterior_primitive_halfNode_eq N φ R F hrep hzero) K hK
    refine ⟨C, R', hC, hR', fun z hz => ?_⟩
    have h1 : KSPS.integralRiccatiLeft φ 1 =
        -hierarchyCharge φ ⟨1, le_rfl, Nat.succ_le_succ (Nat.zero_le N)⟩ := by
      have h := WKB_hierarchy_coefficients_complex N φ 1 le_rfl (Nat.succ_le_succ (Nat.zero_le N))
      rw [if_pos rfl] at h
      exact h
    have hk : ∀ (k : ℕ) (hk : 1 ≤ k ∧ k ≤ N + 1), 2 ≤ k →
        KSPS.integralRiccatiLeft φ k = hierarchyCharge φ ⟨k, hk.1, hk.2⟩ := by
      intro k hk hk2
      have h := WKB_hierarchy_coefficients_complex N φ k hk.1 hk.2
      rw [if_neg (by omega)] at h
      exact h
    have e := M016ChartAux.laurent_regroup N K hK1 hK (KSPS.integralRiccatiLeft φ)
      (fun k hk => hierarchyCharge φ ⟨k, hk.1, hk.2⟩) (2 * Complex.I * z) (F z + Complex.I * z) h1 hk
    have hbz := hb z hz
    rw [e] at hbz
    exact hbz

end NlsGge.ThirdConsultation.M
