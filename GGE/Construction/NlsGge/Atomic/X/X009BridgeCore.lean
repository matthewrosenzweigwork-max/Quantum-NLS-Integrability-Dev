import Mathlib
import NlsGge.Birkhoff.F05Identity38j

                                                                                                                       
                                                                                             
                                                                                                              
                                                        
                                                                                        
                                                                                                            
                                                                                                    
                                                                                                    
                                                                        
                                                                                                                       
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core NlsGge.AblowitzLadik

namespace NlsGge.Atomic.X009.X009Aux

theorem gr_eq_mk (z : ℤ → ℂ)
    (hz : Summable (fun n : ℤ => sobolevModeWeight ((2 - 1 : ℕ) : ℝ) n * ‖z n‖ ^ 2)) :
    toCarrier38 _ (gaussianRealization38 2 z) =
      carrierMk38 ((2 - 1 : ℕ) : ℝ) z ((mem_seqSobolev38_iff _ _).2 hz) := by
  show (gaussianRealization38 2 z : Hm1 2) =
    (carrierMk38 ((2 - 1 : ℕ) : ℝ) z ((mem_seqSobolev38_iff _ _).2 hz) : Hm1 2)
  apply Subtype.ext
  funext n
  exact seqRealization_apply38 _ z hz n

theorem phiInv_eq_of_summable (B : BirkhoffInput38)
    (Ψ : SobolevCarrier38 ((2 - 1 : ℕ) : ℝ) → SobolevCarrier38 ((2 - 1 : ℕ) : ℝ))
    (hT : B.TinvC (2 - 1) = Ψ) (z : ℤ → ℂ)
    (hz : Summable (fun n : ℤ => sobolevModeWeight ((2 - 1 : ℕ) : ℝ) n * ‖z n‖ ^ 2)) :
    B.PhiInvX38 2 z =
      ofCarrier38 _ (reflC38 _ (Ψ (toCarrier38 _ (gaussianRealization38 2 z)))) := by
  have hzm : z ∈ seqSobolev38 ((2 - 1 : ℕ) : ℝ) := (mem_seqSobolev38_iff _ _).2 hz
  show ofCarrier38 _ (reflC38 _ (B.cleanTinvC (2 - 1) z)) = _
  rw [B.cleanTinvC_of_mem (2 - 1) z hzm, hT, gr_eq_mk z hz]

theorem ae_summable_alQ4 {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 < β₁) (h2 : 0 < β₂) :
    ∀ᵐ z ∂gammaM38 2 (alQ4Beta38 β₀ β₁ β₂),
      Summable (fun n : ℤ => sobolevModeWeight ((2 - 1 : ℕ) : ℝ) n * ‖z n‖ ^ 2) := by
  have hβ : ∀ i ≤ 2, 0 ≤ alQ4Beta38 β₀ β₁ β₂ i := by
    intro i _
    unfold alQ4Beta38
    split_ifs <;> linarith
  have hb0 : 0 < alQ4Beta38 β₀ β₁ β₂ 0 := by simpa [alQ4Beta38] using h0
  have hb2 : 0 < alQ4Beta38 β₀ β₁ β₂ 2 := by simpa [alQ4Beta38] using h2
  exact ae_summable38 (m := 2) le_rfl hβ hb0 hb2

theorem ae_phiInv_eq_of (B : BirkhoffInput38)
    (Ψ : SobolevCarrier38 ((2 - 1 : ℕ) : ℝ) → SobolevCarrier38 ((2 - 1 : ℕ) : ℝ))
    (hT : B.TinvC (2 - 1) = Ψ) (G : (ℤ → ℂ) → Hm1 2)
    (hG : ∀ z, G z = ofCarrier38 _ (reflC38 _ (Ψ (toCarrier38 _ (gaussianRealization38 2 z)))))
    {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 < β₁) (h2 : 0 < β₂) :
    B.PhiInvX38 2 =ᵐ[gammaM38 2 (alQ4Beta38 β₀ β₁ β₂)] G := by
  filter_upwards [ae_summable_alQ4 h0 h1 h2] with z hz
  rw [phiInv_eq_of_summable B Ψ hT z hz, hG z]

theorem normalizer_eq_of (B : BirkhoffInput38) (G : (ℤ → ℂ) → Hm1 2) (β : ℕ → ℝ)
    (hae : B.PhiInvX38 2 =ᵐ[gammaM38 2 β] G) :
    (∫ z, Real.exp (-Rm38 2 β (G z)) ∂gammaM38 2 β) = ZM38 B 2 β := by
  unfold ZM38
  exact integral_congr_ae (hae.mono fun z hz => by simp only [hz])

theorem law_eq_of (B : BirkhoffInput38) (G : (ℤ → ℂ) → Hm1 2) (β : ℕ → ℝ)
    (hae : B.PhiInvX38 2 =ᵐ[gammaM38 2 β] G) (hZ : 0 < ZM38 B 2 β) :
    ((ENNReal.ofReal (∫ z, Real.exp (-Rm38 2 β (G z)) ∂gammaM38 2 β))⁻¹ •
      (gammaM38 2 β).withDensity
        (fun z => ENNReal.ofReal (Real.exp (-Rm38 2 β (G z))))).map G = muM38 B 2 β := by
  rw [normalizer_eq_of B G β hae]
  have hden : (ENNReal.ofReal (ZM38 B 2 β))⁻¹ •
      (gammaM38 2 β).withDensity (fun z => ENNReal.ofReal (Real.exp (-Rm38 2 β (G z)))) =
      muHatM38 B 2 β := by
    unfold muHatM38
    rw [← withDensity_smul' _ _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hZ).ne')]
    refine withDensity_congr_ae ?_
    filter_upwards [hae] with z hz
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hz, ENNReal.ofReal_div_of_pos hZ, div_eq_mul_inv, mul_comm]
  rw [hden]
  unfold muM38
  refine (Measure.map_congr ?_).symm
  have hac : muHatM38 B 2 β ≪ gammaM38 2 β := by
    unfold muHatM38
    exact withDensity_absolutelyContinuous _ _
  exact hac.ae_le hae

end NlsGge.Atomic.X009.X009Aux
