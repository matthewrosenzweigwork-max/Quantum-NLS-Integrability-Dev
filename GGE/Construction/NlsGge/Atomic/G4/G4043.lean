import Mathlib
import NlsGge.GK38.ContourActionDeformation
import NlsGge.GK38.XiSqCanonical
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G5033Host
import Armstrong.Work.ActualCartesianXYModels
import Armstrong.Work.ActualScalarCartesianModels

                                                                                                                  
                                                                                                                           
                                                       
                                                                                                                               
                                                                                                                     
                                                                                                                                   
                                          
                                                                                                             
                                                                                         
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
namespace G4043Aux
noncomputable section

theorem xy_radius_algebra (a P M : ℂ) :
    (a / (Real.sqrt 8 : ℂ) * (P + M)) ^ 2 +
      (a / ((Real.sqrt 8 : ℂ) * Complex.I) * (P - M)) ^ 2 = a ^ 2 * (P * M) / 2 := by
  have hs : ((Real.sqrt 8 : ℝ) : ℂ) ^ 2 = 8 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
    norm_num
  have h1 : (a / (Real.sqrt 8 : ℂ) * (P + M)) ^ 2 =
      a ^ 2 / ((Real.sqrt 8 : ℂ) ^ 2) * (P + M) ^ 2 := by ring
  have h2 : (a / ((Real.sqrt 8 : ℂ) * Complex.I) * (P - M)) ^ 2 =
      a ^ 2 / ((Real.sqrt 8 : ℂ) ^ 2 * Complex.I ^ 2) * (P - M) ^ 2 := by ring
  rw [h1, h2, hs, Complex.I_sq]
  ring

end
end G4043Aux

noncomputable section

theorem G4043 (n : ℤ) (φ : PotPair) (hφ : φ ∈ sourceBetaW) :
  gkActionC38 φ n = (cartesianX n φ ^ 2 + cartesianY n φ ^ 2) / 2 := by
  have hgk : φ ∈ gkW := sourceFamily.W_gk (sourceFamily.V_W hφ)
  have hprod := gk16_actual_scalar_models_product38 sourceF n φ hgk
  have hmul := xiSq38_multiplied n φ hgk
  have hxi := xiN38_sq n φ
  have hE : Complex.exp (Complex.I * betaSum n φ) * Complex.exp (-Complex.I * betaSum n φ) = 1 := by
    rw [← Complex.exp_add]
    have : Complex.I * betaSum n φ + -Complex.I * betaSum n φ = 0 := by ring
    rw [this, Complex.exp_zero]
  have key := G4043Aux.xy_radius_algebra (xiN38 n φ)
    (gk16ActualScalarZPlus38 sourceF n φ * Complex.exp (Complex.I * betaSum n φ))
    (gk16ActualScalarZMinus38 sourceF n φ * Complex.exp (-Complex.I * betaSum n φ))
  have hPM : gk16ActualScalarZPlus38 sourceF n φ * Complex.exp (Complex.I * betaSum n φ) *
      (gk16ActualScalarZMinus38 sourceF n φ * Complex.exp (-Complex.I * betaSum n φ)) =
        gamma2 φ n := by
    rw [mul_mul_mul_comm, hE, mul_one]
    exact hprod
  rw [hPM, hxi] at key
  have hX : cartesianX n φ = xiN38 n φ / (Real.sqrt 8 : ℂ) *
      (gk16ActualScalarZPlus38 sourceF n φ * Complex.exp (Complex.I * betaSum n φ) +
        gk16ActualScalarZMinus38 sourceF n φ * Complex.exp (-Complex.I * betaSum n φ)) := rfl
  have hY : cartesianY n φ = xiN38 n φ / ((Real.sqrt 8 : ℂ) * Complex.I) *
      (gk16ActualScalarZPlus38 sourceF n φ * Complex.exp (Complex.I * betaSum n φ) -
        gk16ActualScalarZMinus38 sourceF n φ * Complex.exp (-Complex.I * betaSum n φ)) := rfl
  rw [hX, hY, key]
  linear_combination (-(1 : ℂ) / 4) * hmul

end
end NlsGge.GKDefinitionDesign
