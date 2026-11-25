import Mathlib
import NlsGge.GK38.Defs
import NlsGge.GK38.XiCommonDomain
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G5033Host
import NlsGge.Atomic.G4.G4036Host
import NlsGge.Atomic.G4.G4036
import NlsGge.Atomic.G4.G4014
import NlsGge.Atomic.G3.G3031All

                                                                                                    
                                                                                                                                            
                                                                                                                                                    
                                                                                                                                      
                                                                                                                                      
                                                                              
                                                 
                                                                                                   
                                                                                                                            
                                                                                                                
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
namespace G4041Aux
noncomputable section

theorem sourceBetaW_subset_gkW : sourceBetaW ⊆ gkW :=
  fun _ h => sourceFamily.W_gk (sourceFamily.V_W h)

theorem analytic_pieces (n : ℤ) :
    AnalyticOnNhd ℂ (xiN38 n) sourceBetaW ∧
    AnalyticOnNhd ℂ (fun φ : PotPair => cartesianZExtended n 1 φ *
      Complex.exp (Complex.I * betaSum n φ)) sourceBetaW ∧
    AnalyticOnNhd ℂ (fun φ : PotPair => cartesianZExtended n (-1) φ *
      Complex.exp (-Complex.I * betaSum n φ)) sourceBetaW := by
  have hb := betaSum_analyticOnNhd_sourceBetaW n
  have hxi : AnalyticOnNhd ℂ (xiN38 n) sourceBetaW :=
    (xiN38_analytic_commonDomain n).mono sourceFamily.V_xi
  refine ⟨hxi, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · exact (G4036 n 1 (Or.inl rfl) φ hφ).mul
      (analyticAt_const.mul (hb φ hφ)).cexp
  · exact (G4036 n (-1) (Or.inr rfl) φ hφ).mul
      (analyticAt_const.mul (hb φ hφ)).cexp

end
end G4041Aux

noncomputable section

theorem G4041 (n : ℤ) :
  AnalyticOnNhd ℂ (cartesianX n) sourceBetaW ∧
  AnalyticOnNhd ℂ (cartesianY n) sourceBetaW := by
  obtain ⟨hxi, hP, hM⟩ := G4041Aux.analytic_pieces n
  constructor
  · have h : AnalyticOnNhd ℂ (fun φ : PotPair =>
        (xiN38 n φ / (Real.sqrt 8 : ℂ)) *
          (cartesianZExtended n 1 φ * Complex.exp (Complex.I * betaSum n φ) +
            cartesianZExtended n (-1) φ * Complex.exp (-Complex.I * betaSum n φ)))
        sourceBetaW :=
      fun φ hφ => (hxi.div_const φ hφ).mul ((hP φ hφ).add (hM φ hφ))
    refine h.congr sourceFamily.V_open (fun φ hφ => ?_)
    have hgk := G4041Aux.sourceBetaW_subset_gkW hφ
    simp only [cartesianX, gk16ScalarXModel38, G4014Aux.cartZ_plus n φ hgk,
      G4014Aux.cartZ_minus n φ hgk]
  · have h : AnalyticOnNhd ℂ (fun φ : PotPair =>
        (xiN38 n φ / ((Real.sqrt 8 : ℂ) * Complex.I)) *
          (cartesianZExtended n 1 φ * Complex.exp (Complex.I * betaSum n φ) -
            cartesianZExtended n (-1) φ * Complex.exp (-Complex.I * betaSum n φ)))
        sourceBetaW :=
      fun φ hφ => (hxi.div_const φ hφ).mul ((hP φ hφ).sub (hM φ hφ))
    refine h.congr sourceFamily.V_open (fun φ hφ => ?_)
    have hgk := G4041Aux.sourceBetaW_subset_gkW hφ
    simp only [cartesianY, gk16ScalarYModel38, G4014Aux.cartZ_plus n φ hgk,
      G4014Aux.cartZ_minus n φ hgk]

end
end NlsGge.GKDefinitionDesign
