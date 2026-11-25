import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G3.G3003Host
import Armstrong.Work.RawBetaSum
import Armstrong.Work.RawBetaSumSpectralMass
import Armstrong.Work.RawBetaMagnitudeInverseProof

                                                                                      
                                                                           
                                                                                                                         
                                                                                                                                   
                                                                                                                                  
                                                                                                        
                                                                                                                                  
                                                                                                                    
                                                                                                                               
                                                                                                                                                   
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G3_011 :
  ∃ Winverse : Set PotPair,
    IsOpen Winverse ∧ range realSlice ⊆ Winverse ∧ Winverse ⊆ sourceW ∧
    ∀ φ0 ∈ Winverse, ∃ V : Set PotPair, ∃ C : ℝ,
      IsOpen V ∧ φ0 ∈ V ∧ V ⊆ Winverse ∧ 0 < C ∧
      ∀ φ ∈ V, ∀ n m : ℤ,
        ‖offDiagonalBeta n m φ‖ ≤ C * ‖gk151BetaMass38 φ m‖ * Lib.c3w n m := by
  obtain ⟨Wi, hWiO, hWiR, hWiW, hloc⟩ :=
    gk151_inverseDistance_bound_working38 sourceW sourceFamily.W_open
      sourceFamily.W_real sourceFamily.W_gk sourceF sourceFamily.F_analytic
      sourceFamily.F_zero sourceFamily.F_inverse sourceFamily.F_period
      sourceFamily.F_real
  refine ⟨Wi, hWiO, hWiR, hWiW, fun φ0 hφ0 => ?_⟩
  obtain ⟨V, C, hVo, hφV, hVW, hC, hb⟩ := hloc φ0 hφ0
  refine ⟨V, C, hVo, hφV, hVW, hC, fun φ hφ n m => ?_⟩
  by_cases hmn : m = n
  · have hdiag := congrFun (gk151BetaAmbient_diag38 sourceW sourceFamily.W_open
      sourceFamily.W_real sourceFamily.W_gk sourceF sourceFamily.F_analytic
      sourceFamily.F_zero sourceFamily.F_period n) φ
    have hz : offDiagonalBeta n m φ = 0 := by
      rw [hmn]
      exact hdiag
    rw [hz, norm_zero]
    exact mul_nonneg (mul_nonneg hC.le (norm_nonneg _)) (Lib.c3w_nonneg n m)
  · have hφW : φ ∈ sourceW := hWiW (hVW hφ)
    have h := hb ⟨φ, hφW⟩ hφ n m hmn
    have heq := gk151BetaAmbient_eq_source38 sourceW sourceFamily.W_open
      sourceFamily.W_real sourceFamily.W_gk sourceF sourceFamily.F_analytic
      sourceFamily.F_zero sourceFamily.F_period n m hmn ⟨φ, hφW⟩
    have e : offDiagonalBeta n m φ =
        gkSourceBeta38 sourceW sourceFamily.W_open sourceFamily.W_real
          sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
          sourceFamily.F_period n m hmn ⟨φ, hφW⟩ := heq
    rw [e, norm_gk151BetaMass38]
    exact h

end
end NlsGge.GKDefinitionDesign
