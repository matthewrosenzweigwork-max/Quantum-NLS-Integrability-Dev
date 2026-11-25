import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G3.G3SourcePathHost
import NlsGge.ThirdConsultation.G3.G3003Host
import NlsGge.GK38.AngleEndpointVariety
import Armstrong.Frozen.RawBeta.gkBetaSourceWellDefined38
import Armstrong.Work.RawBetaSum
import Armstrong.Work.RawBetaEndpointZero

                                                                                      
                                                                           
                                                                                                                    
                                                                                                                      
                                                                                                                              
                                                                                                                                  
                                                                                                                     
                                                            
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem offDiagonalBeta_sourceValue_g3016 (n m : ℤ) (hmn : m ≠ n) (φ : SourcePotential) :
    GKSourceBetaValue38 n m hmn sourceF (sourceGK φ) (offDiagonalBeta n m φ.1) := by
  have hspec := Classical.choose_spec
    ((gkBetaSourceWellDefined38 sourceW sourceFamily.W_open sourceFamily.W_real
      sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
      sourceFamily.F_period n φ.1 φ.2 m hmn).1)
  have heq : offDiagonalBeta n m φ.1 =
      gkSourceBeta38 sourceW sourceFamily.W_open sourceFamily.W_real
        sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
        sourceFamily.F_period n m hmn φ :=
    gk151BetaAmbient_eq_source38 sourceW sourceFamily.W_open sourceFamily.W_real
      sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
      sourceFamily.F_period n m hmn φ
  rw [heq]
  exact hspec.1

theorem G3_016 (n m : ℤ) (hmn : m ≠ n) (φ0 : PotPair)
    (hφ0 : φ0 ∈ endpointSet m) :
  offDiagonalBeta n m φ0 = 0 ∧
  Tendsto (offDiagonalBeta n m) (𝓝[sourceW] φ0) (𝓝 0) ∧
  ContinuousAt (offDiagonalBeta n m) φ0 := by
  obtain ⟨hW, hper⟩ := hφ0
  have htip : muSeq φ0 m = lamMinus φ0 m ∨ muSeq φ0 m = lamPlus φ0 m :=
    (angleEndpointDetector_zero_iff38 φ0 (sourceFamily.W_gk hW) m).mp hper
  have hzero : offDiagonalBeta n m φ0 = 0 :=
    rawBetaSourceValueEqZeroAtTip38 n m hmn sourceF (sourceGK ⟨φ0, hW⟩)
      (offDiagonalBeta n m φ0)
      (offDiagonalBeta_sourceValue_g3016 n m hmn ⟨φ0, hW⟩) htip
  have han : AnalyticOnNhd ℂ (offDiagonalBeta n m) sourceW :=
    gk151BetaAmbient_analytic38 sourceW sourceFamily.W_open sourceFamily.W_real
      sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
      sourceFamily.F_period n m
  have hcont : ContinuousAt (offDiagonalBeta n m) φ0 :=
    han.continuousOn.continuousAt (sourceFamily.W_open.mem_nhds hW)
  refine ⟨hzero, ?_, hcont⟩
  have ht : Tendsto (offDiagonalBeta n m) (𝓝 φ0) (𝓝 (offDiagonalBeta n m φ0)) :=
    hcont.tendsto
  rw [hzero] at ht
  exact ht.mono_left nhdsWithin_le_nhds

end
end NlsGge.GKDefinitionDesign
