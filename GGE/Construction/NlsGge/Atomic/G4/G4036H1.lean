import Mathlib
import NlsGge.Atomic.G4.G4036Host
import NlsGge.Atomic.G5.G5001
import NlsGge.GK38.AngleDirichletAnalytic
import NlsGge.GK38.GradFundamentalDefs
import NlsGge.GK38.XiSqOmittedRoot

                                                                                                          
                                                                                                   
                                                                                                               
                                                                                                                 
                                                                                     
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem terminalRoot_analytic (n : ℤ) :
  AnalyticOnNhd ℂ (terminalRoot n) sourceBetaW := by
  intro φ hφ
  have hgk : φ ∈ gkW := g5001_gk φ hφ
  have hμ : AnalyticAt ℂ (fun ψ : PotPair => muSeq ψ n) φ :=
    analyticOnNhd_muSeq_complex38 n φ hgk
  have hJ : AnalyticAt ℂ (fun ψ : PotPair => (ψ, muSeq ψ n)) φ := analyticAt_id.prod hμ
  have hnum : AnalyticAt ℂ (fun ψ : PotPair => antiDiscrim ψ (muSeq ψ n)) φ :=
    AnalyticAt.comp (g := fun p : PotPair × ℂ => antiDiscrim p.1 p.2)
      (f := fun ψ : PotPair => (ψ, muSeq ψ n))
      (analyticOnNhd_antiDiscrim (φ, muSeq φ n) (Set.mem_univ _)) hJ
  have hA : AnalyticAt ℂ (fun ψ : PotPair => a5OmittedRootProduct38 n (ψ, muSeq ψ n)) φ :=
    AnalyticAt.comp (g := a5OmittedRootProduct38 n)
      (f := fun ψ : PotPair => (ψ, muSeq ψ n))
      (a5OmittedRoot_analytic38 n (φ, muSeq φ n) (g5001_dom φ hφ n)) hJ
  have hpi : (Lib.piN n : ℂ) ≠ 0 := by exact_mod_cast Lib.piN_ne_zero n
  have hA0 : a5OmittedRootProduct38 n (φ, muSeq φ n) ≠ 0 :=
    a5OmittedRoot_ne_zero38 n (φ, muSeq φ n) (g5001_dom φ hφ n)
  have hden : AnalyticAt ℂ (fun ψ : PotPair =>
      ((2 * Complex.I) / (Lib.piN n : ℂ)) * a5OmittedRootProduct38 n (ψ, muSeq ψ n)) φ :=
    analyticAt_const.mul hA
  have hden0 : ((2 * Complex.I) / (Lib.piN n : ℂ)) * a5OmittedRootProduct38 n (φ, muSeq φ n) ≠ 0 :=
    mul_ne_zero (div_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hpi) hA0
  exact hnum.div hden hden0

end
end NlsGge.GKDefinitionDesign
