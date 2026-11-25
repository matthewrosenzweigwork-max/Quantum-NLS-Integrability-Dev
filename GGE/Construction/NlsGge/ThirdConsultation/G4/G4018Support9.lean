import Mathlib
import NlsGge.Atomic.X.X006
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.Atomic.G4.G4NormalizedHost
import NlsGge.GK38.AbelianRatio
import NlsGge.GK38.XiSqLocal
                                                                                                     
                                                                                                          
                                      
                                                                                                         
                                                                                                          
                                                                                                        
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GKDefinitionDesign

namespace NlsGge.G4018Support

theorem sourceF_extend_analytic (n : ℤ) :
    AnalyticOnNhd ℂ (fun φ : PotPair => p2Extend38 n (sourceF n φ)) sourceW := by
  intro φ hφ
  exact ((p2Extend38 n).analyticAt (sourceF n φ)).comp (sourceFamily.F_analytic n φ hφ)

theorem normalizedZeta_joint_analytic (V : Set PotPair) (hVW : V ⊆ sourceW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : ∀ φ ∈ V, IsolatingFamily38 φ C R) (n : ℤ) :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => normalizedZeta n p.1 p.2)
      (V ×ˢ Metric.ball (C n) (R n)) := by
  intro p hp
  obtain ⟨hφV, hlam⟩ := hp
  have hgk : p.1 ∈ gkW := sourceFamily.W_gk (hVW hφV)
  have hdom : (p.1, p.2) ∈ a5OmittedRootDomain38 n :=
    a5OwnClosedBall_omittedDomain38 p.1 hgk C R (hfam p.1 hφV) n p.2
      (Metric.ball_subset_closedBall hlam)
  have h1 : AnalyticAt ℂ (fun q : PotPair × ℂ => q.1) p := analyticAt_fst
  have h2 : AnalyticAt ℂ (fun q : PotPair × ℂ => p2Extend38 n (sourceF n q.1)) p :=
    AnalyticAt.comp (g := fun φ : PotPair => p2Extend38 n (sourceF n φ)) (f := fun q : PotPair × ℂ => q.1)
      (sourceF_extend_analytic n p.1 (hVW hφV)) h1
  have hg : AnalyticAt ℂ
      (fun q : PotPair × ℂ => ((q.1, p2Extend38 n (sourceF n q.1)), q.2)) p :=
    (h1.prod h2).prod analyticAt_snd
  have hf := p2OmittedRatio_analytic38 n
    (((p.1, p2Extend38 n (sourceF n p.1)), p.2)) hdom
  exact AnalyticAt.comp (g := p2OmittedRatio38 n)
    (f := fun q : PotPair × ℂ => ((q.1, p2Extend38 n (sourceF n q.1)), q.2)) hf hg

end NlsGge.G4018Support
