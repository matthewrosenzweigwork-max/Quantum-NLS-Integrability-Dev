import Mathlib
import Armstrong.Work.CartesianTerminalRootSpec
import NlsGge.Atomic.X.X006
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic

                                                                                                                                      
                                                                                                                                           
                                                                                                                                    
                                                                                                                                     
                                                                                                                            
                                                                                                                                                
                    
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations


namespace NlsGge.ThirdConsultation.KSN
open NlsGge.GKDefinitionDesign
open SummationFilter Metric

def deltaFactor (n : ℤ) (φ : PotPair) (z : ℂ) : ℂ :=
  a5OmittedRootProduct38 n (φ, z) / (Lib.piN n : ℂ)

abbrev terminalRoot := gk16TerminalRoot38

theorem KSN002_main (n : ℤ) :
  AnalyticOnNhd ℂ (fun φ : PotPair => deltaFactor n φ (muSeq φ n)) sourceBetaW ∧
  ∀ φ ∈ sourceBetaW,
    Multipliable (fun k : ℤ => a5OmittedRootFactor38 n k (φ, muSeq φ n))
      (symmetricIcc ℤ) ∧
    deltaFactor n φ (muSeq φ n) ≠ 0 ∧
    antiDiscrim φ (muSeq φ n) =
      2 * Complex.I * terminalRoot n φ * deltaFactor n φ (muSeq φ n) ∧
    (terminalRoot n φ)^2 =
      (lamPlus φ n - muSeq φ n) * (lamMinus φ n - muSeq φ n) := by
  have hsub : ∀ φ ∈ sourceBetaW, φ ∈ gkW := fun φ hφ =>
    NlsGge.Atomic.ExistingPhysicalFamily.actualPhysicalLocalFamily.W_gk
      (NlsGge.Atomic.ExistingPhysicalFamily.actualPhysicalLocalFamily.V_W hφ)
  have hdomain : ∀ φ ∈ sourceBetaW, (φ, muSeq φ n) ∈ a5OmittedRootDomain38 n := by
    intro φ hφ
    have hφg := hsub φ hφ
    have hfam := isolating_family38 φ hφg
    obtain ⟨c, N, hgeom, hspec⟩ := hfam
    have hmu := (hspec.1 n).2.1
    exact a5OwnClosedBall_omittedDomain38 φ hφg (discC φ) (discR φ) (isolating_family38 φ hφg) n
      (muSeq φ n) (ball_subset_closedBall hmu)
  have hPa : ∀ φ ∈ sourceBetaW, AnalyticAt ℂ (fun ψ : PotPair => a5OmittedRootProduct38 n (ψ, muSeq ψ n)) φ := by
    intro φ hφ
    have hJ : AnalyticAt ℂ (fun ψ : PotPair => (ψ, muSeq ψ n)) φ :=
      analyticAt_id.prod (analyticOnNhd_muSeq_complex38 n φ (hsub φ hφ))
    exact AnalyticAt.comp (g := a5OmittedRootProduct38 n) (f := fun ψ : PotPair => (ψ, muSeq ψ n))
      (a5OmittedRoot_analytic38 n (φ, muSeq φ n) (hdomain φ hφ)) hJ
  have hpi : (Lib.piN n : ℂ) ≠ 0 := by exact_mod_cast Lib.piN_ne_zero n
  have hPne : ∀ φ ∈ sourceBetaW, a5OmittedRootProduct38 n (φ, muSeq φ n) ≠ 0 := fun φ hφ =>
    a5OmittedRoot_ne_zero38 n (φ, muSeq φ n) (hdomain φ hφ)
  refine ⟨?_, fun φ hφ => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro φ hφ
    unfold deltaFactor
    exact (hPa φ hφ).div analyticAt_const hpi
  · exact a5OmittedRoot_multipliable38 n (φ, muSeq φ n) (hdomain φ hφ)
  · unfold deltaFactor
    exact div_ne_zero (hPne φ hφ) hpi
  · unfold terminalRoot deltaFactor gk16TerminalRoot38
    have hP0 := hPne φ hφ
    field_simp
  · have hsq := gk16_terminal_root_sq38 n φ (hsub φ hφ)
    unfold terminalRoot
    rw [hsq]
    ring

end NlsGge.ThirdConsultation.KSN
