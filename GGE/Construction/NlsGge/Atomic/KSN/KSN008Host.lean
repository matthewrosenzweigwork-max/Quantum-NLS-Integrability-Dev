import Mathlib
import NlsGge.Atomic.KSN.KSN002
import NlsGge.Atomic.KSN.KSN007Host
import NlsGge.Atomic.G4.G4036Host
import NlsGge.Atomic.G4.G4022Host

set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38
open NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

theorem ksn_terminalRoot_eq_native (n : ℤ) (φ : PotPair) :
    NlsGge.ThirdConsultation.KSN.terminalRoot n φ =
      NlsGge.GKDefinitionDesign.terminalRoot n φ := by
  rfl

theorem ksn_collapsedDD_eq_neg_native (n : ℤ) (φ : PotPair) (z : ℂ) :
    NlsGge.ThirdConsultation.KSN.collapsedDD n φ z =
      -NlsGge.GKDefinitionDesign.zetaDividedDifference n φ z := by
  by_cases hz : z = tauN φ n
  · simp [collapsedDD, zetaDividedDifference, hz]
  · simp only [collapsedDD, zetaDividedDifference, if_neg hz]
    ring

theorem ksn_collapsedIntegral_eq_neg_chi (n : ℤ) (φ : PotPair) :
    NlsGge.ThirdConsultation.KSN.collapsedIntegral n φ =
      -NlsGge.GKDefinitionDesign.chi n φ := by
  unfold collapsedIntegral NlsGge.GKDefinitionDesign.chi
  rw [show (fun t : ℝ => collapsedDD n φ
      (tauN φ n + (t : ℂ) * (muSeq φ n - tauN φ n))) =
      fun t : ℝ => -NlsGge.GKDefinitionDesign.zetaDividedDifference n φ
        (tauN φ n + (t : ℂ) * (muSeq φ n - tauN φ n)) from by
        funext t
        exact ksn_collapsedDD_eq_neg_native n φ _]
  rw [intervalIntegral.integral_neg]
  ring

end
end NlsGge.ThirdConsultation.KSN
