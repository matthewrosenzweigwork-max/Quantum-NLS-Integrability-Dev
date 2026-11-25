import Mathlib
import NlsGge.Atomic.KSN.KSN008
import NlsGge.Atomic.G4.G4036H1
import NlsGge.Atomic.G4.G4036H3

set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38
open NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN

private theorem ksn009_eta_analytic_on_source (n a : ℤ) :
    AnalyticOnNhd ℂ (eta n a) sourceBetaW := by
  intro φ hφ
  have hT : AnalyticAt ℂ
      (fun ψ : PotPair => NlsGge.GKDefinitionDesign.terminalRoot n ψ) φ :=
    (NlsGge.GKDefinitionDesign.terminalRoot_analytic n) φ hφ
  have hC : AnalyticAt ℂ
      (fun ψ : PotPair => ownCorrection n ψ (muSeq ψ n)) φ :=
    (NlsGge.GKDefinitionDesign.ownCorrection_at_dirichlet_analytic n) φ hφ
  have hfun : eta n a = fun ψ : PotPair =>
      Complex.exp (-(a : ℂ) * NlsGge.GKDefinitionDesign.terminalRoot n ψ *
        ownCorrection n ψ (muSeq ψ n)) := rfl
  rw [hfun]
  exact (((analyticAt_const.mul hT).mul hC)).cexp

theorem KSN009_main (n a : ℤ) (ha : a = 1 ∨ a = -1) :
  AnalyticOnNhd ℂ (eta n a) sourceBetaW ∧
  ∀ (φ h : PotPair) (D : Set ℂ), IsOpen D →
    (∀ z ∈ D, φ + z • h ∈ sourceBetaW ∧ gamma2 (φ + z • h) n = 0) →
    AnalyticOnNhd ℂ (fun z : ℂ => eta n a (φ + z • h)) D := by
  refine ⟨ksn009_eta_analytic_on_source n a, ?_⟩
  intro φ h D hD hcollapsed
  have hline : AnalyticOnNhd ℂ (fun z : ℂ => φ + z • h) Set.univ := by
    have hid : AnalyticOnNhd ℂ (fun z : ℂ => z) Set.univ := analyticOnNhd_id
    have hconst : AnalyticOnNhd ℂ (fun _ : ℂ => h) Set.univ := analyticOnNhd_const
    have hsmul : AnalyticOnNhd ℂ (fun z : ℂ => z • h) Set.univ := hid.smul hconst
    exact analyticOnNhd_const.add hsmul
  have hlineD : AnalyticOnNhd ℂ (fun z : ℂ => φ + z • h) D :=
    hline.mono (Set.subset_univ D)
  have hmaps : Set.MapsTo (fun z : ℂ => φ + z • h) D sourceBetaW := by
    intro z hz
    exact (hcollapsed z hz).1
  change AnalyticOnNhd ℂ ((eta n a) ∘ (fun z : ℂ => φ + z • h)) D
  exact (ksn009_eta_analytic_on_source n a).comp hlineD hmaps

end NlsGge.ThirdConsultation.KSN
