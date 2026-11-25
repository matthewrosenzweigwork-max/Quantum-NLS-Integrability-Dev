import Mathlib
import NlsGge.Atomic.KSN.KSN002
import NlsGge.Atomic.KSN.KSN004Host
import NlsGge.Atomic.KSN.KSN007Host
import NlsGge.Atomic.KSN.KSN008Host
import NlsGge.Atomic.KSN.KSN008Sup1
import NlsGge.Atomic.G4.G4017
import NlsGge.Atomic.G4.G4023
import NlsGge.Atomic.G4.G4028
import NlsGge.Atomic.G4.G4036H1
import NlsGge.Atomic.G4.G4036H3

set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38
open NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

private theorem ksn_eta_analytic_from_native (n a : ℤ) :
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

theorem ksn_collapse_primitive_value
    (n : ℤ) (φ : PotPair) (hφ : φ ∈ sourceBetaW)
    (hγ : gamma2 φ n = 0) :
    (tauN φ n - muSeq φ n) * ownCorrection n φ (muSeq φ n) =
      collapsedIntegral n φ := by
  rw [ksn_collapsedIntegral_eq_neg_chi]
  exact NlsGge.G4023Support.collapse_identity n φ hφ hγ

theorem ksn_eta_at_collapse_offCentre
    (n a : ℤ) (φ : PotPair) (hφ : φ ∈ sourceBetaW)
    (hγ : gamma2 φ n = 0) (hμ : muSeq φ n ≠ tauN φ n) :
    eta n a φ =
      Complex.exp (-(a : ℂ) * sheetSign n φ * collapsedIntegral n φ) := by
  have hgk : φ ∈ gkW := G4017Aux.sourceBetaW_gkW hφ
  have hgamma := gamma2_value38 φ hgk n
  have hγ' := hγ
  rw [hgamma] at hγ'
  have hEnds : lamPlus φ n = lamMinus φ n :=
    sub_eq_zero.mp (eq_zero_of_pow_eq_zero hγ')
  have hTau : tauN φ n = lamMinus φ n := by
    rw [tauN_value38 φ hgk n, hEnds]
    ring
  have hμoff : muSeq φ n ∉ gapSegment φ n := by
    change muSeq φ n ∉ segment ℝ (lamMinus φ n) (lamPlus φ n)
    rw [hEnds, segment_same, Set.mem_singleton_iff]
    intro hm
    exact hμ (hm.trans hTau.symm)
  have hoff : φ ∈ offGapSet n := ⟨hφ, hμoff⟩
  have hroot := NlsGge.G4028Support.terminalRoot_eq n φ hoff
  have hstandard : standardRoot φ n (muSeq φ n) = tauN φ n - muSeq φ n := by
    unfold standardRoot
    rw [hγ]
    exact stdRoot_degenerate38 _ _
  have hprimitive := ksn_collapse_primitive_value n φ hφ hγ
  calc
    eta n a φ = Complex.exp
        (-(a : ℂ) * terminalRoot n φ * ownCorrection n φ (muSeq φ n)) := rfl
    _ = Complex.exp
        (-(a : ℂ) * (sheetSign n φ * standardRoot φ n (muSeq φ n)) *
          ownCorrection n φ (muSeq φ n)) := by
            rw [ksn_terminalRoot_eq_native n φ, hroot]
    _ = Complex.exp
        (-(a : ℂ) * sheetSign n φ *
          ((tauN φ n - muSeq φ n) * ownCorrection n φ (muSeq φ n))) := by
            rw [hstandard]
            congr 1
            ring
    _ = Complex.exp
        (-(a : ℂ) * sheetSign n φ * collapsedIntegral n φ) := by
            rw [hprimitive]

theorem KSN008_main (n a : ℤ) (ha : a = 1 ∨ a = -1)
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ sourceBetaW) (hγ : gamma2 φ₀ n = 0) :
  ContinuousAt (eta n a) φ₀ ∧
  (muSeq φ₀ n = tauN φ₀ n → eta n a φ₀ = 1) ∧
  (muSeq φ₀ n ≠ tauN φ₀ n →
    canonRoot38 φ₀ (muSeq φ₀ n) ≠ 0 ∧
    (sheetSign n φ₀ = 1 ∨ sheetSign n φ₀ = -1) ∧
    eta n a φ₀ = Complex.exp (-(a : ℂ) * sheetSign n φ₀ * collapsedIntegral n φ₀) ∧
    ∃ U : Set PotPair, IsOpen U ∧ φ₀ ∈ U ∧ U ⊆ sourceBetaW ∧
      ∀ φ ∈ U, gamma2 φ n = 0 → sheetSign n φ = sheetSign n φ₀) := by
  refine ⟨(ksn_eta_analytic_from_native n a φ₀ hφ₀).continuousAt, ?_, ?_⟩
  · intro hμ
    have hgk : φ₀ ∈ gkW := G4017Aux.sourceBetaW_gkW hφ₀
    have hgamma := gamma2_value38 φ₀ hgk n
    have hγ' := hγ
    rw [hgamma] at hγ'
    have hEnds : lamPlus φ₀ n = lamMinus φ₀ n :=
      sub_eq_zero.mp (eq_zero_of_pow_eq_zero hγ')
    have hTau : tauN φ₀ n = lamMinus φ₀ n := by
      rw [tauN_value38 φ₀ hgk n, hEnds]
      ring
    have hμminus : muSeq φ₀ n = lamMinus φ₀ n := hμ.trans hTau
    have hμplus : muSeq φ₀ n = lamPlus φ₀ n := hμminus.trans hEnds.symm
    obtain ⟨_, hmain⟩ := KSN002_main n
    obtain ⟨_, _, _, hrootSq⟩ := hmain φ₀ hφ₀
    rw [hμplus] at hrootSq
    have hrootSq0 : (terminalRoot n φ₀) ^ 2 = 0 := by simpa using hrootSq
    have hmul : terminalRoot n φ₀ * terminalRoot n φ₀ = 0 := by
      simpa [pow_two] using hrootSq0
    have hroot0 : terminalRoot n φ₀ = 0 := by
      rcases mul_eq_zero.mp hmul with h | h <;> assumption
    simp [eta, hroot0]
  · intro hμ
    obtain ⟨hroot, hsign, U, hUopen, hUφ₀, hUsubset, hconst⟩ :=
      NlsGge.Atomic.KSN008Sup1.sheetSign_collapse_facts n φ₀ hφ₀ hγ hμ
    exact ⟨hroot, hsign,
      ksn_eta_at_collapse_offCentre n a φ₀ hφ₀ hγ hμ,
      U, hUopen, hUφ₀, hUsubset, hconst⟩

end
end NlsGge.ThirdConsultation.KSN
