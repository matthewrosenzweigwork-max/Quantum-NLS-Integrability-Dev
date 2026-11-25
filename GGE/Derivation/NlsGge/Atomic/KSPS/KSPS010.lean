import Mathlib
import NlsGge.ThirdConsultation.KSPSRiccatiHost
import NlsGge.ThirdConsultation.KSPSSupport.EXP01
import NlsGge.ThirdConsultation.KSPSSupport.UNI01
import NlsGge.ThirdConsultation.KSPSSupport.A1U01
import NlsGge.ThirdConsultation.KSPSSupport.A2ID01
import NlsGge.ThirdConsultation.KSPSSupport.A2BND01
import NlsGge.ThirdConsultation.KSPSSupport.CORE01
import NlsGge.ThirdConsultation.KSPSSupport.RHO01
import NlsGge.ThirdConsultation.KSPSSupport.NLT01
import NlsGge.ThirdConsultation.KSPSSupport.ANA01
import NlsGge.ThirdConsultation.KSPSSupport.CLAUSES01

/- KSPS-010 packet WKB_residual_regularity, PRODUCTION (proof development, AUTHOR; not reviewed).
   Target NlsGge/Atomic/KSPS/KSPS010.lean (TASK_INDEX).
   Head: Pro round 6 (commit c5547100) section 10B, verbatim except the two lexical repairs listed in
   KSPS010_SPEC_DRAFT.json: (a) qualification of the KSPSRiccati names as KSPSRiccati.X; (b) «partial». -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.Common NlsGge.ThirdConsultation.KSPS
open NlsGge.ThirdConsultation.KSPSRiccati

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def WKBResidualBounds (N : ℕ) (φ : SobolevC N) : Prop :=
  1 ≤ N ∧
  (∀ b : Bool, KSPSRiccati.coefficient φ b 1 = -KSPSRiccati.sideInput φ b) ∧
  (∀ (b : Bool) (k : ℕ), 1 ≤ k → k ≤ N + 1 →
    physicalSobolev ((N + 1 - k : ℕ) : ℝ) (KSPSRiccati.coefficient φ b k)) ∧
  (∀ (b : Bool) (k : ℕ), 1 ≤ k → k ≤ N →
    (∀ j ∈ Finset.Icc 1 (k - 1),
      productInL2 (KSPSRiccati.coefficient φ b j) (KSPSRiccati.coefficient φ b (k - j))) ∧
    productInL2 (KSPSRiccati.sidePotential φ b) (KSPSRiccati.recurrenceProduct φ b k) ∧
    KSPSRiccati.coefficient φ b (k + 1) = KSPSRiccati.signedDerivative b (KSPSRiccati.coefficient φ b k) +
      physicalProduct (KSPSRiccati.sidePotential φ b) (KSPSRiccati.recurrenceProduct φ b k)) ∧
  (∀ b : Bool, physicalSobolev 2 (KSPSRiccati.nonlinearTop φ b)) ∧
  (∀ (b : Bool) (j : ℕ), j ∈ Finset.Icc (N + 1) (2 * N) →
    physicalSobolev 1 (KSPSRiccati.quadratic φ b j)) ∧
  (∀ (b : Bool) (lam : ℂ), lam ≠ 0 →
    productInL2 (KSPSRiccati.«partial» φ b lam) (KSPSRiccati.«partial» φ b lam) ∧
    productInL2 (KSPSRiccati.sidePotential φ b)
      (physicalProduct (KSPSRiccati.«partial» φ b lam) (KSPSRiccati.«partial» φ b lam)) ∧
    KSPSRiccati.rho φ b lam = KSPSRiccati.rhoTail φ b lam ∧
    MemLp (KSPSRiccati.forcing φ b lam) 2 KSPSRiccati.intervalMeasure ∧
    MemLp (KSPSRiccati.a1 φ b) 2 KSPSRiccati.intervalMeasure ∧
    MemLp (KSPSRiccati.a2 φ b lam) 2 KSPSRiccati.intervalMeasure ∧
    (KSPSRiccati.forcing φ b lam =ᵐ[KSPSRiccati.intervalMeasure] fun x =>
      coverRep38 (KSPSRiccati.coefficient φ b (N + 1)) x +
        (2 * Complex.I * lam)⁻¹ * KSPSRiccati.a1 φ b x +
        ((2 * Complex.I * lam) ^ 2)⁻¹ * KSPSRiccati.a2 φ b lam x)) ∧
  (∀ Λ : ℝ, 0 < Λ → ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
    ∀ ψ : SobolevC N, ‖ψ - φ‖ < ε →
      (∀ (b : Bool) (k : ℕ), 1 ≤ k → k ≤ N + 1 →
        physicalSobolev ((N + 1 - k : ℕ) : ℝ) (KSPSRiccati.coefficient ψ b k) ∧
        physicalSobolevNorm ((N + 1 - k : ℕ) : ℝ)
          (KSPSRiccati.coefficient ψ b k) ≤ C) ∧
      (∀ b : Bool, MemLp (KSPSRiccati.a1 ψ b) 2 KSPSRiccati.intervalMeasure ∧
        eLpNorm (KSPSRiccati.a1 ψ b) 2 KSPSRiccati.intervalMeasure ≤ ENNReal.ofReal C) ∧
      ∀ (b : Bool) (lam : ℂ), Λ ≤ ‖lam‖ →
        MemLp (KSPSRiccati.a2 ψ b lam) 2 KSPSRiccati.intervalMeasure ∧
        eLpNorm (KSPSRiccati.a2 ψ b lam) 2 KSPSRiccati.intervalMeasure ≤ ENNReal.ofReal C)

/-- The WKB residual regularity packet (Pro round 6, section 10B). -/
theorem WKB_residual_regularity
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) :
  WKBResidualBounds N φ := by
  refine ⟨hN, fun b => KSPSSupport.h150_C1 φ b, fun b k hk1 hk2 => KSPSSupport.h150_coef_mem N hN φ b k hk1 hk2,
    fun b k hk1 hk2 => KSPSSupport.h150_C3 hN φ b k hk1 hk2,
    fun b => KSPSSupport.nonlinearTop_H2 N hN φ b,
    fun b j hj => KSPSSupport.quadratic_H1 φ b j hN, ?_, ?_⟩
  · intro b lam hlam
    exact ⟨KSPSSupport.h150_C6_partial_productInL2 hN φ b lam,
      KSPSSupport.h150_C6_side_productInL2 hN φ b lam,
      KSPSSupport.h150_rho_eq_rhoTail N hN φ b lam hlam,
      KSPSSupport.h150_forcing_memLp φ b lam,
      KSPSSupport.h150_a1_memLp φ b,
      KSPSSupport.h150_a2_memLp φ b lam,
      KSPSSupport.h150_forcing_ae φ b lam hlam⟩
  · intro Λ hΛ
    obtain ⟨Du, hDu, hU⟩ := KSPSSupport.h161_coef_uniform N hN
      (‖φ.1‖ + ‖φ.2‖ + 2) (by positivity)
    obtain ⟨Ca1, hCa1, hA1⟩ := KSPSSupport.h161_a1_uniform N hN
      (‖φ.1‖ + ‖φ.2‖ + 2) (by positivity)
    obtain ⟨Ca2, hCa2, hA2⟩ := KSPSSupport.h161_a2_uniform N hN
      (‖φ.1‖ + ‖φ.2‖ + 2) (by positivity) Λ hΛ
    refine ⟨1, Du + Ca1 + Ca2 + 1, one_pos, by linarith, fun ψ hψ => ?_⟩
    have hS := KSPSSupport.h161_ball_sum φ ψ hψ
    refine ⟨fun b k hk1 hk2 => ?_, fun b => ?_, fun b lam hlam => ?_⟩
    · obtain ⟨hm, hn⟩ := hU ψ hS b k hk1 hk2
      exact ⟨hm, hn.trans (by linarith)⟩
    · obtain ⟨hm, hn⟩ := hA1 ψ hS b
      exact ⟨hm, hn.trans (ENNReal.ofReal_le_ofReal (by linarith))⟩
    · obtain ⟨hm, hn⟩ := hA2 ψ hS b lam hlam
      exact ⟨hm, hn.trans (ENNReal.ofReal_le_ofReal (by linarith))⟩

end
end NlsGge.ThirdConsultation.KSPS
