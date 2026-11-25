import Mathlib
import NlsGge.Atomic.KSPS.KSPS013
import NlsGge.Atomic.KSPS.KSPS014
import NlsGge.ThirdConsultation.KSPS.KSPS016Uniform1
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform4
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform8
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform13
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform14

/- KSPS025U15 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). GLUE (root main probe: the joint
   closure contains KSPS025Uniform13, above the worker-lane memory cap).
   Target NlsGge/ThirdConsultation/KSPS/KSPS025Uniform15.lean. Pro round-15 SUPPORT (never a packet), chain B.
   * h26q_uniform: the h26q statement of proof development/KSPS025_CHAINB_STOP.md, unconditional:
     KSPS025U14.h26q_of with hloc = KSPS025U4.periodic_loc_uniform, hthr = KSPS016U.threshold_mono,
     hSb = KSPS016U.Sb_le, h13 = KSPS-013 integrated_riccati_vanishing, h14 = KSPS-014 WKB_monodromy_entries .2,
     hE = KSPS025U13.entries_tail_uniform.
   * h26_uniform: the full h26 binder of KSPS025U7/U8 (cutoff = max of the two cutoffs; both conjuncts are
     monotone in the tail condition).
   * midpoint_spectral_expansion_uniform_of24: KSPS025U8.midpoint_spectral_expansion_uniform_of26_24 with h26
     discharged; only h24 remains (reduced by proof development's KSPS025U10/U11 to h17U, proof development). -/
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS025U15
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

theorem h26q_uniform (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ (M : ℕ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∃ hplus hminus : ℤ → ℂ, ∀ n : ℤ, (M : ℤ) ≤ |n| →
        NlsGge.ThirdConsultation.KSPSWKB.endpointQuadraticFormula N φ n hplus hminus := by
  obtain ⟨a, ha, hloc⟩ := NlsGge.ThirdConsultation.KSPS025U4.periodic_loc_uniform N hN B₀ hB₀
  exact NlsGge.ThirdConsultation.KSPS025U14.h26q_of N hN B₀ hB₀ a ha hloc
    (NlsGge.ThirdConsultation.KSPSVolterra.threshold N B₀)
    (fun φ hφ => NlsGge.ThirdConsultation.KSPS016U.threshold_mono N hφ)
    (∑ k ∈ Finset.Icc 1 N, NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B₀ k)
    (fun φ hφ => NlsGge.ThirdConsultation.KSPS016U.Sb_le φ hφ)
    (fun φ _ k hk => NlsGge.ThirdConsultation.KSPS.integrated_riccati_vanishing N k φ hk)
    (fun φ _ lam hlam => (NlsGge.ThirdConsultation.KSPS.WKB_monodromy_entries N (sobolevNorm N φ) φ lam le_rfl hlam).2)
    (NlsGge.ThirdConsultation.KSPS025U13.entries_tail_uniform N hN B₀ hB₀)

theorem h26_uniform (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ (M : ℕ) (CE : ℝ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      (∀ (upper : Bool) (i j : Fin 2) (F : Finset ℤ), (∀ n ∈ F, (M : ℤ) ≤ |n|) →
        ∑ n ∈ F, (indexWeight n ^ (N + 1) * ‖NlsGge.ThirdConsultation.KSPSWKB.endpointEntryError N φ upper i j n‖) ^ 2 ≤ CE) ∧
      ∃ hplus hminus : ℤ → ℂ, ∀ n : ℤ, (M : ℤ) ≤ |n| →
        NlsGge.ThirdConsultation.KSPSWKB.endpointQuadraticFormula N φ n hplus hminus := by
  obtain ⟨ME, CE, hE⟩ := NlsGge.ThirdConsultation.KSPS025U13.entries_tail_uniform N hN B₀ hB₀
  obtain ⟨MQ, hQ⟩ := h26q_uniform N hN B₀ hB₀
  refine ⟨max ME MQ, CE, fun φ hφ => ⟨fun upper i j F hF => hE φ hφ upper i j F (fun n hn =>
    le_trans (by exact_mod_cast le_max_left ME MQ) (hF n hn)), ?_⟩⟩
  obtain ⟨hplus, hminus, h⟩ := hQ φ hφ
  exact ⟨hplus, hminus, fun n hn => h n (le_trans (by exact_mod_cast le_max_right ME MQ) hn)⟩

theorem midpoint_spectral_expansion_uniform_of24
    (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀)
    (h24 : ∃ (M : ℕ) (C : ℝ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ F : Finset ℤ, (∀ n ∈ F, (M : ℤ) ≤ |n|) →
        ∑ n ∈ F, (indexWeight n ^ (N + 1) * ‖criticalEigenvalue φ n - spectralPolynomial φ n‖) ^ 2 ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
        WeightedL2Error ((N + 1 : ℕ) : ℝ)
          (fun n => NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n) ∧
        ∀ F : Finset ℤ,
          (∑ n ∈ F,
            (indexWeight n ^ (N + 1) *
              ‖NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n‖)^2) ≤ C^2 :=
  NlsGge.ThirdConsultation.KSPS025U8.midpoint_spectral_expansion_uniform_of26_24 N hN B₀ hB₀
    (h26_uniform N hN B₀ hB₀) h24

end
end NlsGge.ThirdConsultation.KSPS025U15
