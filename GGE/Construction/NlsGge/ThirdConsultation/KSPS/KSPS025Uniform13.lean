import Mathlib
import NlsGge.Atomic.KSPS.KSPS013
import NlsGge.ThirdConsultation.KSPS.KSPS016Uniform1
import NlsGge.ThirdConsultation.KSPS.KSPSAntitraceUniform
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform4
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform12

                                                                                                               
                                                                                                         
                                                                                                                
                                                                                                             
                                                                                                               
                                                                                                           
                                                                                                      
                                                                                                 
                                                 
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS025U13
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS
open NlsGge.ThirdConsultation.KSPSWKB

theorem entries_tail_uniform (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ (M : ℕ) (CE : ℝ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (upper : Bool) (i j : Fin 2) (F : Finset ℤ), (∀ n ∈ F, (M : ℤ) ≤ |n|) →
        ∑ n ∈ F, (indexWeight n ^ (N + 1) *
          ‖NlsGge.ThirdConsultation.KSPSWKB.endpointEntryError N φ upper i j n‖) ^ 2 ≤ CE := by
  obtain ⟨a, ha, hloc⟩ := NlsGge.ThirdConsultation.KSPS025U4.periodic_loc_uniform N hN B₀ hB₀
  have hKB : (0 : ℝ) ≤ 2 * B₀ := by positivity
  have hball : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ‖φ.1‖ + ‖φ.2‖ ≤ 2 * B₀ := fun φ hφ =>
    (NlsGge.ThirdConsultation.KSPSWKB.norm_fst_add_snd_le φ).trans (by linarith)
  have hone : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      sobolevNorm 1 (NlsGge.ThirdConsultation.KSPSU1.toOne hN φ) ≤ B₀ := fun φ hφ =>
    (NlsGge.ThirdConsultation.KSPSU1.sobolevNorm_toOne_le hN φ).trans hφ
  obtain ⟨NL, CL, -, hL⟩ := endpoint_remainder_tail_U hN (2 * B₀) B₀ hKB hB₀ false a ha
  obtain ⟨NU, CU, -, hU⟩ := endpoint_remainder_tail_U hN (2 * B₀) B₀ hKB hB₀ true a ha
  obtain ⟨N1, C1, -, h1⟩ := NlsGge.ThirdConsultation.KSPSUG.diag_lower_tail_U hN (2 * B₀) B₀ hKB hB₀ a ha
  obtain ⟨N2, C2, -, h2⟩ := NlsGge.ThirdConsultation.KSPSUG.diag_upper_tail_U hN (2 * B₀) B₀ hKB hB₀ a ha
  refine NlsGge.ThirdConsultation.KSPS025U12.entries_tail_of N hN B₀ hB₀ a ha hloc
    (NlsGge.ThirdConsultation.KSPSVolterra.threshold N B₀)
    (fun φ hφ => NlsGge.ThirdConsultation.KSPS016U.threshold_mono N hφ)
    (fun φ hφ => integrated_riccati_vanishing N (N + 1) φ ⟨by omega, le_rfl⟩)
    (((2 * Real.pi) ^ N) ^ 2 * B₀ ^ 2) ?_
    NL CL (fun φ hφ xi hxi F hF => hL φ (hball φ hφ) (NlsGge.ThirdConsultation.KSPSU1.toOne hN φ)
      (hone φ hφ) (NlsGge.ThirdConsultation.KSPSU1.toPotPair_toOne hN φ) xi hxi F hF)
    NU CU (fun φ hφ xi hxi F hF => hU φ (hball φ hφ) (NlsGge.ThirdConsultation.KSPSU1.toOne hN φ)
      (hone φ hφ) (NlsGge.ThirdConsultation.KSPSU1.toPotPair_toOne hN φ) xi hxi F hF)
    N1 C1 (fun φ hφ xi hxi F hF => h1 φ (hball φ hφ) (NlsGge.ThirdConsultation.KSPSU1.toOne hN φ)
      (hone φ hφ) (NlsGge.ThirdConsultation.KSPSU1.toPotPair_toOne hN φ) xi hxi F hF)
    N2 C2 (fun φ hφ xi hxi F hF => h2 φ (hball φ hφ) (NlsGge.ThirdConsultation.KSPSU1.toOne hN φ)
      (hone φ hφ) (NlsGge.ThirdConsultation.KSPSU1.toPotPair_toOne hN φ) xi hxi F hF)
  intro φ hφ F hF
  obtain ⟨hS1, hS2⟩ := NlsGge.ThirdConsultation.KSPS016U.fourier_sums_le φ hφ F
  have hν : ∀ n ∈ F, (1 : ℝ) ≤ |(n : ℝ)| := fun n hn => by
    have : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast hF n hn
    rw [Int.cast_abs] at this
    simpa using this
  refine ⟨(Finset.sum_le_sum (fun n hn => pow_le_pow_left₀ (norm_nonneg _)
      (NlsGge.ThirdConsultation.KSPS016U.deriv_fourier_le φ n (hν n hn)).1 2)).trans hS1,
    (Finset.sum_le_sum (fun n hn => pow_le_pow_left₀ (norm_nonneg _)
      (NlsGge.ThirdConsultation.KSPS016U.deriv_fourier_le φ n (hν n hn)).2 2)).trans hS2⟩

end
end NlsGge.ThirdConsultation.KSPS025U13
