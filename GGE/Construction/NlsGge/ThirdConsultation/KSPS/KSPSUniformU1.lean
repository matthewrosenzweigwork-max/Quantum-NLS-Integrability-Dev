import Mathlib
import NlsGge.Atomic.KSN.KSN012Sup6
import NlsGge.ThirdConsultation.KSPS.KSPS011Support4

                                                                              
                                                                                                  
                                                                                                               
                                                                                                               
                                                                                                                
                                                                                                               
                                                                                                                   
                                                                            
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPSU1
noncomputable section
open NlsGge.ThirdConsultation.KSPS

/-- the order-one image of an order-N potential (same body as KSPS011Support4.exists_toPair_eq's witness) -/
def toOne {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) : SobolevC 1 :=
  (NlsGge.Atomic.LIB008.physicalSobolevSequenceInclusion (N : ℝ) ((1 : ℕ) : ℝ)
      (by exact_mod_cast hN) φ.1,
    NlsGge.Atomic.LIB008.physicalSobolevSequenceInclusion (N : ℝ) ((1 : ℕ) : ℝ)
      (by exact_mod_cast hN) φ.2)

theorem toPotPair_toOne {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) :
    toPotPair (toOne hN φ) = toPotPair φ := by
  unfold toOne toPotPair
  simp only [NlsGge.ThirdConsultation.KSPS011Support4.embed_inclusion hN]

theorem sobolevNorm_toOne_le {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) :
    sobolevNorm 1 (toOne hN φ) ≤ sobolevNorm N φ := by
  unfold sobolevNorm toOne
  apply Real.sqrt_le_sqrt
  have h1 := NlsGge.Atomic.LIB008.physicalSobolevSequenceInclusion_norm_le (N : ℝ) ((1 : ℕ) : ℝ)
      (by exact_mod_cast hN) φ.1
  have h2 := NlsGge.Atomic.LIB008.physicalSobolevSequenceInclusion_norm_le (N : ℝ) ((1 : ℕ) : ℝ)
      (by exact_mod_cast hN) φ.2
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) h1 2) (pow_le_pow_left₀ (norm_nonneg _) h2 2)

theorem mu_toOne {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (n : ℤ) : mu (toOne hN φ) n = mu φ n := by
  unfold mu; rw [toPotPair_toOne]

theorem crit_toOne {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (n : ℤ) :
    criticalEigenvalue (toOne hN φ) n = criticalEigenvalue φ n := by
  unfold criticalEigenvalue; rw [toPotPair_toOne]

theorem loc_uniform (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∀ n : ℤ,
      ‖mu φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n ∧
      ‖criticalEigenvalue φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n := by
  obtain ⟨a, ha, h⟩ := NlsGge.ThirdConsultation.KSN012U.sup6_unif_loc (B₀ + 1) (by linarith)
  refine ⟨a, ha, fun φ hφ n => ?_⟩
  have h1 := h (toOne hN φ) (by linarith [sobolevNorm_toOne_le hN φ]) n
  rw [mu_toOne, crit_toOne] at h1
  exact h1

theorem mu_localization_uniform (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ n : ℤ, ‖mu φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n := by
  obtain ⟨a, ha, h⟩ := loc_uniform N hN B₀ hB₀
  exact ⟨a, ha, fun φ hφ n => (h φ hφ n).1⟩

theorem crit_localization_uniform (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ n : ℤ, ‖criticalEigenvalue φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n := by
  obtain ⟨a, ha, h⟩ := loc_uniform N hN B₀ hB₀
  exact ⟨a, ha, fun φ hφ n => (h φ hφ n).2⟩

end
end NlsGge.ThirdConsultation.KSPSU1
