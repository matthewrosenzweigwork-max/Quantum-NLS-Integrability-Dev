import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS017Uniform1
import NlsGge.ThirdConsultation.KSPS.KSPS017Uniform2
import NlsGge.ThirdConsultation.KSPS.KSPS012Support6
import NlsGge.ThirdConsultation.KSPS.KSPS003Support2
import NlsGge.ThirdConsultation.KSPS.KSPSUniformU3
import NlsGge.ThirdConsultation.KSPS.KSPS012Host

                                                                                 
                                                                                                                
                                                                                                                    
                                                                                 
                                                                                                                  
                                                                                                               
                                                                                                                                                 
                                                                                                           
                                                      
                                                                                         
                                                                                                           
                                                                                                                
                                                                                                      
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace NlsGge.ThirdConsultation.KSPS017U5
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign NlsGge.Atomic.Common
open NlsGge.ThirdConsultation.KSPS NlsGge.ThirdConsultation.KSPS017W

theorem norm_pair_le {N : ℕ} (φ : SobolevC N) : ‖φ.1‖ + ‖φ.2‖ ≤ 2 * sobolevNorm N φ := by
  have h1 := NlsGge.ThirdConsultation.KSPSU3.norm_fst_le N φ
  have h2 := NlsGge.ThirdConsultation.KSPSU3.norm_snd_le N φ
  linarith

theorem coef_top_le {N : ℕ} (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∀ b : Bool,
      ‖NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)‖ ≤ D := by
  obtain ⟨D, hD0, hTop⟩ := NlsGge.ThirdConsultation.KSPSSupport.h161_coef_top N hN (2 * B₀) (by positivity)
  refine ⟨D, hD0, fun φ hφ b => ?_⟩
  have hS : ‖φ.1‖ + ‖φ.2‖ ≤ 2 * B₀ := (norm_pair_le φ).trans (by linarith)
  have h := hTop φ hS b
  rw [Nat.sub_self, Nat.cast_zero, NlsGge.ThirdConsultation.KSPSSupport.h161_norm_eq_psn0] at h
  exact h

/-- Generic diagonal instantiation (strip bound already in Pdiag form). -/
theorem diag_core {N : ℕ} (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) (b : Bool) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1)
    (a : ℝ) (ha : 0 ≤ a) (C L : ℝ) (hC : 0 ≤ C) (hL : 1 ≤ L)
    (hone : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∃ φ' : SobolevC 1, sobolevNorm 1 φ' ≤ B₀ ∧
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = toPotPair φ)
    (hstrip : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∀ φ' : SobolevC 1, sobolevNorm 1 φ' ≤ B₀ →
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = toPotPair φ →
      ∀ z : ℂ, ∀ hz : z ≠ 0, L ≤ ‖z‖ → |z.im| ≤ a + 1 →
      ‖NlsGge.ThirdConsultation.KSPSWKB.sourceRemainderVector φ b ⟨z, hz⟩ 1 (if b then 1 else 0) -
        Pdiag σ (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)))
          (coverRep38 (physicalSobolevDerivative38 1 (if b then φ'.2 else φ'.1)))
          (sobolevPointValue 1 (if b then φ'.2 else φ'.1) 1)
          (∫ t in (0 : ℝ)..1, coverRep38 (physicalSobolevEmbed 1 (if b then φ'.2 else φ'.1)) t *
            coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) t) z‖ ≤ C / ‖z‖ ^ 2) :
    ∃ (ND : ℕ) (K : ℝ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (g : ℂ → ℂ), (∀ z : ℂ, z ≠ 0 → DifferentiableAt ℂ g z) →
      (∀ (z : ℂ) (hz : z ≠ 0), g z = NlsGge.ThirdConsultation.KSPSWKB.sourceRemainderVector φ b ⟨z, hz⟩ 1 (if b then 1 else 0)) →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (ND : ℤ) ≤ |n|) →
      ∑ n ∈ F, (indexWeight n * ‖deriv g (xi n) -
        -Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) *
          (if b then integralRiccatiRight φ (N + 1) else integralRiccatiLeft φ (N + 1))‖) ^ 2 ≤ K := by
  obtain ⟨D, hD0, hD⟩ := coef_top_le hN B₀ hB₀
  obtain ⟨K, -, hK⟩ := NlsGge.ThirdConsultation.KSPS017U1.diag_deriv_tail_U σ hσ a ha C L hC hL
    (‖iotaCLM‖ * B₀) ((B₀ ^ 2 + D ^ 2) / 2) (D ^ 2) (‖derivCLM‖ * B₀) (by positivity) (by positivity)
    (by positivity) (by positivity)
  refine ⟨⌈2 * a + L + 2⌉₊, K, fun φ hφ g hgd hge xi hxi F hF => ?_⟩
  obtain ⟨φ', hφ'B, hφ'⟩ := hone φ hφ
  set u : PhysicalSobolev38 ((1 : ℕ) : ℝ) := if b then φ'.2 else φ'.1 with hudef
  set c : PhysicalL2 := NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1) with hcdef
  have hu : ‖u‖ ≤ B₀ := by
    cases b
    · exact (NlsGge.ThirdConsultation.KSPSU3.norm_fst_le 1 φ').trans hφ'B
    · exact (NlsGge.ThirdConsultation.KSPSU3.norm_snd_le 1 φ').trans hφ'B
  have hc : ‖c‖ ≤ D := hD φ hφ b
  have hJ : (∫ t in (0 : ℝ)..1, coverRep38 (physicalSobolevEmbed 1 u) t * coverRep38 c t) =
      (if b then integralRiccatiRight φ (N + 1) else integralRiccatiLeft φ (N + 1)) := by
    cases b
    · simp only [hudef, hcdef, Bool.false_eq_true, ↓reduceIte]
      rw [NlsGge.ThirdConsultation.KSPSU3.integralRiccatiLeft_eq_cover, ← hφ']; rfl
    · simp only [hudef, hcdef, ↓reduceIte]
      show _ = ∫ x in (0 : ℝ)..1, coverRep38 (toPotPair φ).2 x *
        coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) x
      rw [← hφ']; rfl
  have hJb : ‖∫ t in (0 : ℝ)..1, coverRep38 (physicalSobolevEmbed 1 u) t * coverRep38 c t‖ ≤
      (B₀ ^ 2 + D ^ 2) / 2 := by
    refine (NlsGge.ThirdConsultation.KSPSSupport.h161_prefix_le (physicalSobolevEmbed 1 u) c
      ⟨zero_le_one, le_rfl⟩).trans ?_
    have h1 : ‖physicalSobolevEmbed 1 u‖ ≤ B₀ :=
      (NlsGge.ThirdConsultation.KSPSSupport.h161_embed_norm_le 1 u).trans hu
    have h1s := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h2s := pow_le_pow_left₀ (norm_nonneg _) hc 2
    linarith
  have hpv : ‖sobolevPointValue 1 u 1‖ ≤ ‖iotaCLM‖ * B₀ :=
    (NlsGge.ThirdConsultation.KSPS003Support2.pv_sup u 1).trans
      (mul_le_mul_of_nonneg_left hu (by positivity))
  have hLd : ∫ s in (0 : ℝ)..1, ‖coverRep38 (physicalSobolevDerivative38 1 u) s‖ ≤ ‖derivCLM‖ * B₀ :=
    (NlsGge.ThirdConsultation.KSPS003Support2.deriv_L1 u).trans
      (mul_le_mul_of_nonneg_left hu (by positivity))
  have hCc : ∫ t in (0 : ℝ)..1, ‖coverRep38 c t‖ ^ 2 ≤ D ^ 2 := by
    rw [integral_sq_coverRep38_one]; exact pow_le_pow_left₀ (norm_nonneg _) hc 2
  have happ : ∀ z : ℂ, z ≠ 0 → L ≤ ‖z‖ → |z.im| ≤ a + 1 →
      ‖g z - Pdiag σ (coverRep38 c) (coverRep38 (physicalSobolevDerivative38 1 u))
        (sobolevPointValue 1 u 1)
        (∫ t in (0 : ℝ)..1, coverRep38 (physicalSobolevEmbed 1 u) t * coverRep38 c t) z‖ ≤ C / ‖z‖ ^ 2 := by
    intro z hz hzL him
    rw [hge z hz]
    exact hstrip φ hφ φ' hφ'B hφ' z hz hzL him
  have res := hK (coverRep38 c) (coverRep38 (physicalSobolevDerivative38 1 u))
    (NlsGge.ThirdConsultation.KSPSSupport.coverRep38_memLp_Icc c)
    (stronglyMeasurable_coverRep38 _).aestronglyMeasurable (intervalIntegrable_coverRep38_sq_one _)
    (intervalIntegrable_coverRep38_one _) hCc hLd (sobolevPointValue 1 u 1)
    (∫ t in (0 : ℝ)..1, coverRep38 (physicalSobolevEmbed 1 u) t * coverRep38 c t) hpv hJb
    xi hxi g hgd happ F hF
  rw [hJ] at res
  exact res

/-- Ball-uniform S017-2, lower diagonal (b = false), from the KSPSUG.diag_approx_false_U body. -/
theorem diag_tail_false_of {N : ℕ} (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) (a : ℝ) (ha : 0 ≤ a)
    (hone : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∃ φ' : SobolevC 1, sobolevNorm 1 φ' ≤ B₀ ∧
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = toPotPair φ)
    (C L : ℝ) (hC : 0 ≤ C) (hL : 1 ≤ L)
    (hap : ∀ φ : SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ 2 * B₀ →
      ∀ φ' : SobolevC 1, sobolevNorm 1 φ' ≤ B₀ →
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = toPotPair φ →
      ∀ lam : {z : ℂ // z ≠ 0}, L ≤ ‖lam.1‖ → |lam.1.im| ≤ a + 1 →
      ‖NlsGge.ThirdConsultation.KSPSWKB.sourceRemainderVector φ false lam 1 0 -
        (-Complex.exp (-(2 * Complex.I * lam.1)) * NlsGge.ThirdConsultation.KSPSWKB.endpointOsc lam.1 (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * lam.1 * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ'.1) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) t))‖ ≤
        C / ‖lam.1‖ ^ 2) :
    ∃ (ND : ℕ) (K : ℝ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (g : ℂ → ℂ), (∀ z : ℂ, z ≠ 0 → DifferentiableAt ℂ g z) →
      (∀ (z : ℂ) (hz : z ≠ 0), g z = NlsGge.ThirdConsultation.KSPSWKB.sourceRemainderVector φ false ⟨z, hz⟩ 1 0) →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (ND : ℤ) ≤ |n|) →
      ∑ n ∈ F, (indexWeight n * ‖deriv g (xi n) -
        -Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1)‖) ^ 2 ≤ K := by
  obtain ⟨ND, K, h⟩ := diag_core hN B₀ hB₀ false 1 (Or.inl rfl) a ha C L hC hL hone (by
    intro φ hφ φ' hφ'B hφ' z hz hzL him
    have hS : ‖φ.1‖ + ‖φ.2‖ ≤ 2 * B₀ := (norm_pair_le φ).trans (by linarith)
    have hcore := NlsGge.ThirdConsultation.KSPSWKB.core_decomp φ'.1 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) hz
    have hb := hap φ hS φ' hφ'B hφ' ⟨z, hz⟩ hzL him
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hcore] at hb
    refine le_of_eq_of_le ?_ hb
    unfold Pdiag
    congr 2
    simp only [Int.cast_one, one_mul]
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring)
  refine ⟨ND, K, fun φ hφ g hgd hge xi hxi F hF => ?_⟩
  have := h φ hφ g hgd (by simpa using hge) xi hxi F hF
  simpa using this

/-- Ball-uniform S017-2, upper diagonal (b = true), from the KSPSUG.diag_approx_true_U body. -/
theorem diag_tail_true_of {N : ℕ} (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) (a : ℝ) (ha : 0 ≤ a)
    (hone : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∃ φ' : SobolevC 1, sobolevNorm 1 φ' ≤ B₀ ∧
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = toPotPair φ)
    (C L : ℝ) (hC : 0 ≤ C) (hL : 1 ≤ L)
    (hap : ∀ φ : SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ 2 * B₀ →
      ∀ φ' : SobolevC 1, sobolevNorm 1 φ' ≤ B₀ →
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = toPotPair φ →
      ∀ lam : {z : ℂ // z ≠ 0}, L ≤ ‖lam.1‖ → |lam.1.im| ≤ a + 1 →
      ‖NlsGge.ThirdConsultation.KSPSWKB.sourceRemainderVector φ true lam 1 1 -
        (-Complex.exp (-(2 * Complex.I * (-lam.1))) * NlsGge.ThirdConsultation.KSPSWKB.endpointOsc (-lam.1) (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * (-lam.1) * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ'.2) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) t))‖ ≤
        C / ‖lam.1‖ ^ 2) :
    ∃ (ND : ℕ) (K : ℝ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (g : ℂ → ℂ), (∀ z : ℂ, z ≠ 0 → DifferentiableAt ℂ g z) →
      (∀ (z : ℂ) (hz : z ≠ 0), g z = NlsGge.ThirdConsultation.KSPSWKB.sourceRemainderVector φ true ⟨z, hz⟩ 1 1) →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (ND : ℤ) ≤ |n|) →
      ∑ n ∈ F, (indexWeight n * ‖deriv g (xi n) -
        -Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiRight φ (N + 1)‖) ^ 2 ≤ K := by
  obtain ⟨ND, K, h⟩ := diag_core hN B₀ hB₀ true (-1) (Or.inr rfl) a ha C L hC hL hone (by
    intro φ hφ φ' hφ'B hφ' z hz hzL him
    have hS : ‖φ.1‖ + ‖φ.2‖ ≤ 2 * B₀ := (norm_pair_le φ).trans (by linarith)
    have hz' : -z ≠ 0 := neg_ne_zero.2 hz
    have hcore := NlsGge.ThirdConsultation.KSPSWKB.core_decomp φ'.2 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) hz'
    have hb := hap φ hS φ' hφ'B hφ' ⟨z, hz⟩ hzL him
    simp only [↓reduceIte]
    rw [hcore] at hb
    refine le_of_eq_of_le ?_ hb
    unfold Pdiag
    congr 2
    simp only [Int.cast_neg, Int.cast_one, neg_one_mul]
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring)
  refine ⟨ND, K, fun φ hφ g hgd hge xi hxi F hF => ?_⟩
  have := h φ hφ g hgd (by simpa using hge) xi hxi F hF
  simpa using this

/-- Ball-uniform S017-3 for component idx_b, from the KSPS017U3.off_approx_U_of conclusion body. -/
theorem off_tail_of {N : ℕ} (B₀ : ℝ) (b : Bool) (a : ℝ) (ha : 0 ≤ a)
    (hone : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∃ φ' : SobolevC 1, sobolevNorm 1 φ' ≤ B₀ ∧
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = toPotPair φ)
    (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ‖NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)‖ ≤ D)
    (C L : ℝ) (hC : 0 ≤ C) (hL : 1 ≤ L)
    (happ : ∀ φ : SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ 2 * B₀ →
      ∀ φ' : SobolevC 1, sobolevNorm 1 φ' ≤ B₀ →
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = toPotPair φ →
      ∀ lam : {z : ℂ // z ≠ 0}, L ≤ ‖lam.1‖ → |lam.1.im| ≤ a + 1 →
      ‖NlsGge.ThirdConsultation.KSPSWKB.sourceRemainderVector φ b lam 1 (if b then 0 else 1) -
        (if b then -Complex.I else Complex.I) *
          NlsGge.ThirdConsultation.KSPSWKB.endpointOsc ((if b then (-1 : ℂ) else 1) * lam.1)
            (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)))‖ ≤ C / ‖lam.1‖) :
    ∃ (NO : ℕ) (K : ℝ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (g : ℂ → ℂ), (∀ z : ℂ, z ≠ 0 → DifferentiableAt ℂ g z) →
      (∀ (z : ℂ) (hz : z ≠ 0), g z = NlsGge.ThirdConsultation.KSPSWKB.sourceRemainderVector φ b ⟨z, hz⟩ 1 (if b then 0 else 1)) →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (NO : ℤ) ≤ |n|) →
      ∑ n ∈ F, ‖deriv g (xi n)‖ ^ 2 ≤ K := by
  obtain ⟨K, -, hK⟩ := NlsGge.ThirdConsultation.KSPS017U2.offdiag_deriv_tail_U b a ha C L hC hL (D ^ 2)
    (by positivity)
  refine ⟨⌈2 * a + L + 2⌉₊, K, fun φ hφ g hgd hge xi hxi F hF => ?_⟩
  obtain ⟨φ', hφ'B, hφ'⟩ := hone φ hφ
  have hS : ‖φ.1‖ + ‖φ.2‖ ≤ 2 * B₀ := (norm_pair_le φ).trans (by linarith)
  set c : PhysicalL2 := NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1) with hcdef
  have hCc : ∫ t in (0 : ℝ)..1, ‖coverRep38 c t‖ ^ 2 ≤ D ^ 2 := by
    rw [integral_sq_coverRep38_one]; exact pow_le_pow_left₀ (norm_nonneg _) (hD φ hφ) 2
  exact hK (coverRep38 c) (NlsGge.ThirdConsultation.KSPSSupport.coverRep38_memLp_Icc c)
    (stronglyMeasurable_coverRep38 _).aestronglyMeasurable (intervalIntegrable_coverRep38_sq_one _) hCc
    xi hxi g hgd (fun z hz hzL him => by
      rw [hge z hz]; exact happ φ hS φ' hφ'B hφ' ⟨z, hz⟩ hzL him) F hF

end
end NlsGge.ThirdConsultation.KSPS017U5
