import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS011Quant4
import NlsGge.ThirdConsultation.KSPS.KSPS011Quant5
import NlsGge.ThirdConsultation.KSPS.KSPS012Quant3
import NlsGge.ThirdConsultation.KSPS.KSPS012Quant4
import NlsGge.ThirdConsultation.KSPS.KSPS016Uniform1
import NlsGge.ThirdConsultation.KSPS.KSPSAntitraceCore
import NlsGge.ThirdConsultation.KSPS.KSPSUniformU1

/- KSPSAU PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/ThirdConsultation/KSPS/KSPSAntitraceUniform.lean. GLUE (exceeds the worker-lane memory cap; needs a
   ROOT MAIN PROBE). Discharges the explicit split hypotheses of the lane-verified cores by the landed producers:
   * KSPSUG.diag_approx_false_U / _true_U  := KSPS012Q3.diag_approx_*_U_of + KSPSWKB.sourceRemainder_endpoint_expansion_U;
   * KSPSUG.diag_lower_tail_U / _upper_tail_U := KSPS012Q4.diag_*_tail_of + the above (tail-uniform KSPS-012 e1/e2);
   * KSPSUG.boundary_characteristics_WKB_tail_U := KSPS016U.boundary_tail_of + KSPSWKB.endpoint_remainder_tail_U
     (b = false / true, φ' = KSPSU1.toOne) + the diag tails (KB = 2B₀, B = B₀);
   * KSPS.antitrace_at_dirichlet_uniform: Pro round 15 Q5 head (PRO_DEFINITION_RESPONSE_FP80_15.md, followup13),
     VERBATIM; proof KSPSAT.antitrace_of + KSPSU1.mu_localization_uniform + the KSPS-016 tail at ξ = μ.
   No hypothesis added to the Pro head. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.Schur NlsGge.Analysis NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSUG
open NlsGge.ThirdConsultation.KSPSWKB

theorem diag_approx_false_U {N : ℕ} (hN : 1 ≤ N) (KB B : ℝ) (hKB : 0 ≤ KB) (hB : 0 ≤ B)
    (a : ℝ) (ha : 0 ≤ a) :
    ∃ C L : ℝ, 0 ≤ C ∧ 1 ≤ L ∧ ∀ φ : SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ KB →
      ∀ φ' : SobolevC 1, sobolevNorm 1 φ' ≤ B →
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = toPotPair φ →
      ∀ lam : {z : ℂ // z ≠ 0}, L ≤ ‖lam.1‖ → |lam.1.im| ≤ a →
      ‖sourceRemainderVector φ false lam 1 0 -
        (-Complex.exp (-(2 * Complex.I * lam.1)) * endpointOsc lam.1 (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * lam.1 * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ'.1) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) t))‖ ≤
        C / ‖lam.1‖ ^ 2 := by
  obtain ⟨C8, L8, hC8, hL8, h8⟩ := sourceRemainder_endpoint_expansion_U hN KB B hKB hB a ha
  exact NlsGge.ThirdConsultation.KSPS012Q3.diag_approx_false_U_of hN KB B hKB hB a ha C8 L8 hC8 hL8 h8

theorem diag_approx_true_U {N : ℕ} (hN : 1 ≤ N) (KB B : ℝ) (hKB : 0 ≤ KB) (hB : 0 ≤ B)
    (a : ℝ) (ha : 0 ≤ a) :
    ∃ C L : ℝ, 0 ≤ C ∧ 1 ≤ L ∧ ∀ φ : SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ KB →
      ∀ φ' : SobolevC 1, sobolevNorm 1 φ' ≤ B →
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = toPotPair φ →
      ∀ lam : {z : ℂ // z ≠ 0}, L ≤ ‖lam.1‖ → |lam.1.im| ≤ a →
      ‖sourceRemainderVector φ true lam 1 1 -
        (-Complex.exp (-(2 * Complex.I * (-lam.1))) * endpointOsc (-lam.1) (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * (-lam.1) * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ'.2) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) t))‖ ≤
        C / ‖lam.1‖ ^ 2 := by
  obtain ⟨C8, L8, hC8, hL8, h8⟩ := sourceRemainder_endpoint_expansion_U hN KB B hKB hB a ha
  exact NlsGge.ThirdConsultation.KSPS012Q3.diag_approx_true_U_of hN KB B hKB hB a ha C8 L8 hC8 hL8 h8

/-- tail-uniform KSPS-012 lower diagonal remainder e1 = w·(endpointDiagonalLower − (−1)^n/(2iξ) I_{N+1}) -/
theorem diag_lower_tail_U {N : ℕ} (hN : 1 ≤ N) (KB B : ℝ) (hKB : 0 ≤ KB) (hB : 0 ≤ B)
    (a : ℝ) (ha : 0 ≤ a) :
    ∃ (N0 : ℕ) (Ct : ℝ), 0 ≤ Ct ∧ ∀ φ : SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ KB →
      ∀ φ' : SobolevC 1, sobolevNorm 1 φ' ≤ B →
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = toPotPair φ →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (N0 : ℤ) ≤ |n|) →
      ∑ n ∈ F, ‖(indexWeight n : ℂ) *
        (endpointDiagonalLower N φ xi n -
          (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1))‖ ^ 2 ≤ Ct := by
  obtain ⟨C, L, hC, hL1, hap⟩ := diag_approx_false_U hN KB B hKB hB a ha
  exact NlsGge.ThirdConsultation.KSPS012Q4.diag_lower_tail_of hN KB B hKB hB a ha C L hC hL1 hap

/-- tail-uniform KSPS-012 upper diagonal remainder e2 = w·(endpointDiagonalUpper − (−1)^{n+1}/(2iξ) J_{N+1}) -/
theorem diag_upper_tail_U {N : ℕ} (hN : 1 ≤ N) (KB B : ℝ) (hKB : 0 ≤ KB) (hB : 0 ≤ B)
    (a : ℝ) (ha : 0 ≤ a) :
    ∃ (N0 : ℕ) (Ct : ℝ), 0 ≤ Ct ∧ ∀ φ : SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ KB →
      ∀ φ' : SobolevC 1, sobolevNorm 1 φ' ≤ B →
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = toPotPair φ →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (N0 : ℤ) ≤ |n|) →
      ∑ n ∈ F, ‖(indexWeight n : ℂ) *
        (endpointDiagonalUpper N φ xi n -
          (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) * integralRiccatiRight φ (N + 1))‖ ^ 2 ≤ Ct := by
  obtain ⟨C, L, hC, hL1, hap⟩ := diag_approx_true_U hN KB B hKB hB a ha
  exact NlsGge.ThirdConsultation.KSPS012Q4.diag_upper_tail_of hN KB B hKB hB a ha C L hC hL1 hap

/-- ball-uniform TAIL form of KSPS-016 (proof development's U2 restricted to |n| ≥ N0) -/
theorem boundary_characteristics_WKB_tail_U (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀)
    (a : ℝ) (ha : 0 ≤ a) :
    ∃ (N0 : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (N0 : ℤ) ≤ |n|) →
        (∑ n ∈ F, (indexWeight n ^ (N + 1) * ‖KSPSWKB.antitraceError N φ xi n‖) ^ 2 ≤ C) ∧
        (∑ n ∈ F, (indexWeight n ^ (N + 1) * ‖KSPSWKB.dirichletError N φ xi n‖) ^ 2 ≤ C) := by
  have hKB : (0 : ℝ) ≤ 2 * B₀ := by positivity
  have hball : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ‖φ.1‖ + ‖φ.2‖ ≤ 2 * B₀ := fun φ hφ =>
    (norm_fst_add_snd_le φ).trans (by linarith)
  have hone : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      sobolevNorm 1 (NlsGge.ThirdConsultation.KSPSU1.toOne hN φ) ≤ B₀ := fun φ hφ =>
    (NlsGge.ThirdConsultation.KSPSU1.sobolevNorm_toOne_le hN φ).trans hφ
  obtain ⟨NL, CL, hCL, hL⟩ := endpoint_remainder_tail_U hN (2 * B₀) B₀ hKB hB₀ false a ha
  obtain ⟨NU, CU, hCU, hU⟩ := endpoint_remainder_tail_U hN (2 * B₀) B₀ hKB hB₀ true a ha
  obtain ⟨N1, C1, hC1, h1⟩ := diag_lower_tail_U hN (2 * B₀) B₀ hKB hB₀ a ha
  obtain ⟨N2, C2, hC2, h2⟩ := diag_upper_tail_U hN (2 * B₀) B₀ hKB hB₀ a ha
  exact NlsGge.ThirdConsultation.KSPS016U.boundary_tail_of N hN B₀ hB₀ a ha
    NL CL hCL (fun φ hφ xi hxi F hF => hL φ (hball φ hφ) (NlsGge.ThirdConsultation.KSPSU1.toOne hN φ)
      (hone φ hφ) (NlsGge.ThirdConsultation.KSPSU1.toPotPair_toOne hN φ) xi hxi F hF)
    NU CU hCU (fun φ hφ xi hxi F hF => hU φ (hball φ hφ) (NlsGge.ThirdConsultation.KSPSU1.toOne hN φ)
      (hone φ hφ) (NlsGge.ThirdConsultation.KSPSU1.toPotPair_toOne hN φ) xi hxi F hF)
    N1 C1 hC1 (fun φ hφ xi hxi F hF => h1 φ (hball φ hφ) (NlsGge.ThirdConsultation.KSPSU1.toOne hN φ)
      (hone φ hφ) (NlsGge.ThirdConsultation.KSPSU1.toPotPair_toOne hN φ) xi hxi F hF)
    N2 C2 hC2 (fun φ hφ xi hxi F hF => h2 φ (hball φ hφ) (NlsGge.ThirdConsultation.KSPSU1.toOne hN φ)
      (hone φ hφ) (NlsGge.ThirdConsultation.KSPSU1.toPotPair_toOne hN φ) xi hxi F hF)

end NlsGge.ThirdConsultation.KSPSUG

namespace NlsGge.ThirdConsultation.KSPS

theorem antitrace_at_dirichlet_uniform
    (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
        WeightedL2Error ((N + 1 : ℕ) : ℝ)
          (fun n => KSPSWKB.antitrace φ (mu φ n) -
            Complex.I * (-1 : ℂ)^n *
              (physicalFourier (toPotPair φ).1 (-n) -
               physicalFourier (toPotPair φ).2 n)) ∧
        ∀ F : Finset ℤ,
          (∑ n ∈ F,
            (indexWeight n ^ (N + 1) *
              ‖KSPSWKB.antitrace φ (mu φ n) -
                Complex.I * (-1 : ℂ)^n *
                  (physicalFourier (toPotPair φ).1 (-n) -
                   physicalFourier (toPotPair φ).2 n)‖)^2) ≤ C^2 := by
  obtain ⟨a, ha, hmu⟩ := NlsGge.ThirdConsultation.KSPSU1.mu_localization_uniform N hN B₀ hB₀
  obtain ⟨N0, CT, hCT, hT⟩ :=
    NlsGge.ThirdConsultation.KSPSUG.boundary_characteristics_WKB_tail_U N hN B₀ hB₀ a ha
  exact NlsGge.ThirdConsultation.KSPSAT.antitrace_of N hN B₀ hB₀ a ha hmu N0 CT hCT
    (fun φ hφ F hF => hT φ hφ (mu φ) (hmu φ hφ) F hF)

end NlsGge.ThirdConsultation.KSPS
