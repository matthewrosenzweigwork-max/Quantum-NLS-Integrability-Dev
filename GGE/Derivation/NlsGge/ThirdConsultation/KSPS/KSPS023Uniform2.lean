import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPSUniformU1
import NlsGge.ThirdConsultation.KSPS.KSPS016Uniform1
import NlsGge.ThirdConsultation.KSPS.KSPSAntitraceUniform
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform5
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform6
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform9
import NlsGge.ThirdConsultation.KSPS.KSPS023Uniform1

/- KSPS023U2 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). GLUE (root main probe: the joint
   closure contains KSPSAntitraceUniform, above the worker-lane memory cap).
   Target NlsGge/ThirdConsultation/KSPS/KSPS023Uniform2.lean. Pro round-15 SUPPORT (never a packet), chain B.
   dirichlet_spectral_expansion_uniform: ball-uniform KSPS-023 companion (Pro's finite-sum uniform style, ALL labels,
   one constant C before φ), UNCONDITIONAL: KSPS023U.dirichlet_uniform_of with
     hloc0 = KSPSU1.mu_localization_uniform; hconst0 = KSPS025U5.riccati_consts_uniform (Jsum, Lsum, I_(N+1) parts);
     hgerm0 = KSPS025U9.germ_uniform; hsp0 = KSPS025U6.spectralPolynomial_sub_le;
     hthr = KSPS016U.threshold_mono at B₀; hSb = KSPS016U.Sb_le; hfour = KSPS016U.deriv_fourier_le + fourier_sums_le
     (exactly as in KSPS025U13); hD16 = the Dirichlet conjunct of KSPSUG.boundary_characteristics_WKB_tail_U at ξ = μ
     (localization from the same KSPSU1.mu_localization_uniform). -/
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS023U
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation.KSPS

theorem dirichlet_spectral_expansion_uniform (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
        WeightedL2Error ((N + 1 : ℕ) : ℝ)
          (fun n => mu φ n - spectralPolynomial φ n -
            (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2) ∧
        ∀ F : Finset ℤ,
          (∑ n ∈ F,
            (indexWeight n ^ (N + 1) *
              ‖mu φ n - spectralPolynomial φ n -
                (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2‖) ^ 2) ≤ C ^ 2 := by
  obtain ⟨a, ha, hmu⟩ := NlsGge.ThirdConsultation.KSPSU1.mu_localization_uniform N hN B₀ hB₀
  obtain ⟨N0, CD, -, hT⟩ :=
    NlsGge.ThirdConsultation.KSPSUG.boundary_characteristics_WKB_tail_U N hN B₀ hB₀ a ha
  obtain ⟨L, hL, hLb⟩ := NlsGge.ThirdConsultation.KSPS025U5.riccati_consts_uniform N hN B₀ hB₀
  refine dirichlet_uniform_of N hN B₀ hB₀ ⟨a, ha, hmu⟩
    ⟨L, hL, fun φ hφ => ⟨(hLb φ hφ).1, (hLb φ hφ).2.2.1, (hLb φ hφ).2.2.2⟩⟩
    (NlsGge.ThirdConsultation.KSPS025U9.germ_uniform N hN B₀ hB₀)
    (NlsGge.ThirdConsultation.KSPS025U6.spectralPolynomial_sub_le N hN B₀ hB₀)
    (NlsGge.ThirdConsultation.KSPSVolterra.threshold N B₀)
    (fun φ hφ => NlsGge.ThirdConsultation.KSPS016U.threshold_mono N hφ)
    (∑ k ∈ Finset.Icc 1 N, NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B₀ k)
    (fun φ hφ => NlsGge.ThirdConsultation.KSPS016U.Sb_le φ hφ)
    (((2 * Real.pi) ^ N) ^ 2 * B₀ ^ 2) ?_
    ⟨N0, CD, fun φ hφ F hF => (hT φ hφ (mu φ) (hmu φ hφ) F hF).2⟩
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
end NlsGge.ThirdConsultation.KSPS023U
