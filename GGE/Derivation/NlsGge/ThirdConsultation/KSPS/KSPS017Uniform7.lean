import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS017Uniform6
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform1
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform3
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform15
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform16

/- KSPS017U7 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). WRAPPER (root main probe).
   Target NlsGge/ThirdConsultation/KSPS/KSPS017Uniform7.lean, namespace NlsGge.ThirdConsultation.KSPS.
   Pro round-15 heads VERBATIM from root/gpt6pro_followup13/handoff/definitions_design_20261027/STATEMENTS/KSPS.md
   (request pin cc702018; the newest source touching them): midpoint_spectral_expansion_uniform,
   midpoint_first_order_uniform, midpoint_dirichlet_difference_uniform. The exact names were grepped in NlsGge at
   HEAD 177eb8cca: no landed declaration takes any of them (first_two_spectral_coefficients_bounded is landed in
   KSPS025Uniform1 and is reused, not restated). Pro marks these as support additions (no packet increment).
   Proofs: KSPS025U15.midpoint_spectral_expansion_uniform_of24 / KSPS025U16.midpoint_dirichlet_difference_uniform_of24
   applied to KSPS017U6.h24_uniform; KSPS025U3.midpoint_first_order_uniform_of applied to the first head and the
   landed first_two_spectral_coefficients_bounded (Pro's own route, F = {k}). No hypothesis added; no repair. -/
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section
open NlsGge.Pilot NlsGge.GK38

theorem midpoint_spectral_expansion_uniform
    (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
        WeightedL2Error ((N + 1 : ℕ) : ℝ)
          (fun n => midpoint φ n - spectralPolynomial φ n) ∧
        ∀ F : Finset ℤ,
          (∑ n ∈ F,
            (indexWeight n ^ (N + 1) *
              ‖midpoint φ n - spectralPolynomial φ n‖)^2) ≤ C^2 :=
  NlsGge.ThirdConsultation.KSPS025U15.midpoint_spectral_expansion_uniform_of24 N hN B₀ hB₀
    (NlsGge.ThirdConsultation.KSPS017U6.h24_uniform N hN B₀ hB₀)

theorem midpoint_first_order_uniform
    (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ B : ℝ, 0 < B ∧
      ∀ φ : SobolevC 1, sobolevNorm 1 φ ≤ B₀ →
        ‖massCoefficient φ‖ ≤ B ∧
        ∀ k : ℤ, k ≠ 0 →
          ‖midpoint φ k - (k : ℂ) * Real.pi -
            massCoefficient φ / (k : ℂ)‖ ≤
              B / (k.natAbs : ℝ)^2 :=
  NlsGge.ThirdConsultation.KSPS025U3.midpoint_first_order_uniform_of
    NlsGge.ThirdConsultation.KSPS.midpoint_spectral_expansion_uniform
    NlsGge.ThirdConsultation.KSPS.first_two_spectral_coefficients_bounded B₀ hB₀

theorem midpoint_dirichlet_difference_uniform
    (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
        WeightedL2Error ((N + 1 : ℕ) : ℝ)
          (fun n => midpoint φ n - mu φ n +
            (physicalFourier (toPotPair φ).1 (-n) +
             physicalFourier (toPotPair φ).2 n) / 2) ∧
        ∀ F : Finset ℤ,
          (∑ n ∈ F,
            (indexWeight n ^ (N + 1) *
              ‖midpoint φ n - mu φ n +
                (physicalFourier (toPotPair φ).1 (-n) +
                 physicalFourier (toPotPair φ).2 n) / 2‖)^2) ≤ C^2 :=
  NlsGge.ThirdConsultation.KSPS025U16.midpoint_dirichlet_difference_uniform_of24 N hN B₀ hB₀
    (NlsGge.ThirdConsultation.KSPS017U6.h24_uniform N hN B₀ hB₀)

end
end NlsGge.ThirdConsultation.KSPS
