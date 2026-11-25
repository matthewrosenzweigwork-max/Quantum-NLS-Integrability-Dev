import Mathlib
import NlsGge.ThirdConsultation.M.M033Bridge
import NlsGge.Atomic.M.M010Host
import NlsGge.ThirdConsultation.M.SpectralRadiusHost
import NlsGge.ThirdConsultation.M.CentralGapScalar

/- MCENTRALGAP PRODUCTION01 (proof development, AUTHOR; not reviewed). Proposed target
   NlsGge/ThirdConsultation/M/CentralGap.lean, namespace NlsGge.ThirdConsultation.M. Pro round 16 §Q2 support
   (no packet increment): zero_gap_small_H1, central_gap_radius, heads VERBATIM (followup14
   PRO_DEFINITION_RESPONSE_FP80_16.md L439-509). Route (Pro L534-581 "zero-label treatment"):
   indexWeight 0 = 1, so 8Q² ≤ 1 makes label 0 a high label for M033Bridge.high_endpoints, giving
   |λ₀^±| ≤ Q² + √2 Q; Q ≤ 1/4 gives ≤ 1/2 (√2 < 3/2); Q ≥ 1/4 and 0 not low give ≤ (1+4√2)Q² < 8πQ²; genuinely
   low labels use M033Bridge.low_endpoints, (8Q² - 1/2)π ≤ 8πQ². closedGap is the landed M010Host one
   (Icc of the AllE02 endpoints, the same endpoints as in M033Bridge). Consumes no M-016 piece.
   Imports: M033Bridge, M010Host (landed); SpectralRadiusHost, CentralGapScalar (this batch). -/
set_option autoImplicit false
open NlsGge.Pilot NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.M

theorem zero_gap_small_H1
    (u : SobolevR 1) (hsmall : MTwoMode.H1Norm u ≤ (1 / 4 : ℝ)) :
    ∀ x : ℝ, x ∈ closedGap (physicalOfSobolev u) 0 → |x| ≤ (1 / 2 : ℝ) := by
  intro x hx
  have hQ0 := NlsGge.ThirdConsultation.M033Bridge.H1Norm_nonneg u
  have hw0 : NlsGge.Atomic.M.M054.indexWeight 0 = 1 := by
    simp [NlsGge.Atomic.M.M054.indexWeight]
  have h8 : 8 * MTwoMode.H1Norm u ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight 0 := by
    rw [hw0]; nlinarith
  obtain ⟨hlo, hhi⟩ := NlsGge.ThirdConsultation.M033Bridge.high_endpoints u 0 h8
  rw [Int.cast_zero, zero_mul, sub_zero, hw0, show (2 : ℤ) * 0 = 0 by norm_num, hw0, div_one,
    div_one] at hlo hhi
  have hb := NlsGge.ThirdConsultation.MCentralGapS.small_bound hQ0 hsmall
  exact NlsGge.ThirdConsultation.MCentralGapS.abs_le_of_mem_Icc hx (hlo.trans hb) (hhi.trans hb)

theorem central_gap_radius
    (u : SobolevR 1) (hlarge : (1 / 4 : ℝ) ≤ MTwoMode.H1Norm u)
    (n : ℤ) (hn : n = 0 ∨ LowModeH1Threshold u n) :
    ∀ x : ℝ, x ∈ closedGap (physicalOfSobolev u) n →
      |x| ≤ MEstimates.spectralRadius u := by
  intro x hx
  unfold MEstimates.spectralRadius
  by_cases hlow : LowModeH1Threshold u n
  · obtain ⟨hlo, hhi⟩ := NlsGge.ThirdConsultation.M033Bridge.low_endpoints u n hlow
    have hb := NlsGge.ThirdConsultation.MCentralGapS.low_bound (MTwoMode.H1Norm u)
    exact NlsGge.ThirdConsultation.MCentralGapS.abs_le_of_mem_Icc hx (hlo.trans hb) (hhi.trans hb)
  · have h0 : n = 0 := hn.resolve_right hlow
    subst h0
    have hw0 : NlsGge.Atomic.M.M054.indexWeight 0 = 1 := by
      simp [NlsGge.Atomic.M.M054.indexWeight]
    have h8 : 8 * MTwoMode.H1Norm u ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight 0 := not_lt.mp hlow
    obtain ⟨hlo, hhi⟩ := NlsGge.ThirdConsultation.M033Bridge.high_endpoints u 0 h8
    rw [Int.cast_zero, zero_mul, sub_zero, hw0, show (2 : ℤ) * 0 = 0 by norm_num, hw0, div_one,
      div_one] at hlo hhi
    have hb := NlsGge.ThirdConsultation.MCentralGapS.large_bound hlarge
    exact NlsGge.ThirdConsultation.MCentralGapS.abs_le_of_mem_Icc hx (hlo.trans hb) (hhi.trans hb)

end NlsGge.ThirdConsultation.M
