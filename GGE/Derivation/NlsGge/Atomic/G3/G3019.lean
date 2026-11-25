import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.Atomic.G2.G2046
import NlsGge.Atomic.G2.G2019
import NlsGge.GK38.TauGammaContourGlue

/- G3-019 (proof development, AUTHOR; not self-reviewed).  Head from defs3 STATEMENTS/G3.md G3-019 verbatim (followup2 baseline); hosts betaOmega, betaSegmentPoint verbatim from
   DEFINITIONS/G3.lean.md; sourceW from the SourceFamilyBasic host (X-006 family).  Route: ‖γ/ω‖ ≤ ε/2 gives ‖γ‖ ≤ ε‖ω‖/2; τ - segmentPoint(t) = γ/2 - tω so its norm is
   ≥ 3ε‖ω‖/4; the sqrt identity is the definition of stdRoot38 with gamma2 = gap^2 (gamma2_pair_gap38, tau_pair_mean38 as in landed G2019).  `hφ : φ ∈ sourceW` is used
   to land in gkW via sourceFamily.W_gk; no hypothesis change (the gkW-only route is not taken). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def betaOmega (m : ℤ) (φ : PotPair) : ℂ :=
  muSeq φ m - lamMinus φ m

def betaSegmentPoint (m : ℤ) (φ : PotPair) (t : ℝ) : ℂ :=
  lamMinus φ m + (t : ℂ) * betaOmega m φ

theorem G3_019 (m : ℤ) (φ : PotPair) (hφ : φ ∈ sourceW)
    (ε t : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hω : betaOmega m φ ≠ 0)
    (hratio : ‖gap φ m / betaOmega m φ‖ ≤ ε/2) (ht : t ∈ Icc ε 1) :
  ε*‖betaOmega m φ‖/2 ≤ ‖tauN φ m-betaSegmentPoint m φ t‖ ∧
  tauN φ m-betaSegmentPoint m φ t ≠ 0 ∧
  ‖gap φ m/(2*(tauN φ m-betaSegmentPoint m φ t))‖ ≤ 1/3 ∧
  standardRoot φ m (betaSegmentPoint m φ t) =
    (tauN φ m-betaSegmentPoint m φ t) *
      Complex.sqrt (1-gap φ m^2/(4*(tauN φ m-betaSegmentPoint m φ t)^2)) := by
  have hgk : φ ∈ gkW := sourceFamily.W_gk hφ
  have h1 : tauN φ m = (lamPlus φ m + lamMinus φ m) / 2 :=
    tau_pair_mean38 discC discR isolating_selectors_admissible38 φ hgk m
  have h2 : gamma2 φ m = gap φ m ^ 2 := by
    have := gamma2_pair_gap38 discC discR isolating_selectors_admissible38 φ hgk m
    exact this
  set ω := betaOmega m φ with hωdef
  set γ := gap φ m with hγdef
  set d := tauN φ m - betaSegmentPoint m φ t with hd
  have hdeq : d = γ / 2 - (t : ℂ) * ω := by
    simp only [hd, betaSegmentPoint, h1, hγdef, gap]
    ring
  have hωn : 0 < ‖ω‖ := norm_pos_iff.2 hω
  have hγn : ‖γ‖ ≤ ε * ‖ω‖ / 2 := by
    rw [norm_div, div_le_iff₀ hωn] at hratio
    nlinarith
  have hpos : 0 < t := lt_of_lt_of_le hε ht.1
  have htω : ‖(t : ℂ) * ω‖ = t * ‖ω‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le]
  have hlow : 3 * ε * ‖ω‖ / 4 ≤ ‖d‖ := by
    have h3 : ‖(t : ℂ) * ω‖ ≤ ‖γ / 2‖ + ‖d‖ := by
      have : (t : ℂ) * ω = γ / 2 - d := by rw [hdeq]; ring
      rw [this]
      exact norm_sub_le _ _
    have h4 : ‖γ / 2‖ = ‖γ‖ / 2 := by
      rw [norm_div]; simp
    have h5 : ε * ‖ω‖ ≤ t * ‖ω‖ := mul_le_mul_of_nonneg_right ht.1 hωn.le
    rw [htω, h4] at h3
    linarith
  have hεω : 0 < ε * ‖ω‖ := mul_pos hε hωn
  refine ⟨by linarith, ?_, ?_, ?_⟩
  · intro h0
    rw [h0, norm_zero] at hlow
    linarith
  · have hdn : 0 < ‖d‖ := by linarith
    have h2n : ‖(2 : ℂ)‖ = 2 := by simp
    rw [norm_div, norm_mul, h2n, div_le_iff₀ (mul_pos two_pos hdn)]
    nlinarith
  · have hdz : d ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hlow
      linarith
    unfold standardRoot stdRoot38
    rw [h2, div_div]

end
end NlsGge.GKDefinitionDesign
