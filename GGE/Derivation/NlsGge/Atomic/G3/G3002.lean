import Mathlib
import NlsGge.Atomic.G2.G2048
import NlsGge.Atomic.G2.G2074
import NlsGge.ThirdConsultation.G2.G2073Support1
import NlsGge.ThirdConsultation.G2.G2072Host
import NlsGge.GK38.TauGamma
import NlsGge.GK38.StdRootBranchesScalar
import NlsGge.Atomic.G3.G3ZetaHost

/- G3_002 PRODUCTION01 (proof development, AUTHOR; not self-reviewed). Target NlsGge/Atomic/G3/G3002.lean, namespace NlsGge.GKDefinitionDesign.
   Head VERBATIM from followup4 STATEMENTS/G3.md (sha256 d03d1697...), section "## G3-002".
   Imports only landed production modules plus the shared G3 ZETA host. No hypothesis beyond the head. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G3_002 (n m : ℤ) (hmn : m ≠ n) (φ : PotPair)
    (hφ : φ ∈ sourceW) (hgap : gamma2 φ m = 0) :
  normalizedRoot n m φ = tauN φ m ∧
  (∀ z : ℂ, standardRoot φ m z = tauN φ m-z) ∧
  (∀ z : ℂ, z ≠ tauN φ m →
    (normalizedRoot n m φ-z)/standardRoot φ m z = 1) ∧
  AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) (tauN φ m) ∧
  AnalyticOnNhd ℂ (betaZeta n m φ) (ball (discC φ m) (discR φ m)) ∧
  (∀ z ∈ ball (discC φ m) (discR φ m), z ≠ tauN φ m →
    psi n φ z/canonRoot38 φ z = betaZeta n m φ z) := by
  have hgk : φ ∈ gkW := sourceFamily.W_gk hφ
  have h1 : normalizedRoot n m φ = tauN φ m := by
    obtain ⟨V, _hVo, hφV, _hVW, B, _hB, hA⟩ := G2_074 φ hφ
    obtain ⟨A, hfac, _, _⟩ := hA φ hφV n
    have h : normalizedRoot n m φ = tauN φ m + gamma2 φ m * A ⟨m, hmn⟩ := hfac ⟨m, hmn⟩
    rw [h, hgap, zero_mul, add_zero]
  have h2 : ∀ z : ℂ, standardRoot φ m z = tauN φ m - z := by
    intro z
    unfold standardRoot
    rw [hgap]
    exact stdRoot_degenerate38 _ _
  have h3 : ∀ z : ℂ, z ≠ tauN φ m → (normalizedRoot n m φ - z) / standardRoot φ m z = 1 := by
    intro z hz
    rw [h1, h2 z, div_self (sub_ne_zero.mpr (Ne.symm hz))]
  have hsq : (lamPlus φ m - lamMinus φ m) ^ 2 = 0 := by
    rw [← gamma2_value38 φ hgk m, hgap]
  have hdiff : lamPlus φ m - lamMinus φ m = 0 := (pow_eq_zero_iff two_ne_zero).mp hsq
  have hPM : lamPlus φ m = lamMinus φ m := sub_eq_zero.mp hdiff
  have hτ : tauN φ m = lamMinus φ m := by
    rw [tauN_value38 φ hgk m, hPM]
    ring
  have hseg : segment ℝ (lamMinus φ m) (lamPlus φ m) = {tauN φ m} := by
    rw [hPM, hτ, segment_same]
  have hR : ∀ z ∈ Metric.closedBall (discC φ m) (discR φ m), z ≠ tauN φ m →
      (φ, z) ∈ rootDomain38 := by
    intro z hz hne
    show φ ∈ gkW ∧ z ∉ gapSegments38 φ
    refine ⟨hgk, fun hzg => ?_⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hzg
    by_cases hkm : k = m
    · rw [hkm, hseg] at hk
      exact hne (Set.mem_singleton_iff.1 hk)
    · exact closedBall_avoids_other_gaps φ hgk m k hkm z hz hk
  have hAn : AnalyticOnNhd ℂ (betaZeta n m φ) (Metric.ball (discC φ m) (discR φ m)) := by
    have hC := normalizedChi_analytic_closedBall φ hφ n m hmn
    have hc : (Real.pi : ℂ) * ((n - m : ℤ) : ℂ) ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
        (Int.cast_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hmn)))
    have heq : betaZeta n m φ = fun z =>
        ((Real.pi : ℂ) * ((n - m : ℤ) : ℂ))⁻¹ * normalizedChi n m φ z := by
      funext z
      simp only [betaZeta, normalizedChi]
      exact (inv_mul_cancel_left₀ hc _).symm
    rw [heq]
    intro z hz
    exact analyticAt_const.mul (hC z (Metric.ball_subset_closedBall hz))
  have hG : ∀ z ∈ Metric.ball (discC φ m) (discR φ m), z ≠ tauN φ m →
      psi n φ z / canonRoot38 φ z = betaZeta n m φ z := by
    intro z hz hne
    have key := (G2_048 φ hgk (p2Extend38 n (sourceF n φ)) n m hmn z
      (hR z (Metric.ball_subset_closedBall hz) hne)).2.2.2
    rw [← normalizedRoot_eq_sigmaOf n m φ hmn, h3 z hne, one_mul] at key
    exact key
  exact ⟨h1, h2, h3, analyticAt_const, hAn, hG⟩

end
end NlsGge.GKDefinitionDesign
