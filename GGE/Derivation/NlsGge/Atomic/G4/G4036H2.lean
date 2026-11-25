import Mathlib
import NlsGge.Atomic.G4.G4036Host
import NlsGge.Atomic.G4.G4036Cauchy
import NlsGge.Atomic.G4.G4020
import NlsGge.Atomic.G4.G4021
import NlsGge.Atomic.G2.G2019
import NlsGge.ThirdConsultation.G2.G2073Support1
import NlsGge.GK38.TauGamma
import NlsGge.GK38.StdRootBranchesSlit
import NlsGge.GK38.XiSqOmittedRoot

/- G4-036 H2 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G4/G4036H2.lean.
   Head: Pro round 10 section 9 `ownCorrection_analytic_and_ode` (verbatim). Route as Pro: the literal compact
   nested Cauchy integral is `cauchyOwnCorr` (G4036Cauchy, definitional); the Cauchy-projection / integration by
   parts core is proved there for the fixed circle. Here: the own closed disc misses every other cut
   (G2073Support1 tube lemma), K = normalizedZeta is analytic there (p2OmittedRatio_analytic38), the standard
   root is analytic and nonzero on the circle (stdRoot_slit38), w^2 = P off tau (stdRoot_sq_of_ne38), and the
   normalized zero period comes from G4-020 (gapContourMean K = gapContourMean 1 = 1). The family lemma is stated
   for any isolating family (C, R) of phi so that H3 reuses it on a fixed circle. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.Atomic.G4036Cauchy

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g4036_ownCorrection_eq (n : ℤ) (φ : PotPair) :
    ownCorrection n φ = cauchyOwnCorr (discC φ n) (discR φ n)
      (normalizedZeta n φ) (standardRoot φ n) := rfl

/-- On a closed isolating disc of any isolating family, the own cut is the only one met. -/
theorem g4036_K_analytic (φ : PotPair) (hgk : φ ∈ gkW) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hs : IsolatingSpectral38 φ C R) (n : ℤ) :
    AnalyticOnNhd ℂ (normalizedZeta n φ) (Metric.closedBall (C n) (R n)) := by
  intro lam hlam
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hg.2.2.1
  have hpos : 0 < c⁻¹ / 2 := by have := inv_pos.2 hc0; linarith
  have hdom : (φ, lam) ∈ a5OmittedRootDomain38 n := by
    show φ ∈ gkW ∧ ∀ m : ℤ, m ≠ n → lam ∉ segment ℝ (lamMinus φ m) (lamPlus φ m)
    refine ⟨hgk, fun m hm => g2073s1_tube_avoids C R c N hg φ hs n m hm lam ?_⟩
    have := mem_closedBall.1 hlam
    linarith
  have hjoint : AnalyticAt ℂ (p2OmittedRatio38 n) ((φ, p2Extend38 n (sourceF n φ)), lam) :=
    p2OmittedRatio_analytic38 n ((φ, p2Extend38 n (sourceF n φ)), lam) hdom
  have hpair : AnalyticAt ℂ (fun w : ℂ => ((φ, p2Extend38 n (sourceF n φ)), w)) lam :=
    AnalyticAt.prod analyticAt_const analyticAt_id
  exact hjoint.comp hpair

theorem g4036_tau_mem (φ : PotPair) (hgk : φ ∈ gkW) (n : ℤ) :
    tauN φ n ∈ segment ℝ (lamMinus φ n) (lamPlus φ n) := by
  have h := stdRoot_midpoint_mem38 (lamMinus φ n) (lamPlus φ n)
  rw [tauN_value38 φ hgk n, add_comm (lamPlus φ n) (lamMinus φ n)]
  exact h

theorem g4036_std_eq (φ : PotPair) (hgk : φ ∈ gkW) (n : ℤ) :
    standardRoot φ n = fun y : ℂ => stdRoot38 ((lamMinus φ n + lamPlus φ n) / 2)
      ((lamPlus φ n - lamMinus φ n) ^ 2) y :=
  funext (g2019_standardRoot_pair φ hgk n)

/-- Circle facts for the standard root on the sphere of an isolating disc. -/
theorem g4036_root_sphere (φ : PotPair) (hgk : φ ∈ gkW) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hs : IsolatingSpectral38 φ C R) (n : ℤ) :
    (∀ z ∈ Metric.sphere (C n) (R n), AnalyticAt ℂ (standardRoot φ n) z) ∧
    (∀ z ∈ Metric.sphere (C n) (R n), standardRoot φ n z ≠ 0) ∧
    (∀ z ∈ Metric.sphere (C n) (R n), ∀ᶠ y in 𝓝 z,
      standardRoot φ n y ^ 2 = (y - tauN φ n) ^ 2 - gamma2 φ n / 4) := by
  have hnot : ∀ z ∈ Metric.sphere (C n) (R n), z ∉ segment ℝ (lamMinus φ n) (lamPlus φ n) := by
    intro z hz hseg
    have h1 := mem_ball.1 ((hs.1 n).1 hseg)
    have h2 := mem_sphere.1 hz
    linarith
  refine ⟨fun z hz => ?_, fun z hz => g2073s1_std_ne φ hgk n z (hnot z hz), fun z hz => ?_⟩
  · obtain ⟨hne, hslit⟩ := stdRoot_slit38 (lamMinus φ n) (lamPlus φ n) z (hnot z hz)
    rw [g4036_std_eq φ hgk n]
    exact stdRoot_analyticAt38 (τ := fun _ : ℂ => (lamMinus φ n + lamPlus φ n) / 2)
      (g2 := fun _ : ℂ => (lamPlus φ n - lamMinus φ n) ^ 2) (z := fun y : ℂ => y)
      analyticAt_const analyticAt_const analyticAt_id hne hslit
  · have hzτ : z ≠ tauN φ n := fun h => hnot z hz (h ▸ g4036_tau_mem φ hgk n)
    filter_upwards [eventually_ne_nhds hzτ] with y hy
    have hy' : tauN φ n - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
    have := stdRoot_sq_of_ne38 (g2 := gamma2 φ n) hy'
    show stdRoot38 (tauN φ n) (gamma2 φ n) y ^ 2 = _
    rw [this]
    ring

/-- The ODE and analyticity for any isolating family of phi, given the zero period on the n-th circle. -/
theorem g4036_family_ode (φ : PotPair) (hgk : φ ∈ gkW) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hs : IsolatingSpectral38 φ C R) (n : ℤ)
    (hper : (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, deriv (circleMap (C n) (R n)) θ *
      ((normalizedZeta n φ (circleMap (C n) (R n) θ) - 1) /
        standardRoot φ n (circleMap (C n) (R n) θ))) = 0) :
    AnalyticOnNhd ℂ (cauchyOwnCorr (C n) (R n) (normalizedZeta n φ) (standardRoot φ n))
      (Metric.ball (C n) (R n)) ∧
    ∀ z : ℂ, z ∈ Metric.ball (C n) (R n) →
      ((z - tauN φ n) ^ 2 - gamma2 φ n / 4) *
          deriv (cauchyOwnCorr (C n) (R n) (normalizedZeta n φ) (standardRoot φ n)) z +
        (z - tauN φ n) * cauchyOwnCorr (C n) (R n) (normalizedZeta n φ) (standardRoot φ n) z =
          normalizedZeta n φ z - 1 := by
  obtain ⟨hwa, hw0, hsq⟩ := g4036_root_sphere φ hgk C R hs n
  exact cauchyOwnCorr_analytic_ode (hg.1 n).1 (g4036_K_analytic φ hgk C R c N hg hs n) hwa hw0 hsq hper

/-- Zero normalized period on the chosen circle from G4-020. -/
theorem g4036_zero_period_chosen (n : ℤ) (φ : PotPair) (hφ : φ ∈ sourceBetaW) :
    (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, deriv (circleMap (discC φ n) (discR φ n)) θ *
      ((normalizedZeta n φ (circleMap (discC φ n) (discR φ n) θ) - 1) /
        standardRoot φ n (circleMap (discC φ n) (discR φ n) θ))) = 0 := by
  obtain ⟨hK, h1, hmK, hm1⟩ := G4020 n φ hφ
  have h2pi : (-2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hA : circleIntegral (fun lam => normalizedZeta n φ lam / localRoot n φ lam)
      (discC φ n) (discR φ n) = -2 * (Real.pi : ℂ) * Complex.I := by
    have := hmK
    unfold gapContourMean at this
    field_simp at this
    linear_combination (-1 : ℂ) * this
  have hB : circleIntegral (fun lam => (1 : ℂ) / localRoot n φ lam)
      (discC φ n) (discR φ n) = -2 * (Real.pi : ℂ) * Complex.I := by
    have := hm1
    unfold gapContourMean at this
    field_simp at this
    linear_combination (-1 : ℂ) * this
  have hsub := circleIntegral.integral_sub hK h1
  have : circleIntegral (fun lam => normalizedZeta n φ lam / localRoot n φ lam -
      1 / localRoot n φ lam) (discC φ n) (discR φ n) = 0 := by
    have e := hsub
    rw [hA, hB] at e
    simpa using e
  unfold circleIntegral at this
  rw [← this]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  show _ = _ • _
  simp only [smul_eq_mul, localRoot, sub_div]

theorem ownCorrection_analytic_and_ode
    (n : ℤ) (φ : PotPair) (hφ : φ ∈ sourceBetaW) :
  AnalyticOnNhd ℂ (ownCorrection n φ)
    (Metric.ball (discC φ n) (discR φ n)) ∧
  ∀ z : ℂ, z ∈ Metric.ball (discC φ n) (discR φ n) →
    ((z - tauN φ n) ^ 2 - gamma2 φ n / 4) *
        deriv (ownCorrection n φ) z +
      (z - tauN φ n) * ownCorrection n φ z =
        normalizedZeta n φ z - 1 := by
  have hgk : φ ∈ gkW := sourceFamily.W_gk (sourceFamily.V_W hφ)
  obtain ⟨c, N, hg, hs⟩ := isolating_family38 φ hgk
  rw [g4036_ownCorrection_eq]
  exact g4036_family_ode φ hgk (discC φ) (discR φ) c N hg hs n (g4036_zero_period_chosen n φ hφ)

end
end NlsGge.GKDefinitionDesign
