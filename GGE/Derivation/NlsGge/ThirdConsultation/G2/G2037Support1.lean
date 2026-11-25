import NlsGge.Atomic.G2.G2046
import NlsGge.ThirdConsultation.KO.Basic
import NlsGge.ThirdConsultation.G2.G2073Support1
import NlsGge.GK38.XiSqOmittedRoot
import NlsGge.GK38.ContourAction
import NlsGge.GK38.IsolatingFamily
import NlsGge.GK38.TauGammaCircleMoments
import NlsGge.ThirdConsultation.G2.G2037Host

/- G2-037 SUPPORT S1 (proof development, AUTHOR; not self-reviewed; SUPPORTING, not the packet).
   Proves, for the head `G2_037` (STATEMENTS/G2.md, printed p. 68), the conjuncts
     (1)  the finite set S = {n | lower n ≠ upper n},
     (2)  AnalyticOnNhd on (finiteGapCuts u S)ᶜ,
     (4a) circle integrability on every isolating circle,
     (4b) zero circle period for every n ∉ S.
   Verbatim statements; no hypothesis added. NOT claimed: conjunct (3) (see S2), (4c) for n ∈ S
   (zero periods around open gaps) and conjunct (5) (global primitive, Laurent expansion at infinity).
   Route for (4b): Cauchy's disc theorem; closed disc of n misses every other gap segment by the
   landed tube lemma g2073s1_tube_avoids (inlined byte-identically in the selftest). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory SummationFilter
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- The standard root is a nonzero rescaling of the normalized root factor. -/
theorem g2037s1_std_eq (φ : PotPair) (k : ℤ) (w : ℂ) :
    standardRoot φ k w = rootFactor38 k (φ, w) * (Lib.piN k : ℂ) := by
  unfold standardRoot rootFactor38
  exact (div_mul_cancel₀ _ (by exact_mod_cast Lib.piN_ne_zero k)).symm

/-- One standard root factor is analytic and nonvanishing off its own cut. -/
theorem g2037s1_factor (φ : PotPair) (hφ : φ ∈ gkW) (k : ℤ) (z : ℂ)
    (hz : z ∉ segment ℝ (lamMinus φ k) (lamPlus φ k)) :
    AnalyticAt ℂ (fun w : ℂ => standardRoot φ k w) z ∧ standardRoot φ k z ≠ 0 := by
  have hfa : AnalyticAt ℂ (fun w : ℂ => rootFactor38 k (φ, w)) z :=
    (a5RootFactor_analyticAt38 k (φ, z) hφ hz).comp (analyticAt_const.prod analyticAt_id)
  have hfun : (fun w : ℂ => standardRoot φ k w)
      = fun w : ℂ => rootFactor38 k (φ, w) * (Lib.piN k : ℂ) :=
    funext (g2037s1_std_eq φ k)
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hfa.mul analyticAt_const
  · rw [g2037s1_std_eq φ k z]
    exact mul_ne_zero (a5RootFactor_ne_zero38 k (φ, z) hφ hz) (by exact_mod_cast Lib.piN_ne_zero k)

/-- Conjunct (1): the finite set of non-collapsed indices. -/
theorem g2037s1_finite_mem (u : PhysicalL2) (hfg : NlsGge.ThirdConsultation.finiteGap u) :
    ∃ S : Finset ℤ, ∀ n : ℤ, n ∈ S ↔ actualGapLowerAllE02_38 u n ≠ actualGapUpperAllE02_38 u n := by
  have hfin : Set.Finite {n : ℤ | actualGapLowerAllE02_38 u n ≠ actualGapUpperAllE02_38 u n} := hfg
  exact ⟨hfin.toFinset, fun n => (Set.Finite.mem_toFinset hfin).trans Iff.rfl⟩

/-- Conjunct (2): the finite product is analytic off the finitely many cuts. -/
theorem g2037s1_fgd_analyticOn (u : PhysicalL2) (S : Finset ℤ) :
    AnalyticOnNhd ℂ (finiteGapDifferential u S) (finiteGapCuts u S)ᶜ := by
  intro z hz
  have hprod : AnalyticAt ℂ (fun w : ℂ => ∏ n ∈ S,
      (lamDot (realSlice u) n - w) / standardRoot (realSlice u) n w) z := by
    apply Finset.analyticAt_fun_prod
    intro n hn
    have hzn : z ∉ segment ℝ (lamMinus (realSlice u) n) (lamPlus (realSlice u) n) := by
      intro hseg
      have hmem : z ∈ finiteGapCuts u S := by
        unfold finiteGapCuts
        exact Set.mem_biUnion (Finset.mem_coe.2 hn) hseg
      exact hz hmem
    obtain ⟨hA, hne⟩ := g2037s1_factor (realSlice u) (realSlice_mem_gkW u) n z hzn
    exact (analyticAt_const.sub analyticAt_id).div hA hne
  unfold finiteGapDifferential
  exact analyticAt_const.mul hprod

/-- Conjunct (4a): the finite product is circle integrable on every isolating circle. -/
theorem g2037s1_circleIntegrable (u : PhysicalL2) (S : Finset ℤ) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hCR : IsolatingFamily38 (realSlice u) C R) (n : ℤ) :
    CircleIntegrable (finiteGapDifferential u S) (C n) (R n) := by
  have hr : 0 < R n := isolating_radius_pos38 hCR n
  apply ContinuousOn.circleIntegrable hr.le
  intro z hz
  have hzgap : z ∉ gapSegments38 (realSlice u) :=
    fixed_sphere_subset (realSlice u) C R hCR n hz
  have hzc : z ∉ finiteGapCuts u S := by
    intro hc
    unfold finiteGapCuts at hc
    obtain ⟨k, _, hk⟩ := Set.mem_iUnion₂.1 hc
    exact hzgap (Set.mem_iUnion.2 ⟨k, hk⟩)
  exact ((g2037s1_fgd_analyticOn u S z hzc).continuousAt).continuousWithinAt

/-- Conjunct (4b): zero circle period on the isolating circle of every index n ∉ S. -/
theorem g2037s1_zero_period_off (u : PhysicalL2) (S : Finset ℤ) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hCR : IsolatingFamily38 (realSlice u) C R) (n : ℤ) (hn : n ∉ S) :
    circleIntegral (finiteGapDifferential u S) (C n) (R n) = 0 := by
  obtain ⟨c, N, hg, hspec⟩ := hCR
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hg.2.2.1
  have hr : 0 ≤ R n := (hg.1 n).1.le
  have hcut : ∀ z ∈ Metric.closedBall (C n) (R n), z ∉ finiteGapCuts u S := by
    intro z hz hc
    unfold finiteGapCuts at hc
    obtain ⟨k, hkS, hk⟩ := Set.mem_iUnion₂.1 hc
    have hkn : k ≠ n := by
      rintro rfl
      exact hn (Finset.mem_coe.1 hkS)
    have hpos : 0 < c⁻¹ / 2 := by
      have := inv_pos.2 hc0
      linarith
    have hdist : dist z (C n) < R n + c⁻¹ / 2 := by
      have := mem_closedBall.1 hz
      linarith
    exact g2073s1_tube_avoids C R c N hg (realSlice u) hspec n k hkn z hdist hk
  have hcont : ContinuousOn (finiteGapDifferential u S) (Metric.closedBall (C n) (R n)) := by
    intro z hz
    exact ((g2037s1_fgd_analyticOn u S z (hcut z hz)).continuousAt).continuousWithinAt
  have hdiff : ∀ z ∈ Metric.ball (C n) (R n) \ (∅ : Set ℂ),
      DifferentiableAt ℂ (finiteGapDifferential u S) z := by
    rintro z ⟨hz, -⟩
    exact (g2037s1_fgd_analyticOn u S z
      (hcut z (Metric.ball_subset_closedBall hz))).differentiableAt
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr
    Set.countable_empty hcont hdiff

end
end NlsGge.GKDefinitionDesign
