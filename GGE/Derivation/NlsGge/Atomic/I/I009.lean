import Mathlib
import NlsGge.Spectral.ActualConvexMomentE02_38
import NlsGge.Spectral.ActualGapHeightHolderE02_38
import NlsGge.Spectral.ActualSpectralRemainderE02_38
import NlsGge.Spectral.ActualGapActionAllNE02_38

/- I-009 PROOF01 (proof development). Main statement verbatim from the supplemental design (NLS_GGE_SUPPLEMENTAL_DESIGN_20261027.md,
   section I-009, node I009.main). No new hypothesis.
   Route (design "Lemma DAG"): integrability and summability from actualConvexMoment_E02_38; the sum/integral identity from
   actualGapHeight_integral_eq_sum_E02_38 with f = fun x => W (2*x) (continuous); the action vanishes off the finite set
   of open gaps (level set = Icc lower upper, nonempty, so lower = upper on closed gaps); the difference integrand is
   the pointwise difference of the two integrands (remainderIntegrandE02_38 unfolds to (W(2x) - W(2p x)) v).
   Interface adaptation: none. -/

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff
open NlsGge.Pilot NlsGge.Schur NlsGge.Analysis
open NlsGge.SpectralFoundations

namespace NlsGge.Atomic.I009

theorem finiteGap_convex_difference
    (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (hfin : {n : ℤ |
      actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n}.Finite)
    (W : ℝ → ℝ) (hW : ContDiff ℝ 2 W)
    (hconv : ConvexOn ℝ Set.univ W) :
    Integrable (fun x : ℝ => W (2*x) * actualGapHeightE02_38 u x) ∧
    Integrable (remainderIntegrandE02_38 W u) ∧
    Summable (fun n : ℤ => W (2*Real.pi*n) * actualGapActionAllE02_38 u n) ∧
    (2/Real.pi) * (∫ x : ℝ, W (2*x) * actualGapHeightE02_38 u x) -
      (∑' n : ℤ, W (2*Real.pi*n) * actualGapActionAllE02_38 u n) =
        (2/Real.pi) * ∫ x : ℝ, remainderIntegrandE02_38 W u x := by
  obtain ⟨hint1, hsum1, -⟩ := actualConvexMoment_E02_38 u hu hfin W hW hconv
  have hf : Continuous (fun x : ℝ => W (2*x)) :=
    hW.continuous.comp (continuous_const.mul continuous_id)
  obtain ⟨hint2, hid⟩ := actualGapHeight_integral_eq_sum_E02_38 u hfin (fun x => W (2*x)) hf
  -- the action vanishes outside the finite set of open gaps
  have hzero : ∀ n : ℤ, n ∉ hfin.toFinset → actualGapActionAllE02_38 u n = 0 := by
    intro n hn
    have hne : (actualGapLevelSetE02_38 u n).Nonempty := (actualGapLevelSet_eq_Icc_E02_38 u n).1
    have hEq := (actualGapLevelSet_eq_Icc_E02_38 u n).2
    have hle : actualGapLowerAllE02_38 u n ≤ actualGapUpperAllE02_38 u n := by
      rw [hEq] at hne
      exact Set.nonempty_Icc.1 hne
    have hnot : ¬ actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n := by
      intro hlt
      exact hn ((Set.Finite.mem_toFinset hfin).2 hlt)
    have heq : actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n :=
      le_antisymm hle (not_lt.1 hnot)
    unfold actualGapActionAllE02_38
    rw [heq, intervalIntegral.integral_same, mul_zero]
  have hsumeq : ∑' n : ℤ, W (2*Real.pi*n) * actualGapActionAllE02_38 u n =
      ∑ n ∈ hfin.toFinset, W (2*Real.pi*n) * actualGapActionAllE02_38 u n := by
    apply tsum_eq_sum
    intro n hn
    rw [hzero n hn, mul_zero]
  have hJ : (2/Real.pi) * ∫ l : ℝ, W (2 * actualQuasimomentumRealPartE02_38 u l) * actualGapHeightE02_38 u l =
      ∑ n ∈ hfin.toFinset, W (2*Real.pi*n) * actualGapActionAllE02_38 u n := by
    rw [hid, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    have h2 : (2:ℝ) * ((n:ℝ) * Real.pi) = 2 * Real.pi * n := by ring
    unfold actualGapActionAllE02_38
    simp only [h2]
    ring
  have hrem : remainderIntegrandE02_38 W u =
      fun x => W (2*x) * actualGapHeightE02_38 u x -
        W (2 * actualQuasimomentumRealPartE02_38 u x) * actualGapHeightE02_38 u x := by
    funext x
    unfold remainderIntegrandE02_38
    ring
  have hint3 : Integrable (remainderIntegrandE02_38 W u) := by
    rw [hrem]; exact hint1.sub hint2
  refine ⟨hint1, hint3, hsum1, ?_⟩
  rw [hsumeq, ← hJ, hrem, integral_sub hint1 hint2]
  ring

end NlsGge.Atomic.I009
