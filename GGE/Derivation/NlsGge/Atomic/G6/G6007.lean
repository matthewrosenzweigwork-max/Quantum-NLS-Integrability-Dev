import Mathlib
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.Atomic.G6.G6004
import NlsGge.Atomic.G6.G6006

/- G6-007 PRODUCTION01 (target NlsGge/Atomic/G6/G6007.lean; author proof development, reviewer proof development).
   G6-007 (proof development, AUTHOR). Statement verbatim from defs3 STATEMENTS/G6.md G6-007.
   Continuity into l^1: coordinatewise L2 continuity of the actions (production gapAction_L2_continuous38) plus convergence of the total
   mass (X-006 Phi_mass via g6_action_hasSum), Scheffe via sum of mins and dominated convergence.
   Properness: continuous plus preimages of compacts sequentially compact (G6006), Y metric so isProperMap_iff_isCompact_preimage.
   MASS IDENTITY SOURCE: the L2-wide action-mass identity HasSum actions = ||u||^2 for every u : PhysicalL2 is the landed X-006 field Phi_mass (via
   NlsGge.Atomic.X.X006 actualPhysicalLocalFamily; the single selection only). OWNER DECISION 2026-10-30 (option 1, root/AUDIT_DEFERRED_NOTES01.md):
   production may import the Armstrong closure of X-006 for X-006 and its consumers; this packet is such a consumer. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g6_lp1_norm_eq (f : ActionSequence) : ‖f‖ = ∑' n : ℤ, |f n| := by
  have := lp.hasSum_norm (p := (1 : ℝ≥0∞)) (by norm_num) f
  have h2 : HasSum (fun n : ℤ => ‖f n‖) ‖f‖ := by simpa using this
  simpa [Real.norm_eq_abs] using h2.tsum_eq.symm

theorem g6_abs_sub_eq (a b : ℝ) : |a - b| = a + b - 2 * min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring

theorem g6_actionSequence_continuous : Continuous actionSequence := by
  apply continuous_iff_seqContinuous.mpr
  intro x x0 hx
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hA : ∀ y : PhysicalL2, Summable (fun n : ℤ => actualGapActionAllE02_38 y n) :=
    fun y => (g6_action_hasSum y).summable
  have hnn := NlsGge.GK38.actionNonnegative38
  have hco : ∀ n : ℤ, Tendsto (fun j => actualGapActionAllE02_38 (x j) n) atTop
      (𝓝 (actualGapActionAllE02_38 x0 n)) := fun n =>
    ((NlsGge.GK38.gapAction_L2_continuous38 n).tendsto x0).comp hx
  have hmin : Tendsto (fun j => ∑' n : ℤ, min (actualGapActionAllE02_38 (x j) n)
      (actualGapActionAllE02_38 x0 n)) atTop (𝓝 (∑' n : ℤ, actualGapActionAllE02_38 x0 n)) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun j n => min (actualGapActionAllE02_38 (x j) n) (actualGapActionAllE02_38 x0 n))
      (g := fun n => actualGapActionAllE02_38 x0 n) (bound := fun n => actualGapActionAllE02_38 x0 n)
      (hA x0)
      (fun n => by
        simpa only [min_self] using (hco n).min (tendsto_const_nhds (x := actualGapActionAllE02_38 x0 n)))
      (Eventually.of_forall fun j n => by
        rw [Real.norm_of_nonneg (le_min (hnn _ n) (hnn _ n))]
        exact min_le_right _ _)
    exact this
  have hmass : Tendsto (fun j => ∑' n : ℤ, actualGapActionAllE02_38 (x j) n) atTop
      (𝓝 (∑' n : ℤ, actualGapActionAllE02_38 x0 n)) := by
    simp_rw [(g6_action_hasSum _).tsum_eq]
    exact (hx.norm.pow 2)
  have key : Tendsto (fun j => (∑' n : ℤ, actualGapActionAllE02_38 (x j) n) +
      (∑' n : ℤ, actualGapActionAllE02_38 x0 n) -
      2 * ∑' n : ℤ, min (actualGapActionAllE02_38 (x j) n) (actualGapActionAllE02_38 x0 n))
      atTop (𝓝 0) := by
    have := (hmass.add_const (∑' n : ℤ, actualGapActionAllE02_38 x0 n)).sub (hmin.const_mul 2)
    convert this using 2
    ring
  refine key.congr fun j => ?_
  simp only [Function.comp_apply]
  rw [g6_lp1_norm_eq]
  have hmj : Summable (fun n : ℤ => min (actualGapActionAllE02_38 (x j) n) (actualGapActionAllE02_38 x0 n)) :=
    Summable.of_nonneg_of_le (fun n => le_min (hnn _ n) (hnn _ n)) (fun n => min_le_right _ _) (hA x0)
  have e : ∀ n : ℤ, |(actionSequence (x j) - actionSequence x0) n| =
      actualGapActionAllE02_38 (x j) n + actualGapActionAllE02_38 x0 n -
        2 * min (actualGapActionAllE02_38 (x j) n) (actualGapActionAllE02_38 x0 n) := by
    intro n
    rw [lp.coeFn_sub, Pi.sub_apply, g6_actionSequence_apply, g6_actionSequence_apply]
    exact g6_abs_sub_eq _ _
  rw [tsum_congr e]
  rw [((hA _).add (hA x0)).tsum_sub (hmj.mul_left 2), (hA _).tsum_add (hA x0), tsum_mul_left]

theorem G6007 :
  (∀ u : PhysicalL2, Memℓp (fun n : ℤ => actualGapActionAllE02_38 u n) 1 ∧
    ∀ n : ℤ, actionSequence u n = actualGapActionAllE02_38 u n) ∧
  Continuous actionSequence ∧ IsProperMap actionSequence := by
  refine ⟨fun u => ⟨g6_action_mem u, g6_actionSequence_apply u⟩, g6_actionSequence_continuous, ?_⟩
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨g6_actionSequence_continuous, fun K hK => ?_⟩
  apply IsSeqCompact.isCompact
  intro x hxK
  obtain ⟨y, hyK, r1, hr1, hy⟩ := hK.isSeqCompact (fun j => hxK j)
  obtain ⟨v, r2, hr2, hlim, hv⟩ := G6006 (x ∘ r1) y hy
  refine ⟨v, ?_, r1 ∘ r2, hr1.comp hr2, hlim⟩
  show actionSequence v ∈ K
  rw [hv]; exact hyK

end
end NlsGge.GKDefinitionDesign
