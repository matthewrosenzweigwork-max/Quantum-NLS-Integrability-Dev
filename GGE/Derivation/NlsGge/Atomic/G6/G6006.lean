import Mathlib
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.Atomic.G6.G6004
import NlsGge.Atomic.G6.G6005

/- G6-006 PRODUCTION01 (target NlsGge/Atomic/G6/G6006.lean; author proof development, reviewer proof development).
   G6-006 (proof development, AUTHOR). Statement verbatim from defs3 STATEMENTS/G6.md G6-006.
   Uses G6004 (weak subsequence, mass limit), G6005 (landed: action continuity along weakly convergent bounded sequences)
   and the L2-wide action-mass identity (X-006 Phi_mass via g6_action_hasSum). Weak plus norm convergence gives strong convergence.
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

theorem G6006 (u : ℕ → PhysicalL2) (Istar : ActionSequence)
    (hI : Tendsto (fun j : ℕ => actionSequence (u j)) atTop (𝓝 Istar)) :
  ∃ (v : PhysicalL2) (r : ℕ → ℕ), StrictMono r ∧
    Tendsto (u ∘ r) atTop (𝓝 v) ∧ actionSequence v = Istar := by
  obtain ⟨h1, _, ⟨C, _, hC⟩, v, r, hr, hw⟩ := G6004 u Istar hI
  have hnn : ∀ n, 0 ≤ Istar n := fun n =>
    ge_of_tendsto' (g6_lp_coord_tendsto _ _ hI n) fun j => by
      rw [g6_actionSequence_apply]; exact NlsGge.GK38.actionNonnegative38 _ n
  have hbd : Bornology.IsBounded (Set.range (u ∘ r)) := by
    rw [isBounded_iff_forall_norm_le]
    exact ⟨C, by rintro _ ⟨j, rfl⟩; exact hC (r j)⟩
  have hcoord : ∀ n : ℤ, actualGapActionAllE02_38 v n = Istar n := by
    intro n
    have ha := G6005 n (u ∘ r) v hbd hw
    have hb : Tendsto (fun j : ℕ => actualGapActionAllE02_38 (u (r j)) n) atTop (𝓝 (Istar n)) := by
      have := (g6_lp_coord_tendsto _ _ hI n).comp hr.tendsto_atTop
      simpa [Function.comp_def, g6_actionSequence_apply] using this
    exact tendsto_nhds_unique ha hb
  have hseq : actionSequence v = Istar := by
    apply Subtype.ext
    funext n
    rw [show (actionSequence v : ℤ → ℝ) n = actionSequence v n from rfl, g6_actionSequence_apply, hcoord n]
  have hmass : ‖v‖ ^ 2 = ∑' n : ℤ, Istar n := by
    rw [← (g6_action_hasSum v).tsum_eq]
    exact tsum_congr hcoord
  refine ⟨v, r, hr, ?_, hseq⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hin : Tendsto (fun j : ℕ => inner ℝ v (u (r j))) atTop (𝓝 (inner ℝ v v)) :=
    hw (innerSL ℝ v)
  have hsq : Tendsto (fun j : ℕ => ‖u (r j) - v‖ ^ 2) atTop (𝓝 0) := by
    have hn : Tendsto (fun j : ℕ => ‖u (r j)‖ ^ 2) atTop (𝓝 (∑' n : ℤ, Istar n)) :=
      h1.comp hr.tendsto_atTop
    have := (hn.sub (hin.const_mul 2)).add_const (‖v‖ ^ 2)
    have e : ∑' n : ℤ, Istar n - 2 * inner ℝ v v + ‖v‖ ^ 2 = 0 := by
      rw [real_inner_self_eq_norm_sq, ← hmass]; ring
    rw [e] at this
    refine this.congr fun j => ?_
    rw [norm_sub_sq_real, real_inner_comm]
  have h := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at h
  refine h.congr fun j => ?_
  simp only [Function.comp_apply]
  exact Real.sqrt_sq (norm_nonneg _)

end
end NlsGge.GKDefinitionDesign
