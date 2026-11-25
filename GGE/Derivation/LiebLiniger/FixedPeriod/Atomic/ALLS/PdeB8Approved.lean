import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB8DistDuh

/-! # Track B: approved contracts 6 (`l2_class_duhamel`), 5 (`l2_class_unique`) and
11 (`l2_exists_unique`)

Statements copied verbatim from the owner-approved `TRACK_B_EXACT_STATEMENTS_FOR_APPROVAL.txt`
(sha256 943a37c24a40c74b1e025c9f243c49372b9e071c313bebf28cda3ace2f3ca056).
* contract 6: `duhamel_of_isDistributionalNLS` (PdeB8DistDuh) and
  `isDistributionalNLS_of_duhamel` (PdeB8DuhDist);
* contract 5: contract 6 (⇒) turns both class solutions into `IsDuhSol`; `duh_unique`;
* contract 11: existence from `duh_exists` and contract 6 (⇐); uniqueness from `duh_unique`.
`l2Flow` is NOT defined here (staged behind the independent proof review).
-/

namespace LiebLiniger.FixedPeriod.ALLS.PdeB
open MeasureTheory NlsGge.Pilot NlsGge.NLS38 NlsGge.Birkhoff NlsGge.Sobolev38
open scoped ContDiff
set_option autoImplicit false
noncomputable section

/-! ### Approved contract 6 -/

theorem l2_class_duhamel (u : ℝ → PhysicalL2) (U : ℝ × PhysicalCircle → ℂ) (hc : Continuous u)
    (hU : IsSpacetimeRep u U) (h4 : IsL4Loc U) :
    IsDistributionalNLS U ↔ IsHm1Duhamel u U := by
  exact ⟨duhamel_of_isDistributionalNLS hc hU h4, isDistributionalNLS_of_duhamel hU h4⟩

/-! ### Approved contract 5 -/

theorem l2_class_unique (u v : ℝ → PhysicalL2) (hu : IsL2ClassSolution u)
    (hv : IsL2ClassSolution v) (h0 : u 0 = v 0) : u = v := by
  obtain ⟨hcu, U, hrU, h4U, hDU⟩ := hu
  obtain ⟨hcv, V, hrV, h4V, hDV⟩ := hv
  exact duh_unique ⟨hcu, U, hrU, h4U, (l2_class_duhamel u U hcu hrU h4U).1 hDU⟩
    ⟨hcv, V, hrV, h4V, (l2_class_duhamel v V hcv hrV h4V).1 hDV⟩ h0

/-! ### Approved contract 11 -/

theorem l2_exists_unique (u₀ : PhysicalL2) :
    ∃! u : ℝ → PhysicalL2, IsL2NLSSolution u ∧ u 0 = u₀ := by
  obtain ⟨u, ⟨hc, U, hr, h4, hD⟩, h0, -⟩ := duh_exists u₀
  refine ⟨u, ⟨⟨hc, U, hr, h4, (l2_class_duhamel u U hc hr h4).2 hD, hD⟩, h0⟩, ?_⟩
  rintro v ⟨⟨hcv, V, hrV, h4V, -, hDV⟩, hv0⟩
  exact duh_unique ⟨hcv, V, hrV, h4V, hDV⟩ ⟨hc, U, hr, h4, hD⟩ (hv0.trans h0.symm)

end

end LiebLiniger.FixedPeriod.ALLS.PdeB
