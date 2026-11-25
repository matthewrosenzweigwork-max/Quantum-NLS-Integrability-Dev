import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB8Approved

/-! # Track B: the global L² NLS flow `l2Flow` and its characterizations (approved contracts 12–14)

One versioned semantic unit, admitted after the proved and independently reviewed approved
contract 11 `l2_exists_unique` (PdeB8Approved).  Definition and statements copied verbatim from the
owner-approved `TRACK_B_EXACT_STATEMENTS_FOR_APPROVAL.txt`
(sha256 943a37c24a40c74b1e025c9f243c49372b9e071c313bebf28cda3ace2f3ca056).
* `l2Flow`: the unchanged choice formula from the proved `l2_exists_unique`;
* contract 12 `l2Flow_solution`: the chosen trajectory is an `IsL2NLSSolution` with the datum;
* contract 13 `l2Flow_unique`: it is the unique such solution;
* contract 14 `l2Flow_class_char`: it is also the unique `IsL2ClassSolution` with the datum
  (approved contract 5 `l2_class_unique`).
-/

namespace LiebLiniger.FixedPeriod.ALLS.PdeB
open MeasureTheory NlsGge.Pilot NlsGge.NLS38 NlsGge.Birkhoff NlsGge.Sobolev38
open scoped ContDiff
set_option autoImplicit false
noncomputable section

def l2Flow (t : ℝ) (u₀ : PhysicalL2) : PhysicalL2 :=
  (l2_exists_unique u₀).exists.choose t

/-! ### Approved contract 12 -/

theorem l2Flow_solution (u₀ : PhysicalL2) :
    IsL2NLSSolution (fun t => l2Flow t u₀) ∧ l2Flow 0 u₀ = u₀ := by
  exact (l2_exists_unique u₀).exists.choose_spec

/-- An `IsL2NLSSolution` is an `IsL2ClassSolution` (forget the Duhamel field). -/
theorem isL2ClassSolution_of_isL2NLSSolution {u : ℝ → PhysicalL2} (hu : IsL2NLSSolution u) :
    IsL2ClassSolution u := by
  obtain ⟨hc, U, hr, h4, hD, -⟩ := hu
  exact ⟨hc, U, hr, h4, hD⟩

/-! ### Approved contract 13 -/

theorem l2Flow_unique (u₀ : PhysicalL2) (u : ℝ → PhysicalL2) :
    (IsL2NLSSolution u ∧ u 0 = u₀) ↔ u = fun t => l2Flow t u₀ := by
  constructor
  · intro h
    exact (l2_exists_unique u₀).unique h (l2Flow_solution u₀)
  · rintro rfl
    exact l2Flow_solution u₀

/-! ### Approved contract 14 -/

theorem l2Flow_class_char (u₀ : PhysicalL2) (u : ℝ → PhysicalL2) :
    (IsL2ClassSolution u ∧ u 0 = u₀) ↔ u = fun t => l2Flow t u₀ := by
  constructor
  · rintro ⟨hu, hu0⟩
    exact l2_class_unique u (fun t => l2Flow t u₀) hu
      (isL2ClassSolution_of_isL2NLSSolution (l2Flow_solution u₀).1)
      (hu0.trans (l2Flow_solution u₀).2.symm)
  · rintro rfl
    exact ⟨isL2ClassSolution_of_isL2NLSSolution (l2Flow_solution u₀).1, (l2Flow_solution u₀).2⟩

end

end LiebLiniger.FixedPeriod.ALLS.PdeB
