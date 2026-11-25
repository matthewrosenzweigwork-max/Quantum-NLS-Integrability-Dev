import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB10Flow
import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB7Approved
import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB9Approved

/-! # Track B: approved contracts 15 (`l2Flow_add`), 16 (`l2Flow_norm`) and 25 (`l2Flow_of_isNLSSolM`)

Statements copied verbatim from the owner-approved `TRACK_B_EXACT_STATEMENTS_FOR_APPROVAL.txt`
(sha256 943a37c24a40c74b1e025c9f243c49372b9e071c313bebf28cda3ace2f3ca056).  Every proof goes
through the characterization `l2Flow_unique` (approved contract 13, PdeB10Flow):
* contract 15: the time shift of the flow trajectory (approved contract 9) is the solution through
  `l2Flow t u₀`;
* contract 16: the global Duhamel solution of `duh_exists` conserves mass; contract 6 makes it an
  `IsL2NLSSolution`, hence it is the flow trajectory;
* contract 25: approved contract 24 makes an `h^m` solution an `IsL2NLSSolution`.
-/

namespace LiebLiniger.FixedPeriod.ALLS.PdeB
open MeasureTheory NlsGge.Pilot NlsGge.NLS38 NlsGge.Birkhoff NlsGge.Sobolev38
open scoped ContDiff
set_option autoImplicit false
noncomputable section

/-! ### Approved contract 15 -/

theorem l2Flow_add (s t : ℝ) (u₀ : PhysicalL2) :
    l2Flow (s + t) u₀ = l2Flow s (l2Flow t u₀) := by
  have hw : IsL2NLSSolution (fun r => l2Flow (r + t) u₀) :=
    isL2NLSSolution_shift (fun r => l2Flow r u₀) (l2Flow_solution u₀).1 t
  have e := (l2Flow_unique (l2Flow t u₀) (fun r => l2Flow (r + t) u₀)).1
    ⟨hw, by simp only [zero_add]⟩
  exact congrFun e s

/-! ### Approved contract 16 -/

theorem l2Flow_norm (t : ℝ) (u₀ : PhysicalL2) : ‖l2Flow t u₀‖ = ‖u₀‖ := by
  obtain ⟨v, ⟨hc, U, hr, h4, hD⟩, h0, hn⟩ := duh_exists u₀
  have hv : IsL2NLSSolution v := ⟨hc, U, hr, h4, (l2_class_duhamel v U hc hr h4).2 hD, hD⟩
  have e := (l2Flow_unique u₀ v).1 ⟨hv, h0⟩
  rw [← congrFun e t]
  exact hn t

/-! ### Approved contract 25 -/

theorem l2Flow_of_isNLSSolM (m : ℕ) (hm : 1 ≤ m) (u : ℝ → PhysicalL2)
    (hsol : IsNLSSolM m (fun t => physicalFourier (u t))) (t : ℝ) :
    u t = l2Flow t (u 0) := by
  have e := (l2Flow_unique (u 0) u).1 ⟨isL2NLSSolution_of_isNLSSolM m hm u hsol, rfl⟩
  exact congrFun e t

end

end LiebLiniger.FixedPeriod.ALLS.PdeB
