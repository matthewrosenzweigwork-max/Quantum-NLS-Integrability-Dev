import Mathlib
import NlsGge.ThirdConsultation.PDE.Round14Action

/- PDE060SUP PRODUCTION01 (proof development, AUTHOR; not reviewed). Proposed target
   NlsGge/ThirdConsultation/PDE/PDE060Cone.lean, namespace NlsGge.ThirdConsultation.PDE. Support for PDE-060
   (no packet increment): the first conjunct of the PDE-060 head, MeasurableSet positiveActionCone, for the product
   σ-algebra on ℤ → ℝ. For nonnegative raw actions, summability of w_n I_n is equivalent to a uniform bound on all finite
   partial sums, which is a countable union over C ∈ ℕ of countable intersections over Finset ℤ of measurable sets. -/
set_option autoImplicit false
open MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GKDefinitionDesign
namespace NlsGge.ThirdConsultation.PDE

theorem positiveActionCone_eq :
    positiveActionCone =
      {I : ℤ → ℝ | ∀ n : ℤ, 0 ≤ I n} ∩
        ⋃ C : ℕ, ⋂ s : Finset ℤ, {I : ℤ → ℝ | ∑ n ∈ s, actionWeight n * I n ≤ C} := by
  ext I
  simp only [positiveActionCone, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter]
  constructor
  · rintro ⟨h0, hs⟩
    refine ⟨h0, ⌈∑' n : ℤ, actionWeight n * I n⌉₊, fun s => ?_⟩
    have hnn : ∀ n, 0 ≤ actionWeight n * I n := fun n =>
      mul_nonneg (sobolevModeWeight_pos 1 n).le (h0 n)
    exact (hs.sum_le_tsum s (fun n _ => hnn n)).trans (Nat.le_ceil _)
  · rintro ⟨h0, C, hC⟩
    have hnn : ∀ n, 0 ≤ actionWeight n * I n := fun n =>
      mul_nonneg (sobolevModeWeight_pos 1 n).le (h0 n)
    exact ⟨h0, summable_of_sum_le hnn hC⟩

theorem positiveActionCone_measurableSet : MeasurableSet positiveActionCone := by
  rw [positiveActionCone_eq]
  refine MeasurableSet.inter ?_ ?_
  · have : {I : ℤ → ℝ | ∀ n : ℤ, 0 ≤ I n} = ⋂ n : ℤ, {I : ℤ → ℝ | 0 ≤ I n} := by
      ext I; simp
    rw [this]
    exact MeasurableSet.iInter (fun n => measurableSet_le measurable_const (measurable_pi_apply n))
  · refine MeasurableSet.iUnion (fun C => MeasurableSet.iInter (fun s => ?_))
    exact measurableSet_le
      (Finset.measurable_sum s (fun n _ => (measurable_pi_apply n).const_mul _)) measurable_const

end NlsGge.ThirdConsultation.PDE
