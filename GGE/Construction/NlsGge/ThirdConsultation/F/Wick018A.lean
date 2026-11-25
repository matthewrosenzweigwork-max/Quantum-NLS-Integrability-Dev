import Mathlib
import NlsGge.ThirdConsultation.F.Round5

                                                                                                     
                                                                                                     
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.Measure

namespace NlsGge.ThirdConsultation.F
attribute [local instance] Classical.propDecidable

namespace Wick018A

/-- W1: occurrence binomial expansion over all subsets (low occurrences `R`). -/
theorem prod_add_subsets {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : ι → ℂ) :
    ∏ t, (x t + y t) =
      ∑ R : Finset ι, (∏ t ∈ R, x t) * ∏ t ∈ (Finset.univ \ R), y t := by
  rw [Finset.prod_add]
  rfl

/-- W2 (general): reindexing a sum over `Perm (Fin p)` to a sum over bijections `A ≃ B`. -/
theorem sum_perm_eq_sum_equiv {p : ℕ} {A B : Type*} [Fintype A] [Fintype B]
    [Fintype (A ≃ B)] (e : Fin p ≃ A) (f : Fin p ≃ B) (C : A → B → ℂ) :
    ∑ σ : Equiv.Perm (Fin p), ∏ r : Fin p, C (e r) (f (σ r)) =
      ∑ τ : A ≃ B, ∏ a : A, C a (τ a) := by
  refine Fintype.sum_equiv (Equiv.equivCongr e f) _ _ (fun σ => ?_)
  rw [← e.prod_comp]
  refine Finset.prod_congr rfl (fun r _ => ?_)
  simp [Equiv.equivCongr_apply_apply]

/-- W2 with the `Fin.cast` indexing of LIB056 `finiteComplexWickPairingSum`. -/
theorem sum_perm_cast_eq_sum_equiv {p q : ℕ} (h : p = q) {A B : Type*} [Fintype A] [Fintype B]
    [Fintype (A ≃ B)] (e : Fin p ≃ A) (f : Fin q ≃ B) (C : A → B → ℂ) :
    ∑ σ : Equiv.Perm (Fin p), ∏ r : Fin p, C (e r) (f (Fin.cast h (σ r))) =
      ∑ τ : A ≃ B, ∏ a : A, C a (τ a) :=
  sum_perm_eq_sum_equiv e ((finCongr h).trans f) C

/-- Existence of the enumerations for `contractionPatterns` members. -/
theorem exists_enum {q : Jet →₀ ℕ} {R : Finset (OccType38 q)} (hR : R ∈ contractionPatterns q) :
    ∃ k : ℕ, (tailUnbar q R).card = k ∧ (tailBar q R).card = k ∧
      Nonempty (Fin k ≃ ↥(tailUnbar q R)) ∧ Nonempty (Fin k ≃ ↥(tailBar q R)) := by
  have h : (tailUnbar q R).card = (tailBar q R).card := (Finset.mem_filter.1 hR).2.2
  refine ⟨(tailUnbar q R).card, rfl, h.symm, ⟨?_⟩, ⟨?_⟩⟩
  · exact (Finset.equivFin _).symm
  · exact (finCongr h).trans (Finset.equivFin _).symm

/-- W2 specialised: `wickMatchingSum` as a sum over `Perm (Fin k)` of products of
tail covariances, for any enumerations of the unbarred and barred tail occurrences. -/
theorem wickMatchingSum_eq_perm (m : ℕ) (β : ℕ → ℝ) (N : ℕ) (q : Jet →₀ ℕ)
    (R : Finset (OccType38 q)) {k : ℕ}
    (e : Fin k ≃ ↥(tailUnbar q R)) (f : Fin k ≃ ↥(tailBar q R)) :
    wickMatchingSum m β N q R =
      ∑ σ : Equiv.Perm (Fin k), ∏ r : Fin k,
        tailCovariance m β N (occOrd38 q (e r).1) (occOrd38 q (f (σ r)).1) := by
  unfold wickMatchingSum
  exact (sum_perm_eq_sum_equiv e f
    (fun i j => tailCovariance m β N (occOrd38 q i.1) (occOrd38 q j.1))).symm

end Wick018A

end NlsGge.ThirdConsultation.F
end
