import Mathlib.Analysis.Normed.Group.InfiniteSum

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace NlsGge.Schur

/-- A zero summand may be removed from an absolutely convergent sum, with the
remaining indices expressed using the explicit inequality subtype. -/
theorem tsum_eq_tsum_subtype_ne_of_zero
    {α : Type*} [DecidableEq α] (f : α → ℝ) (hf : Summable f)
    (a : α) (ha : f a = 0) :
    (∑' x : α, f x) = ∑' x : {x : α // x ≠ a}, f x.val := by
  have hs := hf.sum_add_tsum_subtype_compl ({a} : Finset α)
  let e : {x : α // x ∉ ({a} : Finset α)} ≃ {x : α // x ≠ a} :=
    Equiv.subtypeEquivRight (fun x => by simp [Finset.mem_singleton])
  have he :
      (∑' x : {x : α // x ∉ ({a} : Finset α)}, f x.val) =
        ∑' x : {x : α // x ≠ a}, f x.val := by
    exact e.tsum_eq (fun x : {x : α // x ≠ a} => f x.val)
  calc
    (∑' x : α, f x) =
        (∑ x ∈ ({a} : Finset α), f x) +
          ∑' x : {x : α // x ∉ ({a} : Finset α)}, f x.val := hs.symm
    _ = ∑' x : {x : α // x ≠ a}, f x.val := by
      rw [Finset.sum_singleton, ha, zero_add, he]

end NlsGge.Schur
