import NlsGge.Hierarchy.RiccatiAttachedRecursionCore
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati.Core

theorem attachedIcc12_sum_nat {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) :
    (Finset.Icc 1 2).attach.sum (fun l => f l.1) = f 1 + f 2 := by
  rw [Finset.sum_attach]
  rw [show Finset.Icc (1 : ℕ) 2 = {1, 2} by decide]
  simp

theorem attachedIcc13_sum_nat {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) :
    (Finset.Icc 1 3).attach.sum (fun l => f l.1) = f 1 + f 2 + f 3 := by
  rw [Finset.sum_attach]
  rw [show Finset.Icc (1 : ℕ) 3 = {1, 2, 3} by decide]
  simp [add_assoc]

end NlsGge.HierarchyRiccati.Core
