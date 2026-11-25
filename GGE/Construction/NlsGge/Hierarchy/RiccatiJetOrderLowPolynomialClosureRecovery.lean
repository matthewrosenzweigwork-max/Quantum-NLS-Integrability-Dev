import NlsGge.Hierarchy.RiccatiAttachedRecursionCore
import Mathlib.Algebra.MvPolynomial.Basic

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati.Core

/-- A polynomial is low at cutoff `j` when every jet in every supported
monomial has derivative order at most `j - 1`. -/
def HasJetOrderAtMostNativeRecovery (j : ℕ) (P : Poly) : Prop :=
  ∀ m ∈ P.support, ∀ v ∈ m.support, v.2 ≤ j - 1

theorem hasJetOrderAtMost_addNativeRecovery
    {j : ℕ} {P Q : Poly}
    (hP : HasJetOrderAtMostNativeRecovery j P)
    (hQ : HasJetOrderAtMostNativeRecovery j Q) :
    HasJetOrderAtMostNativeRecovery j (P + Q) := by
  classical
  intro m hm v hv
  have hm' : m ∈ P.support ∪ Q.support := MvPolynomial.support_add hm
  rcases Finset.mem_union.mp hm' with hm' | hm'
  · exact hP m hm' v hv
  · exact hQ m hm' v hv

theorem hasJetOrderAtMost_smulNativeRecovery
    {j : ℕ} (a : ℤ) {P : Poly}
    (hP : HasJetOrderAtMostNativeRecovery j P) :
    HasJetOrderAtMostNativeRecovery j (a • P) := by
  classical
  intro m hm v hv
  exact hP m (MvPolynomial.support_smul hm) v hv

theorem hasJetOrderAtMost_negNativeRecovery
    {j : ℕ} {P : Poly}
    (hP : HasJetOrderAtMostNativeRecovery j P) :
    HasJetOrderAtMostNativeRecovery j (-P) := by
  classical
  intro m hm v hv
  rw [MvPolynomial.support_neg] at hm
  exact hP m hm v hv

theorem hasJetOrderAtMost_finset_sumNativeRecovery
    {j : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Poly)
    (h : ∀ i ∈ s, HasJetOrderAtMostNativeRecovery j (f i)) :
    HasJetOrderAtMostNativeRecovery j (∑ i ∈ s, f i) := by
  classical
  intro m hm v hv
  have hm' := MvPolynomial.support_sum (s := s) (f := f) hm
  obtain ⟨i, hi, hmi⟩ := Finset.mem_biUnion.mp hm'
  exact h i hi m hmi v hv

end NlsGge.HierarchyRiccati.Core
