import NlsGge.Hierarchy.RiccatiChargeRemainderSupportOrderBoundsAfterBidegreeThirdRecoveryThird
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati.Core

/-- Number of top-order jet factors in a monomial, counted with the exponent
multiplicity stored in its Finsupp. -/
def riccatiTopJetSlotMultiplicityMinimumRecovery30Third
    (m : ℕ) (q : Jet →₀ ℕ) : ℕ :=
  ∑ v ∈ q.support, if v.2 + 1 = m then q v else 0

/-- Under the exact total derivative-count bound used for the local
`H^(m-1)` remainder, at most two factor slots can have derivative order
`m-1`. The count includes repeated occurrences of one jet variable. -/
theorem riccatiTopJetSlotMultiplicity_le_twoMinimumRecovery30Third
    (m : ℕ) (hm : 2 ≤ m) (q : Jet →₀ ℕ)
    (hD : riccatiJetDerivativeOrderSumNativeRecovery q ≤ 2 * m - 2) :
    riccatiTopJetSlotMultiplicityMinimumRecovery30Third m q ≤ 2 := by
  classical
  let S := q.support
  have hleft :
      riccatiTopJetSlotMultiplicityMinimumRecovery30Third m q * (m - 1) =
        ∑ v ∈ S, (if v.2 + 1 = m then q v * (m - 1) else 0) := by
    unfold riccatiTopJetSlotMultiplicityMinimumRecovery30Third
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases htop : v.2 + 1 = m
    · simp [htop]
    · simp [htop]
  have hterms : ∀ v ∈ S,
      (if v.2 + 1 = m then q v * (m - 1) else 0) ≤ q v * v.2 := by
    intro v hv
    by_cases htop : v.2 + 1 = m
    · have horder : v.2 = m - 1 := by omega
      rw [if_pos htop, horder]
    · simp [htop]
  have hsum := Finset.sum_le_sum hterms
  have hDsum : riccatiJetDerivativeOrderSumNativeRecovery q =
      ∑ v ∈ S, q v * v.2 := by
    unfold riccatiJetDerivativeOrderSumNativeRecovery
    dsimp [S]
    simp only [Finsupp.sum]
  have hmul :
      riccatiTopJetSlotMultiplicityMinimumRecovery30Third m q * (m - 1) ≤
        2 * (m - 1) := by
    calc
      riccatiTopJetSlotMultiplicityMinimumRecovery30Third m q * (m - 1) =
          ∑ v ∈ S, (if v.2 + 1 = m then q v * (m - 1) else 0) := hleft
      _ ≤ ∑ v ∈ S, q v * v.2 := hsum
      _ = riccatiJetDerivativeOrderSumNativeRecovery q := hDsum.symm
      _ ≤ 2 * m - 2 := hD
      _ = 2 * (m - 1) := by omega
  have hpositive : 0 < m - 1 := by omega
  exact Nat.le_of_mul_le_mul_right hmul hpositive

end NlsGge.HierarchyRiccati.Core
