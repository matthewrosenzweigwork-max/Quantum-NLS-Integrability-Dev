import NlsGge.Hierarchy.RiccatiSpatialDerivativeBidegreeShiftAfterSingleSumComponentsThird
import NlsGge.Hierarchy.RiccatiLowOrderAlgebraAfterCore
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-! The actual attached Riccati recursion preserves the source differential
weight and gauge charge. This induction consumes the proved support
bidegree of the actual spatial derivation; it does not assume the shift. -/

namespace NlsGge.HierarchyRiccati.Core

open scoped BigOperators Pointwise

private theorem riccatiJetBidegreeAfterComponents_add (m n : Jet →₀ ℕ) :
    riccatiJetBidegreeAfterComponents (m + n) =
      riccatiJetBidegreeAfterComponents m + riccatiJetBidegreeAfterComponents n := by
  change
    (riccatiJetWeightHomAfterComponents (m + n),
      riccatiJetGaugeHomAfterComponents (m + n)) =
    (riccatiJetWeightHomAfterComponents m + riccatiJetWeightHomAfterComponents n,
      riccatiJetGaugeHomAfterComponents m + riccatiJetGaugeHomAfterComponents n)
  rw [map_add, map_add]

private theorem hasRiccatiJetBidegreeAfterComponents_add {P Q : Poly} {d : ℕ × ℤ}
    (hP : HasRiccatiJetBidegreeAfterComponents P d)
    (hQ : HasRiccatiJetBidegreeAfterComponents Q d) :
    HasRiccatiJetBidegreeAfterComponents (P + Q) d := by
  classical
  intro m hm
  have hm' : m ∈ P.support ∪ Q.support := MvPolynomial.support_add hm
  rcases Finset.mem_union.mp hm' with hm' | hm'
  · exact hP m hm'
  · exact hQ m hm'

private theorem hasRiccatiJetBidegreeAfterComponents_mul {P Q : Poly}
    {d e : ℕ × ℤ} (hP : HasRiccatiJetBidegreeAfterComponents P d)
    (hQ : HasRiccatiJetBidegreeAfterComponents Q e) :
    HasRiccatiJetBidegreeAfterComponents (P * Q) (d + e) := by
  classical
  intro m hm
  have hm' : m ∈ P.support + Q.support := MvPolynomial.support_mul P Q hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hm'
  rw [riccatiJetBidegreeAfterComponents_add, hP a ha, hQ b hb]

private theorem hasRiccatiJetBidegreeAfterComponents_sum {ι : Type*}
    (s : Finset ι) (f : ι → Poly) {d : ℕ × ℤ}
    (h : ∀ i ∈ s, HasRiccatiJetBidegreeAfterComponents (f i) d) :
    HasRiccatiJetBidegreeAfterComponents (s.sum f) d := by
  classical
  intro m hm
  have hm' := MvPolynomial.support_sum (s := s) (f := f) hm
  obtain ⟨i, hi, hmi⟩ := Finset.mem_biUnion.mp hm'
  exact h i hi m hmi

private theorem hasRiccatiJetBidegreeAfterComponents_neg {P : Poly}
    {d : ℕ × ℤ} (hP : HasRiccatiJetBidegreeAfterComponents P d) :
    HasRiccatiJetBidegreeAfterComponents (-P) d := by
  intro m hm
  have hm' : m ∈ P.support := by
    rw [MvPolynomial.support_neg] at hm
    exact hm
  exact hP m hm'

private theorem hasRiccatiJetBidegreeAfterComponents_int_smul {P : Poly}
    {d : ℕ × ℤ} (a : ℤ) (hP : HasRiccatiJetBidegreeAfterComponents P d) :
    HasRiccatiJetBidegreeAfterComponents (a • P) d := by
  intro m hm
  exact hP m (MvPolynomial.support_smul hm)

/-- Every actual recursive coefficient has differential weight `k` and
U(1) gauge charge `+1` on its finite monomial support. -/
theorem riccati_p_has_bidegree_after_components :
    ∀ k : ℕ, 1 ≤ k → HasRiccatiJetBidegreeAfterComponents (p k) (k, 1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk
      cases k with
      | zero => omega
      | succ k =>
          cases k with
          | zero =>
              have hX := hasRiccatiJetBidegreeAfterComponents_X (true, 0)
              simpa [p_one] using hasRiccatiJetBidegreeAfterComponents_neg hX
          | succ n =>
              have hPrev : HasRiccatiJetBidegreeAfterComponents (p (n + 1)) (n + 1, 1) :=
                ih (n + 1) (by omega) (by omega)
              have hderiv := spatialDerivation_bidegree_shift_after_components
                (p (n + 1)) (n + 1, 1) hPrev
              have hterms : ∀ l : {j : ℕ // j ∈ Finset.Icc 1 n},
                  HasRiccatiJetBidegreeAfterComponents
                    (p (n + 1 - l.1) * p l.1) (n + 1, 2) := by
                intro l
                have hl := attachedIcc_bounds n l
                have hleft : HasRiccatiJetBidegreeAfterComponents (p (n + 1 - l.1))
                    (n + 1 - l.1, 1) :=
                  ih (n + 1 - l.1) (by omega) (by omega)
                have hright : HasRiccatiJetBidegreeAfterComponents (p l.1) (l.1, 1) :=
                  ih l.1 (by omega) (by omega)
                have hprod := hasRiccatiJetBidegreeAfterComponents_mul hleft hright
                simpa [Nat.sub_add_cancel (by omega : l.1 ≤ n + 1)] using hprod
              have hsum : HasRiccatiJetBidegreeAfterComponents
                  ((Finset.Icc 1 n).attach.sum fun l =>
                    p (n + 1 - l.1) * p l.1) (n + 1, 2) := by
                apply hasRiccatiJetBidegreeAfterComponents_sum
                intro l hl
                exact hterms l
              have hnonlinear : HasRiccatiJetBidegreeAfterComponents
                  (MvPolynomial.X (false, 0) *
                    ((Finset.Icc 1 n).attach.sum fun l =>
                      p (n + 1 - l.1) * p l.1)) (n + 2, 1) := by
                have hX := hasRiccatiJetBidegreeAfterComponents_X (false, 0)
                have hprod := hasRiccatiJetBidegreeAfterComponents_mul hX hsum
                have hdegree :
                    ((0 + 1, if false = true then 1 else -1) + (n + 1, 2)) =
                      (n + 2, 1) := by
                  norm_num
                  omega
                exact hdegree ▸ hprod
              rw [p_recurrence n]
              exact hasRiccatiJetBidegreeAfterComponents_add hderiv hnonlinear

end NlsGge.HierarchyRiccati.Core
