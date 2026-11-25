import NlsGge.Hierarchy.RiccatiFinsuppSupportAfterSingleSumComponents
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Tactic

set_option autoImplicit false

/-! Prove the missing spatial-derivative support shift by expanding each
polynomial in its finite monomial support and using the pinned monomial formula
for `MvPolynomial.mkDerivation`. -/

namespace NlsGge.HierarchyRiccati.Core

open scoped BigOperators
open scoped Pointwise

noncomputable section

def SpatialDerivationBidegreeShiftTargetAfterComponents : Prop :=
  ∀ (P : Poly) (d : ℕ × ℤ), HasRiccatiJetBidegreeAfterComponents P d →
    HasRiccatiJetBidegreeAfterComponents (spatialD P) (d.1 + 1, d.2)

@[simp] private theorem riccatiJetBidegreeAfterComponents_add (m n : Jet →₀ ℕ) :
    riccatiJetBidegreeAfterComponents (m + n) =
      riccatiJetBidegreeAfterComponents m + riccatiJetBidegreeAfterComponents n := by
  simp [riccatiJetBidegreeAfterComponents]

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

private theorem riccatiJetBidegreeAfterComponents_replacement (m : Jet →₀ ℕ) (v : Jet)
    (hv : v ∈ m.support) :
    riccatiJetBidegreeAfterComponents
      (m - Finsupp.single v 1 + Finsupp.single (v.1, v.2 + 1) 1) =
        ((riccatiJetBidegreeAfterComponents m).1 + 1,
          (riccatiJetBidegreeAfterComponents m).2) := by
  have hne : m v ≠ 0 := Finsupp.mem_support_iff.mp hv
  have hdecomp :
      riccatiJetBidegreeAfterComponents m =
        riccatiJetBidegreeAfterComponents (m - Finsupp.single v 1) +
          riccatiJetBidegreeAfterComponents (Finsupp.single v 1) := by
    calc
      riccatiJetBidegreeAfterComponents m =
          riccatiJetBidegreeAfterComponents
            (m - Finsupp.single v 1 + Finsupp.single v 1) :=
        congrArg riccatiJetBidegreeAfterComponents
          (Finsupp.sub_add_single_one_cancel hne).symm
      _ = _ := riccatiJetBidegreeAfterComponents_add _ _
  have hOld : riccatiJetBidegreeAfterComponents (Finsupp.single v 1) =
      (v.2 + 1, if v.1 then 1 else -1) := by
    simp [riccatiJetBidegreeAfterComponents,
      riccatiJetWeightHomAfterComponents_single,
      riccatiJetGaugeHomAfterComponents_single]
  have hNew : riccatiJetBidegreeAfterComponents (Finsupp.single (v.1, v.2 + 1) 1) =
      (v.2 + 2, if v.1 then 1 else -1) := by
    simp [riccatiJetBidegreeAfterComponents,
      riccatiJetWeightHomAfterComponents_single,
      riccatiJetGaugeHomAfterComponents_single]
  rw [riccatiJetBidegreeAfterComponents_add, hdecomp, hOld, hNew]
  apply Prod.ext
  · change (riccatiJetBidegreeAfterComponents (m - Finsupp.single v 1)).1 + (v.2 + 2) =
      ((riccatiJetBidegreeAfterComponents (m - Finsupp.single v 1)).1 + (v.2 + 1)) + 1
    omega
  · change (riccatiJetBidegreeAfterComponents (m - Finsupp.single v 1)).2 +
        (if v.1 then 1 else -1) =
      (riccatiJetBidegreeAfterComponents (m - Finsupp.single v 1)).2 +
        (if v.1 then 1 else -1)
    rfl

private theorem hasRiccatiJetBidegreeAfterComponents_monomial (m : Jet →₀ ℕ) (a : ℤ) :
    HasRiccatiJetBidegreeAfterComponents (MvPolynomial.monomial m a) (riccatiJetBidegreeAfterComponents m) := by
  classical
  intro n hn
  have hn' : n = m := by
    exact Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hn)
  subst n
  rfl

private def riccatiSpatialMonomialTermAfterComponents (m : Jet →₀ ℕ) (v : Jet) (k : ℕ) : Poly :=
  MvPolynomial.monomial (m - Finsupp.single v 1) (k : ℤ) *
    MvPolynomial.X (v.1, v.2 + 1)

private theorem riccatiSpatialMonomialTermAfterComponents_bidegree (m : Jet →₀ ℕ) (v : Jet)
    (k : ℕ) (hv : v ∈ m.support) :
    HasRiccatiJetBidegreeAfterComponents (riccatiSpatialMonomialTermAfterComponents m v k)
      ((riccatiJetBidegreeAfterComponents m).1 + 1, (riccatiJetBidegreeAfterComponents m).2) := by
  have hm := hasRiccatiJetBidegreeAfterComponents_monomial (m - Finsupp.single v 1) (k : ℤ)
  have hX := hasRiccatiJetBidegreeAfterComponents_X (v.1, v.2 + 1)
  have hprod := hasRiccatiJetBidegreeAfterComponents_mul hm hX
  have hsingleNew :
      riccatiJetBidegreeAfterComponents (Finsupp.single (v.1, v.2 + 1) 1) =
        (v.2 + 2, if v.1 then 1 else -1) := by
    simp [riccatiJetBidegreeAfterComponents,
      riccatiJetWeightHomAfterComponents_single,
      riccatiJetGaugeHomAfterComponents_single]
  have hsum := riccatiJetBidegreeAfterComponents_add
    (m - Finsupp.single v 1) (Finsupp.single (v.1, v.2 + 1) 1)
  have htarget :
      riccatiJetBidegreeAfterComponents (m - Finsupp.single v 1) +
          (v.2 + 2, if v.1 then 1 else -1) =
        ((riccatiJetBidegreeAfterComponents m).1 + 1,
          (riccatiJetBidegreeAfterComponents m).2) := by
    calc
      _ = riccatiJetBidegreeAfterComponents (m - Finsupp.single v 1) +
            riccatiJetBidegreeAfterComponents (Finsupp.single (v.1, v.2 + 1) 1) := by
          rw [hsingleNew]
      _ = riccatiJetBidegreeAfterComponents
            (m - Finsupp.single v 1 + Finsupp.single (v.1, v.2 + 1) 1) := hsum.symm
      _ = _ := riccatiJetBidegreeAfterComponents_replacement m v hv
  simpa [riccatiSpatialMonomialTermAfterComponents, htarget] using hprod

private theorem hasRiccatiJetBidegreeAfterComponents_int_smul {P : Poly} {d : ℕ × ℤ}
    (a : ℤ) (hP : HasRiccatiJetBidegreeAfterComponents P d) :
    HasRiccatiJetBidegreeAfterComponents (a • P) d := by
  intro m hm
  exact hP m (MvPolynomial.support_smul hm)

private theorem spatialD_monomial_bidegree_after_components (m : Jet →₀ ℕ) (a : ℤ) :
    HasRiccatiJetBidegreeAfterComponents (spatialD (MvPolynomial.monomial m a))
      ((riccatiJetBidegreeAfterComponents m).1 + 1, (riccatiJetBidegreeAfterComponents m).2) := by
  classical
  have hsum : HasRiccatiJetBidegreeAfterComponents
      (m.sum fun v k =>
        MvPolynomial.monomial (m - Finsupp.single v 1) (k : ℤ) •
          MvPolynomial.X (v.1, v.2 + 1))
      ((riccatiJetBidegreeAfterComponents m).1 + 1, (riccatiJetBidegreeAfterComponents m).2) := by
    change HasRiccatiJetBidegreeAfterComponents
      (m.support.sum fun v =>
        MvPolynomial.monomial (m - Finsupp.single v 1) ((m v : ℕ) : ℤ) •
          MvPolynomial.X (v.1, v.2 + 1))
      ((riccatiJetBidegreeAfterComponents m).1 + 1, (riccatiJetBidegreeAfterComponents m).2)
    apply hasRiccatiJetBidegreeAfterComponents_sum
    intro v hv
    simpa [smul_eq_mul, riccatiSpatialMonomialTermAfterComponents] using
      riccatiSpatialMonomialTermAfterComponents_bidegree m v (m v) hv
  have hformula : spatialD (MvPolynomial.monomial m a) =
      a • (m.sum fun v k =>
        MvPolynomial.monomial (m - Finsupp.single v 1) (k : ℤ) •
          MvPolynomial.X (v.1, v.2 + 1)) := by
    simpa [spatialD] using
        (MvPolynomial.mkDerivation_monomial (R := ℤ) (σ := Jet) (A := Poly)
        (fun v : Jet => MvPolynomial.X (v.1, v.2 + 1)) m a)
  rw [hformula]
  exact hasRiccatiJetBidegreeAfterComponents_int_smul a hsum

theorem spatialDerivation_bidegree_shift_after_components : SpatialDerivationBidegreeShiftTargetAfterComponents := by
  intro P d hP
  have hsum : HasRiccatiJetBidegreeAfterComponents
      (P.support.sum fun m => spatialD (MvPolynomial.monomial m (P.coeff m)))
      (d.1 + 1, d.2) := by
    apply hasRiccatiJetBidegreeAfterComponents_sum
    intro m hm
    simpa [hP m hm] using spatialD_monomial_bidegree_after_components m (P.coeff m)
  have hEq : spatialD P =
      P.support.sum fun m => spatialD (MvPolynomial.monomial m (P.coeff m)) := by
    calc
      spatialD P = spatialD (∑ m ∈ P.support, MvPolynomial.monomial m (P.coeff m)) := by
        nth_rw 1 [MvPolynomial.as_sum P]
      _ = ∑ m ∈ P.support, spatialD (MvPolynomial.monomial m (P.coeff m)) := by
        simp only [map_sum]
      _ = P.support.sum fun m => spatialD (MvPolynomial.monomial m (P.coeff m)) := rfl
  rw [hEq]
  exact hsum


end

end NlsGge.HierarchyRiccati.Core
