import NlsGge.GK38.AbelianVariationAtInputRoot

/-! Recover a genuine lp2 direction from the vanishing actual variation. Only
distinctness of the retained input roots is needed; the omitted root is free. -/
set_option autoImplicit false
open Set
namespace NlsGge.GK38.P4NumeratorVariation
noncomputable section

theorem column_at_input_root_ne_zero (n r : ℤ) (hrn : r ≠ n)
    (s : Lib.L2Seq)
    (hinj : ∀ i j : ℤ, i ≠ n → j ≠ n → Lib.sigmaOf s i=Lib.sigmaOf s j → i=j) :
    p3NumeratorColumn38 n r s (Lib.sigmaOf s r) ≠ 0 := by
  let z : ℂ := Lib.sigmaOf s r
  let q : Lib.L2Seq := Lib.sOmit n s z
  have hqr : Lib.sigmaOf q r=z :=
    P3JacobianColumns.sigmaOf_sOmit_other n r hrn s z
  have hqn : Lib.sigmaOf q n=z+(Lib.piN n : ℂ) := by
    simp only [q,Lib.sigmaOf,Lib.sOmit_apply,ite_true]
    ring
  have hsep : ∀ m : ℤ, m ≠ r → Lib.sigmaOf q m ≠ Lib.sigmaOf q r := by
    intro m hmr he
    rw [hqr] at he
    by_cases hmn : m=n
    · subst m
      rw [hqn] at he
      have hp : (Lib.piN n : ℂ)=0 := by linear_combination he
      exact (Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero n)) hp
    · rw [P3JacobianColumns.sigmaOf_sOmit_other n m hmn s z] at he
      exact hmr (hinj m r hmn hrn he)
  have hprod : Lib.omitProd r q z ≠ 0 := by
    rw [← hqr]
    exact (Lib.omitProd_root_ne_zero_iff r q).mpr hsep
  exact mul_ne_zero
    (div_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero n))) hprod

theorem direction_zero_of_variation_zero (n : ℤ) (s h : Lib.L2Seq)
    (hn : h n=0)
    (hinj : ∀ i j : ℤ, i ≠ n → j ≠ n → Lib.sigmaOf s i=Lib.sigmaOf s j → i=j)
    (hzero : ∀ z : ℂ, p4NumeratorVariation38 n s h z=0) : h=0 := by
  apply Subtype.ext
  funext r
  change h r=0
  by_cases hrn : r=n
  · subst r; exact hn
  · have hv := hzero (Lib.sigmaOf s r)
    rw [variation_at_input_root n r hrn s h] at hv
    exact (mul_eq_zero.mp hv).resolve_right (column_at_input_root_ne_zero n r hrn s hinj)

end
end NlsGge.GK38.P4NumeratorVariation
