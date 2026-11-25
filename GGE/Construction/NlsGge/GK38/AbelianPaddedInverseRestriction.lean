import NlsGge.GK38.AbelianPaddedOperatorInverse
import NlsGge.GK38.AbelianPaddedJacobianEquicontinuity

/-! The literal block padding is diag(A,2), so its genuine inverse earns
omitted-operator invertibility as well. This is not a general matrix-entry
claim about an arbitrary invertible operator. -/
set_option autoImplicit false
namespace NlsGge.GK38
noncomputable section

theorem p6PadOperator_restrict38 (n : ℤ) (A : P2Space38 n →L[ℂ] P2Space38 n)
    (x : Lib.L2Seq) : p2Restrict38 n (p6PadOperator38 n A x)=A (p2Restrict38 n x) := by
  apply Subtype.ext
  funext m
  exact p6PadOperator_other38 n A x m

theorem p6PadOperator_extend38 (n : ℤ) (A : P2Space38 n →L[ℂ] P2Space38 n)
    (x : P2Space38 n) : p6PadOperator38 n A (p2Extend38 n x)=p2Extend38 n (A x) := by
  apply Subtype.ext
  funext m
  by_cases hm : m=n
  · subst m
    rw [p6PadOperator_self38,p2Extend_self38,p2Extend_self38,mul_zero]
  · change p6PadOperator38 n A (p2Extend38 n x) (⟨m,hm⟩ : P2Index38 n).val=_
    rw [p6PadOperator_other38,p2Restrict_extend38,p2Extend_at38 n (A x) ⟨m,hm⟩]

theorem p6PadOperator_invertible_iff38 (n : ℤ)
    (A : P2Space38 n →L[ℂ] P2Space38 n) :
    (p6PadOperator38 n A).IsInvertible ↔ A.IsInvertible := by
  constructor
  · intro hpad
    have hinj : Function.Injective A := by
      intro x y hxy
      have hext : p2Extend38 n x=p2Extend38 n y := hpad.bijective.1
        (by rw [p6PadOperator_extend38,p6PadOperator_extend38,hxy])
      have h := congrArg (p2Restrict38 n) hext
      simpa only [p2Restrict_extend38] using h
    have hsurj : Function.Surjective A := by
      intro y
      obtain ⟨x,hx⟩ := hpad.bijective.2 (p2Extend38 n y)
      refine ⟨p2Restrict38 n x,?_⟩
      have h := congrArg (p2Restrict38 n) hx
      simpa only [p6PadOperator_restrict38,p2Restrict_extend38] using h
    let e := ContinuousLinearEquiv.ofBijective A
      (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)
    exact ⟨e,rfl⟩
  · exact p6PadOperator_isInvertible38 n A

theorem p6PaddedJacobian_earns_omitted_inverse38 (n : ℤ) (φ : PotPair) (s : Lib.L2Seq)
    (hQ : (p6PaddedJacobian38 n φ s).IsInvertible) :
    (fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (φ,t)) (p2Restrict38 n s)).IsInvertible := by
  exact (p6PadOperator_invertible_iff38 n _).mp hQ

end
end NlsGge.GK38
