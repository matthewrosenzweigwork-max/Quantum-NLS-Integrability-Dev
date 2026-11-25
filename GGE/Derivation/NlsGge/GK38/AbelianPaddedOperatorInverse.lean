import NlsGge.GK38.AbelianRestriction
import Mathlib.Analysis.Normed.Operator.Banach

/-! Genuine full-space padding preserves actual omitted-operator invertibility.
The missing coordinate is multiplied by 2, including index zero. -/
set_option autoImplicit false
open Set
namespace NlsGge.GK38
noncomputable section

def p6PadOperator38 (n : ℤ) (A : P2Space38 n →L[ℂ] P2Space38 n) :
    Lib.L2Seq →L[ℂ] Lib.L2Seq :=
  (p2Extend38 n).comp (A.comp (p2Restrict38 n))+
    (2 : ℂ) • ((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 n).comp
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n))

theorem p6PadOperator_self38 (n : ℤ) (A : P2Space38 n →L[ℂ] P2Space38 n)
    (x : Lib.L2Seq) : p6PadOperator38 n A x n=2*x n := by
  change p2Extend38 n (A (p2Restrict38 n x)) n+
    (2 : ℂ)*(lp.single (E := fun _ : ℤ => ℂ) 2 n (x n)) n=_
  rw [p2Extend_self38,lp.single_apply_self,zero_add]

theorem p6PadOperator_other38 (n : ℤ) (A : P2Space38 n →L[ℂ] P2Space38 n)
    (x : Lib.L2Seq) (m : P2Index38 n) :
    p6PadOperator38 n A x m.val=A (p2Restrict38 n x) m := by
  change p2Extend38 n (A (p2Restrict38 n x)) m.val+
    (2 : ℂ)*(lp.single (E := fun _ : ℤ => ℂ) 2 n (x n)) m.val=_
  rw [p2Extend_at38,lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 n (x n) m.property,
    mul_zero,add_zero]

theorem p6PadOperator_isInvertible38 (n : ℤ)
    (A : P2Space38 n →L[ℂ] P2Space38 n) (hA : A.IsInvertible) :
    (p6PadOperator38 n A).IsInvertible := by
  have hinjA := hA.bijective.1
  obtain ⟨e,he⟩ := hA
  have hkernel (x : Lib.L2Seq) (hx : p6PadOperator38 n A x=0) : x=0 := by
    have hn := congrArg (fun z : Lib.L2Seq => z n) hx
    rw [p6PadOperator_self38] at hn
    change (2 : ℂ)*x n=0 at hn
    have hxn : x n=0 := (mul_eq_zero.mp hn).resolve_left (by norm_num)
    have hAx : A (p2Restrict38 n x)=0 := by
      apply Subtype.ext
      funext m
      have hm := congrArg (fun z : Lib.L2Seq => z m.val) hx
      rw [p6PadOperator_other38] at hm
      exact hm
    have hRx : p2Restrict38 n x=0 := hinjA (hAx.trans (map_zero A).symm)
    apply Subtype.ext
    funext m
    by_cases hm : m=n
    · subst m
      exact hxn
    · exact congrArg (fun z : P2Space38 n => z ⟨m,hm⟩) hRx
  have hinj : Function.Injective (p6PadOperator38 n A) := by
    intro x y hxy
    exact sub_eq_zero.mp (hkernel (x-y) (by rw [map_sub,hxy,sub_self]))
  have hsurj : Function.Surjective (p6PadOperator38 n A) := by
    intro y
    let x : Lib.L2Seq := p2Extend38 n (e.symm (p2Restrict38 n y))+
      lp.single 2 n (y n/2)
    have hxn : x n=y n/2 := by
      change p2Extend38 n (e.symm (p2Restrict38 n y)) n+
        (lp.single (E := fun _ : ℤ => ℂ) 2 n (y n/2)) n=_
      rw [p2Extend_self38,lp.single_apply_self,zero_add]
    have hRx : p2Restrict38 n x=e.symm (p2Restrict38 n y) := by
      apply Subtype.ext
      funext m
      change p2Extend38 n (e.symm (p2Restrict38 n y)) m.val+
        (lp.single (E := fun _ : ℤ => ℂ) 2 n (y n/2)) m.val=_
      rw [p2Extend_at38,lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 n (y n/2)
        m.property,add_zero]
    refine ⟨x,?_⟩
    apply Subtype.ext
    funext m
    by_cases hm : m=n
    · subst m
      rw [p6PadOperator_self38,hxn]
      ring
    · change p6PadOperator38 n A x (⟨m,hm⟩ : P2Index38 n).val=y m
      rw [p6PadOperator_other38,hRx,← he]
      exact congrArg (fun z : P2Space38 n => z ⟨m,hm⟩) (e.apply_symm_apply (p2Restrict38 n y))
  let E := ContinuousLinearEquiv.ofBijective (p6PadOperator38 n A)
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)
  exact ⟨E,rfl⟩

end
end NlsGge.GK38
