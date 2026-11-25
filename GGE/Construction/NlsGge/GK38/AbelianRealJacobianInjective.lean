import NlsGge.GK38.AbelianDirectionRecovery
import NlsGge.GK38.AbelianNullVariationZero
import NlsGge.GK38.AbelianRealJacobian

/-! Actual real Jacobian injectivity. The null direction is transported through
the proved real/complex derivative identity, not a hypothesized matrix model. -/
set_option autoImplicit false
open Set
open NlsGge.Pilot
namespace NlsGge.GK38.P4NumeratorVariation
noncomputable section

theorem real_jacobian_kernel_zero (n : ℤ) (u : PhysicalL2) (s h : P3RealSpace38 n)
    (hinj : ∀ i j : ℤ, i ≠ n → j ≠ n →
      Lib.sigmaOf (p2Extend38 n (p3RealInclude38 n s)) i=
        Lib.sigmaOf (p2Extend38 n (p3RealInclude38 n s)) j → i=j)
    (hnull : (fderiv ℝ (p3RealFn38 n u) s) h=0) : h=0 := by
  have he := congrArg (fun T : P3RealSpace38 n →L[ℝ] P2Space38 n => T h)
    (p3RealFn_fderiv_include38 n u s)
  have hc : (fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (realSlice u,t))
      (p3RealInclude38 n s)) (p3RealInclude38 n h)=0 := by
    simp only [ContinuousLinearMap.comp_apply] at he
    change p3RealInclude38 n ((fderiv ℝ (p3RealFn38 n u) s) h)=
      (fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (realSlice u,t))
        (p3RealInclude38 n s)) (p3RealInclude38 n h) at he
    rw [hnull,map_zero] at he
    exact he.symm
  have hs : p2RealSeq38 n (p3RealInclude38 n s) := fun m => Complex.ofReal_im (s m)
  have hh : p2RealSeq38 n (p3RealInclude38 n h) := fun m => Complex.ofReal_im (h m)
  have hv := null_direction_variation_zero n u (p3RealInclude38 n s)
    (p3RealInclude38 n h) hs hh hc
  have hz := direction_zero_of_variation_zero n
    (p2Extend38 n (p3RealInclude38 n s)) (p2Extend38 n (p3RealInclude38 n h))
    (p2Extend_self38 n _) hinj hv
  apply Subtype.ext
  funext m
  have hm := congrArg (fun q : Lib.L2Seq => q m.1) hz
  rw [p2Extend_at38 n (p3RealInclude38 n h) m] at hm
  change (h m : ℂ)=0 at hm
  change h m=0
  exact Complex.ofReal_eq_zero.mp hm

theorem real_jacobian_injective (n : ℤ) (u : PhysicalL2) (s : P3RealSpace38 n)
    (hinj : ∀ i j : ℤ, i ≠ n → j ≠ n →
      Lib.sigmaOf (p2Extend38 n (p3RealInclude38 n s)) i=
        Lib.sigmaOf (p2Extend38 n (p3RealInclude38 n s)) j → i=j) :
    Function.Injective (fderiv ℝ (p3RealFn38 n u) s) := by
  intro h k he
  have hz : (fderiv ℝ (p3RealFn38 n u) s) (h-k)=0 := by
    rw [map_sub,he,sub_self]
  exact sub_eq_zero.mp (real_jacobian_kernel_zero n u s (h-k) hinj hz)

end
end NlsGge.GK38.P4NumeratorVariation
