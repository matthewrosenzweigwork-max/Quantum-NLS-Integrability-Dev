import NlsGge.GK38.AbelianComplexificationCoordinates
import NlsGge.GK38.AbelianActualGapJacobianInverse
import Mathlib.Analysis.Normed.Operator.Banach

/-! Complex actual Jacobian invertibility earned from actual real invertibility
and the genuine complex-linear derivative, without a complex inverse oracle. -/
set_option autoImplicit false
open Set
open NlsGge.Pilot
namespace NlsGge.GK38.P4NumeratorVariation
noncomputable section

theorem complex_jacobian_include (n : ℤ) (u : PhysicalL2) (s h : P3RealSpace38 n) :
    (fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (realSlice u,t))
      (p3RealInclude38 n s)) (p3RealInclude38 n h)=
    p3RealInclude38 n ((fderiv ℝ (p3RealFn38 n u) s) h) := by
  have he := congrArg (fun T : P3RealSpace38 n →L[ℝ] P2Space38 n => T h)
    (p3RealFn_fderiv_include38 n u s)
  simp only [ContinuousLinearMap.comp_apply] at he
  change p3RealInclude38 n ((fderiv ℝ (p3RealFn38 n u) s) h)=
    (fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (realSlice u,t))
      (p3RealInclude38 n s)) (p3RealInclude38 n h) at he
  exact he.symm

theorem complex_jacobian_coordinates (n : ℤ) (u : PhysicalL2) (s : P3RealSpace38 n)
    (z : P2Space38 n) :
    (fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (realSlice u,t))
      (p3RealInclude38 n s)) z=
    p3RealInclude38 n ((fderiv ℝ (p3RealFn38 n u) s) (p3RealPart38 n z))+
      Complex.I • p3RealInclude38 n ((fderiv ℝ (p3RealFn38 n u) s) (imagPart n z)) := by
  let Q := fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (realSlice u,t))
    (p3RealInclude38 n s)
  calc
    Q z=Q (p3RealInclude38 n (p3RealPart38 n z)+
        Complex.I • p3RealInclude38 n (imagPart n z)) := congrArg Q (complex_coordinates n z)
    _ = _ := by rw [map_add,map_smul,complex_jacobian_include,complex_jacobian_include]

theorem complex_jacobian_inverse_of_real_inverse (n : ℤ) (u : PhysicalL2)
    (s : P3RealSpace38 n) (hreal : (fderiv ℝ (p3RealFn38 n u) s).IsInvertible) :
    (fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (realSlice u,t))
      (p3RealInclude38 n s)).IsInvertible := by
  let Q := fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (realSlice u,t))
    (p3RealInclude38 n s)
  let A := fderiv ℝ (p3RealFn38 n u) s
  have hinjA : Function.Injective A := hreal.bijective.1
  obtain ⟨e,he⟩ := hreal
  have hAe (x : P3RealSpace38 n) : A (e.symm x)=x := by
    change (fderiv ℝ (p3RealFn38 n u) s) (e.symm x)=x
    rw [← he]
    exact e.apply_symm_apply x
  have hkernel (z : P2Space38 n) (hz : Q z=0) : z=0 := by
    have hr := congrArg (p3RealPart38 n) hz
    have hi := congrArg (imagPart n) hz
    rw [complex_jacobian_coordinates n u s z,map_add,p3RealPart_include38,
      realPart_I_include,map_zero,add_zero] at hr
    rw [complex_jacobian_coordinates n u s z,map_add,imagPart_include,
      imagPart_I_include,map_zero,zero_add] at hi
    have hr' : p3RealPart38 n z=0 := hinjA (by simpa only [map_zero] using hr)
    have hi' : imagPart n z=0 := hinjA (by simpa only [map_zero] using hi)
    rw [complex_coordinates n z,hr',hi',map_zero,smul_zero,add_zero]
  have hinj : Function.Injective Q := by
    intro x y hxy
    have hz : Q (x-y)=0 := by rw [map_sub,hxy,sub_self]
    exact sub_eq_zero.mp (hkernel (x-y) hz)
  have hsurj : Function.Surjective Q := by
    intro z
    refine ⟨p3RealInclude38 n (e.symm (p3RealPart38 n z))+
      Complex.I • p3RealInclude38 n (e.symm (imagPart n z)),?_⟩
    rw [map_add,map_smul,complex_jacobian_include,complex_jacobian_include]
    change p3RealInclude38 n (A (e.symm (p3RealPart38 n z)))+
      Complex.I • p3RealInclude38 n (A (e.symm (imagPart n z)))=z
    rw [hAe,hAe]
    exact (complex_coordinates n z).symm
  let E := ContinuousLinearEquiv.ofBijective Q
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)
  exact ⟨E,rfl⟩

theorem actual_gap_complex_jacobian_inverse (n : ℤ) (u : PhysicalL2)
    (s : P3RealSpace38 n) (hs : s ∈ p5RealGapCube38 n u) :
    (fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (realSlice u,t))
      (p3RealInclude38 n s)).IsInvertible :=
  complex_jacobian_inverse_of_real_inverse n u s (actual_gap_real_jacobian_inverse n u s hs)

end
end NlsGge.GK38.P4NumeratorVariation
