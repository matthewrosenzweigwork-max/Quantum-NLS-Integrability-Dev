import NlsGge.GK38.AbelianFullRealInverse
import Mathlib.Analysis.Normed.Operator.Banach

/-! Actual full complex Qstar invertibility at real original-family inputs,
earned by real/imaginary coordinates and the actual real inverse. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38.P6FullJacobian
noncomputable section

theorem actual_complex_Qstar_coordinates (u : PhysicalL2) (s : P6RealSpace38)
    (z : Lib.L2Seq) :
    p6Qstar38 (realSlice u) (p6RealInclude38 s) z=
      p6RealInclude38 (p6RealQstar38 u s (p6RealPart38 z))+
        Complex.I • p6RealInclude38 (p6RealQstar38 u s (p6ImagPart38 z)) := by
  let Q := p6Qstar38 (realSlice u) (p6RealInclude38 s)
  calc
    Q z=Q (p6RealInclude38 (p6RealPart38 z)+
        Complex.I • p6RealInclude38 (p6ImagPart38 z)) := congrArg Q (p6Complex_coordinates38 z)
    _ = _ := by rw [map_add,map_smul,← p6RealQstar_include38,← p6RealQstar_include38]

theorem actual_complex_Qstar_inverse_of_real_inverse (u : PhysicalL2)
    (s : P6RealSpace38) (hreal : (p6RealQstar38 u s).IsInvertible) :
    (p6Qstar38 (realSlice u) (p6RealInclude38 s)).IsInvertible := by
  let Q := p6Qstar38 (realSlice u) (p6RealInclude38 s)
  let A := p6RealQstar38 u s
  have hinjA : Function.Injective A := hreal.bijective.1
  obtain ⟨e,he⟩ := hreal
  have hAe (x : P6RealSpace38) : A (e.symm x)=x := by
    change p6RealQstar38 u s (e.symm x)=x
    rw [← he]
    exact e.apply_symm_apply x
  have hkernel (z : Lib.L2Seq) (hz : Q z=0) : z=0 := by
    have hr := congrArg p6RealPart38 hz
    have hi := congrArg p6ImagPart38 hz
    rw [actual_complex_Qstar_coordinates u s z,map_add,p6RealPart_include38,
      p6RealPart_I_include38,map_zero,add_zero] at hr
    rw [actual_complex_Qstar_coordinates u s z,map_add,p6ImagPart_include38,
      p6ImagPart_I_include38,map_zero,zero_add] at hi
    have hr' : p6RealPart38 z=0 := hinjA (by simpa only [map_zero] using hr)
    have hi' : p6ImagPart38 z=0 := hinjA (by simpa only [map_zero] using hi)
    rw [p6Complex_coordinates38 z,hr',hi',map_zero,smul_zero,add_zero]
  have hinj : Function.Injective Q := by
    intro x y hxy
    have hz : Q (x-y)=0 := by rw [map_sub,hxy,sub_self]
    exact sub_eq_zero.mp (hkernel (x-y) hz)
  have hsurj : Function.Surjective Q := by
    intro z
    refine ⟨p6RealInclude38 (e.symm (p6RealPart38 z))+
      Complex.I • p6RealInclude38 (e.symm (p6ImagPart38 z)),?_⟩
    rw [map_add,map_smul,← p6RealQstar_include38,← p6RealQstar_include38]
    change p6RealInclude38 (A (e.symm (p6RealPart38 z)))+
      Complex.I • p6RealInclude38 (A (e.symm (p6ImagPart38 z)))=z
    rw [hAe,hAe]
    exact (p6Complex_coordinates38 z).symm
  let E := ContinuousLinearEquiv.ofBijective Q
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)
  exact ⟨E,rfl⟩

theorem original_family_complex_Qstar_inverse (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R) (s : P6RealSpace38)
    (hσ : ∀ k : ℤ, Lib.sigmaOf (p6RealInclude38 s) k ∈ closedBall (C k) (R k)) :
    (p6Qstar38 (realSlice u) (p6RealInclude38 s)).IsInvertible :=
  actual_complex_Qstar_inverse_of_real_inverse u s
    (original_family_real_Qstar_inverse u C R hfam s hσ)

theorem original_family_full_Qstar_inverse (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R) (s : Lib.L2Seq)
    (hs : ∀ k : ℤ, (s k).im=0)
    (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k)) :
    (p6Qstar38 (realSlice u) s).IsInvertible := by
  have hJ := p6RealInclude_realPart38 s hs
  have hσ' : ∀ k : ℤ,
      Lib.sigmaOf (p6RealInclude38 (p6RealPart38 s)) k ∈ closedBall (C k) (R k) := by
    simpa only [hJ] using hσ
  have he := original_family_complex_Qstar_inverse u C R hfam (p6RealPart38 s) hσ'
  simpa only [hJ] using he

end
end NlsGge.GK38.P6FullJacobian
