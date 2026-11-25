import NlsGge.GK38.AbelianClosedSolutionProjection

/-! Uncompiled ACTUAL free solution and singleton free fiber, earned from
the accepted all-complex free Fn fixture and actual collapsed free gaps. -/
set_option autoImplicit false
open Set
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p5RealFn_free_zero38 (n : ℤ) :
    p3RealFn38 n (0 : PhysicalL2) (0 : P3RealSpace38 n)=0 := by
  apply (p3RealInclude38 n).injective
  rw [p3RealFn_graph38]
  simpa only [map_zero] using P3FreeDerivative.actualFn_zero n

theorem p5RealGapCube_free_zero38 (n : ℤ) :
    (0 : P3RealSpace38 n) ∈ p5RealGapCube38 n (0 : PhysicalL2) := by
  intro m
  change countingCenter38 m.1+(0 : ℂ) ∈ segment ℝ
    (lamMinus (realSlice (0 : PhysicalL2)) m.1) (lamPlus (realSlice (0 : PhysicalL2)) m.1)
  simp only [map_zero,lamMinus_zero38,lamPlus_zero38,add_zero,segment_same,mem_singleton_iff]

theorem p5RealGapCube_free_unique38 (n : ℤ) (t : P3RealSpace38 n)
    (ht : t ∈ p5RealGapCube38 n (0 : PhysicalL2)) : t=0 := by
  apply Subtype.ext
  funext m
  change t m=0
  have hm := ht m
  simp only [map_zero,lamMinus_zero38,lamPlus_zero38,segment_same,mem_singleton_iff] at hm
  have hc : (t m : ℂ)=0 := add_left_cancel (show
      countingCenter38 m.1+(t m : ℂ)=countingCenter38 m.1+0 by
    simpa only [add_zero] using hm)
  exact Complex.ofReal_injective hc

def p5FreeSolution38 (n : ℤ) : p5RealSolutionSpace38 n :=
  ⟨(0,0),p5RealGapCube_free_zero38 n,p5RealFn_free_zero38 n⟩

theorem p5FreeSolution_projection38 (n : ℤ) :
    p5RealSolutionProjection38 n (p5FreeSolution38 n)=0 := rfl

theorem p5FreeSolution_fiber_unique38 (n : ℤ) (p : p5RealSolutionSpace38 n)
    (hp : p5RealSolutionProjection38 n p=0) : p=p5FreeSolution38 n := by
  have he : p.val.1=0 := hp
  apply Subtype.ext
  apply Prod.ext
  · exact he
  · apply p5RealGapCube_free_unique38 n p.val.2
    rw [← he]
    exact p.property.1

end
end NlsGge.GK38
