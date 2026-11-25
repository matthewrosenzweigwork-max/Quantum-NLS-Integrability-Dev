import NlsGge.GK38.AbelianGlobalContinuousSolution
import Mathlib.Topology.Homeomorph.Defs

/-! Uncompiled pointwise uniqueness: actual covering monodromy transports
EVERY fiber to the actual singleton free fiber. No solution is omitted by
merely considering the chosen global continuous section. -/
set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p5SolutionProjection_injective_of_actual_inverse38 (n : ℤ)
    (hQ : ∀ p : p5RealSolutionSpace38 n,
      (fderiv ℝ (p3RealFn38 n p.val.1) p.val.2).IsInvertible) :
    Function.Injective (p5RealSolutionProjection38 n) := by
  have hcov := p5SolutionProjection_covering_of_actual_inverse38 n hQ
  intro p q he
  let u : PhysicalL2 := p5RealSolutionProjection38 n p
  let γ : Path.Homotopic.Quotient u (0 : PhysicalL2) :=
    .mk (PathConnectedSpace.somePath u 0)
  let p' : (p5RealSolutionProjection38 n) ⁻¹' {u} := ⟨p,rfl⟩
  let q' : (p5RealSolutionProjection38 n) ⁻¹' {u} := ⟨q,he.symm⟩
  have hp0 : (hcov.monodromy γ p').val=p5FreeSolution38 n :=
    p5FreeSolution_fiber_unique38 n _ (hcov.monodromy γ p').property
  have hq0 : (hcov.monodromy γ q').val=p5FreeSolution38 n :=
    p5FreeSolution_fiber_unique38 n _ (hcov.monodromy γ q').property
  have himage : hcov.monodromy γ p'=hcov.monodromy γ q' :=
    Subtype.ext (hp0.trans hq0.symm)
  have hpq : p'=q' := (hcov.monodromy_bijective γ).injective himage
  exact congrArg Subtype.val hpq

theorem p5SolutionProjection_bijective_of_actual_inverse38 (n : ℤ)
    (hQ : ∀ p : p5RealSolutionSpace38 n,
      (fderiv ℝ (p3RealFn38 n p.val.1) p.val.2).IsInvertible) :
    Function.Bijective (p5RealSolutionProjection38 n) := by
  refine ⟨p5SolutionProjection_injective_of_actual_inverse38 n hQ,?_⟩
  obtain ⟨L,⟨_hLzero,hLproj⟩,_hLunique⟩ := p5Global_solution_lift_of_actual_inverse38 n hQ
  intro u
  exact ⟨L u,congrFun hLproj u⟩

theorem p5SolutionProjection_homeomorph_of_actual_inverse38 (n : ℤ)
    (hQ : ∀ p : p5RealSolutionSpace38 n,
      (fderiv ℝ (p3RealFn38 n p.val.1) p.val.2).IsInvertible) :
    ∃ H : p5RealSolutionSpace38 n ≃ₜ PhysicalL2,
      (H : p5RealSolutionSpace38 n → PhysicalL2)=p5RealSolutionProjection38 n := by
  let e := Equiv.ofBijective (p5RealSolutionProjection38 n)
    (p5SolutionProjection_bijective_of_actual_inverse38 n hQ)
  let H := e.toHomeomorphOfContinuousClosed
    (p5SolutionProjection_covering_of_actual_inverse38 n hQ).continuous
    (p5RealSolutionProjection_isClosedMap38 n)
  exact ⟨H,rfl⟩

theorem p5Actual_gap_solution_pointwise_unique_of_inverse38 (n : ℤ)
    (hQ : ∀ p : p5RealSolutionSpace38 n,
      (fderiv ℝ (p3RealFn38 n p.val.1) p.val.2).IsInvertible) (u : PhysicalL2) :
    ∃! t : P3RealSpace38 n, t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t=0 := by
  obtain ⟨σ,hσ,_hunique⟩ := p5Global_continuous_gap_solution_of_actual_inverse38 n hQ
  refine ⟨σ u,hσ u,?_⟩
  intro t ht
  let p : p5RealSolutionSpace38 n := ⟨(u,t),ht⟩
  let q : p5RealSolutionSpace38 n := ⟨(u,σ u),hσ u⟩
  have he : p=q := p5SolutionProjection_injective_of_actual_inverse38 n hQ
    (show p5RealSolutionProjection38 n p=p5RealSolutionProjection38 n q from rfl)
  exact congrArg (fun x : p5RealSolutionSpace38 n => x.val.2) he

end
end NlsGge.GK38
