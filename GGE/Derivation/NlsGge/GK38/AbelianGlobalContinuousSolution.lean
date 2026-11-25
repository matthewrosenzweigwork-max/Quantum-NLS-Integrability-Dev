import NlsGge.GK38.AbelianSolutionCovering
import NlsGge.GK38.AbelianFreeSolutionFiber
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-! Uncompiled global continuation via EARNED actual covering/free fiber.
The literal actual hQ is the sole parent-P4 realization dependency. The
physical real Hilbert base is contractible and locally path-connected by
the pinned topological-vector-space instances, never by an assumed oracle. -/
set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p5Global_solution_lift_of_actual_inverse38 (n : ℤ)
    (hQ : ∀ p : p5RealSolutionSpace38 n,
      (fderiv ℝ (p3RealFn38 n p.val.1) p.val.2).IsInvertible) :
    ∃! L : C(PhysicalL2,p5RealSolutionSpace38 n),
      L (0 : PhysicalL2)=p5FreeSolution38 n ∧ p5RealSolutionProjection38 n ∘ L=id := by
  have hcov := p5SolutionProjection_covering_of_actual_inverse38 n hQ
  exact hcov.existsUnique_continuousMap_lifts (ContinuousMap.id PhysicalL2) 0
    (p5FreeSolution38 n) (p5FreeSolution_projection38 n)

theorem p5Global_continuous_gap_solution_of_actual_inverse38 (n : ℤ)
    (hQ : ∀ p : p5RealSolutionSpace38 n,
      (fderiv ℝ (p3RealFn38 n p.val.1) p.val.2).IsInvertible) :
    ∃! σ : C(PhysicalL2,P3RealSpace38 n),
      ∀ u : PhysicalL2, σ u ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u (σ u)=0 := by
  obtain ⟨L,⟨hLzero,hLproj⟩,hLunique⟩ := p5Global_solution_lift_of_actual_inverse38 n hQ
  let σ : C(PhysicalL2,P3RealSpace38 n) :=
    ⟨fun u => (L u).val.2,continuous_snd.comp (continuous_subtype_val.comp L.continuous)⟩
  have hfirst (u : PhysicalL2) : (L u).val.1=u := congrFun hLproj u
  have hσ (u : PhysicalL2) : σ u ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u (σ u)=0 := by
    have hp := (L u).property
    change (L u).val.2 ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u (L u).val.2=0
    simpa only [hfirst] using hp
  refine ⟨σ,hσ,?_⟩
  intro τ hτ
  let M : C(PhysicalL2,p5RealSolutionSpace38 n) :=
    ⟨fun u => ⟨(u,τ u),hτ u⟩,
      (continuous_id.prodMk τ.continuous).subtype_mk hτ⟩
  have hMzero : M (0 : PhysicalL2)=p5FreeSolution38 n :=
    p5FreeSolution_fiber_unique38 n (M 0) rfl
  have hMproj : p5RealSolutionProjection38 n ∘ M=id := rfl
  have he : M=L := hLunique M ⟨hMzero,hMproj⟩
  apply ContinuousMap.ext
  intro u
  exact congrArg (fun K : C(PhysicalL2,p5RealSolutionSpace38 n) => (K u).val.2) he

end
end NlsGge.GK38
