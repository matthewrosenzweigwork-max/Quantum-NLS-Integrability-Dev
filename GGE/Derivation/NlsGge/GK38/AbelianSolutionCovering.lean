import NlsGge.GK38.AbelianLocalSolutionHomeomorph
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.DiscreteSubset

/-! Uncompiled concrete compact+discrete fibers and covering. Literal actual
hQ remains the one parent-P4 realization dependency. Closedness, compactness,
discreteness, finiteness and local homeomorphism are EARNED in this chain. -/
set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p5RealSolutionFiber_isDiscrete_of_actual_inverse38 (n : ℤ)
    (hQ : ∀ p : p5RealSolutionSpace38 n,
      (fderiv ℝ (p3RealFn38 n p.val.1) p.val.2).IsInvertible) (u : PhysicalL2) :
    IsDiscrete (p5RealSolutionFiber38 n u) := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro t ht
  let p : p5RealSolutionSpace38 n := ⟨(u,t),ht⟩
  obtain ⟨U,V,ψ,_hUo,huU,hVo,htV,hψbase,_hψan,hbranch⟩ :=
    p5Actual_local_analytic_gap_graph_of_inverse38 n u t ht.1 ht.2 (hQ p)
  refine ⟨V,hVo,?_⟩
  ext t'
  constructor
  · intro ht'
    have he := ((hbranch u huU).2.2.2 t' ht'.1).mp ht'.2
    rw [hψbase] at he
    exact mem_singleton_iff.mpr he.symm
  · intro he
    rw [mem_singleton_iff] at he
    subst t'
    exact ⟨htV,ht⟩

theorem p5RealSolutionFiber_finite_of_actual_inverse38 (n : ℤ)
    (hQ : ∀ p : p5RealSolutionSpace38 n,
      (fderiv ℝ (p3RealFn38 n p.val.1) p.val.2).IsInvertible) (u : PhysicalL2) :
    (p5RealSolutionFiber38 n u).Finite :=
  (p5RealSolutionFiber_isCompact38 n u).finite
    (p5RealSolutionFiber_isDiscrete_of_actual_inverse38 n hQ u)

theorem p5SolutionProjection_finiteFiber_of_actual_inverse38 (n : ℤ)
    (hQ : ∀ p : p5RealSolutionSpace38 n,
      (fderiv ℝ (p3RealFn38 n p.val.1) p.val.2).IsInvertible) (u : PhysicalL2) :
    ((p5RealSolutionProjection38 n) ⁻¹' {u}).Finite := by
  apply Set.Finite.of_injOn (f := fun p : p5RealSolutionSpace38 n => p.val.2) ?_ ?_
    (p5RealSolutionFiber_finite_of_actual_inverse38 n hQ u)
  · intro p hp
    have he : p.val.1=u := by
      simpa only [mem_preimage,mem_singleton_iff,p5RealSolutionProjection38] using hp
    change p.val.2 ∈ p5RealSolutionFiber38 n u
    rw [← he]
    exact p.property
  · intro p hp q hq he
    have hp' : p.val.1=u := by
      simpa only [mem_preimage,mem_singleton_iff,p5RealSolutionProjection38] using hp
    have hq' : q.val.1=u := by
      simpa only [mem_preimage,mem_singleton_iff,p5RealSolutionProjection38] using hq
    apply Subtype.ext
    apply Prod.ext
    · exact hp'.trans hq'.symm
    · exact he

theorem p5SolutionProjection_covering_of_actual_inverse38 (n : ℤ)
    (hQ : ∀ p : p5RealSolutionSpace38 n,
      (fderiv ℝ (p3RealFn38 n p.val.1) p.val.2).IsInvertible) :
    IsCoveringMap (p5RealSolutionProjection38 n) := by
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  apply (p5RealSolutionProjection_isClosedMap38 n).isCoveringMapOn_of_isLocalHomeomorphOn
  · intro u _
    exact p5SolutionProjection_finiteFiber_of_actual_inverse38 n hQ u
  · simpa only [preimage_univ] using p5SolutionProjection_localHomeomorph_of_actual_inverse38 n hQ

end
end NlsGge.GK38
