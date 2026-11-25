import Mathlib

                                                                                                                       
                                                                                                                      
                                                                                                                             
                                                                                                               
                                                                                                                  
                                                                                                                         
                                                                                                                  
                                                                                                             
set_option autoImplicit false
open Set Filter
open scoped Topology

namespace NlsGge.Birkhoff
namespace R132Aux

theorem chart_of {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T : E → E) (hT : ContDiff ℝ 1 T) (U : Set E) (hU : IsOpen U) (hinj : Set.InjOn T U)
    (hdet : ∀ x ∈ U, (fderiv ℝ T x).det ≠ 0) :
    ∃ S : E → E, IsOpen (T '' U) ∧ Set.BijOn T U (T '' U) ∧ Set.MapsTo S (T '' U) U ∧
      (∀ x : E, x ∈ U → S (T x) = x) ∧ (∀ y : E, y ∈ T '' U → T (S y) = y) ∧
      ContDiffOn ℝ 1 T U ∧ ContDiffOn ℝ 1 S (T '' U) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  -- invertibility of the derivative first
  have hder : ∀ x (hx : x ∈ U), HasFDerivAt T
      (((fderiv ℝ T x).toContinuousLinearEquivOfDetNeZero (hdet x hx) : E ≃L[ℝ] E) : E →L[ℝ] E) x := by
    intro x hx
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact ((hT.differentiable one_ne_zero) x).hasFDerivAt
  have hstrict : ∀ x (hx : x ∈ U), HasStrictFDerivAt T
      (((fderiv ℝ T x).toContinuousLinearEquivOfDetNeZero (hdet x hx) : E ≃L[ℝ] E) : E →L[ℝ] E) x :=
    fun x hx => hT.contDiffAt.hasStrictFDerivAt' (hder x hx) one_ne_zero
  set S : E → E := Function.invFunOn T U with hSdef
  have hS1 : ∀ y ∈ T '' U, S y ∈ U ∧ T (S y) = y := by
    rintro y ⟨x, hx, rfl⟩
    exact Function.invFunOn_pos ⟨x, hx, rfl⟩
  have hS2 : ∀ x ∈ U, S (T x) = x := fun x hx =>
    hinj (hS1 (T x) ⟨x, hx, rfl⟩).1 hx (hS1 (T x) ⟨x, hx, rfl⟩).2
  refine ⟨S, ?_, ⟨mapsTo_image T U, hinj, surjOn_image T U⟩, fun y hy => (hS1 y hy).1, hS2,
    fun y hy => (hS1 y hy).2, hT.contDiffOn, ?_⟩
  · refine isOpen_iff_mem_nhds.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [← (hstrict x hx).map_nhds_eq_of_equiv]
    exact image_mem_map (hU.mem_nhds hx)
  · rintro _ ⟨x, hx, rfl⟩
    have hca : ContDiffAt ℝ 1 T x := hT.contDiffAt
    have hg := hca.to_localInverse (hder x hx) one_ne_zero
    have hev : S =ᶠ[𝓝 (T x)] hca.localInverse (hder x hx) one_ne_zero := by
      have h1 := (hstrict x hx).eventually_right_inverse
      have h2 := (hstrict x hx).localInverse_tendsto.eventually (hU.mem_nhds hx)
      filter_upwards [h1, h2] with y hy1 hy2
      have hyim : y ∈ T '' U := ⟨_, hy2, hy1⟩
      obtain ⟨hSU, hTS⟩ := hS1 y hyim
      exact hinj hSU hy2 (hTS.trans hy1.symm)
    exact (hg.congr_of_eventuallyEq hev).contDiffWithinAt

end R132Aux
end NlsGge.Birkhoff
