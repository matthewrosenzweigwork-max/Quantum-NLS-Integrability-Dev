import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Set.UnionLift

/-! Analytic functions with earned pointwise overlap agreement glue on the
actual open union. The pinned Set.iUnionLift supplies the set-theoretic gluing;
local equality on an OPEN chart supplies genuine analytic regularity. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38.P6AnalyticGluing
noncomputable section
variable {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem exists_analytic_eqOn_open_union (U : I → Set E) (hU : ∀ i, IsOpen (U i))
    (f : I → E → F) (ha : ∀ i, AnalyticOnNhd ℂ (f i) (U i))
    (hc : ∀ i j x, x ∈ U i → x ∈ U j → f i x=f j x) :
    ∃ g : E → F, AnalyticOnNhd ℂ g (⋃ i, U i) ∧ ∀ i, EqOn g (f i) (U i) := by
  classical
  let W : Set E := ⋃ i, U i
  let G : W → F := Set.iUnionLift U (fun i x => f i x.val)
    (fun i j x hi hj => hc i j x hi hj) W (by intro x hx; exact hx)
  let g : E → F := fun x => if hx : x ∈ W then G ⟨x,hx⟩ else 0
  have heq (i : I) : EqOn g (f i) (U i) := by
    intro x hx
    have hxW : x ∈ W := mem_iUnion.mpr ⟨i,hx⟩
    change (if h : x ∈ W then G ⟨x,h⟩ else 0)=f i x
    rw [dite_eq_left hxW]
    exact Set.iUnionLift_of_mem ⟨x,hxW⟩ hx
  refine ⟨g,?_,heq⟩
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  have hlocal : f i =ᶠ[𝓝 x] g := by
    filter_upwards [(hU i).mem_nhds hi] with y hy
    exact (heq i hy).symm
  exact (ha i x hi).congr hlocal

end
end NlsGge.GK38.P6AnalyticGluing
