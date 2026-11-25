import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Tactic

/-! Bounded inverse of an arbitrary self-adjoint partial operator bounded below by one.
No discrete spectrum or compact resolvent hypothesis is used. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped InnerProductSpace ComplexOrder
namespace QuantumNLS.BoundedInverseR13
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The literal quadratic-form lower bound on the operator domain. -/
def LowerOne (A : E →ₗ.[ℂ] E) : Prop :=
  ∀ x : A.domain, ‖(x : E)‖^2 ≤ (inner ℂ (A x) (x : E)).re

omit [CompleteSpace E] in
theorem norm_le (A : E →ₗ.[ℂ] E) (h : LowerOne A) (x : A.domain) :
    ‖(x : E)‖ ≤ ‖A x‖ := by
  have hi := re_inner_le_norm (𝕜 := ℂ) (A x) (x : E)
  change (inner ℂ (A x) (x : E)).re ≤ ‖A x‖ * ‖(x : E)‖ at hi
  have hl := h x
  by_cases hz : ‖(x : E)‖ = 0
  · simp [hz]
  · have hp := (norm_nonneg (x : E)).lt_of_ne' hz
    nlinarith

omit [CompleteSpace E] in
theorem injective (A : E →ₗ.[ℂ] E) (h : LowerOne A) : Function.Injective A := by
  intro x y hxy
  apply Subtype.ext
  have hh := norm_le A h (x-y)
  simp only [LinearPMap.map_sub,hxy,sub_self,norm_zero] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

theorem closed_range (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (h : LowerOne A) :
    IsClosed (A.toFun.range : Set E) := by
  let : CompleteSpace A.graph := hA.isClosed.completeSpace_coe
  let j : A.graph →ₗᵢ[ℂ] E :=
    { toLinearMap := (LinearMap.snd ℂ E E).comp A.graph.subtype
      norm_map' := by
        intro z
        obtain ⟨x,hx,hy⟩ := (A.mem_graph_iff).mp z.property
        change ‖z.val.2‖ = ‖z.val‖
        rw [Prod.norm_def,← hx,← hy,max_eq_right (norm_le A h x)] }
  have hr : Set.range j = (A.toFun.range : Set E) := by
    ext y
    constructor
    · rintro ⟨z,rfl⟩
      obtain ⟨x,_,hy⟩ := (A.mem_graph_iff).mp z.property
      exact ⟨x,hy⟩
    · rintro ⟨x,rfl⟩
      exact ⟨⟨((x : E),A x),A.mem_graph x⟩,rfl⟩
  rw [← hr]
  exact j.isometry.isClosedEmbedding.isClosed_range

theorem range_orthogonal (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (h : LowerOne A) :
    A.toFun.rangeᗮ = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro y hy
  have ho : ∀ x : A.domain, inner ℂ y (A x) = 0 := by
    intro x
    exact (A.toFun.range.mem_orthogonal' y).mp hy (A x) ⟨x,rfl⟩
  have hd : y ∈ A.adjoint.domain :=
    A.mem_adjoint_domain_of_exists y ⟨0,fun x => by simp [ho x]⟩
  have hz : A.adjoint ⟨y,hd⟩ = 0 :=
    LinearPMap.adjoint_apply_eq hA.dense_domain _ (fun x => by simp [ho x])
  have he : A.adjoint = A := hA
  have hyA : y ∈ A.domain := by rwa [he] at hd
  have hzA : A ⟨y,hyA⟩ = 0 := ((LinearPMap.ext_iff.mp he).2).symm.trans hz
  have hn := norm_le A h ⟨y,hyA⟩
  simp only [hzA,norm_zero] at hn
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

theorem full_range (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (h : LowerOne A) :
    A.toFun.range = ⊤ := by
  have hd := Submodule.topologicalClosure_eq_top_iff.mpr (range_orthogonal A hA h)
  rwa [(closed_range A hA h).submodule_topologicalClosure_eq] at hd

def equiv (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (h : LowerOne A) :
    A.domain ≃ₗ[ℂ] E :=
  LinearEquiv.ofBijective A.toFun ⟨injective A h,LinearMap.range_eq_top.mp (full_range A hA h)⟩

/-- The everywhere-defined bounded inverse, constructed from the actual operator. -/
def inverse (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (h : LowerOne A) : E →L[ℂ] E :=
  (A.domain.subtype.comp (equiv A hA h).symm.toLinearMap).mkContinuous 1 (fun y => by
    have hn := norm_le A h ((equiv A hA h).symm y)
    have he : A ((equiv A hA h).symm y) = y := (equiv A hA h).apply_symm_apply y
    simpa only [one_mul,LinearMap.comp_apply,Submodule.subtype_apply,
      LinearEquiv.coe_toLinearMap,he] using hn)

theorem inverse_apply (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (h : LowerOne A)
    (x : A.domain) : inverse A hA h (A x) = (x : E) := by
  change ((equiv A hA h).symm ((equiv A hA h) x) : E) = _
  rw [LinearEquiv.symm_apply_apply]

theorem inverse_mem (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (h : LowerOne A)
    (y : E) : inverse A hA h y ∈ A.domain := ((equiv A hA h).symm y).property

theorem apply_inverse (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (h : LowerOne A)
    (y : E) : A ⟨inverse A hA h y,inverse_mem A hA h y⟩ = y :=
  (equiv A hA h).apply_symm_apply y

theorem inverse_norm (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (h : LowerOne A) :
    ‖inverse A hA h‖ ≤ 1 := by
  apply (inverse A hA h).opNorm_le_bound zero_le_one
  intro y
  simpa only [one_mul,apply_inverse] using
    norm_le A h ⟨inverse A hA h y,inverse_mem A hA h y⟩

theorem inverse_injective (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (h : LowerOne A) :
    Function.Injective (inverse A hA h) := by
  intro x y hxy
  apply (equiv A hA h).symm.injective
  exact Subtype.ext hxy

theorem inverse_symmetric (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (h : LowerOne A) :
    (inverse A hA h).IsSymmetric := by
  change ∀ x y : E, inner ℂ (inverse A hA h x) y = inner ℂ x (inverse A hA h y)
  intro x y
  let u : A.domain := ⟨inverse A hA h x,inverse_mem A hA h x⟩
  let v : A.domain := ⟨inverse A hA h y,inverse_mem A hA h y⟩
  have hf := LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
  have he : A.adjoint = A := hA
  rw [he] at hf
  have hx : A u = x := apply_inverse A hA h x
  have hy : A v = y := apply_inverse A hA h y
  simpa only [hx,hy,u,v] using (hf u v).symm

theorem inverse_positive (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (h : LowerOne A) :
    (inverse A hA h).IsPositive := by
  refine ⟨inverse_symmetric A hA h,fun y => ?_⟩
  have hl := h ⟨inverse A hA h y,inverse_mem A hA h y⟩
  rw [apply_inverse] at hl
  change 0 ≤ (inner ℂ (inverse A hA h y) y).re
  have he := inner_re_symm (𝕜 := ℂ) y (inverse A hA h y)
  change (inner ℂ y (inverse A hA h y)).re = (inner ℂ (inverse A hA h y) y).re at he
  rw [he] at hl
  exact (sq_nonneg _).trans hl

theorem inverse_le_one (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (h : LowerOne A) :
    inverse A hA h ≤ 1 := by
  rw [ContinuousLinearMap.le_def]
  refine ⟨?_,fun x => ?_⟩
  · exact LinearMap.IsSymmetric.one.sub (inverse_symmetric A hA h)
  · change 0 ≤ (inner ℂ ((1-inverse A hA h) x) x).re
    have hi := re_inner_le_norm (𝕜 := ℂ) (inverse A hA h x) x
    change (inner ℂ (inverse A hA h x) x).re ≤ ‖inverse A hA h x‖ * ‖x‖ at hi
    have hn := norm_le A h ⟨inverse A hA h x,inverse_mem A hA h x⟩
    rw [apply_inverse] at hn
    have hh := inner_self_eq_norm_sq (𝕜 := ℂ) x
    change (inner ℂ x x).re = ‖x‖^2 at hh
    simp only [sub_apply,one_apply_eq_self,inner_sub_left,Complex.sub_re,hh]
    nlinarith [norm_nonneg x]
end QuantumNLS.BoundedInverseR13
