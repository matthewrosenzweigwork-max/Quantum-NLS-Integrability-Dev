import QuantumNLS.BoundedInverseR13
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-! Form square root from the CFC square root of the bounded inverse. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped InnerProductSpace ComplexOrder
namespace QuantumNLS.InverseSquareRootR13
open BoundedInverseR13
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (h : LowerOne A)

def rootInv : E →L[ℂ] E := CFC.sqrt (inverse A hA h)

theorem rootInv_nonneg : 0 ≤ rootInv A hA h := CFC.sqrt_nonneg _

theorem rootInv_selfAdjoint : IsSelfAdjoint (rootInv A hA h) :=
  (rootInv_nonneg A hA h).isSelfAdjoint

theorem rootInv_square : rootInv A hA h * rootInv A hA h = inverse A hA h :=
  CFC.sqrt_mul_sqrt_self _ (ContinuousLinearMap.nonneg_iff_isPositive.mpr (inverse_positive A hA h))

theorem rootInv_injective : Function.Injective (rootInv A hA h) := by
  intro x y hxy
  apply inverse_injective A hA h
  rw [← rootInv_square A hA h]
  simp only [mul_apply_eq_comp,hxy]

theorem rootInv_dense : DenseRange (rootInv A hA h) := by
  change Dense ((rootInv A hA h).range : Set E)
  rw [Submodule.dense_iff_topologicalClosure_eq_top,Submodule.topologicalClosure_eq_top_iff]
  rw [ContinuousLinearMap.IsStarNormal.orthogonal_range (rootInv_selfAdjoint A hA h).isStarNormal]
  exact LinearMap.ker_eq_bot.mpr (rootInv_injective A hA h)

/-- Maximal inverse of R^(1/2); its domain is precisely ran R^(1/2). -/
def half : E →ₗ.[ℂ] E := ((rootInv A hA h).toPMap ⊤).inverse

theorem half_domain : (half A hA h).domain = (rootInv A hA h).range := by
  rw [half,LinearPMap.inverse_domain]
  ext x
  change (∃ y : (⊤ : Submodule ℂ E), rootInv A hA h (y : E) = x) ↔
    ∃ y : E, rootInv A hA h y = x
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨(y : E),hy⟩
  · rintro ⟨y,hy⟩
    exact ⟨⟨y,Submodule.mem_top⟩,hy⟩

theorem root_ker : ((rootInv A hA h).toPMap ⊤).ker = ⊥ := by
  rw [LinearMap.toPMap_ker,LinearMap.ker_eq_bot.mpr (rootInv_injective A hA h),inf_bot_eq]

theorem half_root (y : E) :
    half A hA h ⟨rootInv A hA h y,by rw [half_domain]; exact ⟨y,rfl⟩⟩ = y := by
  exact LinearPMap.inverse_apply_eq (root_ker A hA h)
    (x := ⟨y,Submodule.mem_top⟩) rfl

theorem domain_le_half : A.domain ≤ (half A hA h).domain := by
  intro x hx
  rw [half_domain]
  refine ⟨rootInv A hA h (A ⟨x,hx⟩),?_⟩
  change (rootInv A hA h * rootInv A hA h) (A ⟨x,hx⟩) = x
  rw [rootInv_square,inverse_apply]

theorem half_on_domain (x : A.domain) :
    half A hA h ⟨(x : E),domain_le_half A hA h x.property⟩ = rootInv A hA h (A x) := by
  have he : rootInv A hA h (rootInv A hA h (A x)) = (x : E) := by
    change (rootInv A hA h * rootInv A hA h) (A x) = _
    rw [rootInv_square,inverse_apply]
  exact LinearPMap.inverse_apply_eq (root_ker A hA h)
    (x := ⟨rootInv A hA h (A x),Submodule.mem_top⟩) he

/-- The constructed inverse is the form square root on dom A. -/
theorem half_form_identity (x : A.domain) :
    ‖half A hA h ⟨(x : E),domain_le_half A hA h x.property⟩‖^2 =
      (inner ℂ (A x) (x : E)).re := by
  rw [half_on_domain]
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (rootInv_selfAdjoint A hA h)
  have hi := hs (A x) (rootInv A hA h (A x))
  change inner ℂ (rootInv A hA h (A x)) (rootInv A hA h (A x)) =
    inner ℂ (A x) (rootInv A hA h (rootInv A hA h (A x))) at hi
  have he : rootInv A hA h (rootInv A hA h (A x)) = (x : E) := by
    change (rootInv A hA h * rootInv A hA h) (A x) = _
    rw [rootInv_square,inverse_apply]
  rw [he] at hi
  have hh := congrArg Complex.re hi
  have hself := inner_self_eq_norm_sq (𝕜 := ℂ) (rootInv A hA h (A x))
  change (inner ℂ (rootInv A hA h (A x)) (rootInv A hA h (A x))).re =
    ‖rootInv A hA h (A x)‖^2 at hself
  rw [hself] at hh
  exact hh

end QuantumNLS.InverseSquareRootR13
