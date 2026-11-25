import QuantumNLS.InverseSquareRootR13
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped InnerProductSpace ComplexOrder
namespace QuantumNLS.InverseRootPropertiesR13
open BoundedInverseR13 InverseSquareRootR13
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (h : LowerOne A)

theorem root_half (x : (half A hA h).domain) : rootInv A hA h (half A hA h x) = (x : E) := by
  have hx : (x : E) ∈ (rootInv A hA h).range := by
    simpa only [half_domain] using x.property
  obtain ⟨y,hy⟩ := hx
  have he : x = ⟨rootInv A hA h y,by rw [half_domain]; exact ⟨y,rfl⟩⟩ :=
    Subtype.ext hy.symm
  rw [he,half_root]

theorem half_dense : Dense ((half A hA h).domain : Set E) := by
  rw [half_domain]
  exact rootInv_dense A hA h

theorem half_symmetric : (half A hA h).IsFormalAdjoint (half A hA h) := by
  intro x y
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (rootInv_selfAdjoint A hA h)
  calc
    inner ℂ (half A hA h x) (y : E) =
        inner ℂ (half A hA h x) (rootInv A hA h (half A hA h y)) := by rw [root_half]
    _ = inner ℂ (rootInv A hA h (half A hA h x)) (half A hA h y) := (hs _ _).symm
    _ = inner ℂ (x : E) (half A hA h y) := by rw [root_half]

theorem adjoint_root (y : (half A hA h).adjoint.domain) :
    rootInv A hA h ((half A hA h).adjoint y) = (y : E) := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (rootInv_selfAdjoint A hA h)
  apply ext_inner_right ℂ
  intro z
  have hh := LinearPMap.adjoint_isFormalAdjoint (half_dense A hA h)
    y ⟨rootInv A hA h z,by rw [half_domain]; exact ⟨z,rfl⟩⟩
  rw [half_root] at hh
  calc
    inner ℂ (rootInv A hA h ((half A hA h).adjoint y)) z =
        inner ℂ ((half A hA h).adjoint y) (rootInv A hA h z) := hs _ _
    _ = inner ℂ (y : E) z := hh

theorem half_selfAdjoint : IsSelfAdjoint (half A hA h) := by
  change (half A hA h).adjoint = half A hA h
  apply le_antisymm
  · constructor
    · intro y hy
      rw [half_domain]
      exact ⟨(half A hA h).adjoint ⟨y,hy⟩,adjoint_root A hA h _⟩
    · intro x y hxy
      apply rootInv_injective A hA h
      rw [adjoint_root,root_half]
      exact hxy
  · exact LinearPMap.IsFormalAdjoint.le_adjoint (half_dense A hA h) (half_symmetric A hA h)

theorem half_positive (x : (half A hA h).domain) :
    0 ≤ (inner ℂ (half A hA h x) (x : E)).re := by
  have hp := ContinuousLinearMap.nonneg_iff_isPositive.mp (rootInv_nonneg A hA h)
  have hh := hp.re_inner_nonneg_right (half A hA h x)
  change 0 ≤ (inner ℂ (half A hA h x) (rootInv A hA h (half A hA h x))).re at hh
  rw [root_half] at hh
  exact hh

/-- Exact operator action, not just equality of quadratic forms. -/
theorem half_twice_on_domain (x : A.domain) :
    ∃ hx : half A hA h ⟨(x : E),domain_le_half A hA h x.property⟩ ∈ (half A hA h).domain,
      half A hA h ⟨half A hA h ⟨(x : E),domain_le_half A hA h x.property⟩,hx⟩ = A x := by
  have hm : half A hA h ⟨(x : E),domain_le_half A hA h x.property⟩ ∈ (half A hA h).domain := by
    rw [half_on_domain,half_domain]
    exact ⟨A x,rfl⟩
  refine ⟨hm,?_⟩
  have he := half_root A hA h (A x)
  simpa only [half_on_domain] using he

/-- The maximal composition domain of the square is exactly dom A. -/
theorem square_domain (x : (half A hA h).domain)
    (hx : half A hA h x ∈ (half A hA h).domain) : (x : E) ∈ A.domain := by
  let y : (half A hA h).domain := ⟨half A hA h x,hx⟩
  have he : inverse A hA h (half A hA h y) = (x : E) := by
    rw [← rootInv_square]
    change rootInv A hA h (rootInv A hA h (half A hA h y)) = (x : E)
    rw [root_half]
    exact root_half A hA h x
  exact he ▸ inverse_mem A hA h (half A hA h y)
end QuantumNLS.InverseRootPropertiesR13
