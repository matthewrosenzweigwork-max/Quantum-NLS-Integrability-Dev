import QuantumNLS.TerraMultiRound26Compression

/-! Antiunitarity of the actual swap on the free fiber and interval space. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.LocalSpectral.Round27
open Round23 Round24 Round26

/-- A real isometry that reverses multiplication by `i` conjugates the complex inner product. -/
theorem anti_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗᵢ[ℝ] E) (hi : ∀ x, T (Complex.I • x) = -Complex.I • T x)
    (x y : E) : ⟪T x, T y⟫_ℂ = conj ⟪x, y⟫_ℂ := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  have hre := T.inner_map_map x y
  have him := T.inner_map_map x (Complex.I • y)
  rw [hi] at him
  rw [real_inner_eq_re_inner ℂ, real_inner_eq_re_inner ℂ] at hre him
  apply Complex.ext
  · rw [Complex.conj_re]
    exact hre
  · rw [Complex.conj_im]
    simpa [inner_smul_right] using him

def swapFiberReal : E2 →ₗᵢ[ℝ] E2 := swapConjIsometry

def swapL2Real (L : ℝ) : H2 L →ₗᵢ[ℝ] H2 L where
  toLinearMap := (swapOp L).toLinearMap
  norm_map' x := liftFiber_norm L swapConjIsometry swapConj_involutive x

theorem swapOp_involution (L : ℝ) (x : H2 L) : swapOp L (swapOp L x) = x :=
  liftFiber_involution L swapConjIsometry swapConj_involutive x

theorem swapFiber_inner (v w : E2) :
    ⟪swapConj v, swapConj w⟫_ℂ = conj ⟪v, w⟫_ℂ := by
  apply anti_inner swapFiberReal
  intro x
  ext i
  fin_cases i <;> simp [swapFiberReal, swapConjIsometry, swapConj, vec2, map_mul]

theorem swapOp_inner (L : ℝ) (x y : H2 L) :
    ⟪swapOp L x, swapOp L y⟫_ℂ = conj ⟪x, y⟫_ℂ := by
  apply anti_inner (swapL2Real L)
  intro v
  change liftFiber L swapConjIsometry (Complex.I • v) =
    -Complex.I • liftFiber L swapConjIsometry v
  simpa using liftFiber_swap_smul L Complex.I v

/-- The adjoint of the source embedding commutes with the antiunitary swaps. -/
theorem adjoint_embed_swap (L : ℝ) (n : ℤ) (x : H2 L) :
    (ContinuousLinearMap.adjoint (embed L n)) (swapOp L x) =
      swapConj ((ContinuousLinearMap.adjoint (embed L n)) x) := by
  apply ext_inner_left ℂ
  intro v
  have hs := swapOp_inner L (embed L n (swapConj v)) x
  change ⟪liftFiber L swapConjIsometry (embed L n (swapConj v)), swapOp L x⟫_ℂ =
    conj ⟪embed L n (swapConj v), x⟫_ℂ at hs
  rw [embed_swap, swapConj_involutive] at hs
  have hf := swapFiber_inner (swapConj v) ((ContinuousLinearMap.adjoint (embed L n)) x)
  rw [swapConj_involutive] at hf
  calc
    ⟪v, (ContinuousLinearMap.adjoint (embed L n)) (swapOp L x)⟫_ℂ =
        ⟪embed L n v, swapOp L x⟫_ℂ := ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = conj ⟪embed L n (swapConj v), x⟫_ℂ := hs
    _ = conj ⟪swapConj v, (ContinuousLinearMap.adjoint (embed L n)) x⟫_ℂ :=
      congrArg (starRingEnd ℂ) (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
    _ = ⟪v, swapConj ((ContinuousLinearMap.adjoint (embed L n)) x)⟫_ℂ := hf.symm


end QuantumNLS.LocalSpectral.Round27
#print axioms QuantumNLS.LocalSpectral.Round27.anti_inner
#print axioms QuantumNLS.LocalSpectral.Round27.swapFiberReal
#print axioms QuantumNLS.LocalSpectral.Round27.swapL2Real
#print axioms QuantumNLS.LocalSpectral.Round27.swapOp_involution
#print axioms QuantumNLS.LocalSpectral.Round27.swapFiber_inner
#print axioms QuantumNLS.LocalSpectral.Round27.swapOp_inner
#print axioms QuantumNLS.LocalSpectral.Round27.adjoint_embed_swap
