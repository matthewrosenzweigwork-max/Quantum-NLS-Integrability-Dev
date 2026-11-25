import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
Signed real determinant/trace formula on finite-dimensional real vector spaces.
Finite-dimensionality is an explicit binder of `finiteDet2`, even though mathlib
also totalizes the ordinary linear-map determinant in infinite dimension.
This is NOT a definition of the infinite-dimensional regularized determinant.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace NlsGge.Analysis.RegularizedDeterminant

/-- The finite-dimensional signed regularized determinant of identity plus B. -/
def finiteDet2 {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : V →ₗ[ℝ] V) : ℝ :=
  LinearMap.det (1 + B) * Real.exp (-(LinearMap.trace ℝ V B))

/-- Matrix version, over the real scalar field and full real dimension. -/
def matrixDet2 {I : Type*} [Fintype I] [DecidableEq I] (B : Matrix I I ℝ) : ℝ :=
  Matrix.det (1 + B) * Real.exp (-Matrix.trace B)

variable {V W : Type*}
variable [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

@[simp] theorem finiteDet2_zero : finiteDet2 (0 : V →ₗ[ℝ] V) = 1 := by
  simp [finiteDet2]

@[simp] theorem finiteDet2_subsingleton [Subsingleton V] (B : V →ₗ[ℝ] V) :
    finiteDet2 B = 1 := by
  have hB : B = 0 := Subsingleton.elim _ _
  rw [hB, finiteDet2_zero]

theorem finiteDet2_eq_matrix {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I ℝ V) (B : V →ₗ[ℝ] V) :
    finiteDet2 B = matrixDet2 (LinearMap.toMatrix b b B) := by
  unfold finiteDet2 matrixDet2
  rw [← LinearMap.det_toMatrix b (1 + B), LinearMap.trace_eq_matrix_trace ℝ b B]
  simp only [map_add, LinearMap.toMatrix_one]

theorem matrixDet2_basis_independent {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (b : Module.Basis I ℝ V) (c : Module.Basis J ℝ V) (B : V →ₗ[ℝ] V) :
    matrixDet2 (LinearMap.toMatrix b b B) = matrixDet2 (LinearMap.toMatrix c c B) :=
  (finiteDet2_eq_matrix b B).symm.trans (finiteDet2_eq_matrix c B)

/-- The rectangular determinant identity, transferred from the pinned matrix theorem. -/
theorem det_one_add_comp_comm (f : V →ₗ[ℝ] W) (g : W →ₗ[ℝ] V) :
    LinearMap.det (1 + g.comp f) = LinearMap.det (1 + f.comp g) := by
  classical
  let b := Module.finBasis ℝ V
  let c := Module.finBasis ℝ W
  rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix c]
  simp only [map_add, LinearMap.toMatrix_one]
  rw [LinearMap.toMatrix_comp b c b, LinearMap.toMatrix_comp c b c]
  exact Matrix.det_one_add_mul_comm _ _

/-- Finite-dimensional regularized determinants are invariant under interchange of factors. -/
theorem finiteDet2_comp_comm (f : V →ₗ[ℝ] W) (g : W →ₗ[ℝ] V) :
    finiteDet2 (g.comp f) = finiteDet2 (f.comp g) := by
  unfold finiteDet2
  rw [det_one_add_comp_comm f g, LinearMap.trace_comp_comm' f g]

/-- No positivity of the determinant, nor smallness of B, is needed. -/
theorem finiteDet2_ne_zero_of_injective (B : V →ₗ[ℝ] V)
    (h : Function.Injective (1 + B : V →ₗ[ℝ] V)) : finiteDet2 B ≠ 0 := by
  have hdet : LinearMap.det (1 + B) ≠ 0 := by
    intro hz
    have hk := (LinearMap.det_eq_zero_iff_ker_ne_bot).mp hz
    exact hk (LinearMap.ker_eq_bot.mpr h)
  exact mul_ne_zero hdet (Real.exp_ne_zero _)

/-- An actual algebraic right inverse already suffices in finite dimension. -/
theorem finiteDet2_ne_zero_of_rightInverse (B C : V →ₗ[ℝ] V)
    (h : (1 + B) * C = 1) : finiteDet2 B ≠ 0 := by
  have hdet : LinearMap.det (1 + B) ≠ 0 := by
    intro hz
    have hd := congrArg LinearMap.det h
    have hd' : (0 : ℝ) = 1 := by
      simpa only [map_mul, map_one, hz, zero_mul] using hd
    exact zero_ne_one hd'
  exact mul_ne_zero hdet (Real.exp_ne_zero _)

/-- Real conjugation, with no orthogonality assumption in finite dimension. -/
theorem finiteDet2_conjugate (B : V →ₗ[ℝ] V) (e : V ≃ₗ[ℝ] W) :
    finiteDet2 (e.toLinearMap.comp (B.comp e.symm.toLinearMap)) = finiteDet2 B := by
  have hI : 1 + e.toLinearMap.comp (B.comp e.symm.toLinearMap) =
      e.toLinearMap.comp ((1 + B).comp e.symm.toLinearMap) := by
    ext x
    simp
  have ht : LinearMap.trace ℝ W (e.toLinearMap.comp (B.comp e.symm.toLinearMap)) =
      LinearMap.trace ℝ V B := by
    rw [LinearMap.trace_comp_comm' (B.comp e.symm.toLinearMap) e.toLinearMap]
    congr 1
    ext x
    simp
  unfold finiteDet2
  rw [hI, LinearMap.det_conj, ht]

/-- The finite-dimensional multiplicative anomaly has the negative trace sign. -/
theorem finiteDet2_product (B C : V →ₗ[ℝ] V) :
    finiteDet2 (B + C + B * C) = finiteDet2 B * finiteDet2 C *
      Real.exp (-(LinearMap.trace ℝ V (B * C))) := by
  have hI : 1 + (B + C + B * C) = (1 + B) * (1 + C) := by
    noncomm_ring
  simp only [finiteDet2, hI, map_mul, map_add, neg_add_rev, Real.exp_add]
  ring

/-- A regression against accidentally squaring, or taking the absolute value of, the determinant. -/
theorem finiteDet2_negative_example :
    finiteDet2 ((-2 : ℝ) • (1 : ℝ →ₗ[ℝ] ℝ)) = -Real.exp 2 := by
  norm_num [finiteDet2, LinearMap.det_ring, LinearMap.trace_one]

theorem finiteDet2_negative_example_lt_zero :
    finiteDet2 ((-2 : ℝ) • (1 : ℝ →ₗ[ℝ] ℝ)) < 0 := by
  rw [finiteDet2_negative_example]
  linarith [Real.exp_pos 2]

section MatrixConjugation
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem matrix_trace_conjugate (B C D : Matrix I I ℝ)
    (hDC : D * C = 1) : Matrix.trace (C * B * D) = Matrix.trace B := by
  rw [Matrix.trace_mul_comm, ← mul_assoc, hDC, one_mul]

theorem matrixDet2_conjugate (B C D : Matrix I I ℝ)
    (hCD : C * D = 1) (hDC : D * C = 1) :
    matrixDet2 (C * B * D) = matrixDet2 B := by
  have hI : 1 + C * B * D = C * (1 + B) * D := by
    rw [mul_add, mul_one, add_mul, hCD]
  unfold matrixDet2
  rw [hI, Matrix.det_conj_of_mul_eq_one hCD hDC, matrix_trace_conjugate B C D hDC]

/-- Positivity discharges, rather than assumes, invertibility of the diagonal coordinate change. -/
theorem positive_diagonal_inverse_pair (w : I → ℝ) (hw : forall i, 0 < w i) :
    Matrix.diagonal w * Matrix.diagonal (fun i => (w i)⁻¹) = 1 ∧
    Matrix.diagonal (fun i => (w i)⁻¹) * Matrix.diagonal w = 1 := by
  constructor
  · rw [Matrix.diagonal_mul_diagonal]
    have h : (fun i => w i * (w i)⁻¹) = (fun _ : I => (1 : ℝ)) := by
      funext i
      simp [ne_of_gt (hw i)]
    rw [h]
    simp
  · rw [Matrix.diagonal_mul_diagonal]
    have h : (fun i => (w i)⁻¹ * w i) = (fun _ : I => (1 : ℝ)) := by
      funext i
      simp [ne_of_gt (hw i)]
    rw [h]
    simp

/-- Ordinary determinant, trace, and the finite regularized determinant all survive the weighted change. -/
theorem positive_diagonal_conjugation (B : Matrix I I ℝ)
    (w : I → ℝ) (hw : forall i, 0 < w i) :
    Matrix.det (Matrix.diagonal w * B * Matrix.diagonal (fun i => (w i)⁻¹)) =
        Matrix.det B ∧
    Matrix.trace (Matrix.diagonal w * B * Matrix.diagonal (fun i => (w i)⁻¹)) =
        Matrix.trace B ∧
    matrixDet2 (Matrix.diagonal w * B * Matrix.diagonal (fun i => (w i)⁻¹)) =
        matrixDet2 B := by
  have h := positive_diagonal_inverse_pair w hw
  exact ⟨Matrix.det_conj_of_mul_eq_one h.1 h.2,
    matrix_trace_conjugate B _ _ h.2, matrixDet2_conjugate B _ _ h.1 h.2⟩

end MatrixConjugation

/-- Finite Gaussian trace cancellation, before any divergence identification by the Ramer owner. -/
theorem finiteDet2_trace_cancellation {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (B : H →ₗ[ℝ] H) (x k : H) :
    abs (finiteDet2 B) * Real.exp (-(inner ℝ x k - LinearMap.trace ℝ H B) - norm k ^ 2 / 2) =
      abs (LinearMap.det (1 + B)) *
        Real.exp (-(norm (x + k) ^ 2 - norm x ^ 2) / 2) := by
  have hs : norm (x + k) ^ 2 = norm x ^ 2 + 2 * inner ℝ x k + norm k ^ 2 := by
    calc
      norm (x + k) ^ 2 = inner ℝ (x + k) (x + k) :=
        (real_inner_self_eq_norm_sq (x + k)).symm
      _ = norm x ^ 2 + 2 * inner ℝ x k + norm k ^ 2 := by
        simp only [inner_add_left, inner_add_right, real_inner_self_eq_norm_sq,
          real_inner_comm k x]
        ring
  have he : -(LinearMap.trace ℝ H B) +
      (-(inner ℝ x k - LinearMap.trace ℝ H B) - norm k ^ 2 / 2) =
      -(norm (x + k) ^ 2 - norm x ^ 2) / 2 := by
    rw [hs]
    ring
  unfold finiteDet2
  rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_assoc, ← Real.exp_add, he]

end NlsGge.Analysis.RegularizedDeterminant
