import NlsGge.Analysis.RegularizedDeterminant.FiniteDimensional
import NlsGge.Analysis.RegularizedDeterminant.MatrixCarleman
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
Dimension-free local Lipschitz estimate for the real finite regularized determinant
`matrixDet2 A = det (1 + A) * exp (-trace A)` in the Frobenius (Hilbert--Schmidt) norm.

Source: B. Simon, *Trace Ideals and Their Applications*, 2nd ed., Thm 9.2(c)
(see also Gohberg--Goldberg--Krupnik, *Traces and Determinants of Linear Operators*, Ch. IX).
Constant used here: `|det₂(1+A) - det₂(1+B)| ≤ ‖A-B‖₂ exp (2 (‖A‖₂ + ‖B‖₂ + 1)^2)`.

Proof technique (recorded choice): the real matrices are viewed as complex matrices only
inside this proof, and the scalar parameter `z` of `B + z (A - B)` is complex, so that the
Cauchy estimate for the entire function `z ↦ det₂(1 + B + z(A-B))` applies.  The determinant
itself, its hypotheses and its conclusions remain real.  The bound on that entire function is the
Carleman-type inequality `‖det (1+X) exp (-tr X)‖ ≤ exp (‖X‖₂^2/2)` for complex matrices,
taken here as the explicit hypothesis `hCar` and discharged in `MatrixCarleman.lean`.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace NlsGge.Analysis.RegularizedDeterminant

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The real Frobenius (finite Hilbert--Schmidt) norm, written out explicitly. -/
def frob (A : Matrix I I ℝ) : ℝ := Real.sqrt (∑ i, ∑ j, A i j ^ 2)

theorem frob_nonneg (A : Matrix I I ℝ) : 0 ≤ frob A := Real.sqrt_nonneg _

/-- The complex Carleman-type bound, as a named proposition. -/
def CarlemanBound (I : Type*) [Fintype I] [DecidableEq I] : Prop :=
  ∀ X : Matrix I I ℂ, ‖(1 + X).det * Complex.exp (-X.trace)‖ ≤
    Real.exp ((1 / 2) * ∑ i, ∑ j, ‖X i j‖ ^ 2)

section Frobenius
open scoped Matrix.Norms.Frobenius

theorem frobenius_norm_sq {α : Type*} [NormedAddCommGroup α] (X : Matrix I I α) :
    ‖X‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

theorem frob_eq_norm (A : Matrix I I ℝ) : frob A = ‖A‖ := by
  rw [frob, ← Real.sqrt_sq (norm_nonneg A), frobenius_norm_sq]
  simp only [Real.norm_eq_abs, sq_abs]

/-- Complexification of a real matrix (used only inside proofs). -/
def cplx (A : Matrix I I ℝ) : Matrix I I ℂ := A.map (fun x : ℝ => (x : ℂ))

theorem norm_cplx (A : Matrix I I ℝ) : ‖cplx A‖ = ‖A‖ :=
  Matrix.frobenius_norm_map_eq A _ (fun a => by simp)

theorem cplx_sub (A B : Matrix I I ℝ) : cplx (A - B) = cplx A - cplx B := by
  ext i j; simp [cplx]

theorem matrixDet2_cplx (A : Matrix I I ℝ) :
    ((matrixDet2 A : ℝ) : ℂ) = (1 + cplx A).det * Complex.exp (-(cplx A).trace) := by
  unfold matrixDet2
  have h1 : (1 + cplx A) = (Complex.ofRealHom).mapMatrix (1 + A) := by
    ext i j
    by_cases h : i = j <;> simp [cplx, Matrix.one_apply, h]
  have h2 : (cplx A).trace = ((Matrix.trace A : ℝ) : ℂ) := by
    simp [cplx, Matrix.trace, Complex.ofReal_sum]
  rw [h1, ← RingHom.map_det, h2, Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.ofReal_neg]
  rfl

/-- The entire auxiliary function along the complex line through `B` in direction `D`. -/
def lineDet2 (B D : Matrix I I ℂ) (z : ℂ) : ℂ :=
  (1 + (B + z • D)).det * Complex.exp (-(B + z • D).trace)

theorem differentiable_lineDet2 (B D : Matrix I I ℂ) :
    Differentiable ℂ (lineDet2 B D) := by
  unfold lineDet2
  apply Differentiable.mul
  · have : (fun z : ℂ => (1 + (B + z • D)).det) =
        ∑ σ : Equiv.Perm I, fun z : ℂ =>
          Equiv.Perm.sign σ • ∏ i, (1 + (B + z • D)) (σ i) i := by
      funext z; simp [Matrix.det_apply]
    rw [this]
    apply Differentiable.sum
    intro σ _
    apply Differentiable.const_smul
    apply Differentiable.fun_finsetProd
    intro i _
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    fun_prop
  · apply Differentiable.cexp
    simp only [Matrix.trace, Matrix.diag, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    fun_prop

theorem lineDet2_bound (hCar : CarlemanBound I) (B D : Matrix I I ℂ) (z : ℂ) :
    ‖lineDet2 B D z‖ ≤ Real.exp ((1 / 2) * (‖B‖ + ‖z‖ * ‖D‖) ^ 2) := by
  refine (hCar (B + z • D)).trans ?_
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [← frobenius_norm_sq]
  have h : ‖B + z • D‖ ≤ ‖B‖ + ‖z‖ * ‖D‖ :=
    (norm_add_le _ _).trans (by rw [norm_smul])
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- Derivative bound on the real segment `[0,1] ⊂ ℂ`, from the Cauchy estimate. -/
theorem norm_deriv_lineDet2_le (hCar : CarlemanBound I) (B D : Matrix I I ℂ) (hD : 0 < ‖D‖)
    (t : ℂ) (ht : ‖t‖ ≤ 1) :
    ‖deriv (lineDet2 B D) t‖ ≤ ‖D‖ * Real.exp ((1 / 2) * (‖B‖ + ‖D‖ + 1) ^ 2) := by
  have hR : 0 < ‖D‖⁻¹ := inv_pos.mpr hD
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR
    ((differentiable_lineDet2 B D).diffContOnCl)
    (C := Real.exp ((1 / 2) * (‖B‖ + ‖D‖ + 1) ^ 2)) (by
      intro z hz
      refine (lineDet2_bound hCar B D z).trans ?_
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply pow_le_pow_left₀ (by positivity)
      have hz' : ‖z‖ ≤ 1 + ‖D‖⁻¹ := by
        have h1 : ‖z - t‖ = ‖D‖⁻¹ := by
          simpa [mem_sphere_iff_norm] using hz
        calc ‖z‖ = ‖(z - t) + t‖ := by rw [sub_add_cancel]
          _ ≤ ‖z - t‖ + ‖t‖ := norm_add_le _ _
          _ ≤ 1 + ‖D‖⁻¹ := by rw [h1]; linarith
      have : ‖z‖ * ‖D‖ ≤ ‖D‖ + 1 := by
        calc ‖z‖ * ‖D‖ ≤ (1 + ‖D‖⁻¹) * ‖D‖ :=
              mul_le_mul_of_nonneg_right hz' (norm_nonneg _)
          _ = ‖D‖ + 1 := by field_simp
      linarith)
  rwa [div_inv_eq_mul, mul_comm] at h

theorem norm_lineDet2_one_sub_zero_le (hCar : CarlemanBound I) (B D : Matrix I I ℂ) :
    ‖lineDet2 B D 1 - lineDet2 B D 0‖ ≤
      ‖D‖ * Real.exp ((1 / 2) * (‖B‖ + ‖D‖ + 1) ^ 2) := by
  rcases (norm_nonneg D).eq_or_lt with hD | hD
  · have hD0 : D = 0 := norm_eq_zero.mp hD.symm
    subst hD0
    simp [lineDet2]
  · have hconv : Convex ℝ (segment ℝ (0 : ℂ) 1) := convex_segment _ _
    have h := hconv.norm_image_sub_le_of_norm_deriv_le
      (f := lineDet2 B D) (fun x _ => (differentiable_lineDet2 B D) x)
      (fun x hx => norm_deriv_lineDet2_le hCar B D hD x (by
        have := (convex_closedBall (0 : ℂ) 1).segment_subset
          (Metric.mem_closedBall_self zero_le_one) (by simp) hx
        simpa using this))
      (left_mem_segment ℝ 0 1) (right_mem_segment ℝ 0 1)
    simpa using h

/-- **Dimension-free Lipschitz estimate**, Frobenius-norm form. -/
theorem matrixDet2_lipschitz_of_carleman (hCar : CarlemanBound I) (A B : Matrix I I ℝ) :
    |matrixDet2 A - matrixDet2 B| ≤
      ‖A - B‖ * Real.exp (2 * (‖A‖ + ‖B‖ + 1) ^ 2) := by
  have h := norm_lineDet2_one_sub_zero_le hCar (cplx B) (cplx (A - B))
  have h1 : lineDet2 (cplx B) (cplx (A - B)) 1 = ((matrixDet2 A : ℝ) : ℂ) := by
    rw [matrixDet2_cplx, lineDet2, one_smul, cplx_sub, add_sub_cancel]
  have h0 : lineDet2 (cplx B) (cplx (A - B)) 0 = ((matrixDet2 B : ℝ) : ℂ) := by
    rw [matrixDet2_cplx, lineDet2, zero_smul, add_zero]
  rw [h1, h0, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, norm_cplx,
    norm_cplx] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  apply Real.exp_le_exp.mpr
  have hAB : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
  have hA := norm_nonneg A
  have hB := norm_nonneg B
  have hDn := norm_nonneg (A - B)
  nlinarith

end Frobenius

/-- **Dimension-free Lipschitz estimate**, explicit-sum form (no scoped matrix norm). -/
theorem matrixDet2_lipschitz_frob_of_carleman (hCar : CarlemanBound I) (A B : Matrix I I ℝ) :
    |matrixDet2 A - matrixDet2 B| ≤
      frob (A - B) * Real.exp (2 * (frob A + frob B + 1) ^ 2) := by
  simpa only [frob_eq_norm] using matrixDet2_lipschitz_of_carleman hCar A B

theorem carlemanBound (I : Type*) [Fintype I] [DecidableEq I] : CarlemanBound I :=
  fun X => norm_det_one_add_mul_exp_neg_trace_le X

/-- **Dimension-free Lipschitz estimate** for the real finite regularized determinant
(unconditional). -/
theorem matrixDet2_lipschitz (A B : Matrix I I ℝ) :
    |matrixDet2 A - matrixDet2 B| ≤
      frob (A - B) * Real.exp (2 * (frob A + frob B + 1) ^ 2) :=
  matrixDet2_lipschitz_frob_of_carleman (carlemanBound I) A B

end NlsGge.Analysis.RegularizedDeterminant
