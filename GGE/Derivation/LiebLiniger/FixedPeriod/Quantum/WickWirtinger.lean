import LiebLiniger.FixedPeriod.Quantum.WickDerivatives
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Tactic.LinearCombination

/-!
# Actual real derivative and first Wirtinger splitting of a Wick polynomial

The polarized complex derivatives are related here to the real Fréchet
derivative of the literal diagonal polynomial b_A. Thus holomorphic and
antiholomorphic slot conventions are checked against the real function on the
physical one-particle Hilbert space. No differentiability hypothesis is added.
Higher mixed Wirtinger identification is a further theorem.

Source-written candidate; only the root's compiler lane validates it.
-/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

/-- Actual complex derivative of the n-fold pure symmetric tensor map. -/
def wickPureTensorDerivative (n : ℕ) (u : Lp ℂ 2 μ) :
    Lp ℂ 2 μ →L[ℂ] SymmetricSector μ n :=
  ((symmetricTensorContinuousMultilinear μ n).linearDeriv (fun _ => u)).comp
    (wickKernelDiagonalMap μ n)

theorem wickPureTensor_hasFDerivAt (n : ℕ) (u : Lp ℂ 2 μ) :
    HasFDerivAt (pureSymmetricTensor μ n) (wickPureTensorDerivative μ n u) u := by
  have hd := ((symmetricTensorContinuousMultilinear μ n).hasFDerivAt (fun _ => u)).comp u
    (wickKernelDiagonalMap μ n).hasFDerivAt
  simpa only [wickPureTensorDerivative, Function.comp_def, wickKernelDiagonalMap_apply,
    symmetricTensorContinuousMultilinear_diagonal] using hd

/-- The literal b_A has a genuine real Fréchet derivative. -/
def wickKernelRealDerivative {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (u : Lp ℂ 2 μ) :
    Lp ℂ 2 μ →L[ℝ] ℂ :=
  (fderivInnerCLM ℂ (pureSymmetricTensor μ q u, A (pureSymmetricTensor μ p u))).comp
    (((wickPureTensorDerivative μ q u).restrictScalars ℝ).prod
      ((A.comp (wickPureTensorDerivative μ p u)).restrictScalars ℝ))

theorem wickKernelPolynomial_hasFDerivAt_real {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (u : Lp ℂ 2 μ) :
    HasFDerivAt (𝕜 := ℝ) (wickKernelPolynomial μ A) (wickKernelRealDerivative μ A u) u := by
  have hq := (wickPureTensor_hasFDerivAt μ q u).restrictScalars ℝ
  have hp := (A.hasFDerivAt.comp u (wickPureTensor_hasFDerivAt μ p u)).restrictScalars ℝ
  exact hq.inner ℂ hp

/-- Real derivative: the two terms differentiate the actual input and output
slots, with the conjugate-linear first-entry inner-product convention. -/
theorem wickKernelPolynomial_fderiv_real_apply {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (u h : Lp ℂ 2 μ) :
    fderiv ℝ (wickKernelPolynomial μ A) u h =
      inner ℂ (pureSymmetricTensor μ q u) (A (wickPureTensorDerivative μ p u h)) +
        inner ℂ (wickPureTensorDerivative μ q u h) (A (pureSymmetricTensor μ p u)) := by
  rw [(wickKernelPolynomial_hasFDerivAt_real μ A u).fderiv]
  rfl

/-- The complex input derivative agrees with the input term of the real derivative. -/
theorem wickKernelPolarized_fderiv_input_apply {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (v u h : Lp ℂ 2 μ) :
    fderiv ℂ (wickKernelPolarized μ A v) u h =
      inner ℂ (pureSymmetricTensor μ q v) (A (wickPureTensorDerivative μ p u h)) := by
  have hd := (((innerSL ℂ (pureSymmetricTensor μ q v)).comp A).hasFDerivAt).comp u
    (wickPureTensor_hasFDerivAt μ p u)
  have he : ((innerSL ℂ (pureSymmetricTensor μ q v)).comp A) ∘ pureSymmetricTensor μ p =
      wickKernelPolarized μ A v := rfl
  rw [he] at hd
  rw [hd.fderiv]
  rfl

/-- Conjugating the output derivative produces the actual antiholomorphic term. -/
theorem wickKernelPolarized_fderiv_conj_output_apply {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (u v h : Lp ℂ 2 μ) :
    conj (fderiv ℂ (fun w => conj (wickKernelPolarized μ A w u)) v h) =
      inner ℂ (wickPureTensorDerivative μ q v h) (A (pureSymmetricTensor μ p u)) := by
  have hd := (innerSL ℂ (A (pureSymmetricTensor μ p u))).hasFDerivAt.comp v
    (wickPureTensor_hasFDerivAt μ q v)
  have he : (innerSL ℂ (A (pureSymmetricTensor μ p u))) ∘ pureSymmetricTensor μ q =
      (fun w => conj (wickKernelPolarized μ A w u)) := by
    funext w
    change inner ℂ (A (pureSymmetricTensor μ p u)) (pureSymmetricTensor μ q w) =
      conj (inner ℂ (pureSymmetricTensor μ q w) (A (pureSymmetricTensor μ p u)))
    exact (inner_conj_symm _ _).symm
  rw [he] at hd
  rw [hd.fderiv]
  change conj (inner ℂ (A (pureSymmetricTensor μ p u)) (wickPureTensorDerivative μ q v h)) = _
  exact inner_conj_symm (𝕜 := ℂ) (wickPureTensorDerivative μ q v h)
    (A (pureSymmetricTensor μ p u))

/-- The actual real derivative in the direction ih separates into +i times
its holomorphic slot and -i times its conjugate slot. -/
theorem wickKernelPolynomial_fderiv_real_mul_I {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (u h : Lp ℂ 2 μ) :
    fderiv ℝ (wickKernelPolynomial μ A) u (Complex.I • h) =
      Complex.I * inner ℂ (pureSymmetricTensor μ q u)
        (A (wickPureTensorDerivative μ p u h)) -
      Complex.I * inner ℂ (wickPureTensorDerivative μ q u h)
        (A (pureSymmetricTensor μ p u)) := by
  rw [wickKernelPolynomial_fderiv_real_apply]
  have hlin : inner ℂ (pureSymmetricTensor μ q u)
      (A (wickPureTensorDerivative μ p u (Complex.I • h))) =
        Complex.I * inner ℂ (pureSymmetricTensor μ q u)
          (A (wickPureTensorDerivative μ p u h)) := by
    rw [map_smul, map_smul]
    exact inner_smul_right (𝕜 := ℂ) (pureSymmetricTensor μ q u)
      (A (wickPureTensorDerivative μ p u h)) Complex.I
  have hanti : inner ℂ (wickPureTensorDerivative μ q u (Complex.I • h))
      (A (pureSymmetricTensor μ p u)) =
        (-Complex.I) * inner ℂ (wickPureTensorDerivative μ q u h)
          (A (pureSymmetricTensor μ p u)) := by
    rw [map_smul]
    simpa only [Complex.conj_I] using
      (inner_smul_left (𝕜 := ℂ) (wickPureTensorDerivative μ q u h)
        (A (pureSymmetricTensor μ p u)) Complex.I)
  rw [hlin, hanti]
  ring

/-- The source holomorphic slot is exactly the complex-linear part of the
real derivative, extracted with the actual physical complex structure. -/
theorem wickKernelPolynomial_wirtinger_input {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (u h : Lp ℂ 2 μ) :
    (1 / 2 : ℂ) * (fderiv ℝ (wickKernelPolynomial μ A) u h -
      Complex.I * fderiv ℝ (wickKernelPolynomial μ A) u (Complex.I • h)) =
      fderiv ℂ (wickKernelPolarized μ A u) u h := by
  rw [wickKernelPolynomial_fderiv_real_apply, wickKernelPolynomial_fderiv_real_mul_I,
    wickKernelPolarized_fderiv_input_apply]
  let x := inner ℂ (pureSymmetricTensor μ q u) (A (wickPureTensorDerivative μ p u h))
  let y := inner ℂ (wickPureTensorDerivative μ q u h) (A (pureSymmetricTensor μ p u))
  change (1 / 2 : ℂ) * (x + y - Complex.I * (Complex.I * x - Complex.I * y)) = x
  linear_combination (-(x - y) / 2) * Complex.I_mul_I

/-- The source conjugate slot is exactly the conjugate-linear part of the
real derivative, with its conjugation explicitly retained. -/
theorem wickKernelPolynomial_wirtinger_output {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (u h : Lp ℂ 2 μ) :
    (1 / 2 : ℂ) * (fderiv ℝ (wickKernelPolynomial μ A) u h +
      Complex.I * fderiv ℝ (wickKernelPolynomial μ A) u (Complex.I • h)) =
      conj (fderiv ℂ (fun w => conj (wickKernelPolarized μ A w u)) u h) := by
  rw [wickKernelPolynomial_fderiv_real_apply, wickKernelPolynomial_fderiv_real_mul_I,
    wickKernelPolarized_fderiv_conj_output_apply]
  let x := inner ℂ (pureSymmetricTensor μ q u) (A (wickPureTensorDerivative μ p u h))
  let y := inner ℂ (wickPureTensorDerivative μ q u h) (A (pureSymmetricTensor μ p u))
  change (1 / 2 : ℂ) * (x + y + Complex.I * (Complex.I * x - Complex.I * y)) = y
  linear_combination ((x - y) / 2) * Complex.I_mul_I

end LiebLiniger.FixedPeriod.Quantum
