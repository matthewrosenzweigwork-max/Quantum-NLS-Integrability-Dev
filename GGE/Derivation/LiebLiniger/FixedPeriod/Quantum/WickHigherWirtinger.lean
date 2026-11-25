import LiebLiniger.FixedPeriod.Quantum.WickWirtinger
import LiebLiniger.FixedPeriod.Quantum.WickDerivativeContraction
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Higher actual real Wirtinger derivatives of the physical Wick polynomial

The operators below are defined by the real Fréchet derivative and the actual
complex structure. Their iteration is independent of any polarized derivative
or contraction kernel. Equality with the latter is proved through complex
smooth sesquilinear factors. No derivative or product identity is assumed.
-/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate BigOperators ContDiff
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

/-- Actual holomorphic extraction from the real derivative. -/
def wickRealWirtingerInput (f : Lp ℂ 2 μ → ℂ) (h : Lp ℂ 2 μ) : Lp ℂ 2 μ → ℂ :=
  fun u => (1 / 2 : ℂ) *
    (fderiv ℝ f u h - Complex.I * fderiv ℝ f u (Complex.I • h))

/-- Actual conjugate-holomorphic extraction from the same real derivative. -/
def wickRealWirtingerOutput (f : Lp ℂ 2 μ → ℂ) (h : Lp ℂ 2 μ) : Lp ℂ 2 μ → ℂ :=
  fun u => (1 / 2 : ℂ) *
    (fderiv ℝ f u h + Complex.I * fderiv ℝ f u (Complex.I • h))

/-- Ordered iteration of the actual real input extraction, including order zero. -/
def wickIteratedRealWirtingerInput (f : Lp ℂ 2 μ → ℂ) :
    (j : ℕ) → (Fin j → Lp ℂ 2 μ) → Lp ℂ 2 μ → ℂ
  | 0, _ => f
  | j + 1, h => wickRealWirtingerInput μ
      (wickIteratedRealWirtingerInput f j (Fin.tail h)) (h 0)

/-- Ordered iteration of the actual real output extraction. -/
def wickIteratedRealWirtingerOutput (f : Lp ℂ 2 μ → ℂ) :
    (j : ℕ) → (Fin j → Lp ℂ 2 μ) → Lp ℂ 2 μ → ℂ
  | 0, _ => f
  | j + 1, h => wickRealWirtingerOutput μ
      (wickIteratedRealWirtingerOutput f j (Fin.tail h)) (h 0)

section Sesquilinear
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

/-- Both real extractions for arbitrary actual complex differentiable factors.
Differentiability is used to establish the real derivative before extracting it. -/
theorem wickRealWirtinger_inner {U V : Lp ℂ 2 μ → F} (u h : Lp ℂ 2 μ)
    (hU : DifferentiableAt ℂ U u) (hV : DifferentiableAt ℂ V u) :
    wickRealWirtingerInput μ (fun x => inner ℂ (U x) (V x)) h u =
        inner ℂ (U u) (fderiv ℂ V u h) ∧
      wickRealWirtingerOutput μ (fun x => inner ℂ (U x) (V x)) h u =
        inner ℂ (fderiv ℂ U u h) (V u) := by
  have hreal := (hU.hasFDerivAt.restrictScalars ℝ).inner ℂ
    (hV.hasFDerivAt.restrictScalars ℝ)
  have hd (k : Lp ℂ 2 μ) :
      fderiv ℝ (fun x => inner ℂ (U x) (V x)) u k =
        inner ℂ (U u) (fderiv ℂ V u k) + inner ℂ (fderiv ℂ U u k) (V u) := by
    rw [hreal.fderiv]
    rfl
  have hlin : inner ℂ (U u) (fderiv ℂ V u (Complex.I • h)) =
      Complex.I * inner ℂ (U u) (fderiv ℂ V u h) := by
    rw [map_smul]
    exact inner_smul_right (𝕜 := ℂ) (U u) (fderiv ℂ V u h) Complex.I
  have hanti : inner ℂ (fderiv ℂ U u (Complex.I • h)) (V u) =
      (-Complex.I) * inner ℂ (fderiv ℂ U u h) (V u) := by
    rw [map_smul]
    simpa only [Complex.conj_I] using
      inner_smul_left (𝕜 := ℂ) (fderiv ℂ U u h) (V u) Complex.I
  simp only [wickRealWirtingerInput, wickRealWirtingerOutput, hd, hlin, hanti]
  let a := inner ℂ (U u) (fderiv ℂ V u h)
  let b := inner ℂ (fderiv ℂ U u h) (V u)
  change (1 / 2 : ℂ) * (a + b - Complex.I * (Complex.I * a + (-Complex.I) * b)) = a ∧
    (1 / 2 : ℂ) * (a + b + Complex.I * (Complex.I * a + (-Complex.I) * b)) = b
  constructor
  · linear_combination (-(a - b) / 2) * Complex.I_mul_I
  · linear_combination ((a - b) / 2) * Complex.I_mul_I

/-- Iterating the actual real input extraction differentiates only the second
complex smooth factor, for every order and arbitrary ordered directions. -/
theorem wickIteratedRealWirtingerInput_inner {U V : Lp ℂ 2 μ → F}
    (hU : ContDiff ℂ (⊤ : ℕ∞ω) U) (hV : ContDiff ℂ (⊤ : ℕ∞ω) V)
    (j : ℕ) (h : Fin j → Lp ℂ 2 μ) (u : Lp ℂ 2 μ) :
    wickIteratedRealWirtingerInput μ (fun x => inner ℂ (U x) (V x)) j h u =
      inner ℂ (U u) (iteratedFDeriv ℂ j V u h) := by
  induction j generalizing u with
  | zero => simp [wickIteratedRealWirtingerInput]
  | succ j ih =>
    have he : wickIteratedRealWirtingerInput μ (fun x => inner ℂ (U x) (V x)) j
        (Fin.tail h) = fun x => inner ℂ (U x) (iteratedFDeriv ℂ j V x (Fin.tail h)) :=
      funext (fun x => ih (Fin.tail h) x)
    have hv := hV.differentiable_iteratedFDeriv (m := j) (by simp)
    rw [wickIteratedRealWirtingerInput, he]
    rw [(wickRealWirtinger_inner μ u (h 0)
      (hU.differentiable (by simp) u) ((hv u).continuousMultilinear_apply_const (Fin.tail h))).1]
    rw [← (hv u).iteratedFDeriv_succ_apply_left']

/-- The corresponding actual output iteration differentiates only the first
factor, retaining its conjugate-linearity in every extracted direction. -/
theorem wickIteratedRealWirtingerOutput_inner {U V : Lp ℂ 2 μ → F}
    (hU : ContDiff ℂ (⊤ : ℕ∞ω) U) (hV : ContDiff ℂ (⊤ : ℕ∞ω) V)
    (j : ℕ) (h : Fin j → Lp ℂ 2 μ) (u : Lp ℂ 2 μ) :
    wickIteratedRealWirtingerOutput μ (fun x => inner ℂ (U x) (V x)) j h u =
      inner ℂ (iteratedFDeriv ℂ j U u h) (V u) := by
  induction j generalizing u with
  | zero => simp [wickIteratedRealWirtingerOutput]
  | succ j ih =>
    have he : wickIteratedRealWirtingerOutput μ (fun x => inner ℂ (U x) (V x)) j
        (Fin.tail h) = fun x => inner ℂ (iteratedFDeriv ℂ j U x (Fin.tail h)) (V x) :=
      funext (fun x => ih (Fin.tail h) x)
    have hu := hU.differentiable_iteratedFDeriv (m := j) (by simp)
    rw [wickIteratedRealWirtingerOutput, he]
    rw [(wickRealWirtinger_inner μ u (h 0)
      ((hu u).continuousMultilinear_apply_const (Fin.tail h))
      (hV.differentiable (by simp) u)).2]
    rw [← (hu u).iteratedFDeriv_succ_apply_left']
end Sesquilinear

/-- The physical pure tensor is complex smooth at every order, including zero. -/
theorem wickPureTensor_contDiff (n : ℕ) (N : ℕ∞ω) :
    ContDiff ℂ N (pureSymmetricTensor μ n) := by
  have hc : ContDiff ℂ N
      (symmetricTensorContinuousMultilinear μ n ∘ wickKernelDiagonalMap μ n) :=
    (symmetricTensorContinuousMultilinear μ n).contDiff.comp (wickKernelDiagonalMap μ n).contDiff
  simpa only [Function.comp_def, wickKernelDiagonalMap_apply,
    symmetricTensorContinuousMultilinear_diagonal] using hc

/-- All actual real input extractions equal the independent polarized complex
derivative, with the antiholomorphic variable frozen only after differentiation. -/
theorem wickKernelPolynomial_iteratedRealWirtinger_input {p q j : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (u : Lp ℂ 2 μ) (h : Fin j → Lp ℂ 2 μ) :
    wickIteratedRealWirtingerInput μ (wickKernelPolynomial μ A) j h u =
      iteratedFDeriv ℂ j (wickKernelPolarized μ A u) u h := by
  have hp := wickPureTensor_contDiff μ p (⊤ : ℕ∞ω)
  have hq := wickPureTensor_contDiff μ q (⊤ : ℕ∞ω)
  have hv : ContDiff ℂ (⊤ : ℕ∞ω) (A ∘ pureSymmetricTensor μ p) := A.contDiff.comp hp
  have hreal := wickIteratedRealWirtingerInput_inner μ hq hv j h u
  have hcomplex := (innerSL ℂ (pureSymmetricTensor μ q u)).iteratedFDeriv_comp_left (x := u)
    hv.contDiffAt (i := j) (by simp)
  have hc := congrArg (fun T => T h) hcomplex
  change iteratedFDeriv ℂ j (wickKernelPolarized μ A u) u h =
    inner ℂ (pureSymmetricTensor μ q u) (iteratedFDeriv ℂ j (A ∘ pureSymmetricTensor μ p) u h) at hc
  exact hreal.trans hc.symm

/-- All actual real output extractions equal the conjugate of the independent
complex derivative of the conjugated output polarization. -/
theorem wickKernelPolynomial_iteratedRealWirtinger_output {p q j : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (u : Lp ℂ 2 μ) (h : Fin j → Lp ℂ 2 μ) :
    wickIteratedRealWirtingerOutput μ (wickKernelPolynomial μ A) j h u =
      conj (iteratedFDeriv ℂ j (fun w => conj (wickKernelPolarized μ A w u)) u h) := by
  have hp := wickPureTensor_contDiff μ p (⊤ : ℕ∞ω)
  have hq := wickPureTensor_contDiff μ q (⊤ : ℕ∞ω)
  have hv : ContDiff ℂ (⊤ : ℕ∞ω) (A ∘ pureSymmetricTensor μ p) := A.contDiff.comp hp
  have hreal := wickIteratedRealWirtingerOutput_inner μ hq hv j h u
  have hcomplex := (innerSL ℂ (A (pureSymmetricTensor μ p u))).iteratedFDeriv_comp_left (x := u)
    hq.contDiffAt (i := j) (by simp)
  have hc := congrArg (fun T => T h) hcomplex
  have hf : (innerSL ℂ (A (pureSymmetricTensor μ p u))) ∘ pureSymmetricTensor μ q =
      fun w => conj (wickKernelPolarized μ A w u) := by
    funext w
    change inner ℂ (A (pureSymmetricTensor μ p u)) (pureSymmetricTensor μ q w) =
      conj (inner ℂ (pureSymmetricTensor μ q w) (A (pureSymmetricTensor μ p u)))
    exact (inner_conj_symm (𝕜 := ℂ) (A (pureSymmetricTensor μ p u))
      (pureSymmetricTensor μ q w)).symm
  rw [hf] at hc
  change iteratedFDeriv ℂ j (fun w => conj (wickKernelPolarized μ A w u)) u h =
    inner ℂ (A (pureSymmetricTensor μ p u)) (iteratedFDeriv ℂ j (pureSymmetricTensor μ q) u h) at hc
  rw [hc, inner_conj_symm]
  exact hreal

/-- Actual real input extractions vanish above the source input degree. -/
theorem wickKernelPolynomial_iteratedRealWirtinger_input_eq_zero {p q j : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (hj : p < j) (u : Lp ℂ 2 μ) (h : Fin j → Lp ℂ 2 μ) :
    wickIteratedRealWirtingerInput μ (wickKernelPolynomial μ A) j h u = 0 := by
  classical
  haveI : IsEmpty (Fin j ↪ Fin p) := ⟨fun e =>
    (Nat.not_le_of_lt hj) (by simpa using Fintype.card_le_of_injective e e.injective)⟩
  rw [wickKernelPolynomial_iteratedRealWirtinger_input,
    wickKernelPolarized_iteratedFDeriv_input_slots]
  exact Finset.sum_eq_zero (fun e _ => isEmptyElim e)

/-- Actual real output extractions vanish above the source output degree. -/
theorem wickKernelPolynomial_iteratedRealWirtinger_output_eq_zero {p q j : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (hj : q < j) (u : Lp ℂ 2 μ) (h : Fin j → Lp ℂ 2 μ) :
    wickIteratedRealWirtingerOutput μ (wickKernelPolynomial μ A) j h u = 0 := by
  classical
  haveI : IsEmpty (Fin j ↪ Fin q) := ⟨fun e =>
    (Nat.not_le_of_lt hj) (by simpa using Fintype.card_le_of_injective e e.injective)⟩
  rw [wickKernelPolynomial_iteratedRealWirtinger_output,
    wickKernelPolarized_iteratedFDeriv_conj_output_slots]
  simp

variable [IsFiniteMeasure μ]

/-- The complete input free-slot extension is characterized by actual iterated
real extraction on every arbitrary elementary free tensor. -/
theorem wickInputDerivativeFunctional_real_mixed {r j qb : ℕ}
    (A : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ qb)
    (u : Lp ℂ 2 μ) (h : Fin j → Lp ℂ 2 μ) :
    wickInputDerivativeFunctional μ A u u (mixedTensorL2 μ h) =
      wickIteratedRealWirtingerInput μ (wickKernelPolynomial μ A) j h u := by
  rw [wickKernelPolynomial_iteratedRealWirtinger_input]
  exact wickInputDerivativeFunctional_mixed μ A u u h

/-- The conjugate output Riesz pairing has the corresponding actual iterated
real extraction, retaining the inner-product and direction conjugations. -/
theorem wickOutputDerivativeVector_real_mixed {pc j s : ℕ}
    (A : SymmetricSector μ pc →L[ℂ] SymmetricSector μ (j + s))
    (u : Lp ℂ 2 μ) (h : Fin j → Lp ℂ 2 μ) :
    conj (inner ℂ (wickOutputDerivativeVector μ A u u) (mixedTensorL2 μ h)) =
      wickIteratedRealWirtingerOutput μ (wickKernelPolynomial μ A) j h u := by
  rw [wickKernelPolynomial_iteratedRealWirtinger_output,
    wickOutputDerivativeVector_inner_mixed]

end LiebLiniger.FixedPeriod.Quantum
