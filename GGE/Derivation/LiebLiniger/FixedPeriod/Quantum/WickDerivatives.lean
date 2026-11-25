import LiebLiniger.FixedPeriod.Quantum.MixedTensor
import LiebLiniger.FixedPeriod.Quantum.WickSectorMap
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Physical symmetric-tensor derivatives of a Wick kernel polynomial

For the actual bounded kernel A : Sym^p H -> Sym^q H, the source polynomial is
b_A(u) = <u^tensor q, A u^tensor p>. Its polarized version keeps the
antiholomorphic output variable v separate from the holomorphic input u.
This file differentiates that genuine physical polynomial, using the actual
continuous multilinear symmetric-tensor map. No contraction or CCR is assumed.

The first input derivative is the sum over genuine tensor slots. The full
p-th input derivative and conjugated q-th output derivative have their exact
factorials. Intermediate j-th derivative contraction, its tensor-slot composition,
and transport of differential normal ordering to Wick sector maps remain open.

Author candidate: only the root's compiler lane validates it.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace LiebLiniger.FixedPeriod.Quantum

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

/-- The literal source kernel polynomial, on the physical one-particle L² carrier. -/
def wickKernelPolynomial {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (u : Lp ℂ 2 μ) : ℂ :=
  inner ℂ (pureSymmetricTensor μ q u) (A (pureSymmetricTensor μ p u))

/-- Source polarization: conjugate-holomorphic in v, holomorphic in u. -/
def wickKernelPolarized {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (v u : Lp ℂ 2 μ) : ℂ :=
  inner ℂ (pureSymmetricTensor μ q v) (A (pureSymmetricTensor μ p u))

@[simp] theorem wickKernelPolarized_diagonal {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (u : Lp ℂ 2 μ) :
    wickKernelPolarized μ A u u = wickKernelPolynomial μ A u := rfl

/-- The actual holomorphic p-linear input kernel, before taking its diagonal. -/
def wickKernelInputMultilinear {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (v : Lp ℂ 2 μ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin p => Lp ℂ 2 μ) ℂ :=
  ((innerSL ℂ (pureSymmetricTensor μ q v)).comp A).compContinuousMultilinearMap
    (symmetricTensorContinuousMultilinear μ p)

@[simp] theorem wickKernelInputMultilinear_apply {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (v : Lp ℂ 2 μ)
    (h : Fin p → Lp ℂ 2 μ) :
    wickKernelInputMultilinear μ A v h =
      inner ℂ (pureSymmetricTensor μ q v) (A (symmetricTensorContinuousMultilinear μ p h)) := rfl

@[simp] theorem wickKernelInputMultilinear_diagonal {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (v u : Lp ℂ 2 μ) :
    wickKernelInputMultilinear μ A v (fun _ => u) = wickKernelPolarized μ A v u := by
  rw [wickKernelInputMultilinear_apply, symmetricTensorContinuousMultilinear_diagonal]
  rfl

/-- Diagonal insertion is an actual bounded complex-linear map, including p=0. -/
def wickKernelDiagonalMap (p : ℕ) : (Lp ℂ 2 μ) →L[ℂ] (Fin p → Lp ℂ 2 μ) :=
  ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℂ (Lp ℂ 2 μ))

@[simp] theorem wickKernelDiagonalMap_apply (p : ℕ) (u : Lp ℂ 2 μ) :
    wickKernelDiagonalMap μ p u = fun _ => u := rfl

/-- Actual complex Fréchet derivative in the holomorphic input slot. -/
def wickKernelInputDerivative {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (v u : Lp ℂ 2 μ) :
    (Lp ℂ 2 μ) →L[ℂ] ℂ :=
  ((wickKernelInputMultilinear μ A v).linearDeriv (fun _ => u)).comp
    (wickKernelDiagonalMap μ p)

/-- Differentiability is proved before any totalized fderiv identity is used. -/
theorem wickKernelPolarized_hasFDerivAt_input {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (v u : Lp ℂ 2 μ) :
    HasFDerivAt (wickKernelPolarized μ A v) (wickKernelInputDerivative μ A v u) u := by
  have h := ((wickKernelInputMultilinear μ A v).hasFDerivAt (fun _ => u)).comp u
    (wickKernelDiagonalMap μ p).hasFDerivAt
  simpa only [wickKernelInputDerivative, Function.comp_def,
    wickKernelDiagonalMap_apply, wickKernelInputMultilinear_diagonal] using h

/-- The first derivative is exactly the sum over the p physical input slots. -/
theorem wickKernelInputDerivative_apply {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (v u h : Lp ℂ 2 μ) :
    wickKernelInputDerivative μ A v u h =
      ∑ i : Fin p, inner ℂ (pureSymmetricTensor μ q v)
        (A (symmetricTensorContinuousMultilinear μ p
          (Function.update (fun _ => u) i h))) := by
  change (wickKernelInputMultilinear μ A v).linearDeriv (fun _ => u) (fun _ => h) = _
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  rfl

/-- Full physical input derivative: the exact p! factor multiplies A on the
actual symmetrized arbitrary tensor directions. This includes p=0. -/
theorem wickKernelPolarized_iteratedFDeriv_input {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (v u : Lp ℂ 2 μ)
    (h : Fin p → Lp ℂ 2 μ) :
    iteratedFDeriv ℂ p (wickKernelPolarized μ A v) u h =
      p.factorial • inner ℂ (pureSymmetricTensor μ q v)
        (A (symmetricTensorContinuousMultilinear μ p h)) := by
  have hdiag : (fun x => wickKernelInputMultilinear μ A v (fun _ => x)) =
      wickKernelPolarized μ A v := by
    funext x
    exact wickKernelInputMultilinear_diagonal μ A v x
  have hs (σ : Equiv.Perm (Fin p)) :
      wickKernelInputMultilinear μ A v (fun i => h (σ i)) =
        wickKernelInputMultilinear μ A v h := by
    simp only [wickKernelInputMultilinear_apply,
      symmetricTensorContinuousMultilinear_permutation]
  have hd := (wickKernelInputMultilinear μ A v).iteratedFDeriv_comp_diagonal u h
  rw [hdiag] at hd
  simpa only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, wickKernelInputMultilinear_apply] using hd

/-- Conjugating the output-variable polynomial makes that slot holomorphic.
This avoids incorrectly claiming complex differentiability of its conjugate. -/
def wickKernelConjugateOutputMultilinear {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (u : Lp ℂ 2 μ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin q => Lp ℂ 2 μ) ℂ :=
  (innerSL ℂ (A (pureSymmetricTensor μ p u))).compContinuousMultilinearMap
    (symmetricTensorContinuousMultilinear μ q)

@[simp] theorem wickKernelConjugateOutputMultilinear_apply {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (u : Lp ℂ 2 μ)
    (h : Fin q → Lp ℂ 2 μ) :
    wickKernelConjugateOutputMultilinear μ A u h =
      inner ℂ (A (pureSymmetricTensor μ p u)) (symmetricTensorContinuousMultilinear μ q h) := rfl

@[simp] theorem wickKernelConjugateOutputMultilinear_diagonal {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (u v : Lp ℂ 2 μ) :
    wickKernelConjugateOutputMultilinear μ A u (fun _ => v) =
      conj (wickKernelPolarized μ A v u) := by
  rw [wickKernelConjugateOutputMultilinear_apply,
    symmetricTensorContinuousMultilinear_diagonal]
  exact (inner_conj_symm (A (pureSymmetricTensor μ p u)) (pureSymmetricTensor μ q v)).symm

/-- Full conjugated physical output derivative with its exact q! factor. -/
theorem wickKernelPolarized_iteratedFDeriv_conj_output {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (u v : Lp ℂ 2 μ)
    (h : Fin q → Lp ℂ 2 μ) :
    iteratedFDeriv ℂ q (fun w => conj (wickKernelPolarized μ A w u)) v h =
      q.factorial • inner ℂ (A (pureSymmetricTensor μ p u))
        (symmetricTensorContinuousMultilinear μ q h) := by
  have hdiag : (fun x => wickKernelConjugateOutputMultilinear μ A u (fun _ => x)) =
      (fun x => conj (wickKernelPolarized μ A x u)) := by
    funext x
    exact wickKernelConjugateOutputMultilinear_diagonal μ A u x
  have hs (σ : Equiv.Perm (Fin q)) :
      wickKernelConjugateOutputMultilinear μ A u (fun i => h (σ i)) =
        wickKernelConjugateOutputMultilinear μ A u h := by
    simp only [wickKernelConjugateOutputMultilinear_apply,
      symmetricTensorContinuousMultilinear_permutation]
  have hd := (wickKernelConjugateOutputMultilinear μ A u).iteratedFDeriv_comp_diagonal v h
  rw [hdiag] at hd
  simpa only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, wickKernelConjugateOutputMultilinear_apply] using hd

end LiebLiniger.FixedPeriod.Quantum
