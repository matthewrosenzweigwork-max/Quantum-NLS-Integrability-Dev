import LiebLiniger.FixedPeriod.Quantum.WickRealContractionKernel
import LiebLiniger.FixedPeriod.Quantum.FiniteModeWickProduct
import LiebLiniger.FixedPeriod.Quantum.SymmetricTensorBridges
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.StandardSubspace
import Mathlib.Analysis.Complex.Basic

/-! Proposed literal canonical Poisson bracket from the real Fréchet
derivatives of the physical one-particle functions. SOURCE ONLY, UNCOMPILED.
The bracket is independently defined, without using any contraction kernel. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ClosedSubmodule ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

/-- Real Riesz representatives, elaborated on an abstract complete real
Hilbert space before specialization to the physical one-particle carrier. -/
private def q4001_rieszRe {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] ℂ) : H :=
  (InnerProductSpace.toDual ℝ H).symm (Complex.reCLM.comp A)

private def q4001_rieszIm {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] ℂ) : H :=
  (InnerProductSpace.toDual ℝ H).symm (Complex.imCLM.comp A)

/-- Definitional body equality for the exact real Riesz construction. -/
theorem q4001_rieszRe_literal {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] ℂ) :
    q4001_rieszRe A = (InnerProductSpace.toDual ℝ H).symm (Complex.reCLM.comp A) := rfl

/-- Definitional body equality for the exact imaginary Riesz construction. -/
theorem q4001_rieszIm_literal {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] ℂ) :
    q4001_rieszIm A = (InnerProductSpace.toDual ℝ H).symm (Complex.imCLM.comp A) := rfl

private theorem q4001_rieszRe_pairing {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] ℂ) (v : H) : inner ℝ (q4001_rieszRe A) v = (A v).re := by
  exact InnerProductSpace.toDual_symm_apply

private theorem q4001_rieszIm_pairing {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] ℂ) (v : H) : inner ℝ (q4001_rieszIm A) v = (A v).im := by
  exact InnerProductSpace.toDual_symm_apply

/-- Real Riesz gradients of the real and imaginary parts of the actual
real Fréchet derivative. -/
def q4001RealGradientRe (f : Lp ℂ 2 μ → ℂ) (u : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  q4001_rieszRe (fderiv ℝ f u)

def q4001RealGradientIm (f : Lp ℂ 2 μ → ℂ) (u : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  q4001_rieszIm (fderiv ℝ f u)

/-- Canonical complex-bilinear Poisson bracket from the physical real
complex structure. On one mode z=x+iy it is one half of
∂ₓf∂ᵧg−∂ᵧf∂ₓg; in particular {z, conjugate z}=1/i. -/
def q4001CanonicalRealPoisson (f g : Lp ℂ 2 μ → ℂ)
    (u : Lp ℂ 2 μ) : ℂ :=
  -(1 / 2 : ℂ) *
    (fderiv ℝ f u (Complex.I • q4001RealGradientRe μ g u) +
      Complex.I * fderiv ℝ f u (Complex.I • q4001RealGradientIm μ g u))

/-- Riesz representative of the actual holomorphic derivative of the
physical kernel polynomial, defined for every input/output degree. -/
def q4001InputGradient {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (u : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (InnerProductSpace.toDual ℂ (Lp ℂ 2 μ)).symm
    (fderiv ℂ (wickKernelPolarized μ A u) u)

/-- Riesz representative of the conjugated antiholomorphic derivative. -/
def q4001OutputGradient {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (u : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (InnerProductSpace.toDual ℂ (Lp ℂ 2 μ)).symm
    (fderiv ℂ (fun w => conj (wickKernelPolarized μ A w u)) u)

/-- The genuine real derivative splits into the two represented physical
Wirtinger derivatives, including both zero-degree sectors. -/
theorem q4001_kernel_real_derivative_decomposition {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (u h : Lp ℂ 2 μ) :
    fderiv ℝ (wickKernelPolynomial μ A) u h =
      inner ℂ (q4001InputGradient μ A u) h +
        inner ℂ h (q4001OutputGradient μ A u) := by
  have hi : (1 / 2 : ℂ) * (fderiv ℝ (wickKernelPolynomial μ A) u h -
      Complex.I * fderiv ℝ (wickKernelPolynomial μ A) u (Complex.I • h)) =
      inner ℂ (q4001InputGradient μ A u) h := by
    rw [wickKernelPolynomial_wirtinger_input]
    exact (InnerProductSpace.toDual_symm_apply).symm
  have ho : (1 / 2 : ℂ) * (fderiv ℝ (wickKernelPolynomial μ A) u h +
      Complex.I * fderiv ℝ (wickKernelPolynomial μ A) u (Complex.I • h)) =
      inner ℂ h (q4001OutputGradient μ A u) := by
    rw [wickKernelPolynomial_wirtinger_output,
      ← inner_conj_symm (𝕜 := ℂ) h (q4001OutputGradient μ A u)]
    exact congrArg (starRingEnd ℂ) (InnerProductSpace.toDual_symm_apply).symm
  linear_combination hi + ho

/-- Real Riesz representatives of the two real components of the physical
derivative, expressed in terms of its independently obtained Wirtinger
representatives. -/
theorem q4001_kernel_real_gradient_re {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (u : Lp ℂ 2 μ) :
    q4001RealGradientRe μ (wickKernelPolynomial μ A) u =
      q4001InputGradient μ A u + q4001OutputGradient μ A u := by
  apply ext_inner_right ℝ
  intro h
  unfold q4001RealGradientRe
  rw [q4001_rieszRe_pairing]
  change (fderiv ℝ (wickKernelPolynomial μ A) u h).re = _
  rw [q4001_kernel_real_derivative_decomposition]
  rw [ClosedSubmodule.inner_real_eq_re_inner, inner_add_left]
  have hc := inner_conj_symm (𝕜 := ℂ) h (q4001OutputGradient μ A u)
  rw [← hc]
  simp only [Complex.add_re, Complex.conj_re]

/-- Imaginary-component real Riesz representative, retaining the sign forced
by conjugate linearity in the first inner-product entry. -/
theorem q4001_kernel_real_gradient_im {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (u : Lp ℂ 2 μ) :
    q4001RealGradientIm μ (wickKernelPolynomial μ A) u =
      Complex.I • (q4001InputGradient μ A u - q4001OutputGradient μ A u) := by
  apply ext_inner_right ℝ
  intro h
  unfold q4001RealGradientIm
  rw [q4001_rieszIm_pairing]
  change (fderiv ℝ (wickKernelPolynomial μ A) u h).im = _
  rw [q4001_kernel_real_derivative_decomposition]
  rw [ClosedSubmodule.inner_real_eq_re_inner, inner_smul_left, inner_sub_left]
  have hc := inner_conj_symm (𝕜 := ℂ) h (q4001OutputGradient μ A u)
  rw [← hc]
  simp [Complex.mul_re, Complex.add_im, Complex.sub_im]
  have him : (inner ℂ h (q4001OutputGradient μ A u)).im =
      -(inner ℂ (q4001OutputGradient μ A u) h).im :=
    inner_im_symm (𝕜 := ℂ) h (q4001OutputGradient μ A u)
  rw [him]
  ring

/-- The independent canonical real bracket of the actual physical kernel
polynomials is the difference of the two actual first Wirtinger pairings,
with the source order and division by i. -/
theorem q4001_real_poisson_eq_wirtinger_pairings {p q r s : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (B : SymmetricSector μ r →L[ℂ] SymmetricSector μ s)
    (u : Lp ℂ 2 μ) :
    q4001CanonicalRealPoisson μ (wickKernelPolynomial μ A)
        (wickKernelPolynomial μ B) u =
      (inner ℂ (q4001InputGradient μ A u) (q4001OutputGradient μ B u) -
        inner ℂ (q4001InputGradient μ B u) (q4001OutputGradient μ A u)) / Complex.I := by
  unfold q4001CanonicalRealPoisson
  rw [q4001_kernel_real_gradient_re, q4001_kernel_real_gradient_im]
  simp only [q4001_kernel_real_derivative_decomposition, smul_smul,
    Complex.I_mul_I, neg_one_smul, inner_smul_right, inner_smul_left,
    inner_add_right, inner_add_left, inner_sub_right, inner_sub_left,
    inner_neg_right, inner_neg_left, Complex.conj_I, div_eq_mul_inv, Complex.inv_I]
  ring

/-- With no input particles the physical holomorphic gradient vanishes. -/
theorem q4001_input_gradient_zero {q : ℕ}
    (A : SymmetricSector μ 0 →L[ℂ] SymmetricSector μ q) (u : Lp ℂ 2 μ) :
    q4001InputGradient μ A u = 0 := by
  apply ext_inner_right ℂ
  intro h
  have hz := wickKernelPolynomial_iteratedRealWirtinger_input_eq_zero (j := 1)
    μ A (by decide) u (fun _ : Fin 1 => h)
  simpa only [inner_zero_left, q4001InputGradient, InnerProductSpace.toDual_symm_apply,
    wickIteratedRealWirtingerInput_succ, wickIteratedRealWirtingerInput_zero,
    wickRealWirtingerInput, wickKernelPolynomial_wirtinger_input] using hz

/-- With no output particles the physical antiholomorphic gradient vanishes. -/
theorem q4001_output_gradient_zero {p : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ 0) (u : Lp ℂ 2 μ) :
    q4001OutputGradient μ A u = 0 := by
  apply ext_inner_right ℂ
  intro h
  have hz := wickKernelPolynomial_iteratedRealWirtinger_output_eq_zero (j := 1)
    μ A (by decide) u (fun _ : Fin 1 => h)
  have hz' : conj (inner ℂ (q4001OutputGradient μ A u) h) = 0 := by
    simpa only [q4001OutputGradient, InnerProductSpace.toDual_symm_apply,
      wickIteratedRealWirtingerOutput_succ, wickIteratedRealWirtingerOutput_zero,
      wickRealWirtingerOutput, wickKernelPolynomial_wirtinger_output] using hz
  have hc := congrArg (starRingEnd ℂ) hz'
  simpa only [starRingEnd_apply, star_star, map_zero, inner_zero_left] using hc

variable [IsFiniteMeasure μ]

/-- One-slot input functional equals the actual one-particle Riesz
representative of the physical holomorphic derivative. -/
theorem q4001_one_input_functional {a q : ℕ}
    (A : SymmetricSector μ (a + 1) →L[ℂ] SymmetricSector μ q)
    (u h : Lp ℂ 2 μ) :
    wickInputDerivativeFunctional μ A u u ((oneProductL2Equiv μ).symm h) =
      inner ℂ (q4001InputGradient μ A u) h := by
  have hd := wickInputDerivativeFunctional_real_mixed μ A u (fun _ : Fin 1 => h)
  simpa only [mixedTensorL2_diagonal, ← oneProductL2Equiv_symm_eq_pureTensorL2,
    wickIteratedRealWirtingerInput_succ, wickIteratedRealWirtingerInput_zero,
    wickRealWirtingerInput, wickKernelPolynomial_wirtinger_input,
    q4001InputGradient, InnerProductSpace.toDual_symm_apply] using hd

/-- One-slot output vector is the actual one-particle Riesz representative
of the conjugated physical antiholomorphic derivative. -/
theorem q4001_one_output_vector {k b : ℕ}
    (B : SymmetricSector μ k →L[ℂ] SymmetricSector μ (1 + b))
    (u : Lp ℂ 2 μ) :
    (oneProductL2Equiv μ) (wickOutputDerivativeVector μ B u u) =
      q4001OutputGradient μ B u := by
  apply ext_inner_right ℂ
  intro h
  have hd := wickOutputDerivativeVector_real_mixed μ B u (fun _ : Fin 1 => h)
  have hd' : conj (inner ℂ (wickOutputDerivativeVector μ B u u)
      ((oneProductL2Equiv μ).symm h)) =
      conj (inner ℂ (q4001OutputGradient μ B u) h) := by
    simpa only [mixedTensorL2_diagonal, ← oneProductL2Equiv_symm_eq_pureTensorL2,
      wickIteratedRealWirtingerOutput_succ, wickIteratedRealWirtingerOutput_zero,
      wickRealWirtingerOutput, wickKernelPolynomial_wirtinger_output,
      q4001OutputGradient, InnerProductSpace.toDual_symm_apply] using hd
  have hc := congrArg (starRingEnd ℂ) hd'
  have he : inner ℂ (wickOutputDerivativeVector μ B u u)
      ((oneProductL2Equiv μ).symm h) =
      inner ℂ (q4001OutputGradient μ B u) h := by
    simpa only [starRingEnd_apply, star_star] using hc
  calc
    inner ℂ ((oneProductL2Equiv μ) (wickOutputDerivativeVector μ B u u)) h =
        inner ℂ ((oneProductL2Equiv μ) (wickOutputDerivativeVector μ B u u))
          ((oneProductL2Equiv μ) ((oneProductL2Equiv μ).symm h)) := by
      rw [(oneProductL2Equiv μ).apply_symm_apply]
    _ = inner ℂ (wickOutputDerivativeVector μ B u u)
        ((oneProductL2Equiv μ).symm h) :=
      (oneProductL2Equiv μ).inner_map_map _ _
    _ = _ := he

/-- The first source kernel is the independently characterized actual
derivative contraction, when its contracted grades are presented explicitly. -/
theorem q4001_first_source_contraction_real_pairing {a b q k : ℕ}
    (A : SymmetricSector μ (a + 1) →L[ℂ] SymmetricSector μ q)
    (B : SymmetricSector μ k →L[ℂ] SymmetricSector μ (1 + b))
    (u : Lp ℂ 2 μ) :
    wickKernelPolynomial μ (sourceDerivativeContractionKernel μ A B 1) u =
      wickRealDerivativeContraction μ A B u := by
  rw [wickRealDerivativeContraction_kernel]
  exact sourceDerivativeContractionKernel_available_outer_naturality μ a 1 b q k A B u u

/-- In every available first-order branch, the literal source contraction
polynomial is the pairing of the actual physical input and output gradients. -/
theorem q4001_first_source_contraction_gradient_pairing {a b q k : ℕ}
    (A : SymmetricSector μ (a + 1) →L[ℂ] SymmetricSector μ q)
    (B : SymmetricSector μ k →L[ℂ] SymmetricSector μ (1 + b))
    (u : Lp ℂ 2 μ) :
    wickKernelPolynomial μ (sourceDerivativeContractionKernel μ A B 1) u =
      inner ℂ (q4001InputGradient μ A u) (q4001OutputGradient μ B u) := by
  rw [q4001_first_source_contraction_real_pairing]
  change wickInputDerivativeFunctional μ A u u (wickOutputDerivativeVector μ B u u) = _
  calc
    _ = wickInputDerivativeFunctional μ A u u
        ((oneProductL2Equiv μ).symm
          ((oneProductL2Equiv μ) (wickOutputDerivativeVector μ B u u))) :=
      congrArg (wickInputDerivativeFunctional μ A u u)
        ((oneProductL2Equiv μ).symm_apply_apply _).symm
    _ = inner ℂ (q4001InputGradient μ A u)
        ((oneProductL2Equiv μ) (wickOutputDerivativeVector μ B u u)) :=
      q4001_one_input_functional μ A u _
    _ = _ := congrArg (inner ℂ (q4001InputGradient μ A u))
      (q4001_one_output_vector μ B u)

end LiebLiniger.FixedPeriod.Quantum
end
