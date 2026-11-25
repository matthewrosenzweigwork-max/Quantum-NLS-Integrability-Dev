import QuantumNLS.SymplecticBracket
import QuantumNLS.RootBracketScalars

/-!
# R-C4F43CA8 `thm:root-involution`, part (3)(i): the holomorphic chain rule for the complex bracket

For a complex-valued `s` differentiable at `u` and a holomorphic `φ` (derivative `a` at `s u`):
`pbC (φ ∘ s) G u = a · pbC s G u`. This is the bracket form of the chain rule used for `G_z = φ ∘ s_z`.

Realized inputs (frozen): `SymplecticBracket.pbR`, `pbC`, `pbR_eq_omega`; `RootBracketScalars.pbR_const_mul_left`.

Proved here (standard axioms only):
* `pbR_of_fderiv_eq`: the real bracket depends only on the derivative of the first argument at `u`.
* `pbR_add_left`, `pbR_lin`: additivity and linearity in the first slot (differentiable case).
* `pbC_const_mul`: `pbC (a · f) G u = a · pbC f G u` for complex `a`.
* `pbC_chain`: `pbC (φ ∘ s) G u = a · pbC s G u`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace ComplexConjugate BigOperators
open Filter Topology

attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.RootHolomorphicBracket

open QuantumNLS.SymplecticBracket QuantumNLS.RootBracketScalars

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem pbR_of_fderiv_eq (F F₂ K : H → ℝ) (u : H) (h : fderiv ℝ F u = fderiv ℝ F₂ u) :
    pbR F K u = pbR F₂ K u := by
  unfold pbR
  rw [h]

theorem pbR_add_left (F F₂ K : H → ℝ) (u : H) (hF : DifferentiableAt ℝ F u)
    (hF₂ : DifferentiableAt ℝ F₂ u) :
    pbR (fun v => F v + F₂ v) K u = pbR F K u + pbR F₂ K u := by
  unfold pbR
  rw [show fderiv ℝ (fun v => F v + F₂ v) u = fderiv ℝ F u + fderiv ℝ F₂ u from fderiv_add hF hF₂]
  simp

theorem pbR_lin (c d : ℝ) (x y K : H → ℝ) (u : H) (hx : DifferentiableAt ℝ x u)
    (hy : DifferentiableAt ℝ y u) :
    pbR (fun v => c * x v + d * y v) K u = c * pbR x K u + d * pbR y K u := by
  rw [pbR_add_left (fun v => c * x v) (fun v => d * y v) K u (hx.const_mul c) (hy.const_mul d)]
  rw [pbR_const_mul_left c x K u hx, pbR_const_mul_left d y K u hy]

theorem pbC_const_mul (a : ℂ) (f G : H → ℂ) (u : H)
    (hf1 : DifferentiableAt ℝ (fun v => (f v).re) u) (hf2 : DifferentiableAt ℝ (fun v => (f v).im) u) :
    pbC (fun v => a * f v) G u = a * pbC f G u := by
  have e1 : (fun v => (a * f v).re) = fun v => a.re * (f v).re + (-a.im) * (f v).im := by
    funext v
    simp only [Complex.mul_re]
    ring
  have e2 : (fun v => (a * f v).im) = fun v => a.im * (f v).re + a.re * (f v).im := by
    funext v
    simp only [Complex.mul_im]
    ring
  unfold pbC
  rw [e1, e2]
  rw [pbR_lin a.re (-a.im) _ _ (fun v => (G v).re) u hf1 hf2]
  rw [pbR_lin a.re (-a.im) _ _ (fun v => (G v).im) u hf1 hf2]
  rw [pbR_lin a.im a.re _ _ (fun v => (G v).re) u hf1 hf2]
  rw [pbR_lin a.im a.re _ _ (fun v => (G v).im) u hf1 hf2]
  apply Complex.ext
  · simp only [Complex.mul_re]
    ring
  · simp only [Complex.mul_im]
    ring

/-- **Holomorphic chain rule for the complex bracket.** If `φ` has derivative `a` at `s u` and `s` is real-differentiable
at `u` with derivative `S`, then `pbC (φ ∘ s) G u = a · pbC s G u`. -/
theorem pbC_chain (φ : ℂ → ℂ) (a : ℂ) (s : H → ℂ) (S : H →L[ℝ] ℂ) (u : H)
    (hφ : HasDerivAt φ a (s u)) (hs : HasFDerivAt s S u) (G : H → ℂ)
    (hG1 : DifferentiableAt ℝ (fun v => (G v).re) u) (hG2 : DifferentiableAt ℝ (fun v => (G v).im) u) :
    pbC (fun v => φ (s v)) G u = a * pbC s G u := by
  have hφR : HasFDerivAt φ ((ContinuousLinearMap.toSpanSingleton ℂ a).restrictScalars ℝ) (s u) :=
    hφ.hasFDerivAt.restrictScalars ℝ
  have hcomp : HasFDerivAt (fun v => φ (s v)) (((ContinuousLinearMap.toSpanSingleton ℂ a).restrictScalars ℝ).comp S) u :=
    hφR.comp u hs
  have hlin : HasFDerivAt (fun v => a * s v) (a • S) u := hs.const_mul a
  have hder : ((ContinuousLinearMap.toSpanSingleton ℂ a).restrictScalars ℝ).comp S = a • S := by
    ext x
    simp [mul_comm]
  have hre : fderiv ℝ (fun v => (φ (s v)).re) u = fderiv ℝ (fun v => (a * s v).re) u := by
    have h1 : fderiv ℝ (fun v => (φ (s v)).re) u =
        Complex.reCLM.comp (((ContinuousLinearMap.toSpanSingleton ℂ a).restrictScalars ℝ).comp S) :=
      (Complex.reCLM.hasFDerivAt.comp u hcomp).fderiv
    have h2 : fderiv ℝ (fun v => (a * s v).re) u = Complex.reCLM.comp (a • S) :=
      (Complex.reCLM.hasFDerivAt.comp u hlin).fderiv
    rw [h1, h2, hder]
  have him : fderiv ℝ (fun v => (φ (s v)).im) u = fderiv ℝ (fun v => (a * s v).im) u := by
    have h1 : fderiv ℝ (fun v => (φ (s v)).im) u =
        Complex.imCLM.comp (((ContinuousLinearMap.toSpanSingleton ℂ a).restrictScalars ℝ).comp S) :=
      (Complex.imCLM.hasFDerivAt.comp u hcomp).fderiv
    have h2 : fderiv ℝ (fun v => (a * s v).im) u = Complex.imCLM.comp (a • S) :=
      (Complex.imCLM.hasFDerivAt.comp u hlin).fderiv
    rw [h1, h2, hder]
  have hkre : ∀ K : H → ℂ, pbR (fun v => (φ (s v)).re) (fun v => (K v).re) u =
      pbR (fun v => (a * s v).re) (fun v => (K v).re) u :=
    fun K => pbR_of_fderiv_eq _ _ _ u hre
  have hkim : ∀ K : H → ℂ, pbR (fun v => (φ (s v)).im) (fun v => (K v).im) u =
      pbR (fun v => (a * s v).im) (fun v => (K v).im) u :=
    fun K => pbR_of_fderiv_eq _ _ _ u him
  have hkmr : ∀ K : H → ℂ, pbR (fun v => (φ (s v)).im) (fun v => (K v).re) u =
      pbR (fun v => (a * s v).im) (fun v => (K v).re) u :=
    fun K => pbR_of_fderiv_eq _ _ _ u him
  have hkrm : ∀ K : H → ℂ, pbR (fun v => (φ (s v)).re) (fun v => (K v).im) u =
      pbR (fun v => (a * s v).re) (fun v => (K v).im) u :=
    fun K => pbR_of_fderiv_eq _ _ _ u hre
  have hC : pbC (fun v => φ (s v)) G u = pbC (fun v => a * s v) G u := by
    unfold pbC
    simp only [hkre, hkim, hkmr, hkrm]
  rw [hC]
  have hs1 : DifferentiableAt ℝ (fun v => (s v).re) u :=
    (Complex.reCLM.hasFDerivAt.comp u hs).differentiableAt
  have hs2 : DifferentiableAt ℝ (fun v => (s v).im) u :=
    (Complex.imCLM.hasFDerivAt.comp u hs).differentiableAt
  exact pbC_const_mul a s G u hs1 hs2

end QuantumNLS.RootHolomorphicBracket

#print axioms QuantumNLS.RootHolomorphicBracket.pbC_chain
#print axioms QuantumNLS.RootHolomorphicBracket.pbC_const_mul
