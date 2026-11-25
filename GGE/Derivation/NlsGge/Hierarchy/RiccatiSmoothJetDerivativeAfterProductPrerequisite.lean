import NlsGge.Hierarchy.RiccatiPolynomialEvaluationAPI
import NlsGge.Hierarchy.RiccatiComplexHasDerivAtProductCoreThird
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Tactic

set_option autoImplicit false

/-! Smooth realization of independent formal jets and the derivative/evaluation
identity. This is only a smooth-function lemma; periodic integration,
Sobolev representatives and spectral-charge identification remain separate. -/

namespace NlsGge.HierarchyRiccati.Core

open scoped ComplexConjugate ContDiff

noncomputable section

def riccatiJetFunction (u : ℝ → ℂ) (v : Jet) : ℝ → ℂ :=
  iteratedDeriv v.2 (if v.1 then (fun x => star (u x)) else u)

def riccatiJetEvaluation (u : ℝ → ℂ) (x : ℝ) (P : Poly) : ℂ :=
  polynomialEvaluation (fun v => riccatiJetFunction u v x) P

@[simp] theorem riccatiJetEvaluation_X (u : ℝ → ℂ) (x : ℝ) (v : Jet) :
    riccatiJetEvaluation u x (MvPolynomial.X v) = riccatiJetFunction u v x := by
  simp [riccatiJetEvaluation]

@[simp] theorem riccatiJetEvaluation_C (u : ℝ → ℂ) (x : ℝ) (a : ℤ) :
    riccatiJetEvaluation u x (MvPolynomial.C a) = (a : ℂ) := by
  simp [riccatiJetEvaluation]

private theorem contDiff_star_real (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (fun x => star (u x)) := by
  have hstar : ContDiff ℝ ∞ (fun z : ℂ => star z) :=
    ((starL ℝ : ℂ ≃L⋆[ℝ] ℂ).toContinuousLinearMap).contDiff
  exact hstar.comp hu

private theorem riccatiJetFunction_contDiff (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (v : Jet) : ContDiff ℝ ∞ (riccatiJetFunction u v) := by
  unfold riccatiJetFunction
  split
  · rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv v.2 (contDiff_star_real u hu)
  · rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv v.2 hu

private theorem riccatiJetFunction_hasDerivAt (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (v : Jet) (x : ℝ) :
    HasDerivAt (riccatiJetFunction u v)
      (riccatiJetFunction u (v.1, v.2 + 1) x) x := by
  have hcont := riccatiJetFunction_contDiff u hu v
  have hdiff : DifferentiableAt ℝ (riccatiJetFunction u v) x :=
    (hcont.differentiable (by simp)).differentiableAt
  have h := hdiff.hasDerivAt
  change HasDerivAt (riccatiJetFunction u v) (deriv (riccatiJetFunction u v) x) x at h
  have hderiv : deriv (riccatiJetFunction u v) x =
      riccatiJetFunction u (v.1, v.2 + 1) x := by
    cases v with
    | mk barred order =>
        simp [riccatiJetFunction, iteratedDeriv_succ]
  rw [hderiv] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem riccatiJetEvaluation_hasDerivAt (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (P : Poly) (x : ℝ) :
    HasDerivAt (fun y => riccatiJetEvaluation u y P)
      (riccatiJetEvaluation u x (spatialD P)) x := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
      simpa [riccatiJetEvaluation, spatialD_C] using
        (hasDerivAt_const x (a : ℂ))
  | add P Q hP hQ =>
      convert hP.add hQ using 1
      · funext y
        simp [riccatiJetEvaluation]
      · simp [riccatiJetEvaluation, spatialD.map_add]
  | mul_X P v hP =>
      have hX := riccatiJetFunction_hasDerivAt u hu v x
      have hXeval :
          HasDerivAt (fun y => riccatiJetEvaluation u y (MvPolynomial.X v))
            (riccatiJetEvaluation u x (spatialD (MvPolynomial.X v))) x := by
        simpa [riccatiJetEvaluation, spatialD_jet] using hX
      have h : HasDerivAt
          (fun y => riccatiJetEvaluation u y P *
            riccatiJetEvaluation u y (MvPolynomial.X v))
          (riccatiJetEvaluation u x (spatialD P) *
            riccatiJetEvaluation u x (MvPolynomial.X v) +
            riccatiJetEvaluation u x P *
              riccatiJetEvaluation u x (spatialD (MvPolynomial.X v))) x :=
        NlsGge.HierarchyRiccati.hasDerivAt_mul_complex_core hP hXeval
      have hraw := congrArg (riccatiJetEvaluation u x)
        (spatialD.leibniz P (MvPolynomial.X v))
      have hvalue :
          riccatiJetEvaluation u x (spatialD (P * MvPolynomial.X v)) =
            riccatiJetEvaluation u x (spatialD P) *
                riccatiJetEvaluation u x (MvPolynomial.X v) +
              riccatiJetEvaluation u x P *
                riccatiJetEvaluation u x (spatialD (MvPolynomial.X v)) := by
        calc
          _ = riccatiJetEvaluation u x P *
                riccatiJetEvaluation u x (spatialD (MvPolynomial.X v)) +
                riccatiJetEvaluation u x (MvPolynomial.X v) *
                riccatiJetEvaluation u x (spatialD P) := by
              simpa [riccatiJetEvaluation, polynomialEvaluation_add,
                polynomialEvaluation_mul, smul_eq_mul] using hraw
          _ = _ := by ring
      rw [hvalue]
      simpa [riccatiJetEvaluation, polynomialEvaluation_mul] using h

end

/- Differentiating any evaluated formal jet polynomial equals evaluating its
formal spatial derivation, for every smooth complex field. -/

end NlsGge.HierarchyRiccati.Core
