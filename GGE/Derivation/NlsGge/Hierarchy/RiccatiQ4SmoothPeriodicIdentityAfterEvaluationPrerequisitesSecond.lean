import NlsGge.Hierarchy.RiccatiQ4RecurrenceExpansionAfterNatCastPrerequisite
import NlsGge.Hierarchy.RiccatiSpatialDerivationNatCastCoefficientPrerequisite
import NlsGge.Hierarchy.RiccatiQ4PolynomialEvaluationSubtractionPrerequisiteSecond
import NlsGge.Hierarchy.RiccatiSmoothJetDerivativeAfterProductPrerequisite
import NlsGge.Hierarchy.RiccatiPeriodicIteratedDerivClosurePrerequisite
import NlsGge.Hierarchy.PeriodicIntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open scoped ComplexConjugate Interval

def q4EnergyPolynomialAfterEvaluationPrerequisites : Poly :=
  MvPolynomial.X (false, 2) * MvPolynomial.X (true, 2) +
    (MvPolynomial.X (false, 1) * MvPolynomial.X (false, 1)) *
      (MvPolynomial.X (true, 0) * MvPolynomial.X (true, 0)) +
    (MvPolynomial.X (false, 0) * MvPolynomial.X (false, 0)) *
      (MvPolynomial.X (true, 1) * MvPolynomial.X (true, 1)) +
    8 * MvPolynomial.X (false, 0) * MvPolynomial.X (true, 0) *
      MvPolynomial.X (false, 1) * MvPolynomial.X (true, 1) +
    2 * MvPolynomial.X (false, 0) * MvPolynomial.X (false, 0) *
      MvPolynomial.X (false, 0) *
        (MvPolynomial.X (true, 0) * MvPolynomial.X (true, 0) *
          MvPolynomial.X (true, 0))

theorem q4_source_minus_energy_eq_spatialD_flux_after_evaluation_prerequisites :
    formalChargeIntegrand 2 - q4EnergyPolynomialAfterEvaluationPrerequisites =
      spatialD NlsGge.HierarchyRiccati.q4BoundaryFluxPolynomialValueBridge := by
  have h6 : spatialD (6 : Poly) = 0 := by
    change spatialD (6 : ℕ) = 0
    exact spatialD_natCast_eq_zero 6
  rw [formalQ4Density_formula_after_natCast_prerequisite]
  simp [q4EnergyPolynomialAfterEvaluationPrerequisites,
    NlsGge.HierarchyRiccati.q4BoundaryFluxPolynomialValueBridge, h6,
    spatialD.map_add, spatialD.map_sub, spatialD.map_neg,
    spatialD.map_smul, spatialD.leibniz, spatialD_jet]
  ring

end NlsGge.HierarchyRiccati.Core

namespace NlsGge.HierarchyRiccati

open NlsGge.HierarchyRiccati.Core
open MeasureTheory
open scoped ComplexConjugate ContDiff Interval

def q4SourceDensityAfterEvaluationPrerequisites (u : ℝ → ℂ) (x : ℝ) : ℂ :=
  riccatiJetEvaluation u x (formalChargeIntegrand 2)

def q4EnergyDensityAfterEvaluationPrerequisites (u : ℝ → ℂ) (x : ℝ) : ℂ :=
  iteratedDeriv 2 u x * iteratedDeriv 2 (fun y => star (u y)) x +
    (iteratedDeriv 1 u x) ^ 2 * (star (u x)) ^ 2 +
    (u x) ^ 2 * (iteratedDeriv 1 (fun y => star (u y)) x) ^ 2 +
    8 * u x * star (u x) * iteratedDeriv 1 u x *
      iteratedDeriv 1 (fun y => star (u y)) x +
    2 * (u x) ^ 3 * (star (u x)) ^ 3

def q4EnergyPolynomialDensityAfterEvaluationPrerequisites
    (u : ℝ → ℂ) (x : ℝ) : ℂ :=
  riccatiJetEvaluation u x q4EnergyPolynomialAfterEvaluationPrerequisites

def q4BoundaryFluxAfterEvaluationPrerequisites (u : ℝ → ℂ) : ℝ → ℂ :=
  q4BoundaryFluxAfterPolynomialEvaluationBridge u

theorem q4EnergyPolynomialDensity_eq_explicit_after_evaluation_prerequisites
    (u : ℝ → ℂ) (x : ℝ) :
    q4EnergyPolynomialDensityAfterEvaluationPrerequisites u x =
      q4EnergyDensityAfterEvaluationPrerequisites u x := by
  simp [q4EnergyPolynomialDensityAfterEvaluationPrerequisites,
    q4EnergyDensityAfterEvaluationPrerequisites,
    q4EnergyPolynomialAfterEvaluationPrerequisites,
    riccatiJetEvaluation, polynomialEvaluation, riccatiJetFunction]
  ring

private theorem iteratedDeriv_contDiff_after_evaluation_prerequisites
    (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n u) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv n hu

private theorem iteratedDeriv_star_contDiff_after_evaluation_prerequisites
    (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n (fun x => star (u x))) := by
  have hstar : ContDiff ℝ ∞ (fun x => star (u x)) :=
    ((starL ℝ : ℂ ≃L⋆[ℝ] ℂ).toContinuousLinearMap).contDiff.comp hu
  exact iteratedDeriv_contDiff_after_evaluation_prerequisites
    (fun x => star (u x)) hstar n

private theorem q4BoundaryFlux_hasDerivAt_after_evaluation_prerequisites
    (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (x : ℝ) :
    HasDerivAt (q4BoundaryFluxAfterEvaluationPrerequisites u)
      (q4SourceDensityAfterEvaluationPrerequisites u x -
        q4EnergyPolynomialDensityAfterEvaluationPrerequisites u x) x := by
  have h := riccatiJetEvaluation_hasDerivAt u hu
    q4BoundaryFluxPolynomialValueBridge x
  have hvalue :
      riccatiJetEvaluation u x
          (spatialD q4BoundaryFluxPolynomialValueBridge) =
        q4SourceDensityAfterEvaluationPrerequisites u x -
          q4EnergyPolynomialDensityAfterEvaluationPrerequisites u x := by
    calc
      _ = riccatiJetEvaluation u x
          (formalChargeIntegrand 2 - q4EnergyPolynomialAfterEvaluationPrerequisites) := by
        rw [← q4_source_minus_energy_eq_spatialD_flux_after_evaluation_prerequisites]
      _ = _ := riccatiJetEvaluation_sub_prerequisite u x
        (formalChargeIntegrand 2) q4EnergyPolynomialAfterEvaluationPrerequisites
  rw [hvalue] at h
  change HasDerivAt (q4BoundaryFluxAfterPolynomialEvaluationBridge u)
    (q4SourceDensityAfterEvaluationPrerequisites u x -
      q4EnergyPolynomialDensityAfterEvaluationPrerequisites u x) x
  rw [q4BoundaryFluxAfterPolynomialEvaluationBridge_eq_jetEvaluation u]
  exact h

/-- The actual smooth-periodic Q₄ source integral identity, derived from the
recurrence density and the checked smooth-periodic derivative closure. -/
theorem q4_smooth_periodic_source_integral_identity_after_evaluation_prerequisites
    (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) :
    (∫ x in (0 : ℝ)..1, q4SourceDensityAfterEvaluationPrerequisites u x) =
      ∫ x in (0 : ℝ)..1, q4EnergyDensityAfterEvaluationPrerequisites u x := by
  have hstar : ContDiff ℝ ∞ (fun x => star (u x)) :=
    ((starL ℝ : ℂ ≃L⋆[ℝ] ℂ).toContinuousLinearMap).contDiff.comp hu
  have hstarPer : Function.Periodic (fun x => star (u x)) 1 := by
    intro x
    change star (u (x + 1)) = star (u x)
    exact congrArg star (hper x)
  have hperAll : ∀ n : ℕ, Function.Periodic (iteratedDeriv n u) 1 :=
    fun n => periodic_iteratedDeriv_of_contDiff u hu hper n
  have hstarPerAll : ∀ n : ℕ,
      Function.Periodic (iteratedDeriv n (fun x => star (u x))) 1 :=
    fun n => periodic_iteratedDeriv_of_contDiff
      (fun x => star (u x)) hstar hstarPer n
  have hsourceCont : Continuous (q4SourceDensityAfterEvaluationPrerequisites u) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (riccatiJetEvaluation_hasDerivAt u hu (formalChargeIntegrand 2) x).continuousAt
  have henergyCont : Continuous
      (q4EnergyPolynomialDensityAfterEvaluationPrerequisites u) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (riccatiJetEvaluation_hasDerivAt u hu
      q4EnergyPolynomialAfterEvaluationPrerequisites x).continuousAt
  have hdiffCont : Continuous (fun x =>
      q4SourceDensityAfterEvaluationPrerequisites u x -
        q4EnergyPolynomialDensityAfterEvaluationPrerequisites u x) :=
    hsourceCont.sub henergyCont
  have hfluxDerivInt : IntervalIntegrable
      (fun x => q4SourceDensityAfterEvaluationPrerequisites u x -
        q4EnergyPolynomialDensityAfterEvaluationPrerequisites u x)
      MeasureTheory.volume 0 1 := hdiffCont.continuousOn.intervalIntegrable
  have hfluxPer : Function.Periodic (q4BoundaryFluxAfterEvaluationPrerequisites u) 1 := by
    intro x
    change q4BoundaryFluxAfterPolynomialEvaluationBridge u (x + 1) =
      q4BoundaryFluxAfterPolynomialEvaluationBridge u x
    rw [q4BoundaryFluxAfterPolynomialEvaluationBridge_eq_jetEvaluation u]
    change riccatiJetEvaluation u (x + 1) q4BoundaryFluxPolynomialValueBridge =
      riccatiJetEvaluation u x q4BoundaryFluxPolynomialValueBridge
    unfold riccatiJetEvaluation
    apply congrArg (fun values : Jet → ℂ =>
      polynomialEvaluation values q4BoundaryFluxPolynomialValueBridge)
    funext v
    rcases v with ⟨b, n⟩
    cases b
    · exact hperAll n x
    · exact hstarPerAll n x
  have honePer : Function.Periodic (fun _ : ℝ => (1 : ℂ)) 1 := by
    intro x
    rfl
  have honeDeriv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun _ : ℝ => (1 : ℂ)) (0 : ℂ) x := by
    intro x hx
    exact hasDerivAt_const x (1 : ℂ)
  have hfluxDeriv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (q4BoundaryFluxAfterEvaluationPrerequisites u)
        (q4SourceDensityAfterEvaluationPrerequisites u x -
          q4EnergyPolynomialDensityAfterEvaluationPrerequisites u x) x := by
    intro x hx
    exact q4BoundaryFlux_hasDerivAt_after_evaluation_prerequisites u hu x
  have hzeroInt : IntervalIntegrable (fun _ : ℝ => (0 : ℂ))
      MeasureTheory.volume 0 1 := intervalIntegrable_const
  have hfluxIntegralZero :
      (∫ x in (0 : ℝ)..1,
        q4SourceDensityAfterEvaluationPrerequisites u x -
          q4EnergyPolynomialDensityAfterEvaluationPrerequisites u x) = 0 := by
    have hparts := unitPeriod_integral_mul_deriv_eq_neg_deriv_mul
      honePer hfluxPer honeDeriv hfluxDeriv hzeroInt hfluxDerivInt
    simpa using hparts
  have hsourceInt : IntervalIntegrable
      (q4SourceDensityAfterEvaluationPrerequisites u) MeasureTheory.volume 0 1 :=
    hsourceCont.continuousOn.intervalIntegrable
  have henergyInt : IntervalIntegrable
      (q4EnergyPolynomialDensityAfterEvaluationPrerequisites u)
      MeasureTheory.volume 0 1 := henergyCont.continuousOn.intervalIntegrable
  have hsub := intervalIntegral.integral_sub hsourceInt henergyInt
  rw [hsub] at hfluxIntegralZero
  have hpoly := sub_eq_zero.mp hfluxIntegralZero
  simpa only [q4EnergyPolynomialDensity_eq_explicit_after_evaluation_prerequisites]
    using hpoly

end NlsGge.HierarchyRiccati

end
