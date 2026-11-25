import NlsGge.Hierarchy.RiccatiLowOrderAlgebraAfterCore
import NlsGge.Hierarchy.RiccatiPolynomialEvaluationAPI
import NlsGge.Hierarchy.PeriodicIntegrationByParts
import Mathlib.Tactic

set_option autoImplicit false

/-! A concrete E06.04 realization step for the first nontrivial charge.
The formal Q₂ density from the actual p₃ recursion is evaluated on a supplied
jet, then its second-derivative term is integrated by parts on the unit period.
This is only the Q₂ identity; it makes no higher-charge or Sobolev claim. -/

namespace NlsGge.HierarchyRiccati

open MeasureTheory
open NlsGge.HierarchyRiccati.Core
open scoped ComplexConjugate

noncomputable section

/-- Jet values needed by the formal Q₂ density: u, its conjugate, and the
second derivative of the conjugate. -/
def q2JetValues (u d2ubar : ℝ → ℂ) (x : ℝ) : Jet → ℂ := fun v =>
  if v = (false, 0) then u x
  else if v = (true, 0) then star (u x)
  else if v = (true, 2) then d2ubar x
  else 0

/-- Evaluation of the source formal Q₂ density at one point. -/
def q2FormalDensityAt (u d2ubar : ℝ → ℂ) (x : ℝ) : ℂ :=
  polynomialEvaluation (q2JetValues u d2ubar x) (formalChargeIntegrand 1)

/-- The source expression `-u bar(u)'' + (bar u u)^2`, written as a function
of the supplied physical jets. -/
def q2PhysicalDensity (u d2ubar : ℝ → ℂ) (x : ℝ) : ℂ :=
  -(u x * d2ubar x) + (star (u x) * u x) ^ 2

/-- The integration-by-parts representative of the same density. -/
def q2PhysicalEnergyDensity (u du : ℝ → ℂ) (x : ℝ) : ℂ :=
  du x * star (du x) + (star (u x) * u x) ^ 2

theorem q2FormalDensityAt_eq_physical (u d2ubar : ℝ → ℂ) (x : ℝ) :
    q2FormalDensityAt u d2ubar x = q2PhysicalDensity u d2ubar x := by
  rw [q2FormalDensityAt, formalQ2Density_formula]
  simp [polynomialEvaluation, q2JetValues, q2PhysicalDensity]
  ring

/-- Unit-period integration by parts turns the evaluated Q₂ density into its
first-derivative energy density. Derivative and integrability data are explicit
so this lemma does not hide regularity or boundary hypotheses. -/
theorem unitPeriod_q2_integral_identity
    {u du d2ubar : ℝ → ℂ}
    (huPer : Function.Periodic u 1)
    (hstarDuPer : Function.Periodic (fun x => star (du x)) 1)
    (hu : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt u (du x) x)
    (hstarDu : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun y => star (du y)) (d2ubar x) x)
    (hduInt : IntervalIntegrable du MeasureTheory.volume 0 1)
    (hd2ubarInt : IntervalIntegrable d2ubar MeasureTheory.volume 0 1)
    (hleftQuad : IntervalIntegrable (fun x => -(u x * d2ubar x))
      MeasureTheory.volume 0 1)
    (hleftQuartic : IntervalIntegrable (fun x => (star (u x) * u x) ^ 2)
      MeasureTheory.volume 0 1)
    (hrightQuad : IntervalIntegrable (fun x => du x * star (du x))
      MeasureTheory.volume 0 1)
    (hrightQuartic : IntervalIntegrable (fun x => (star (u x) * u x) ^ 2)
      MeasureTheory.volume 0 1) :
    (∫ x in (0 : ℝ)..1, q2PhysicalDensity u d2ubar x) =
      ∫ x in (0 : ℝ)..1, q2PhysicalEnergyDensity u du x := by
  have hfirst :
      (∫ x in (0 : ℝ)..1, -(u x * d2ubar x)) =
        ∫ x in (0 : ℝ)..1, du x * star (du x) := by
    have hibp := unitPeriod_integral_mul_deriv_eq_neg_deriv_mul
      huPer hstarDuPer hu hstarDu hduInt hd2ubarInt
    calc
      _ = -(∫ x in (0 : ℝ)..1, u x * d2ubar x) := by
        rw [intervalIntegral.integral_neg]
      _ = _ := by rw [hibp]; simp
  calc
    _ = (∫ x in (0 : ℝ)..1, -(u x * d2ubar x)) +
          ∫ x in (0 : ℝ)..1, (star (u x) * u x) ^ 2 := by
      unfold q2PhysicalDensity
      rw [intervalIntegral.integral_add hleftQuad hleftQuartic]
    _ = (∫ x in (0 : ℝ)..1, du x * star (du x)) +
          ∫ x in (0 : ℝ)..1, (star (u x) * u x) ^ 2 := by rw [hfirst]
    _ = _ := by
      unfold q2PhysicalEnergyDensity
      rw [intervalIntegral.integral_add hrightQuad hrightQuartic]

end

end NlsGge.HierarchyRiccati
