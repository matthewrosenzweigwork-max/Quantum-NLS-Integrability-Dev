import Mathlib
import NlsGge.GK38.Defs
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.GK38.XiSqCanonical
import NlsGge.Atomic.X.X006
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G5033Host
import Armstrong.Frozen.RawBeta.GKRootedPiecewisePath38
import Armstrong.Frozen.RawBeta.HasGKImproperPathIntegral38
import Armstrong.Work.ActualCartesianXYModels

/- G4_038 PRODUCTION01 (proof development, AUTHOR; not semantically reviewed by its author).
   Target NlsGge/Atomic/G4/G4038.lean, namespace NlsGge.GKDefinitionDesign.
   Head `G4038` VERBATIM from Pro round 8 (PRO_DEFINITION_RESPONSE_FP80_07_08.md, section 28 "g4-038"); it supersedes
   design STATEMENTS/G4.md:672-681 (identical apart from the namespace qualification NlsGge.GK38. of the two path predicates).
   No lexical repair (the head contains no `lambda`).
   Route = Pro's: instantiate the X-006 same-family record (sourceFamily) in Armstrong's gk16_xy_models_of_original_path38
   (Armstrong.Work.ActualCartesianXYModels, owner-approved designated module, also imported by landed G5033Host), then the
   complex cos/sin exponential identities with sqrt 8 = 2 sqrt 2 (see G4038_ROUTE.md). No analytic anchor, no global additive
   angle, no value assigned at collapse. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
namespace G4038Aux
noncomputable section

theorem sqrt8_eq : ((Real.sqrt 8 : ℝ) : ℂ) = 2 * ((Real.sqrt 2 : ℝ) : ℂ) := by
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    have h : (8 : ℝ) = 2 ^ 2 * 2 := by norm_num
    rw [h, Real.sqrt_mul (show (0 : ℝ) ≤ 2 ^ 2 by norm_num) 2,
      Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
  exact_mod_cast h8

theorem xy_algebra (s xi g E1 E2 : ℂ) :
    xi / (2 * s) * (g * E1 + g * E2) = xi * g / s * ((E1 + E2) / 2) ∧
    xi / (2 * s * Complex.I) * (g * E1 - g * E2) =
      xi * g / s * ((E2 - E1) * Complex.I / 2) := by
  constructor
  · ring
  · simp only [div_eq_mul_inv, mul_inv, Complex.inv_I]
    ring

end
end G4038Aux

noncomputable section

theorem G4038 (n : ℤ)
    (φ : {χ : PotPair // χ ∈ sourceW})
    (hV : φ.1 ∈ sourceBetaW)
    (hgap : lamMinus φ.1 n ≠ lamPlus φ.1 n)
    (p : NlsGge.GK38.GKRootedPiecewisePath38
      ⟨φ.1, sourceFamily.W_gk φ.2⟩ n)
    (η : ℂ)
    (hη : NlsGge.GK38.HasGKImproperPathIntegral38
      n n sourceF ⟨φ.1, sourceFamily.W_gk φ.2⟩ p η) :
    cartesianX n φ.1 =
      xiN38 n φ.1 * (lamPlus φ.1 n - lamMinus φ.1 n) /
        (Real.sqrt 2 : ℂ) *
        Complex.cos (η + betaSum n φ.1) ∧
    cartesianY n φ.1 =
      xiN38 n φ.1 * (lamPlus φ.1 n - lamMinus φ.1 n) /
        (Real.sqrt 2 : ℂ) *
        Complex.sin (η + betaSum n φ.1) := by
  have hbeta := sourceFamily.beta_spec n φ hV
  obtain ⟨hX, hY⟩ := gk16_xy_models_of_original_path38 sourceFamily.W sourceFamily.W_open
    sourceFamily.W_real sourceFamily.W_gk sourceFamily.F sourceFamily.F_analytic
    sourceFamily.F_zero sourceFamily.F_period sourceFamily.beta n φ hbeta hgap p η hη
  rw [← hbeta.2] at hX hY
  have hX' : cartesianX n φ.1 =
      (xiN38 n φ.1 / (Real.sqrt 8 : ℂ)) *
        ((lamPlus φ.1 n - lamMinus φ.1 n) *
            Complex.exp (Complex.I * (η + betaSum n φ.1)) +
          (lamPlus φ.1 n - lamMinus φ.1 n) *
            Complex.exp (-Complex.I * (η + betaSum n φ.1))) := hX
  have hY' : cartesianY n φ.1 =
      (xiN38 n φ.1 / ((Real.sqrt 8 : ℂ) * Complex.I)) *
        ((lamPlus φ.1 n - lamMinus φ.1 n) *
            Complex.exp (Complex.I * (η + betaSum n φ.1)) -
          (lamPlus φ.1 n - lamMinus φ.1 n) *
            Complex.exp (-Complex.I * (η + betaSum n φ.1))) := hY
  have e1 : Complex.exp (Complex.I * (η + betaSum n φ.1)) =
      Complex.exp ((η + betaSum n φ.1) * Complex.I) := by
    rw [mul_comm]
  have e2 : Complex.exp (-Complex.I * (η + betaSum n φ.1)) =
      Complex.exp (-(η + betaSum n φ.1) * Complex.I) := by
    congr 1
    ring
  have hcos : Complex.cos (η + betaSum n φ.1) =
      (Complex.exp ((η + betaSum n φ.1) * Complex.I) +
        Complex.exp (-(η + betaSum n φ.1) * Complex.I)) / 2 := rfl
  have hsin : Complex.sin (η + betaSum n φ.1) =
      (Complex.exp (-(η + betaSum n φ.1) * Complex.I) -
        Complex.exp ((η + betaSum n φ.1) * Complex.I)) * Complex.I / 2 := rfl
  refine ⟨?_, ?_⟩
  · rw [hX', G4038Aux.sqrt8_eq, e1, e2, hcos]
    exact (G4038Aux.xy_algebra _ _ _ _ _).1
  · rw [hY', G4038Aux.sqrt8_eq, e1, e2, hsin]
    exact (G4038Aux.xy_algebra _ _ _ _ _).2

end
end NlsGge.GKDefinitionDesign
