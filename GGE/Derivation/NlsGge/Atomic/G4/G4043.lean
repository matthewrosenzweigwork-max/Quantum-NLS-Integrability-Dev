import Mathlib
import NlsGge.GK38.ContourActionDeformation
import NlsGge.GK38.XiSqCanonical
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G5033Host
import Armstrong.Work.ActualCartesianXYModels
import Armstrong.Work.ActualScalarCartesianModels

/- G4-043 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G4/G4043.lean.
   Head `G4043`: design STATEMENTS/G4.md G4-043 section, verbatim (no Pro round 4-12 entry or BINDING_INDEX touches G4-043;
   no lexical repair: the head has no `lambda` binder).
   Route (G4043_ROUTE.md) = packet skeleton, pointwise on all of sourceBetaW (a complex neighbourhood, no continuation needed):
   (1) x^2 + y^2 = xi^2 * Z+ Z- / 2 by the literal models gk16ScalarXModel38/YModel38 (exp(i beta) exp(-i beta) = 1);
   (2) Z+ Z- = gamma2 on all of gkW, collapsed gaps included (Armstrong gk16_actual_scalar_models_product38, as already consumed by
       landed G3024Reduction/G4014/G3006);
   (3) gamma2 * xi^2 = 4 I_n on gkW (xiSq38_multiplied, xiN38_sq). Hence (x^2+y^2)/2 = xi^2 gamma2 / 4 = I_n.
   No analytic anchor, no division by gamma2, no case split, no analytic continuation. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
namespace G4043Aux
noncomputable section

theorem xy_radius_algebra (a P M : ℂ) :
    (a / (Real.sqrt 8 : ℂ) * (P + M)) ^ 2 +
      (a / ((Real.sqrt 8 : ℂ) * Complex.I) * (P - M)) ^ 2 = a ^ 2 * (P * M) / 2 := by
  have hs : ((Real.sqrt 8 : ℝ) : ℂ) ^ 2 = 8 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
    norm_num
  have h1 : (a / (Real.sqrt 8 : ℂ) * (P + M)) ^ 2 =
      a ^ 2 / ((Real.sqrt 8 : ℂ) ^ 2) * (P + M) ^ 2 := by ring
  have h2 : (a / ((Real.sqrt 8 : ℂ) * Complex.I) * (P - M)) ^ 2 =
      a ^ 2 / ((Real.sqrt 8 : ℂ) ^ 2 * Complex.I ^ 2) * (P - M) ^ 2 := by ring
  rw [h1, h2, hs, Complex.I_sq]
  ring

end
end G4043Aux

noncomputable section

theorem G4043 (n : ℤ) (φ : PotPair) (hφ : φ ∈ sourceBetaW) :
  gkActionC38 φ n = (cartesianX n φ ^ 2 + cartesianY n φ ^ 2) / 2 := by
  have hgk : φ ∈ gkW := sourceFamily.W_gk (sourceFamily.V_W hφ)
  have hprod := gk16_actual_scalar_models_product38 sourceF n φ hgk
  have hmul := xiSq38_multiplied n φ hgk
  have hxi := xiN38_sq n φ
  have hE : Complex.exp (Complex.I * betaSum n φ) * Complex.exp (-Complex.I * betaSum n φ) = 1 := by
    rw [← Complex.exp_add]
    have : Complex.I * betaSum n φ + -Complex.I * betaSum n φ = 0 := by ring
    rw [this, Complex.exp_zero]
  have key := G4043Aux.xy_radius_algebra (xiN38 n φ)
    (gk16ActualScalarZPlus38 sourceF n φ * Complex.exp (Complex.I * betaSum n φ))
    (gk16ActualScalarZMinus38 sourceF n φ * Complex.exp (-Complex.I * betaSum n φ))
  have hPM : gk16ActualScalarZPlus38 sourceF n φ * Complex.exp (Complex.I * betaSum n φ) *
      (gk16ActualScalarZMinus38 sourceF n φ * Complex.exp (-Complex.I * betaSum n φ)) =
        gamma2 φ n := by
    rw [mul_mul_mul_comm, hE, mul_one]
    exact hprod
  rw [hPM, hxi] at key
  have hX : cartesianX n φ = xiN38 n φ / (Real.sqrt 8 : ℂ) *
      (gk16ActualScalarZPlus38 sourceF n φ * Complex.exp (Complex.I * betaSum n φ) +
        gk16ActualScalarZMinus38 sourceF n φ * Complex.exp (-Complex.I * betaSum n φ)) := rfl
  have hY : cartesianY n φ = xiN38 n φ / ((Real.sqrt 8 : ℂ) * Complex.I) *
      (gk16ActualScalarZPlus38 sourceF n φ * Complex.exp (Complex.I * betaSum n φ) -
        gk16ActualScalarZMinus38 sourceF n φ * Complex.exp (-Complex.I * betaSum n φ)) := rfl
  rw [hX, hY, key]
  linear_combination (-(1 : ℂ) / 4) * hmul

end
end NlsGge.GKDefinitionDesign
