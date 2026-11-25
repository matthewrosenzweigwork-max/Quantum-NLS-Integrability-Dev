import Mathlib
import NlsGge.Atomic.M.M004
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.Sobolev.SourceReflection
import NlsGge.Hierarchy.RiccatiSobolevIteratedDerivativeL2CLMRecovery30First
import NlsGge.Hierarchy.RiccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth
import NlsGge.Hierarchy.RiccatiMonomialSobolevCMM38
import NlsGge.Hierarchy.RiccatiFormalChargeRemainderUniformNormalizationRecovery29Fourth
import NlsGge.Hierarchy.RiccatiQuadraticLeadingIBP38

/- M-005 production kit (proof development, AUTHOR; not reviewed; target NlsGge/Atomic/M/M005.lean). Definitions verbatim from PRO_DEFINITION_RESPONSE_FP80_02_03.md (M-005); accepted M-004 aliases/theorems are imported (NlsGge.Atomic.M.M004); `SobolevR` is hosted here (M004 does not declare it). Proof: normalized remainder support via riccati_normalized_remainder_monomial_grading; smooth identity from formalChargeIntegrand_integral_quadratic_plus_uniformRemainderNativeRecovery29Fourth + formalChargeQuadraticMainTerm_integral_eq38. -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.M
abbrev SobolevR (m : ℕ) :=
  NlsGge.Atomic.Common.PhysicalSobolev38 (m : ℝ)
end NlsGge.ThirdConsultation.M

open MeasureTheory
open scoped ContDiff

namespace NlsGge.ThirdConsultation.M
noncomputable section

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.HierarchyRiccati.Core
open NlsGge.Atomic.Common

def ordinarySobolevCoordinates (m : ℕ) (u : SobolevR m) :
    SobolevHilbert (m : ℝ) :=
  let x := physicalSobolevFourierEquiv38 (m : ℝ) u
  let a := carrierCoe38 (m : ℝ) x
  ofCarrier38 (m : ℝ)
    (carrierMk38 (m : ℝ) (fun n : ℤ => -a (-n))
      ((mem_seqSobolev38_iff (m : ℝ) _).2
        (sobolevSquareSummable_reflection (m : ℝ) a
          ((mem_seqSobolev38_iff (m : ℝ) a).1
            (carrierCoe38_mem (m : ℝ) x)))))

def physicalOfSobolev {m : ℕ} (u : SobolevR m) : PhysicalL2 :=
  riccatiSobolevIteratedDerivativeL2CLMRecovery30First m 0
    (Nat.zero_le m) (ordinarySobolevCoordinates m u)

def lowerSobolevCast (i m : ℕ) (him : i ≤ m)
    (u : SobolevR m) : SobolevR i :=
  (physicalSobolevFourierEquiv38 (i : ℝ)).symm
    (carrierIncl38 (Nat.cast_le.mpr him : (i : ℝ) ≤ (m : ℝ))
      (physicalSobolevFourierEquiv38 (m : ℝ) u))

def sobolevJetContinuous (m : ℕ) (v : Jet)
    (u : SobolevR m) : C(PhysicalCircle, ℂ) :=
  if h : v.2 + 1 ≤ m then
    riccatiSobolevJetContinuousRepresentativeRecovery30Eighth m v h
      (ordinarySobolevCoordinates m u)
  else 0

def integralMonomial {m : ℕ} (q : Jet →₀ ℕ)
    (u : SobolevR m) : ℂ :=
  ∫ x : PhysicalCircle,
    (∏ v ∈ q.support, (sobolevJetContinuous m v u x) ^ q v)
    ∂spatialMeasure

def derivativeSupNorm {m : ℕ} (i : ℕ) (him : i + 1 ≤ m)
    (u : SobolevR m) : ℝ :=
  ‖riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth
    m i him (ordinarySobolevCoordinates m u)‖

def topDerivativeNorm (m : ℕ) (u : SobolevR m) : ℝ :=
  ‖riccatiSobolevIteratedDerivativeL2CLMRecovery30First m m le_rfl
    (ordinarySobolevCoordinates m u)‖

def topDerivativeEnergy (m : ℕ) (u : SobolevR m) : ℝ :=
  topDerivativeNorm m u ^ 2

def normalizedRemainderIntegral (m : ℕ) (u : SobolevR m) : ℝ :=
  (normalizedChargeRemainder m).support.sum fun q =>
    (((normalizedChargeRemainder m).coeff q : ℤ) : ℝ) *
      (integralMonomial q u).re

def signedCharge (m : ℕ) (u : SobolevR m) : ℝ :=
  topDerivativeEnergy m u + normalizedRemainderIntegral m u

def chargeRemainder (m : ℕ) (u : SobolevR m) : ℝ :=
  signedCharge m u - topDerivativeEnergy m u

def smoothSignedCharge (m : ℕ) (u : ℝ → ℂ) : ℝ :=
  (∫ x in (0 : ℝ)..1,
    riccatiJetEvaluation u x (formalChargeIntegrand m)).re

def smoothTopDerivativeEnergy (m : ℕ) (u : ℝ → ℂ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ‖iteratedDeriv m u x‖ ^ 2

def smoothIntegralMonomial (q : Jet →₀ ℕ) (u : ℝ → ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..1,
    riccatiJetEvaluation u x (MvPolynomial.monomial q (1 : ℤ))

def ChargeMonomialBounds (m : ℕ) (q : Jet →₀ ℕ) : Prop :=
  4 ≤ fieldCount q ∧
  gaugeCharge q = 0 ∧
  riccatiJetDerivativeOrderSumNativeRecovery q =
    2 * m + 2 - fieldCount q ∧
  ∀ v ∈ q.support, v.2 ≤ m - 1

def ChargeNormalForm (m : ℕ)
    (terms : Finset ((Jet →₀ ℕ) × ℤ)) : Prop :=
  (∀ t ∈ terms, ChargeMonomialBounds m t.1) ∧
  ∀ (u : ℝ → ℂ), ContDiff ℝ ∞ u → Function.Periodic u 1 →
    smoothSignedCharge m u =
      smoothTopDerivativeEnergy m u +
        terms.sum (fun t => (t.2 : ℝ) * (smoothIntegralMonomial t.1 u).re)

end
end NlsGge.ThirdConsultation.M

namespace NlsGge.ThirdConsultation.M
open NlsGge.HierarchyRiccati.Core

theorem hierarchy_IBP_normal_form (m : ℕ) (hm : 1 ≤ m) :
  ∃ terms : Finset ((Jet →₀ ℕ) × ℤ), ChargeNormalForm m terms := by
  classical
  refine ⟨(normalizedChargeRemainder m).support.image
    (fun q => (q, (normalizedChargeRemainder m).coeff q)), ?_, ?_⟩
  · intro t ht
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨-, hg, -, h4, hord, -, hv⟩ := riccati_normalized_remainder_monomial_grading m hm q hq
    exact ⟨h4, hg, hord, hv⟩
  · intro u hu hper
    have h1 : (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (formalChargeIntegrand m)) =
        (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (formalChargeQuadraticMainTerm m)) +
        (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (normalizedChargeRemainder m)) :=
      formalChargeIntegrand_integral_quadratic_plus_uniformRemainderNativeRecovery29Fourth
        m u hu hper
    have h2 := formalChargeQuadraticMainTerm_integral_eq38 m u hu hper
    have h3 : (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (normalizedChargeRemainder m)) =
        ∑ q ∈ (normalizedChargeRemainder m).support,
          (((normalizedChargeRemainder m).coeff q : ℤ) : ℂ) *
            ∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (MvPolynomial.monomial q (1 : ℤ)) := by
      conv_lhs => rw [(normalizedChargeRemainder m).as_sum]
      rw [riccatiJetEvaluation_integral_finset_sumNativeRecoverySecond u hu]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      have : ∀ x : ℝ, riccatiJetEvaluation u x
          (MvPolynomial.monomial q ((normalizedChargeRemainder m).coeff q)) =
          (((normalizedChargeRemainder m).coeff q : ℤ) : ℂ) *
            riccatiJetEvaluation u x (MvPolynomial.monomial q (1 : ℤ)) := by
        intro x
        have hmon : MvPolynomial.monomial q ((normalizedChargeRemainder m).coeff q) =
            MvPolynomial.C ((normalizedChargeRemainder m).coeff q) *
              MvPolynomial.monomial q (1 : ℤ) := by
          rw [MvPolynomial.C_mul_monomial, mul_one]
        rw [hmon]
        simp [riccatiJetEvaluation, polynomialEvaluation, map_mul]
      simp_rw [this]
      exact intervalIntegral.integral_const_mul _ _
    unfold smoothSignedCharge smoothTopDerivativeEnergy smoothIntegralMonomial
    rw [h1, h2, h3, intervalIntegral.integral_ofReal, Finset.sum_image (by
      intro a _ b _ hab; exact (Prod.mk.inj hab).1)]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl (fun q _ => ?_)
    simp [Complex.mul_re]

end NlsGge.ThirdConsultation.M
