import Mathlib
import NlsGge.GK38.PairPotential
import NlsGge.GK38.NeumannGauge
import NlsGge.ThirdConsultation.KSPSInversePhaseHost
import NlsGge.ThirdConsultation.M.M053Host
import NlsGge.ThirdConsultation.KSPSCoefficientHost

/- M-053 k = 1 support (proof development, AUTHOR; not reviewed).
   Target NlsGge/ThirdConsultation/M/M053K1Support.lean.  Proves the complex bilinear identity and the
   real-pair physical mass identity at k = 1 only; k >= 2 is the open formal-polynomial/Riccati bridge. -/
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.M
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign

theorem riccatiLeft_one {N : ℕ} (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N) :
    NlsGge.ThirdConsultation.KSPS.riccatiLeft φ 1 =
      -(NlsGge.ThirdConsultation.KSPS.toPotPair φ).2 := by
  simp [NlsGge.ThirdConsultation.KSPS.riccatiLeft, NlsGge.ThirdConsultation.KSPSRiccati.left,
    NlsGge.ThirdConsultation.KSPSRiccati.coefficient, wkbR, wkbList]

theorem integralRiccatiCoefficient_one {N : ℕ}
    (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N) :
    NlsGge.ThirdConsultation.KSPS.integralRiccatiCoefficient φ 1 =
      -∫ x in (0 : ℝ)..1,
        coverRep38 (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1 x *
        coverRep38 (NlsGge.ThirdConsultation.KSPS.toPotPair φ).2 x := by
  unfold NlsGge.ThirdConsultation.KSPS.integralRiccatiCoefficient
    NlsGge.ThirdConsultation.KSPS.integralRiccatiLeft
  rw [riccatiLeft_one, ← intervalIntegral.integral_neg]
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [coverRep38_ae_phys (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1,
    coverRep38_ae_phys (-(NlsGge.ThirdConsultation.KSPS.toPotPair φ).2),
    coverRep38_neg_ae (NlsGge.ThirdConsultation.KSPS.toPotPair φ).2] with x h1 h2 h3
  have e : (-(NlsGge.ThirdConsultation.KSPS.toPotPair φ).2) (x : PhysicalCircle) =
      -(coverRep38 (NlsGge.ThirdConsultation.KSPS.toPotPair φ).2 x) := by
    rw [← h2, h3]
  rw [e, ← h1]
  ring

theorem WKB_hierarchy_coefficients_complex_one
    (N : ℕ)
    (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (hk : 1 ≤ 1) (hkN : 1 ≤ N + 1) :
    NlsGge.ThirdConsultation.KSPS.integralRiccatiCoefficient φ 1 =
      -NlsGge.ThirdConsultation.MRiccati.sourceHierarchyCharge N φ ⟨1, hk, hkN⟩ := by
  rw [integralRiccatiCoefficient_one]
  simp [NlsGge.ThirdConsultation.MRiccati.sourceHierarchyCharge]

theorem bilinear_mass_of_realPair {N : ℕ}
    (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (hφ : NlsGge.ThirdConsultation.MRiccati.RealPair φ) :
    (∫ x in (0 : ℝ)..1,
        coverRep38 (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1 x *
        coverRep38 (NlsGge.ThirdConsultation.KSPS.toPotPair φ).2 x) =
      ((massCharge (NlsGge.ThirdConsultation.MRiccati.realPhysicalFromPair φ) : ℝ) : ℂ) := by
  have h2 : (NlsGge.ThirdConsultation.KSPS.toPotPair φ).2 =
      star (NlsGge.ThirdConsultation.MRiccati.realPhysicalFromPair φ) := by
    have := congrArg Prod.snd hφ
    simpa using this
  have h1 : (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1 =
      NlsGge.ThirdConsultation.MRiccati.realPhysicalFromPair φ := rfl
  rw [h2, h1]
  set u := NlsGge.ThirdConsultation.MRiccati.realPhysicalFromPair φ
  have key : (∫ x in (0 : ℝ)..1, coverRep38 u x * coverRep38 (star u) x) =
      ∫ x in (0 : ℝ)..1, (((‖coverRep38 u x‖ ^ 2 : ℝ)) : ℂ) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [coverRep38_star_ae u] with x hx
    rw [hx]
    change coverRep38 u x * (starRingEnd ℂ) (coverRep38 u x) = _
    rw [Complex.mul_conj']
    push_cast
    ring
  rw [key, intervalIntegral.integral_ofReal, integral_sq_coverRep38_one]
  rfl

theorem WKB_hierarchy_coefficients_one
    (N : ℕ)
    (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (hφ : NlsGge.ThirdConsultation.MRiccati.RealPair φ)
    (hk : 1 ≤ 1) (hkN : 1 ≤ N + 1) :
    NlsGge.ThirdConsultation.KSPS.integralRiccatiCoefficient φ 1 =
      if (1 : ℕ) = 1 then
        -(massCharge
          (NlsGge.ThirdConsultation.MRiccati.realPhysicalFromPair φ) : ℂ)
      else
        hierarchyCharge φ ⟨1, hk, hkN⟩ := by
  rw [if_pos rfl, integralRiccatiCoefficient_one, bilinear_mass_of_realPair φ hφ]

end
end NlsGge.ThirdConsultation.M
