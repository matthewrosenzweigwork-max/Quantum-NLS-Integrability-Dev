import Mathlib
import NlsGge.Atomic.M.M005
import NlsGge.ThirdConsultation.Sobolev.Round5
import NlsGge.GK38.PairVolterra
import NlsGge.Hierarchy.RiccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth
import NlsGge.Hierarchy.RiccatiSobolevIteratedDerivativeL2CLMRecovery30First
import NlsGge.Hierarchy.RiccatiPhysicalH1CanonicalAndDerivativeCLMAfterDerivativeClassLinearityPrerequisite
import NlsGge.Hierarchy.RiccatiPhysicalH1CarrierAfterUnweightedCoordinateSecond
import NlsGge.Hierarchy.RiccatiSobolevJetCoefficientL2BoundRecovery28Second
import NlsGge.Analysis.H1Fourier
import NlsGge.Sobolev.PeriodicBridge

                                                                                         
                                                                         
                                                                                                 
                                                                               
                                                                  
                                                                                                                         
                                                                                                     
                                              
-- BEGIN M037BRIDGE BODY
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.M.M037Bridge

open MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.HierarchyRiccati.Core
open NlsGge.Atomic.Common
open NlsGge.Analysis

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-- The squared L² norm of a continuous function's class is its probability-Haar square integral
(copied from the private `toLp_norm_sq_eq_integral38`, RiccatiDerivativeParseval38.lean:22-40). -/
private theorem toLp_norm_sq_eq_integral (f : C(PhysicalCircle, ℂ)) :
    ‖ContinuousMap.toLp 2 spatialMeasure ℂ f‖ ^ 2 =
      ∫ x : PhysicalCircle, ‖f x‖ ^ 2 ∂spatialMeasure := by
  set g := ContinuousMap.toLp 2 spatialMeasure ℂ f with hg
  have h1 : ‖g‖ ^ 2 = RCLike.re (inner ℂ g g) := (inner_self_eq_norm_sq (𝕜 := ℂ) g).symm
  have h2 : inner ℂ g g = ∫ a : PhysicalCircle, inner ℂ (g a) (g a) ∂spatialMeasure :=
    L2.inner_def g g
  have hint : Integrable (fun a : PhysicalCircle => inner ℂ (g a) (g a)) spatialMeasure :=
    L2.integrable_inner g g
  have h3 : RCLike.re (∫ a : PhysicalCircle, inner ℂ (g a) (g a) ∂spatialMeasure) =
      ∫ a : PhysicalCircle, RCLike.re (inner ℂ (g a) (g a)) ∂spatialMeasure :=
    (integral_re hint).symm
  have hae : ∀ᵐ a ∂spatialMeasure, g a = f a :=
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure f
  rw [h1, h2, h3]
  apply integral_congr_ae
  filter_upwards [hae] with a ha
  rw [ha, inner_self_eq_norm_sq (𝕜 := ℂ)]

/-- Exact weight inequality on the range k + 1 ≤ m: w₁(n)·|n|^{2k} ≤ w_m(n). -/
private theorem weight_key (m k : ℕ) (hkm : k + 1 ≤ m) (n : ℤ) :
    sobolevModeWeight (1 : ℝ) n * |(n : ℝ)| ^ (2 * k) ≤ sobolevModeWeight (m : ℝ) n := by
  have hn : |(n : ℝ)| ≤ japaneseBracket n := by
    unfold japaneseBracket
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs]
    linarith
  have hB : (1 : ℝ) ≤ japaneseBracket n := japaneseBracket_one_le n
  have h1 : sobolevModeWeight (1 : ℝ) n = japaneseBracket n ^ (2 : ℕ) := by
    unfold sobolevModeWeight
    rw [show (2 : ℝ) * 1 = ((2 : ℕ) : ℝ) by norm_num]
    exact Real.rpow_natCast _ _
  have hm : sobolevModeWeight (m : ℝ) n = japaneseBracket n ^ (2 * m) := by
    unfold sobolevModeWeight
    rw [show (2 : ℝ) * (m : ℝ) = ((2 * m : ℕ) : ℝ) by push_cast; ring]
    exact Real.rpow_natCast _ _
  have hp : |(n : ℝ)| ^ (2 * k) ≤ japaneseBracket n ^ (2 * k) :=
    pow_le_pow_left₀ (abs_nonneg _) hn _
  rw [h1, hm]
  calc japaneseBracket n ^ 2 * |(n : ℝ)| ^ (2 * k)
      ≤ japaneseBracket n ^ 2 * japaneseBracket n ^ (2 * k) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
    _ = japaneseBracket n ^ (2 * (k + 1)) := by
        rw [← pow_add]
        congr 1
        ring
    _ ≤ japaneseBracket n ^ (2 * m) := pow_le_pow_right₀ hB (by omega)

/-- The order-k H¹ coefficient candidate lies in the weighted H¹ submodule (summability proved first). -/
private theorem jet_coeff_mem (m k : ℕ) (hkm : k + 1 ≤ m) (x : SobolevHilbert (m : ℝ)) :
    riccatiSobolevJetCoefficientL2Recovery28Second m k x ∈
      weightedSubmodule (sobolevModeWeight (1 : ℝ)) := by
  have hsrc : Summable (fun n : ℤ => sobolevModeWeight (m : ℝ) n *
      ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2) :=
    (weightedHilbert_hasSum (sobolevModeWeight (m : ℝ))
      (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x)).summable
  have hsum : Summable (fun n : ℤ => sobolevModeWeight (1 : ℝ) n *
      ‖riccatiSobolevJetCoefficientL2Recovery28Second m k x n‖ ^ 2) := by
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (sobolevModeWeightPositive 1 |>.out n).le (sq_nonneg _))
      (fun n => ?_) (hsrc.mul_left ((2 * Real.pi) ^ (2 * k)))
    rw [riccatiSobolevJetCoefficient_norm_sqL2Recovery28Second]
    have hw := weight_key m k hkm n
    calc sobolevModeWeight (1 : ℝ) n * ((2 * Real.pi) ^ (2 * k) * |(n : ℝ)| ^ (2 * k) *
          ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2)
        = (2 * Real.pi) ^ (2 * k) * ((sobolevModeWeight (1 : ℝ) n * |(n : ℝ)| ^ (2 * k)) *
          ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2) := by ring
      _ ≤ (2 * Real.pi) ^ (2 * k) * (sobolevModeWeight (m : ℝ) n *
          ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw (sq_nonneg _)) (by positivity)
  change Memℓp (weightedCoordinates (sobolevModeWeight (1 : ℝ))
      (riccatiSobolevJetCoefficientL2Recovery28Second m k x)) 2
  exact (weightedCoordinates_mem_l2_iff (sobolevModeWeight (1 : ℝ))
    (fun n => (sobolevModeWeightPositive 1).out n |>.le) _).2 hsum

/-- Lower jet CLM, as an L² class, is the order-k Riccati derivative class (re-proof of the private
`riccatiLowerJetContinuous_toLp_eq_derivativeL2Recovery31Second`, RiccatiSmoothPeriodicJetsAgreePointwiseRecovery31Second.lean:129-153). -/
private theorem lowerJet_toLp (m k : ℕ) (hkm : k + 1 ≤ m) (x : SobolevHilbert (m : ℝ)) :
    ContinuousMap.toLp 2 spatialMeasure ℂ
        (riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth m k hkm x) =
      riccatiSobolevIteratedDerivativeL2CLMRecovery30First m k (by omega) x := by
  let H : SobolevHilbert (1 : ℝ) :=
    ⟨riccatiSobolevJetCoefficientL2Recovery28Second m k x, jet_coeff_mem m k hkm x⟩
  have hA : riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth m k hkm x =
      physicalH1CanonicalContinuousRepresentativeCLM H := rfl
  have hrep : ContinuousMap.toLp 2 spatialMeasure ℂ
      (riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth m k hkm x) =
      physicalH1CarrierToL2AfterAcceptedCoordinate H := by
    rw [hA, physicalH1CanonicalContinuousRepresentativeCLM_apply]
    change ContinuousMap.toLp 2 spatialMeasure ℂ
        (physicalH1Continuous (physicalH1CarrierToL2AfterAcceptedCoordinate H)
          (physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable H)) = _
    exact physicalH1Continuous_toLp _ _
  rw [hrep]
  apply physicalFourierL2.injective
  apply lp.ext
  funext n
  rw [physicalFourierL2_apply, physicalFourierL2_apply,
    physicalH1CarrierToL2AfterAcceptedCoordinate_fourier,
    riccatiSobolevIteratedDerivativeL2CLMRecovery30First_fourier]

/-- Fourier-level identification of the M005 lower cast: the order-m jet of the ordinary coordinates
equals the order-k derivative of the lowered element (carrierIncl38 and carrierCoe38_incl38). -/
private theorem derivative_eq_lower (m k : ℕ) (hkm : k + 1 ≤ m)
    (u : NlsGge.ThirdConsultation.M.SobolevR m) :
    riccatiSobolevIteratedDerivativeL2CLMRecovery30First m k (by omega)
        (NlsGge.ThirdConsultation.M.ordinarySobolevCoordinates m u) =
      physicalSobolevDerivative38 k
        (NlsGge.ThirdConsultation.M.lowerSobolevCast k m (by omega) u) := by
  have hv : physicalSobolevFourierEquiv38 (k : ℝ)
      (NlsGge.ThirdConsultation.M.lowerSobolevCast k m (by omega) u) =
      carrierIncl38 (Nat.cast_le.mpr (by omega : k ≤ m) : (k : ℝ) ≤ (m : ℝ))
        (physicalSobolevFourierEquiv38 (m : ℝ) u) := by
    unfold NlsGge.ThirdConsultation.M.lowerSobolevCast
    exact LinearIsometryEquiv.apply_symm_apply _ _
  unfold physicalSobolevDerivative38
  apply physicalFourierL2.injective
  apply lp.ext
  funext n
  rw [physicalFourierL2_apply, physicalFourierL2_apply,
    riccatiSobolevIteratedDerivativeL2CLMRecovery30First_fourier,
    riccatiSobolevIteratedDerivativeL2CLMRecovery30First_fourier]
  unfold riccatiSobolevJetCoefficientL2Recovery28Second
  congr 1
  change -(carrierCoe38 (m : ℝ) (physicalSobolevFourierEquiv38 (m : ℝ) u) (-n)) =
    -(carrierCoe38 (k : ℝ) (physicalSobolevFourierEquiv38 (k : ℝ)
      (NlsGge.ThirdConsultation.M.lowerSobolevCast k m (by omega) u)) (-n))
  rw [hv, carrierCoe38_incl38]

/-- L² bridge (false component). Range: k + 1 ≤ m, the exact range where `sobolevJetContinuous` is
nonzero (M005.lean:51-56). Constant 1: both sides are the same L² class. -/
theorem sobolevJetContinuous_toLp_false (m k : ℕ) (hkm : k + 1 ≤ m)
    (u : NlsGge.ThirdConsultation.M.SobolevR m) :
    ContinuousMap.toLp 2 spatialMeasure ℂ
        (NlsGge.ThirdConsultation.M.sobolevJetContinuous m (false, k) u) =
      physicalSobolevDerivative38 k
        (NlsGge.ThirdConsultation.M.lowerSobolevCast k m (by omega) u) := by
  have hjet : NlsGge.ThirdConsultation.M.sobolevJetContinuous m (false, k) u =
      riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth m k hkm
        (NlsGge.ThirdConsultation.M.ordinarySobolevCoordinates m u) := by
    unfold NlsGge.ThirdConsultation.M.sobolevJetContinuous
    rw [dif_pos (show (false, k).2 + 1 ≤ m from hkm)]
    all_goals rfl
  rw [hjet, lowerJet_toLp m k hkm, derivative_eq_lower m k hkm u]

/-- L² bridge, squared norm form, for both Boolean components. Constant c = 1:
∫ ‖sobolevJetContinuous m (b,k) u‖² dμ = ‖physicalSobolevDerivative38 k (lowerSobolevCast k m u)‖². -/
theorem sobolevJetContinuous_sq_integral (m k : ℕ) (hkm : k + 1 ≤ m) (b : Bool)
    (u : NlsGge.ThirdConsultation.M.SobolevR m) :
    ∫ x : PhysicalCircle,
        ‖NlsGge.ThirdConsultation.M.sobolevJetContinuous m (b, k) u x‖ ^ 2 ∂spatialMeasure =
      ‖physicalSobolevDerivative38 k
        (NlsGge.ThirdConsultation.M.lowerSobolevCast k m (by omega) u)‖ ^ 2 := by
  have hf := sobolevJetContinuous_toLp_false m k hkm u
  have hstar : NlsGge.ThirdConsultation.M.sobolevJetContinuous m (true, k) u =
      star (NlsGge.ThirdConsultation.M.sobolevJetContinuous m (false, k) u) := by
    unfold NlsGge.ThirdConsultation.M.sobolevJetContinuous
    rw [dif_pos (show (true, k).2 + 1 ≤ m from hkm), dif_pos (show (false, k).2 + 1 ≤ m from hkm)]
    all_goals rfl
  have hnorm : ∀ x : PhysicalCircle,
      ‖NlsGge.ThirdConsultation.M.sobolevJetContinuous m (b, k) u x‖ =
        ‖NlsGge.ThirdConsultation.M.sobolevJetContinuous m (false, k) u x‖ := by
    intro x
    cases b
    · rfl
    · rw [hstar]
      simp
  simp_rw [hnorm]
  rw [← toLp_norm_sq_eq_integral (NlsGge.ThirdConsultation.M.sobolevJetContinuous m (false, k) u), hf]

end NlsGge.ThirdConsultation.M.M037Bridge
#check @NlsGge.ThirdConsultation.M.M037Bridge.sobolevJetContinuous_toLp_false
#check @NlsGge.ThirdConsultation.M.M037Bridge.sobolevJetContinuous_sq_integral
