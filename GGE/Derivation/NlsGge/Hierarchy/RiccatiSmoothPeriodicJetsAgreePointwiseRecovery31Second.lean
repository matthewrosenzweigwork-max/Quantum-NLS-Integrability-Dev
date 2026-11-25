import NlsGge.Hierarchy.RiccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth
import NlsGge.Hierarchy.RiccatiSmoothPeriodicRealizesAllDerivativeL2ClassesRecovery30
import NlsGge.Analysis.H1Fourier
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot
open NlsGge.Analysis
open MeasureTheory
open scoped ContDiff

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

private theorem riccatiSobolevJetH1_pointwiseBoundRecovery31Second
    (m k : ℕ) (hkm : k + 1 ≤ m) (x : SobolevHilbert (m : ℝ)) (n : ℤ) :
    sobolevModeWeight (1 : ℝ) n *
        ‖riccatiSobolevJetCoefficientL2Recovery28Second m k x n‖ ^ 2 ≤
      (2 * Real.pi) ^ (2 * k) *
        (sobolevModeWeight (m : ℝ) n *
          ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2) := by
  let wM := sobolevModeWeight (m : ℝ)
  let w1 := sobolevModeWeight (1 : ℝ)
  have hn : |(n : ℝ)| ≤ japaneseBracket n := by
    unfold japaneseBracket
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs]
    linarith
  have hpowN : |(n : ℝ)| ^ (2 * k) ≤ japaneseBracket n ^ (2 * k) :=
    pow_le_pow_left₀ (abs_nonneg _) hn _
  have hpowB : japaneseBracket n ^ (2 * (k + 1)) ≤
      japaneseBracket n ^ (2 * m) :=
    pow_le_pow_right₀ (japaneseBracket_one_le n) (by
      have hexp : k + 1 ≤ m := hkm
      omega)
  have hweightM : wM n = japaneseBracket n ^ (2 * m) := by
    dsimp [wM, sobolevModeWeight]
    have he : 2 * (m : ℝ) = ((2 * m : ℕ) : ℝ) := by push_cast; ring
    rw [he]
    exact Real.rpow_natCast _ _
  have hweight1 : w1 n = japaneseBracket n ^ (2 : ℕ) := by
    dsimp [w1, sobolevModeWeight]
    have he : 2 * (1 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
    rw [he]
    exact Real.rpow_natCast _ _
  have hfreq : japaneseBracket n ^ 2 * |(n : ℝ)| ^ (2 * k) ≤
      japaneseBracket n ^ (2 * m) := by
    calc
      japaneseBracket n ^ 2 * |(n : ℝ)| ^ (2 * k) ≤
          japaneseBracket n ^ 2 * japaneseBracket n ^ (2 * k) :=
        mul_le_mul_of_nonneg_left hpowN (by positivity)
      _ = japaneseBracket n ^ (2 * (k + 1)) := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ japaneseBracket n ^ (2 * m) := hpowB
  change w1 n *
      ‖riccatiSobolevJetCoefficientL2Recovery28Second m k x n‖ ^ 2 ≤
    (2 * Real.pi) ^ (2 * k) *
      (wM n * ‖(show WeightedHilbert wM from x) n‖ ^ 2)
  rw [hweight1, riccatiSobolevJetCoefficient_norm_sqL2Recovery28Second]
  calc
    japaneseBracket n ^ 2 *
        ((2 * Real.pi) ^ (2 * k) * |(n : ℝ)| ^ (2 * k) *
          ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2) =
        (2 * Real.pi) ^ (2 * k) *
          (japaneseBracket n ^ 2 * |(n : ℝ)| ^ (2 * k) *
            ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2) := by ring
    _ ≤ (2 * Real.pi) ^ (2 * k) *
        (japaneseBracket n ^ (2 * m) *
          ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hfreq (sq_nonneg _)) (by positivity)
    _ = (2 * Real.pi) ^ (2 * k) *
        (wM n * ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2) := by
      rw [← hweightM]

private theorem riccatiSobolevJetH1_summableRecovery31Second
    (m k : ℕ) (hkm : k + 1 ≤ m) (x : SobolevHilbert (m : ℝ)) :
    Summable (fun n : ℤ => sobolevModeWeight (1 : ℝ) n *
      ‖riccatiSobolevJetCoefficientL2Recovery28Second m k x n‖ ^ 2) := by
  let wM := sobolevModeWeight (m : ℝ)
  have hsource : Summable (fun n : ℤ => wM n *
      ‖(show WeightedHilbert wM from x) n‖ ^ 2) :=
    (weightedHilbert_hasSum wM (show WeightedHilbert wM from x)).summable
  have hmajor := hsource.mul_left ((2 * Real.pi) ^ (2 * k))
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (sobolevModeWeightPositive 1 |>.out n).le (sq_nonneg _))
    (fun n => riccatiSobolevJetH1_pointwiseBoundRecovery31Second m k hkm x n)
    hmajor

private noncomputable def riccatiSobolevJetH1ValueRecovery31Second
    (m k : ℕ) (hkm : k + 1 ≤ m) (x : SobolevHilbert (m : ℝ)) :
    SobolevHilbert (1 : ℝ) := by
  let d := riccatiSobolevJetCoefficientL2Recovery28Second m k x
  have hd := riccatiSobolevJetH1_summableRecovery31Second m k hkm x
  have hmem : d ∈ weightedSubmodule (sobolevModeWeight (1 : ℝ)) := by
    change Memℓp (weightedCoordinates (sobolevModeWeight (1 : ℝ)) d) 2
    exact (weightedCoordinates_mem_l2_iff (sobolevModeWeight (1 : ℝ))
      (fun n => (sobolevModeWeightPositive 1).out n |>.le) d).2 (by simpa [d] using hd)
  exact (⟨d, hmem⟩ : WeightedHilbert (sobolevModeWeight (1 : ℝ)))

private theorem riccatiSobolevJetH1Value_coordinateRecovery31Second
    (m k : ℕ) (hkm : k + 1 ≤ m) (x : SobolevHilbert (m : ℝ)) (n : ℤ) :
    (show WeightedHilbert (sobolevModeWeight (1 : ℝ)) from
      riccatiSobolevJetH1ValueRecovery31Second m k hkm x) n =
      riccatiSobolevJetCoefficientL2Recovery28Second m k x n := rfl


private theorem riccatiJetH1Carrier_fourierEqDerivativeL2Recovery31Second
    (m k : ℕ) (horder : k + 1 ≤ m) (x : SobolevHilbert (m : ℝ)) :
    physicalH1CarrierToL2AfterAcceptedCoordinate
        (riccatiSobolevJetH1ValueRecovery31Second m k horder x) =
      riccatiSobolevIteratedDerivativeL2CLMRecovery30First m k (by omega) x := by
  apply physicalFourierL2.injective
  apply lp.ext
  funext n
  rw [physicalFourierL2_apply, physicalFourierL2_apply,
    physicalH1CarrierToL2AfterAcceptedCoordinate_fourier,
    riccatiSobolevJetH1Value_coordinateRecovery31Second,
    riccatiSobolevIteratedDerivativeL2CLMRecovery30First_fourier]

private theorem riccatiLowerJetContinuous_toLp_eq_derivativeL2Recovery31Second
    (m k : ℕ) (horder : k + 1 ≤ m) (x : SobolevHilbert (m : ℝ)) :
    ContinuousMap.toLp 2 spatialMeasure ℂ
        (riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth
          m k horder x) =
      riccatiSobolevIteratedDerivativeL2CLMRecovery30First m k (by omega) x := by
  have hrep :
      ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth
            m k horder x) =
        physicalH1CarrierToL2AfterAcceptedCoordinate
          (riccatiSobolevJetH1ValueRecovery31Second m k horder x) := by
    change ContinuousMap.toLp 2 spatialMeasure ℂ
        (physicalH1CanonicalContinuousRepresentativeCLM
          (riccatiSobolevJetH1ValueRecovery31Second m k horder x)) = _
    rw [physicalH1CanonicalContinuousRepresentativeCLM_apply]
    change ContinuousMap.toLp 2 spatialMeasure ℂ
        (physicalH1Continuous
          (physicalH1CarrierToL2AfterAcceptedCoordinate
            (riccatiSobolevJetH1ValueRecovery31Second m k horder x))
          (physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable
            (riccatiSobolevJetH1ValueRecovery31Second m k horder x))) = _
    exact physicalH1Continuous_toLp _ _
  exact hrep.trans
    (riccatiJetH1Carrier_fourierEqDerivativeL2Recovery31Second m k horder x)

private theorem riccatiLowerJetContinuous_eq_smoothDerivativeRecovery31Second
    (m k : ℕ) (horder : k + 1 ≤ m) (x : SobolevHilbert (m : ℝ))
    (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1)
    (hclass : riccatiSobolevIteratedDerivativeL2CLMRecovery30First
        m k (by omega) x =
      ContinuousMap.toLp 2 spatialMeasure ℂ
        (riccatiSmoothPeriodicLiftContinuousMapRecovery30First
          (iteratedDeriv k u)
          (by
            rw [iteratedDeriv_eq_iterate]
            exact (ContDiff.iterate_deriv k hu).continuous)
          (NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff u hu hper k))) :
    riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth
        m k horder x =
      riccatiSmoothPeriodicLiftContinuousMapRecovery30First
        (iteratedDeriv k u)
        (by
          rw [iteratedDeriv_eq_iterate]
          exact (ContDiff.iterate_deriv k hu).continuous)
        (NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff u hu hper k) := by
  have hLp :=
    riccatiLowerJetContinuous_toLp_eq_derivativeL2Recovery31Second m k horder x
  have hLp' :
      ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth
            m k horder x) =
        ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First
            (iteratedDeriv k u)
            (by
              rw [iteratedDeriv_eq_iterate]
              exact (ContDiff.iterate_deriv k hu).continuous)
            (NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff
              u hu hper k)) := hLp.trans hclass
  haveI : spatialMeasure.IsOpenPosMeasure := by
    unfold spatialMeasure
    infer_instance
  exact (ContinuousMap.toLp_injective
    (p := 2) (μ := spatialMeasure) (𝕜 := ℂ)) hLp'

/-- One fixed smooth-source Sobolev witness realizes all classical jets
pointwise as the actual continuous Boolean jet representatives at every
continuous lower order. The true component is `star`; the false component is
identity, exactly as in the source polynomial. -/
theorem riccatiSmoothPeriodicJetsAgreePointwiseRecovery31Second
    (m : ℕ) (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) :
    ∃ x : SobolevHilbert (m : ℝ),
      (∀ n : ℤ,
        (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n =
          physicalFourier
            (ContinuousMap.toLp 2 spatialMeasure ℂ
              (riccatiSmoothPeriodicLiftContinuousMapRecovery30First
                u hu.continuous hper)) n) ∧
      ∀ v : Jet, ∀ horder : v.2 + 1 ≤ m,
        riccatiSobolevJetContinuousRepresentativeRecovery30Eighth m v horder x =
          if v.1 then
            star (riccatiSmoothPeriodicLiftContinuousMapRecovery30First
              (iteratedDeriv v.2 u)
              (by
                rw [iteratedDeriv_eq_iterate]
                exact (ContDiff.iterate_deriv v.2 hu).continuous)
              (NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff
                u hu hper v.2))
          else riccatiSmoothPeriodicLiftContinuousMapRecovery30First
            (iteratedDeriv v.2 u)
            (by
              rw [iteratedDeriv_eq_iterate]
              exact (ContDiff.iterate_deriv v.2 hu).continuous)
            (NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff
              u hu hper v.2) := by
  obtain ⟨x, hcoeff, hclasses⟩ :=
    riccatiSmoothPeriodicRealizesAllDerivativeL2ClassesRecovery30 m u hu hper
  refine ⟨x, hcoeff, ?_⟩
  intro v horder
  have hplain := riccatiLowerJetContinuous_eq_smoothDerivativeRecovery31Second
    m v.2 horder x u hu hper (hclasses v.2 (by omega))
  cases hv : v.1 with
  | false =>
      simpa [riccatiSobolevJetContinuousRepresentativeRecovery30Eighth, hv] using hplain
  | true =>
      simpa [riccatiSobolevJetContinuousRepresentativeRecovery30Eighth, hv] using
        congrArg star hplain

end NlsGge.HierarchyRiccati.Core

end
