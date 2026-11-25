import NlsGge.ThirdConsultation.Narrative.G0113
import NlsGge.Spectral.ChargeJensenSobolev38
import NlsGge.Hierarchy.RiccatiSmoothPeriodicJetsAgreePointwiseRecovery31Second
import NlsGge.Hierarchy.RiccatiSmoothClassicalDerivativePhysicalL2AgreementRecovery30Fifth
import NlsGge.Hierarchy.ALSamplingV2Formula38
import NlsGge.Atomic.LIB.LIB002
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.MeasureTheory.Integral.Bochner.L1

                                                          
                                                                         
                                                                            
                                                                            
  

set_option autoImplicit false
noncomputable section

namespace NlsGge.ThirdConsultation.Narrative

open NlsGge.Pilot NlsGge.HierarchyRiccati NlsGge.HierarchyRiccati.Core
open MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate ENNReal

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

local notation "J0" =>
  riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth 2 0 (by decide)
local notation "J1" =>
  riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth 2 1 (by decide)
local notation "D0" =>
  riccatiSobolevIteratedDerivativeL2CLMRecovery30First 2 0 (by decide)
local notation "D1" =>
  riccatiSobolevIteratedDerivativeL2CLMRecovery30First 2 1 (by decide)
local notation "D2" =>
  riccatiSobolevIteratedDerivativeL2CLMRecovery30First 2 2 (by decide)

private theorem g01H2_lower_smooth49 (k : ℕ) (hk : k + 1 ≤ 2)
    (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1)
    (x : SobolevHilbert 2)
    (hsource : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight 2) from x) n =
        physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)) n) :
    riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth 2 k hk x =
      riccatiSmoothPeriodicLiftContinuousMapRecovery30First (iteratedDeriv k u)
        (by
          rw [iteratedDeriv_eq_iterate]
          exact (hu.iterate_deriv k).continuous)
        (periodic_iteratedDeriv_of_contDiff u hu hper k) := by
  obtain ⟨y, hy, hjets⟩ :=
    riccatiSmoothPeriodicJetsAgreePointwiseRecovery31Second 2 u hu hper
  have hxy : x = y := by
    apply Subtype.ext
    funext n
    exact (hsource n).trans (hy n).symm
  subst y
  simpa only [riccatiSobolevJetContinuousRepresentativeRecovery30Eighth,
    Bool.false_eq_true, if_false] using hjets (false, k) hk

private theorem g01H2_lower_smooth_apply49 (k : ℕ) (hk : k + 1 ≤ 2)
    (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1)
    (x : SobolevHilbert 2)
    (hsource : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight 2) from x) n =
        physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)) n)
    (t : ℝ) :
    riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth 2 k hk x
        (t : PhysicalCircle) = iteratedDeriv k u t := by
  rw [g01H2_lower_smooth49 k hk u hu hper x hsource]
  change AddCircle.liftIoc 1 0 (iteratedDeriv k u) (t : PhysicalCircle) = _
  exact liftIoc_coe_eq38 _ (periodic_iteratedDeriv_of_contDiff u hu hper k) t

/-- The actual continuous lower jets represent the same L2 multiplier classes on H2. -/
theorem grouped_q4_H2_lower_jet_L2 (k : ℕ) (hk : k + 1 ≤ 2)
    (x : SobolevHilbert 2) :
    ContinuousMap.toLp 2 spatialMeasure ℂ
        (riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth 2 k hk x) =
      riccatiSobolevIteratedDerivativeL2CLMRecovery30First 2 k (by omega) x := by
  let F : SobolevHilbert 2 → PhysicalL2 := fun y =>
    ContinuousMap.toLp 2 spatialMeasure ℂ
      (riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth 2 k hk y)
  let G := riccatiSobolevIteratedDerivativeL2CLMRecovery30First 2 k (by omega)
  have hF : Continuous F :=
    (ContinuousMap.toLp 2 spatialMeasure ℂ).continuous.comp
      (riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth 2 k hk).continuous
  have hG : Continuous G := G.continuous
  have hagree : Set.EqOn F G (SmoothPeriodicSobolevSet38 2) := by
    rintro y ⟨u, hu, hper, hsource⟩
    have hrep := g01H2_lower_smooth49 k hk u hu hper y hsource
    have hclass := riccatiSobolevIteratedDerivativeL2_agrees_classicalRecovery30First
      2 k (by omega) y u hu hper hsource
    exact (congrArg (ContinuousMap.toLp 2 spatialMeasure ℂ) hrep).trans hclass.symm
  exact congrFun (hF.ext_on (smoothPeriodicSobolev38_dense 2) hG hagree) x

private theorem g01H2_multiplier_weak49 (k : ℕ) (hk : k ≤ 2)
    (x : SobolevHilbert 2) :
    NlsGge.Atomic.LIB002.HasWeakDerivativeL2 1 k (D0 x)
      (riccatiSobolevIteratedDerivativeL2CLMRecovery30First 2 k hk x) := by
  apply NlsGge.Atomic.LIB002.weakTest_identity_of_fourier_coefficients
  intro n
  change physicalFourier
      (riccatiSobolevIteratedDerivativeL2CLMRecovery30First 2 k hk x) n =
    NlsGge.Atomic.LIB002.fourierMultiplier 1 n ^ k * physicalFourier (D0 x) n
  rw [riccatiSobolevIteratedDerivativeL2CLMRecovery30First_fourier 2 k hk x n,
    riccatiSobolevIteratedDerivativeL2CLMRecovery30First_fourier 2 0 (by decide) x n]
  simp only [riccatiSobolevJetCoefficientL2Recovery28Second, pow_zero, one_mul,
    NlsGge.Atomic.LIB002.fourierMultiplier, NlsGge.Pilot.fourierMultiplier,
    Complex.ofReal_one, div_one]

/-- First and second weak derivatives of the same actual H2 physical field,
tested against every smooth periodic test, with the unit-period multiplier. -/
theorem grouped_q4_H2_weak_derivatives (x : SobolevHilbert 2) :
    NlsGge.Atomic.LIB002.HasWeakDerivativeL2 1 1
      (ContinuousMap.toLp 2 spatialMeasure ℂ (J0 x))
      (ContinuousMap.toLp 2 spatialMeasure ℂ (J1 x)) ∧
    NlsGge.Atomic.LIB002.HasWeakDerivativeL2 1 2
      (ContinuousMap.toLp 2 spatialMeasure ℂ (J0 x)) (D2 x) := by
  rw [grouped_q4_H2_lower_jet_L2 0 (by decide) x,
    grouped_q4_H2_lower_jet_L2 1 (by decide) x]
  exact ⟨g01H2_multiplier_weak49 1 (by decide) x,
    g01H2_multiplier_weak49 2 (by decide) x⟩

/-- The continuous H2 zeroth representative is genuinely C1, with the existing first jet. -/
theorem grouped_q4_H2_hasDerivAt (x : SobolevHilbert 2) (t : ℝ) :
    HasDerivAt (fun y : ℝ => J0 x (y : PhysicalCircle)) (J1 x (t : PhysicalCircle)) t := by
  let P : ℕ → SobolevHilbert 2 := fun N => truncSobolev38 2 N x
  have hP : Tendsto P atTop (𝓝 x) := tendsto_truncSobolev38 2 x
  have hJ0 : Tendsto (fun N => J0 (P N)) atTop (𝓝 (J0 x)) :=
    (J0).continuous.continuousAt.tendsto.comp hP
  have hJ1 : Tendsto (fun N => J1 (P N)) atTop (𝓝 (J1 x)) :=
    (J1).continuous.continuousAt.tendsto.comp hP
  have hfield (N : ℕ) :
      (fun y : ℝ => J0 (P N) (y : PhysicalCircle)) = truncField38 2 N x := by
    funext y
    simpa only [iteratedDeriv_zero] using
      g01H2_lower_smooth_apply49 0 (by decide) (truncField38 2 N x)
        (contDiff_truncField38 2 N x) (periodic_truncField38 2 N x)
        (P N) (truncSobolev38_link 2 N x) y
  have hderiv (N : ℕ) (y : ℝ) :
      HasDerivAt (fun r : ℝ => J0 (P N) (r : PhysicalCircle))
        (J1 (P N) (y : PhysicalCircle)) y := by
    rw [hfield N]
    have hfirst : J1 (P N) (y : PhysicalCircle) = deriv (truncField38 2 N x) y := by
      simpa only [iteratedDeriv_one] using
        g01H2_lower_smooth_apply49 1 (by decide) (truncField38 2 N x)
          (contDiff_truncField38 2 N x) (periodic_truncField38 2 N x)
          (P N) (truncSobolev38_link 2 N x) y
    rw [hfirst]
    exact (((contDiff_truncField38 2 N x).differentiable (by simp)).differentiableAt).hasDerivAt
  have huniform : TendstoUniformly
      (fun (N : ℕ) (y : ℝ) => J1 (P N) (y : PhysicalCircle))
      (fun y : ℝ => J1 x (y : PhysicalCircle)) atTop := by
    apply Metric.tendstoUniformly_iff.2
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp hJ1 ε hε] with N hN
    intro y
    refine (ContinuousMap.dist_apply_le_dist
      (f := J1 x) (g := J1 (P N)) (y : PhysicalCircle)).trans_lt ?_
    simpa only [dist_comm] using hN
  have hpoint (y : ℝ) : Tendsto
      (fun N => J0 (P N) (y : PhysicalCircle)) atTop
      (𝓝 (J0 x (y : PhysicalCircle))) :=
    (ContinuousMap.evalCLM ℂ (y : PhysicalCircle)).continuous.continuousAt.tendsto.comp hJ0
  convert! hasDerivAt_of_tendstoUniformly huniform
    (Eventually.of_forall hderiv) hpoint t using 1

/-- The literal squared-modulus derivative on every H2 field, including at zeros. -/
theorem grouped_q4_H2_norm_sq_deriv (x : SobolevHilbert 2) (t : ℝ) :
    deriv (fun y : ℝ => ‖J0 x (y : PhysicalCircle)‖ ^ 2) t =
      2 * ((starRingEnd ℂ) (J0 x (t : PhysicalCircle)) * J1 x (t : PhysicalCircle)).re := by
  rw [grouped_norm_sq_deriv _ t (grouped_q4_H2_hasDerivAt x t).differentiableAt,
    (grouped_q4_H2_hasDerivAt x t).deriv]

private theorem g01H2_l2_square_integrable49 (d : PhysicalL2) :
    Integrable (fun y : PhysicalCircle => ‖d y‖ ^ 2) spatialMeasure := by
  simpa using (Lp.memLp d).integrable_norm_pow (p := 2) (by norm_num)

private theorem g01H2_l2_norm_integral49 (d : PhysicalL2) :
    ‖d‖ ^ 2 = ∫ y : PhysicalCircle, ‖d y‖ ^ 2 ∂spatialMeasure := by
  have hint := L2.integrable_inner (𝕜 := ℂ) d d
  calc
    ‖d‖ ^ 2 = RCLike.re (inner ℂ d d) :=
      (inner_self_eq_norm_sq (𝕜 := ℂ) d).symm
    _ = RCLike.re (∫ y : PhysicalCircle, inner ℂ (d y) (d y) ∂spatialMeasure) :=
      congrArg RCLike.re (L2.inner_def d d)
    _ = ∫ y : PhysicalCircle, RCLike.re (inner ℂ (d y) (d y)) ∂spatialMeasure :=
      (integral_re hint).symm
    _ = ∫ y : PhysicalCircle, ‖d y‖ ^ 2 ∂spatialMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y => inner_self_eq_norm_sq (𝕜 := ℂ) (d y)

private theorem g01H2_l2_lift_integral49 (d : PhysicalL2) :
    IntervalIntegrable (fun t : ℝ => ‖d (t : PhysicalCircle)‖ ^ 2) volume 0 1 ∧
    (∫ t in (0 : ℝ)..1, ‖d (t : PhysicalCircle)‖ ^ 2) = ‖d‖ ^ 2 := by
  refine ⟨NlsGge.AblowitzLadik.alLiftInt38 _ (g01H2_l2_square_integrable49 d), ?_⟩
  exact (unitIntervalIntegral_lift_eq_spatialHaar
    (fun y : PhysicalCircle => ‖d y‖ ^ 2)).trans (g01H2_l2_norm_integral49 d).symm

private theorem g01H2_toLp_norm_integral49 (f : C(PhysicalCircle, ℂ)) :
    ‖ContinuousMap.toLp 2 spatialMeasure ℂ f‖ ^ 2 =
      ∫ y : PhysicalCircle, ‖f y‖ ^ 2 ∂spatialMeasure := by
  rw [g01H2_l2_norm_integral49]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure f] with y hy
  rw [hy]

private theorem g01H2_second_smooth_norm49
    (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1)
    (x : SobolevHilbert 2)
    (hsource : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight 2) from x) n =
        physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)) n) :
    ‖D2 x‖ ^ 2 = ∫ t in (0 : ℝ)..1, ‖iteratedDeriv 2 u t‖ ^ 2 := by
  have hclass := riccatiSobolevIteratedDerivativeL2_agrees_classicalRecovery30First
    2 2 (by decide) x u hu hper hsource
  let f : C(PhysicalCircle, ℂ) := riccatiSmoothPeriodicLiftContinuousMapRecovery30First
    (iteratedDeriv 2 u) (by
      rw [iteratedDeriv_eq_iterate]
      exact (hu.iterate_deriv 2).continuous)
    (periodic_iteratedDeriv_of_contDiff u hu hper 2)
  calc
    ‖D2 x‖ ^ 2 = ‖ContinuousMap.toLp 2 spatialMeasure ℂ f‖ ^ 2 := by rw [hclass]
    _ = ∫ y : PhysicalCircle, ‖f y‖ ^ 2 ∂spatialMeasure := g01H2_toLp_norm_integral49 f
    _ = ∫ t in (0 : ℝ)..1, ‖f (t : PhysicalCircle)‖ ^ 2 :=
      (unitIntervalIntegral_lift_eq_spatialHaar (fun y : PhysicalCircle => ‖f y‖ ^ 2)).symm
    _ = ∫ t in (0 : ℝ)..1, ‖iteratedDeriv 2 u t‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t _
      change ‖AddCircle.liftIoc 1 0 (iteratedDeriv 2 u) (t : PhysicalCircle)‖ ^ 2 = _
      rw [liftIoc_coe_eq38 _ (periodic_iteratedDeriv_of_contDiff u hu hper 2) t]

private def g01H2_lower_polynomial49 (x : SobolevHilbert 2) : C(PhysicalCircle, ℂ) :=
  2 * (star (J0 x) * J0 x) ^ 3 +
    6 * (star (J0 x) * J0 x) * (star (J1 x) * J1 x) +
    (star (J0 x) * J1 x + J0 x * star (J1 x)) ^ 2

private theorem g01H2_lower_polynomial_re49 (x : SobolevHilbert 2) (y : PhysicalCircle) :
    (g01H2_lower_polynomial49 x y).re =
      2 * ‖J0 x y‖ ^ 6 + 6 * ‖J0 x y‖ ^ 2 * ‖J1 x y‖ ^ 2 +
        (2 * ((starRingEnd ℂ) (J0 x y) * J1 x y).re) ^ 2 := by
  have h6 : ‖J0 x y‖ ^ 6 = (‖J0 x y‖ ^ 2) ^ 3 := by ring
  rw [h6]
  change ((2 : ℂ) * ((starRingEnd ℂ) (J0 x y) * J0 x y) ^ 3 +
      6 * ((starRingEnd ℂ) (J0 x y) * J0 x y) *
        ((starRingEnd ℂ) (J1 x y) * J1 x y) +
      ((starRingEnd ℂ) (J0 x y) * J1 x y +
        J0 x y * (starRingEnd ℂ) (J1 x y)) ^ 2).re = _
  simp only [Complex.sq_norm, Complex.normSq_apply]
  simp only [pow_succ, pow_zero, mul_one]
  norm_num [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im] <;> ring

private def g01H2_lower_value49 (x : SobolevHilbert 2) : ℝ :=
  (∫ y : PhysicalCircle,
    ((ContinuousMap.toLp 1 spatialMeasure ℂ) (g01H2_lower_polynomial49 x) :
      PhysicalCircle → ℂ) y ∂spatialMeasure).re

private theorem g01H2_lower_value_continuous49 : Continuous g01H2_lower_value49 := by
  have hpoly : Continuous g01H2_lower_polynomial49 := by
    have h0 := (J0).continuous
    have h1 := (J1).continuous
    unfold g01H2_lower_polynomial49
    fun_prop
  exact Complex.continuous_re.comp
    (continuous_integral.comp ((ContinuousMap.toLp 1 spatialMeasure ℂ).continuous.comp hpoly))

private theorem g01H2_lower_value_integral49 (x : SobolevHilbert 2) :
    g01H2_lower_value49 x = ∫ t in (0 : ℝ)..1,
      2 * ‖J0 x (t : PhysicalCircle)‖ ^ 6 +
      6 * ‖J0 x (t : PhysicalCircle)‖ ^ 2 * ‖J1 x (t : PhysicalCircle)‖ ^ 2 +
      (2 * ((starRingEnd ℂ) (J0 x (t : PhysicalCircle)) * J1 x (t : PhysicalCircle)).re) ^ 2 := by
  have hint : Integrable (fun y : PhysicalCircle => g01H2_lower_polynomial49 x y)
      spatialMeasure :=
    (g01H2_lower_polynomial49 x).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hae := ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℂ) spatialMeasure
    (g01H2_lower_polynomial49 x)
  unfold g01H2_lower_value49
  rw [integral_congr_ae hae]
  calc
    (∫ y : PhysicalCircle, g01H2_lower_polynomial49 x y ∂spatialMeasure).re =
        ∫ y : PhysicalCircle, (g01H2_lower_polynomial49 x y).re ∂spatialMeasure := by
      simpa only [RCLike.re_to_complex] using (integral_re hint).symm
    _ =
        ∫ y : PhysicalCircle,
          2 * ‖J0 x y‖ ^ 6 + 6 * ‖J0 x y‖ ^ 2 * ‖J1 x y‖ ^ 2 +
            (2 * ((starRingEnd ℂ) (J0 x y) * J1 x y).re) ^ 2 ∂spatialMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall (g01H2_lower_polynomial_re49 x)
    _ = _ := (unitIntervalIntegral_lift_eq_spatialHaar
      (fun y : PhysicalCircle => 2 * ‖J0 x y‖ ^ 6 + 6 * ‖J0 x y‖ ^ 2 * ‖J1 x y‖ ^ 2 +
        (2 * ((starRingEnd ℂ) (J0 x y) * J1 x y).re) ^ 2)).symm

private theorem g01H2_charge_eq_norm_lower49 (x : SobolevHilbert 2) :
    chargeSobolev38 3 2 x = ‖D2 x‖ ^ 2 + g01H2_lower_value49 x := by
  have hcharge : Continuous (chargeSobolev38 3 2) :=
    continuous_chargeSobolev38 3 2 (by decide)
  have hrhs : Continuous (fun y : SobolevHilbert 2 =>
      ‖D2 y‖ ^ 2 + g01H2_lower_value49 y) :=
    ((D2).continuous.norm.pow 2).add g01H2_lower_value_continuous49
  have hagree : Set.EqOn (chargeSobolev38 3 2)
      (fun y : SobolevHilbert 2 => ‖D2 y‖ ^ 2 + g01H2_lower_value49 y)
      (SmoothPeriodicSobolevSet38 2) := by
    rintro y ⟨u, hu, hper, hsource⟩
    have hJ0 (t : ℝ) : J0 y (t : PhysicalCircle) = u t := by
      simpa only [iteratedDeriv_zero] using
        g01H2_lower_smooth_apply49 0 (by decide) u hu hper y hsource t
    have hJ1 (t : ℝ) : J1 y (t : PhysicalCircle) = deriv u t := by
      simpa only [iteratedDeriv_one] using
        g01H2_lower_smooth_apply49 1 (by decide) u hu hper y hsource t
    have hlower : g01H2_lower_value49 y = ∫ t in (0 : ℝ)..1,
        2 * ‖u t‖ ^ 6 + 6 * ‖u t‖ ^ 2 * ‖deriv u t‖ ^ 2 +
          (deriv (fun r => ‖u r‖ ^ 2) t) ^ 2 := by
      rw [g01H2_lower_value_integral49]
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [hJ0 t, hJ1 t, grouped_norm_sq_deriv u t
        ((hu.differentiable (by simp)).differentiableAt)]
    have hlead : IntervalIntegrable (fun t => ‖iteratedDeriv 2 u t‖ ^ 2) volume 0 1 := by
      have hc : Continuous (iteratedDeriv 2 u) := by
        rw [iteratedDeriv_eq_iterate]
        exact (hu.iterate_deriv 2).continuous
      exact (hc.norm.pow 2).intervalIntegrable 0 1
    have hrest : IntervalIntegrable (fun t =>
        2 * ‖u t‖ ^ 6 + 6 * ‖u t‖ ^ 2 * ‖deriv u t‖ ^ 2 +
          (deriv (fun r => ‖u r‖ ^ 2) t) ^ 2) volume 0 1 := by
      have huc := hu.continuous
      have hd : Continuous (deriv u) := by
        have h := hu.iterate_deriv 1
        simpa only [Function.iterate_one] using h.continuous
      have heq : deriv (fun r => ‖u r‖ ^ 2) =
          fun t => 2 * ((starRingEnd ℂ) (u t) * deriv u t).re :=
        funext fun t => grouped_norm_sq_deriv u t
          ((hu.differentiable (by simp)).differentiableAt)
      rw [heq]
      exact (by fun_prop : Continuous (fun t =>
        2 * ‖u t‖ ^ 6 + 6 * ‖u t‖ ^ 2 * ‖deriv u t‖ ^ 2 +
          (2 * ((starRingEnd ℂ) (u t) * deriv u t).re) ^ 2)).intervalIntegrable 0 1
    change chargeSobolev38 3 2 y = ‖D2 y‖ ^ 2 + g01H2_lower_value49 y
    rw [chargeSobolev38_smooth 3 2 (by decide) (by decide) u hu hper y hsource,
      grouped_q4_second_integral u hu hper,
      g01H2_second_smooth_norm49 u hu hper y hsource, hlower,
      ← intervalIntegral.integral_add hlead hrest]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  exact congrFun (hcharge.ext_on (smoothPeriodicSobolev38_dense 2) hrhs hagree) x

private theorem g01H2_lift_continuous49 (f : C(PhysicalCircle, ℂ)) :
    Continuous (fun t : ℝ => f (t : PhysicalCircle)) :=
  f.continuous.comp (continuous_quotient_mk' : Continuous ((↑) : ℝ → PhysicalCircle))

/-- Finiteness is established for the complete H2 density before its integral is used. -/
theorem grouped_q4_H2_integrand_intervalIntegrable (x : SobolevHilbert 2) :
    IntervalIntegrable (fun t : ℝ => ‖(D2 x) (t : PhysicalCircle)‖ ^ 2 +
      2 * ‖J0 x (t : PhysicalCircle)‖ ^ 6 +
      6 * ‖J0 x (t : PhysicalCircle)‖ ^ 2 * ‖J1 x (t : PhysicalCircle)‖ ^ 2 +
      (deriv (fun r : ℝ => ‖J0 x (r : PhysicalCircle)‖ ^ 2) t) ^ 2) volume 0 1 := by
  have hlead := (g01H2_l2_lift_integral49 (D2 x)).1
  have h0 := g01H2_lift_continuous49 (J0 x)
  have h1 := g01H2_lift_continuous49 (J1 x)
  have hsix : IntervalIntegrable
      (fun t : ℝ => 2 * ‖J0 x (t : PhysicalCircle)‖ ^ 6) volume 0 1 :=
    ((h0.norm.pow 6).const_mul 2).intervalIntegrable 0 1
  have hweighted : IntervalIntegrable
      (fun t : ℝ => 6 * ‖J0 x (t : PhysicalCircle)‖ ^ 2 * ‖J1 x (t : PhysicalCircle)‖ ^ 2)
      volume 0 1 :=
    (((h0.norm.pow 2).const_mul 6).mul (h1.norm.pow 2)).intervalIntegrable 0 1
  have heq : deriv (fun r : ℝ => ‖J0 x (r : PhysicalCircle)‖ ^ 2) =
      fun (t : ℝ) => 2 * ((starRingEnd ℂ) (J0 x (t : PhysicalCircle)) *
        J1 x (t : PhysicalCircle)).re := funext (grouped_q4_H2_norm_sq_deriv x)
  have hmodulus : IntervalIntegrable
      (fun t : ℝ => (deriv (fun r : ℝ => ‖J0 x (r : PhysicalCircle)‖ ^ 2) t) ^ 2)
      volume 0 1 := by
    rw [heq]
    exact (by fun_prop : Continuous (fun t : ℝ =>
      (2 * ((starRingEnd ℂ) (J0 x (t : PhysicalCircle)) *
        J1 x (t : PhysicalCircle)).re) ^ 2)).intervalIntegrable 0 1
  exact ((hlead.add hsix).add hweighted).add hmodulus

/-- v2 C:eq:Q4 on every H2 field, with its actual weak second derivative and
the literal classical derivative of the squared canonical C1 representative. -/
theorem grouped_q4_second_integral_H2 (x : SobolevHilbert 2) :
    chargeSobolev38 3 2 x = ∫ t in (0 : ℝ)..1,
      ‖(D2 x) (t : PhysicalCircle)‖ ^ 2 +
      2 * ‖J0 x (t : PhysicalCircle)‖ ^ 6 +
      6 * ‖J0 x (t : PhysicalCircle)‖ ^ 2 * ‖J1 x (t : PhysicalCircle)‖ ^ 2 +
      (deriv (fun r : ℝ => ‖J0 x (r : PhysicalCircle)‖ ^ 2) t) ^ 2 := by
  have hlead := g01H2_l2_lift_integral49 (D2 x)
  have h0 := g01H2_lift_continuous49 (J0 x)
  have h1 := g01H2_lift_continuous49 (J1 x)
  have hrest : IntervalIntegrable (fun t : ℝ =>
      2 * ‖J0 x (t : PhysicalCircle)‖ ^ 6 +
      6 * ‖J0 x (t : PhysicalCircle)‖ ^ 2 * ‖J1 x (t : PhysicalCircle)‖ ^ 2 +
      (2 * ((starRingEnd ℂ) (J0 x (t : PhysicalCircle)) * J1 x (t : PhysicalCircle)).re) ^ 2)
      volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ =>
      2 * ‖J0 x (t : PhysicalCircle)‖ ^ 6 +
      6 * ‖J0 x (t : PhysicalCircle)‖ ^ 2 * ‖J1 x (t : PhysicalCircle)‖ ^ 2 +
      (2 * ((starRingEnd ℂ) (J0 x (t : PhysicalCircle)) * J1 x (t : PhysicalCircle)).re) ^ 2)).intervalIntegrable 0 1
  calc
    chargeSobolev38 3 2 x = ‖D2 x‖ ^ 2 + g01H2_lower_value49 x :=
      g01H2_charge_eq_norm_lower49 x
    _ = (∫ t in (0 : ℝ)..1, ‖(D2 x) (t : PhysicalCircle)‖ ^ 2) +
        (∫ t in (0 : ℝ)..1,
          2 * ‖J0 x (t : PhysicalCircle)‖ ^ 6 +
          6 * ‖J0 x (t : PhysicalCircle)‖ ^ 2 * ‖J1 x (t : PhysicalCircle)‖ ^ 2 +
          (2 * ((starRingEnd ℂ) (J0 x (t : PhysicalCircle)) * J1 x (t : PhysicalCircle)).re) ^ 2) := by
      rw [hlead.2, g01H2_lower_value_integral49]
    _ = ∫ t in (0 : ℝ)..1,
        ‖(D2 x) (t : PhysicalCircle)‖ ^ 2 +
          (2 * ‖J0 x (t : PhysicalCircle)‖ ^ 6 +
          6 * ‖J0 x (t : PhysicalCircle)‖ ^ 2 * ‖J1 x (t : PhysicalCircle)‖ ^ 2 +
          (2 * ((starRingEnd ℂ) (J0 x (t : PhysicalCircle)) * J1 x (t : PhysicalCircle)).re) ^ 2) :=
      (intervalIntegral.integral_add hlead.1 hrest).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [grouped_q4_H2_norm_sq_deriv x t]
      ring

/-- The full literal weak-derivative integral is continuous in the actual H2 norm. -/
theorem continuous_grouped_q4_second_integral_H2 :
    Continuous (fun x : SobolevHilbert 2 => ∫ t in (0 : ℝ)..1,
      ‖(D2 x) (t : PhysicalCircle)‖ ^ 2 +
      2 * ‖J0 x (t : PhysicalCircle)‖ ^ 6 +
      6 * ‖J0 x (t : PhysicalCircle)‖ ^ 2 * ‖J1 x (t : PhysicalCircle)‖ ^ 2 +
      (deriv (fun r : ℝ => ‖J0 x (r : PhysicalCircle)‖ ^ 2) t) ^ 2) := by
  have heq : (fun x : SobolevHilbert 2 => ∫ t in (0 : ℝ)..1,
      ‖(D2 x) (t : PhysicalCircle)‖ ^ 2 +
      2 * ‖J0 x (t : PhysicalCircle)‖ ^ 6 +
      6 * ‖J0 x (t : PhysicalCircle)‖ ^ 2 * ‖J1 x (t : PhysicalCircle)‖ ^ 2 +
      (deriv (fun r : ℝ => ‖J0 x (r : PhysicalCircle)‖ ^ 2) t) ^ 2) = chargeSobolev38 3 2 :=
    funext fun x => (grouped_q4_second_integral_H2 x).symm
  rw [heq]
  exact continuous_chargeSobolev38 3 2 (by decide)

end NlsGge.ThirdConsultation.Narrative
