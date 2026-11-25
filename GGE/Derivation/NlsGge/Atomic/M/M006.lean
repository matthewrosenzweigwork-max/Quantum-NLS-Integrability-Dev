import Mathlib
import NlsGge.Atomic.M.M005
import NlsGge.Hierarchy.RiccatiUnitPeriodIntervalToPhysicalHaar
import NlsGge.Hierarchy.RiccatiSmoothClassicalDerivativePhysicalL2AgreementRecovery30Fifth
import NlsGge.Hierarchy.RiccatiSmoothPeriodicJetsAgreePointwiseRecovery31Second

/- M-006 production kit (proof development, AUTHOR; not reviewed; target NlsGge/Atomic/M/M006.lean).  Head, `RepresentsSmoothField` verbatim from
   PRO_DEFINITION_RESPONSE_FP80_02_03.md (M-006).  Accepted elaboration repair (root ruling 2026-10-30): the proved
   `local instance : IsProbabilityMeasure spatialMeasure` (as in G1021.lean:1090), required by `ContinuousMap.toLp 2 spatialMeasure ℂ` in the printed head.
   Route: (1) `u ↦ ordinarySobolevCoordinates m u` is an isometry (reflection invariance of the weight), so every CLM/derivative in the
   definitions is continuous in u; the finite products of continuous jet representatives give continuity of integralMonomial; (2) smooth agreement via
   production riccatiSobolevIteratedDerivativeL2_agrees_classicalRecovery30First (top order) and lowerJetCLM_smooth38 (lower jets); (3) the identity on all of
   H^m by density of Fourier polynomials (each represents a trigonometric polynomial) and continuity of both sides. -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.M
noncomputable section
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core NlsGge.Atomic.Common MeasureTheory
open scoped ContDiff

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure; infer_instance

def RepresentsSmoothField {m : ℕ} (u : SobolevR m)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hper : Function.Periodic f 1) : Prop :=
  physicalOfSobolev u =
    ContinuousMap.toLp 2 spatialMeasure ℂ
      (riccatiSmoothPeriodicLiftContinuousMapRecovery30First
        f hf.continuous hper)



theorem ordinarySobolevCoordinates_norm_sq (m : ℕ) (u : SobolevR m) :
    ‖ordinarySobolevCoordinates m u‖ ^ 2 = ‖u‖ ^ 2 := by
  have hu : ‖u‖ = ‖physicalSobolevFourierEquiv38 (m : ℝ) u‖ :=
    ((physicalSobolevFourierEquiv38 (m : ℝ)).norm_map u).symm
  rw [hu]
  set x := physicalSobolevFourierEquiv38 (m : ℝ) u with hx
  set a := carrierCoe38 (m : ℝ) x with ha
  have h1 : ‖x‖ ^ 2 = ∑' n : ℤ, sobolevModeWeight (m : ℝ) n * ‖a n‖ ^ 2 :=
    weightedHilbert_norm_sq (sobolevModeWeight (m : ℝ)) (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x)
  have h2 : ‖ordinarySobolevCoordinates m u‖ ^ 2 =
      ∑' n : ℤ, sobolevModeWeight (m : ℝ) n * ‖-a (-n)‖ ^ 2 :=
    weightedHilbert_norm_sq (sobolevModeWeight (m : ℝ))
      (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from ordinarySobolevCoordinates m u)
  rw [h2, h1]
  rw [← (Equiv.neg ℤ).tsum_eq (fun n => sobolevModeWeight (m : ℝ) n * ‖a n‖ ^ 2)]
  refine tsum_congr (fun n => ?_)
  simp only [Equiv.neg_apply, norm_neg]
  have : sobolevModeWeight (m : ℝ) (-n) = sobolevModeWeight (m : ℝ) n := by
    simp [sobolevModeWeight, japaneseBracket]
  rw [this]

theorem ordinarySobolevCoordinates_coord (m : ℕ) (u : SobolevR m) (n : ℤ) :
    (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from ordinarySobolevCoordinates m u) n =
      -(carrierCoe38 (m : ℝ) (physicalSobolevFourierEquiv38 (m : ℝ) u) (-n)) := rfl

theorem ordinarySobolevCoordinates_sub (m : ℕ) (u v : SobolevR m) :
    ordinarySobolevCoordinates m (u - v) =
      ordinarySobolevCoordinates m u - ordinarySobolevCoordinates m v := by
  apply Subtype.ext
  funext n
  have h1 := ordinarySobolevCoordinates_coord m (u - v) n
  have h2 := ordinarySobolevCoordinates_coord m u n
  have h3 := ordinarySobolevCoordinates_coord m v n
  have e : carrierCoe38 (m : ℝ) (physicalSobolevFourierEquiv38 (m : ℝ) (u - v)) (-n) =
      carrierCoe38 (m : ℝ) (physicalSobolevFourierEquiv38 (m : ℝ) u) (-n) -
        carrierCoe38 (m : ℝ) (physicalSobolevFourierEquiv38 (m : ℝ) v) (-n) := by
    rw [map_sub]; rfl
  change (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from ordinarySobolevCoordinates m (u - v)) n =
    (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from ordinarySobolevCoordinates m u) n -
      (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from ordinarySobolevCoordinates m v) n
  rw [h1, h2, h3, e]; ring

theorem ordinarySobolevCoordinates_norm (m : ℕ) (u : SobolevR m) :
    ‖ordinarySobolevCoordinates m u‖ = ‖u‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (ordinarySobolevCoordinates_norm_sq m u)

theorem isometry_ordinarySobolevCoordinates (m : ℕ) :
    Isometry (ordinarySobolevCoordinates m) := by
  refine Isometry.of_dist_eq (fun u v => ?_)
  rw [dist_eq_norm, dist_eq_norm, ← ordinarySobolevCoordinates_sub, ordinarySobolevCoordinates_norm]

theorem continuous_ordinarySobolevCoordinates (m : ℕ) :
    Continuous (ordinarySobolevCoordinates m) :=
  (isometry_ordinarySobolevCoordinates m).continuous


theorem continuous_integral_cm : Continuous (fun g : C(PhysicalCircle, ℂ) => ∫ x, g x ∂spatialMeasure) := by
  refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul (fun g h => ?_))
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  have hg : Integrable (fun x => g x) spatialMeasure :=
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hh : Integrable (fun x => h x) spatialMeasure :=
    h.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_sub hg hh]
  have := norm_integral_le_of_norm_le_const (μ := spatialMeasure) (f := fun x => g x - h x)
    (C := ‖g - h‖) (Filter.Eventually.of_forall (fun x => by
      simpa using ContinuousMap.norm_coe_le_norm (g - h) x))
  rw [probReal_univ, mul_one] at this
  simpa using this

theorem continuous_sobolevJetContinuous (m : ℕ) (v : Jet) :
    Continuous (sobolevJetContinuous m v) := by
  unfold sobolevJetContinuous
  by_cases h : v.2 + 1 ≤ m
  · simp only [h, dite_true]
    exact (riccatiSobolevJetContinuousRepresentative_continuousRecovery30Eighth m v h).comp
      (continuous_ordinarySobolevCoordinates m)
  · simp only [h, dite_false]
    exact continuous_const

theorem continuous_integralMonomial (m : ℕ) (q : Jet →₀ ℕ) :
    Continuous (fun u : SobolevR m => integralMonomial q u) := by
  have hprod : Continuous (fun u : SobolevR m =>
      ∏ v ∈ q.support, (sobolevJetContinuous m v u) ^ q v) :=
    continuous_finset_prod _ (fun v _ => (continuous_sobolevJetContinuous m v).pow _)
  have := continuous_integral_cm.comp hprod
  refine this.congr (fun u => ?_)
  simp only [Function.comp, integralMonomial, ContinuousMap.coe_prod, ContinuousMap.coe_pow]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp [Finset.prod_apply]

theorem continuous_termsSum (m : ℕ) (terms : Finset ((Jet →₀ ℕ) × ℤ)) :
    Continuous (fun u : SobolevR m =>
      terms.sum (fun t => (t.2 : ℝ) * (integralMonomial t.1 u).re)) :=
  continuous_finset_sum _ (fun t _ =>
    continuous_const.mul (Complex.continuous_re.comp (continuous_integralMonomial m t.1)))

theorem continuous_topDerivativeEnergy (m : ℕ) :
    Continuous (fun u : SobolevR m => topDerivativeEnergy m u) := by
  unfold topDerivativeEnergy topDerivativeNorm
  exact ((riccatiSobolevIteratedDerivativeL2CLMRecovery30First m m le_rfl).continuous.comp
    (continuous_ordinarySobolevCoordinates m)).norm.pow 2

theorem continuous_signedCharge (m : ℕ) : Continuous (signedCharge m : SobolevR m → ℝ) := by
  unfold signedCharge normalizedRemainderIntegral
  exact (continuous_topDerivativeEnergy m).add
    (continuous_termsSum m ((normalizedChargeRemainder m).support.image (fun q => (q, (normalizedChargeRemainder m).coeff q)))
      |>.congr (fun u => by
        classical
        rw [Finset.sum_image (by intro a _ b _ hab; exact (Prod.mk.inj hab).1)]))


theorem toLp_norm_sq_eq_integral (f : C(PhysicalCircle, ℂ)) :
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

theorem hsource_of_represents {m : ℕ} (u : SobolevR m) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hper : Function.Periodic f 1) (hrep : RepresentsSmoothField u f hf hper) (n : ℤ) :
    (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from ordinarySobolevCoordinates m u) n =
      physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
        (riccatiSmoothPeriodicLiftContinuousMapRecovery30First f hf.continuous hper)) n := by
  have h := riccatiSobolevIteratedDerivativeL2CLMRecovery30First_fourier m 0 (Nat.zero_le m)
    (ordinarySobolevCoordinates m u) n
  have h2 : physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
        (riccatiSmoothPeriodicLiftContinuousMapRecovery30First f hf.continuous hper)) n =
      riccatiSobolevJetCoefficientL2Recovery28Second m 0 (ordinarySobolevCoordinates m u) n := by
    rw [← hrep]; exact h
  rw [h2]
  simp [riccatiSobolevJetCoefficientL2Recovery28Second]

theorem topDerivativeEnergy_smooth {m : ℕ} (u : SobolevR m) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hper : Function.Periodic f 1) (hrep : RepresentsSmoothField u f hf hper) :
    topDerivativeEnergy m u = smoothTopDerivativeEnergy m f := by
  have hagree := riccatiSobolevIteratedDerivativeL2_agrees_classicalRecovery30First
    m m le_rfl (ordinarySobolevCoordinates m u) f hf hper (hsource_of_represents u f hf hper hrep)
  set F := riccatiSmoothPeriodicLiftContinuousMapRecovery30First
    (iteratedDeriv m f)
    (by
      rw [iteratedDeriv_eq_iterate]
      exact (ContDiff.iterate_deriv m hf).continuous)
    (NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff f hf hper m) with hF
  unfold topDerivativeEnergy topDerivativeNorm smoothTopDerivativeEnergy
  rw [hagree, toLp_norm_sq_eq_integral]
  rw [intervalIntegral.integral_of_le zero_le_one]
  rw [← intervalIntegral.integral_of_le zero_le_one]
  have := NlsGge.HierarchyRiccati.unitIntervalIntegral_lift_eq_spatialHaar (fun y : PhysicalCircle => ‖F y‖ ^ 2)
  rw [← this]
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  symm
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  have ht' : t ∈ Set.Ioc (0 : ℝ) (0 + 1) := by simpa using ht
  simp only [hF, riccatiSmoothPeriodicLiftContinuousMapRecovery30First, ContinuousMap.coe_mk,
    AddCircle.liftIoc_coe_apply ht']


theorem sobolevJet_smooth {m : ℕ} (u : SobolevR m) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hper : Function.Periodic f 1) (hrep : RepresentsSmoothField u f hf hper)
    (v : Jet) (hk : v.2 + 1 ≤ m) (y : PhysicalCircle) :
    sobolevJetContinuous m v u y = AddCircle.liftIoc 1 0 (fun t => riccatiJetFunction f v t) y := by
  have hsm := lowerJetCLM_smooth38 m v.2 hk f hf hper (ordinarySobolevCoordinates m u)
    (hsource_of_represents u f hf hper hrep)
  have hy := congrFun hsm y
  unfold sobolevJetContinuous
  rw [dif_pos hk]
  unfold riccatiSobolevJetContinuousRepresentativeRecovery30Eighth
  change (if v.1 = true then star _ else _ : C(PhysicalCircle, ℂ)) y = _
  have e : (fun t => riccatiJetFunction f v t) =
      fun t => conjugateIf38 v.1 (iteratedDeriv v.2 f t) :=
    funext (riccatiJetFunction_eq_conjugateIf38 f v)
  rw [e]
  change _ = (fun t => conjugateIf38 v.1 (iteratedDeriv v.2 f t))
    ((AddCircle.equivIoc 1 0 y : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ)
  by_cases hb : v.1 = true
  · simp only [hb, if_true, ContinuousMap.star_apply, conjugateIf38_apply]
    rw [hy]
    rfl
  · have hb' : v.1 = false := by simpa using hb
    simp only [hb', Bool.false_eq_true, if_false, conjugateIf38_apply]
    rw [hy]
    rfl


theorem eval_monomial_one (f : ℝ → ℂ) (q : Jet →₀ ℕ) (t : ℝ) :
    riccatiJetEvaluation f t (MvPolynomial.monomial q (1 : ℤ)) =
      ∏ v ∈ q.support, (riccatiJetFunction f v t) ^ q v := by
  simp [riccatiJetEvaluation, polynomialEvaluation, MvPolynomial.eval₂Hom, MvPolynomial.eval₂_monomial,
    Finsupp.prod]

theorem integralMonomial_smooth {m : ℕ} (u : SobolevR m) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hper : Function.Periodic f 1) (hrep : RepresentsSmoothField u f hf hper)
    (q : Jet →₀ ℕ) (hq : ∀ v ∈ q.support, v.2 + 1 ≤ m) :
    integralMonomial q u = smoothIntegralMonomial q f := by
  unfold integralMonomial smoothIntegralMonomial
  have e1 : (fun y : PhysicalCircle => ∏ v ∈ q.support, (sobolevJetContinuous m v u y) ^ q v) =
      fun y => ∏ v ∈ q.support, (AddCircle.liftIoc 1 0 (fun t => riccatiJetFunction f v t) y) ^ q v :=
    funext (fun y => Finset.prod_congr rfl (fun v hv => by
      rw [sobolevJet_smooth u f hf hper hrep v (hq v hv) y]))
  rw [e1]
  rw [← NlsGge.HierarchyRiccati.unitIntervalIntegral_lift_eq_spatialHaar
    (fun y : PhysicalCircle => ∏ v ∈ q.support,
      (AddCircle.liftIoc 1 0 (fun t => riccatiJetFunction f v t) y) ^ q v)]
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  have ht' : t ∈ Set.Ioc (0 : ℝ) (0 + 1) := by simpa using ht
  simp only [eval_monomial_one, AddCircle.liftIoc_coe_apply ht']


theorem physicalOfSobolev_polynomial (m : ℕ) (p : PhysicalFourierPolynomial38 (m : ℝ)) :
    physicalOfSobolev (p : SobolevR m) = physicalFourierPolynomialField38 p := by
  apply physicalFourierL2.injective
  apply lp.ext
  funext n
  rw [physicalFourierL2_apply, physicalFourierL2_apply]
  unfold physicalOfSobolev
  rw [riccatiSobolevIteratedDerivativeL2CLMRecovery30First_fourier]
  simp only [riccatiSobolevJetCoefficientL2Recovery28Second, pow_zero, one_mul]
  rw [ordinarySobolevCoordinates_coord, physicalSobolevFourierEquiv38_polynomialCoeff,
    fourierSeq38_apply, neg_neg, neg_neg]

theorem exists_smooth_of_polynomial (m : ℕ) (p : PhysicalFourierPolynomial38 (m : ℝ)) :
    ∃ (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hper : Function.Periodic f 1),
      RepresentsSmoothField (p : SobolevR m) f hf hper := by
  classical
  set w := physicalFourierPolynomialField38 p with hw
  have hfin : {n : ℤ | fourierSeq38 w n ≠ 0}.Finite := p.toPhysicalSubmodule.2
  obtain ⟨B, hB⟩ := (hfin.image Int.natAbs).bddAbove
  have hbd : ∀ n : ℤ, physicalFourier w n ≠ 0 → n.natAbs ≤ B := by
    intro n hn
    have : fourierSeq38 w (-n) ≠ 0 := by
      rw [fourierSeq38_apply, neg_neg]; exact neg_ne_zero.2 hn
    have := hB ⟨-n, this, rfl⟩
    simpa using this
  set z : FourierPlane B := fun i => physicalFourier w (modeIndex B i) with hz
  have hwplane : w = planeL2 B z := by
    apply physicalFourierL2.injective
    apply lp.ext
    funext n
    rw [physicalFourierL2_apply, physicalFourierL2_apply, physicalFourier_planeL2]
    by_cases hn : n < -(B : ℤ) ∨ (B : ℤ) < n
    · rw [physicalFourier_planeField_outside B z n hn]
      by_contra hne
      have := hbd n hne
      omega
    · push_neg at hn
      have hi : n = modeIndex B ⟨(n + B).toNat, by omega⟩ := by
        simp only [modeIndex]; omega
      rw [hi, physicalFourier_planeField]
  have hsm : ContDiff ℝ ∞ (fun t : ℝ => planeField B z (t : PhysicalCircle)) := by
    have : (fun t : ℝ => planeField B z (t : PhysicalCircle)) =
        fun t => ∑ i : Fin (2 * B + 1), fourierRealTerm (modeIndex B i) (z i) t := rfl
    rw [this]
    exact ContDiff.sum (fun i _ => contDiff_fourierRealTerm (modeIndex B i) (z i))
  have hper : Function.Periodic (fun t : ℝ => planeField B z (t : PhysicalCircle)) 1 := by
    intro t
    simp only [AddCircle.coe_add, AddCircle.coe_period, add_zero]
  refine ⟨_, hsm, hper, ?_⟩
  unfold RepresentsSmoothField
  rw [physicalOfSobolev_polynomial, ← hw, hwplane]
  unfold planeL2
  congr 1
  ext y
  simp only [riccatiSmoothPeriodicLiftContinuousMapRecovery30First, ContinuousMap.coe_mk,
    planeContinuous]
  change planeField B z y = planeField B z ((AddCircle.equivIoc 1 0 y : ℝ) : PhysicalCircle)
  rw [AddCircle.coe_equivIoc]


theorem smooth_normal_form (m : ℕ) (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1) :
    smoothSignedCharge m u = smoothTopDerivativeEnergy m u +
      ∑ q ∈ (normalizedChargeRemainder m).support,
        (((normalizedChargeRemainder m).coeff q : ℤ) : ℝ) * (smoothIntegralMonomial q u).re := by
  classical
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
  rw [h1, h2, h3, intervalIntegral.integral_ofReal]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl (fun q _ => ?_)
  simp [Complex.mul_re]

theorem signedCharge_smooth (m : ℕ) (hm : 1 ≤ m) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hper : Function.Periodic f 1) (u : SobolevR m) (hrep : RepresentsSmoothField u f hf hper) :
    signedCharge m u = smoothSignedCharge m f := by
  rw [smooth_normal_form m f hf hper]
  unfold signedCharge normalizedRemainderIntegral
  rw [topDerivativeEnergy_smooth u f hf hper hrep]
  congr 1
  refine Finset.sum_congr rfl (fun q hq => ?_)
  obtain ⟨-, -, -, -, -, -, hv⟩ := riccati_normalized_remainder_monomial_grading m hm q hq
  rw [integralMonomial_smooth u f hf hper hrep q (fun v hv' => by have := hv v hv'; omega)]

theorem hierarchy_Hm_continuous (m : ℕ) (hm : 1 ≤ m) :
  Continuous (signedCharge m : SobolevR m → ℝ) ∧
  (∀ (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
      (hper : Function.Periodic f 1) (u : SobolevR m),
    RepresentsSmoothField u f hf hper →
      signedCharge m u = smoothSignedCharge m f) ∧
  ∀ terms : Finset ((Jet →₀ ℕ) × ℤ),
    ChargeNormalForm m terms →
      Continuous (fun u : SobolevR m =>
        terms.sum (fun t => (t.2 : ℝ) * (integralMonomial t.1 u).re)) ∧
      ∀ u : SobolevR m,
        signedCharge m u = topDerivativeEnergy m u +
          terms.sum (fun t => (t.2 : ℝ) * (integralMonomial t.1 u).re) := by
  refine ⟨continuous_signedCharge m, fun f hf hper u hrep => signedCharge_smooth m hm f hf hper u hrep, ?_⟩
  intro terms hnf
  refine ⟨continuous_termsSum m terms, ?_⟩
  have hcont1 : Continuous (signedCharge m : SobolevR m → ℝ) := continuous_signedCharge m
  have hcont2 : Continuous (fun u : SobolevR m => topDerivativeEnergy m u +
      terms.sum (fun t => (t.2 : ℝ) * (integralMonomial t.1 u).re)) :=
    (continuous_topDerivativeEnergy m).add (continuous_termsSum m terms)
  have hdense : DenseRange ((↑) : PhysicalFourierPolynomial38 (m : ℝ) → SobolevR m) :=
    UniformSpace.Completion.denseRange_coe
  have hag : (signedCharge m : SobolevR m → ℝ) ∘ ((↑) : PhysicalFourierPolynomial38 (m : ℝ) → SobolevR m) =
      (fun u : SobolevR m => topDerivativeEnergy m u +
        terms.sum (fun t => (t.2 : ℝ) * (integralMonomial t.1 u).re)) ∘
        ((↑) : PhysicalFourierPolynomial38 (m : ℝ) → SobolevR m) := by
    funext p
    obtain ⟨f, hf, hper, hrep⟩ := exists_smooth_of_polynomial m p
    simp only [Function.comp]
    rw [signedCharge_smooth m hm f hf hper _ hrep, hnf.2 f hf hper,
      topDerivativeEnergy_smooth _ f hf hper hrep]
    congr 1
    refine Finset.sum_congr rfl (fun t ht => ?_)
    have hv := (hnf.1 t ht).2.2.2
    rw [integralMonomial_smooth _ f hf hper hrep t.1 (fun v hv' => by have := hv v hv'; omega)]
  intro u
  exact congrFun (hdense.equalizer hcont1 hcont2 hag) u

end
end NlsGge.ThirdConsultation.M
