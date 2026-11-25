import Mathlib
import NlsGge.Atomic.M.M053
import NlsGge.Atomic.M.M006
import NlsGge.Hierarchy.A01Spectral38
import NlsGge.Atomic.LIB.LIB002
import NlsGge.Hierarchy.RiccatiLocalChargeReal38
import NlsGge.Hierarchy.RiccatiPeriodicIteratedDerivClosurePrerequisite
import NlsGge.ThirdConsultation.G1.Round5

/- MODD4 CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/ThirdConsultation/M/MOdd4Core.lean, namespace NlsGge.ThirdConsultation.MOdd.  SUPPORT (no packet
   increment) for Pro's bridge odd_hierarchy_charge_eq_signedCharge (followup13 STATEMENTS/M.md:1805), general m,
   SMOOTH CASE.  For a smooth 1-periodic f and its physical L² field L f = smoothL2_38 f:
     * weakDerivative^[j] (L f) = L (iteratedDeriv j f) for EVERY j (no Sobolev hypothesis: the multiplier sequence of
       L f is exactly the reflected coefficient sequence of L f', by LIB002 at order one, so the `Memℓp` branch of the
       weakDerivative definition is taken);
     * star (L f) = L (star ∘ f);  cover representatives of L g agree with g a.e. on (0,1];
     * for φ : SobolevC (2m) with toPotPair φ = realSlice (L f):
         hierarchyCharge φ (2m+1) = ((-1)^(m+1) * smoothSignedCharge m f : ℂ),
       and, when u : SobolevR m is represented by f (M006 RepresentsSmoothField), Pro's head
         hierarchyCharge φ (2m+1) = ((-1)^(m+1) * signedCharge m u : ℂ).
   Route: landed M053 WKB_hierarchy_coefficients_complex + integralRiccatiCoefficient_eq_polyIntegral, the jet
   identification above, the definition of formalChargeIntegrand, formalChargeIntegrand_integral_eq_re38 and M006
   signedCharge_smooth.
   Own imports: Mathlib, Atomic/M/M053, Atomic/M/M006, Hierarchy/A01Spectral38, Atomic/LIB/LIB002,
   Hierarchy/RiccatiLocalChargeReal38, Hierarchy/RiccatiPeriodicIteratedDerivClosurePrerequisite, G1/Round5. -/
set_option autoImplicit false

open MeasureTheory
open scoped ContDiff
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign NlsGge.HierarchyRiccati.Core

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

namespace NlsGge.ThirdConsultation.MOdd
noncomputable section

theorem contDiff_iteratedDeriv_smooth (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv k g) := by
  rw [iteratedDeriv_eq_iterate]
  exact hg.iterate_deriv k

theorem smoothL2_38_congr {g h : ℝ → ℂ} (e : g = h) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (hpg : Function.Periodic g 1) (hph : Function.Periodic h 1) :
    smoothL2_38 g hg hpg = smoothL2_38 h hh hph := by
  subst e
  rfl

theorem reflectedFourierL2_smoothL2_38 (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hper : Function.Periodic g 1) (n : ℤ) :
    reflectedFourierL2 (smoothL2_38 g hg hper) n =
      -fourierCoeffOn (by norm_num : (0 : ℝ) < 1) g (-n) := by
  rw [reflectedFourierL2_apply]
  unfold reflectedFourier
  rw [smoothL2_38, physicalFourier_liftContinuousMap_eq_fourierCoeffOnRecovery30First]

/-- One weak derivative of a smooth lift is the lift of the classical derivative. -/
theorem weakDerivative_smoothL2_38 (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hper : Function.Periodic g 1) :
    weakDerivative (smoothL2_38 g hg hper) =
      smoothL2_38 (iteratedDeriv 1 g) (contDiff_iteratedDeriv_smooth g hg 1)
        (NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff g hg hper 1) := by
  have hd : ∀ n : ℤ,
      (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * reflectedFourierL2 (smoothL2_38 g hg hper) n =
        reflectedFourierL2 (smoothL2_38 (iteratedDeriv 1 g) (contDiff_iteratedDeriv_smooth g hg 1)
          (NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff g hg hper 1)) n := by
    intro n
    rw [reflectedFourierL2_smoothL2_38, reflectedFourierL2_smoothL2_38,
      NlsGge.Atomic.LIB002.fourierCoeffOn_iteratedDeriv_of_smooth_periodic _ g hg hper 1 (-n)]
    simp only [NlsGge.Atomic.LIB002.fourierMultiplier, pow_one]
    push_cast
    ring
  unfold weakDerivative
  dsimp only
  split_ifs with h
  · apply reflectedFourierL2.injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    ext n
    exact hd n
  · refine absurd ?_ h
    convert lp.memℓp (reflectedFourierL2 (smoothL2_38 (iteratedDeriv 1 g)
      (contDiff_iteratedDeriv_smooth g hg 1)
      (NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff g hg hper 1))) using 1
    funext n
    exact hd n

/-- Iterated weak derivatives of a smooth lift are lifts of the classical iterated derivatives (every order). -/
theorem weakDerivative_iterate_smoothL2_38 (j : ℕ) :
    ∀ (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hper : Function.Periodic g 1),
      weakDerivative^[j] (smoothL2_38 g hg hper) =
        smoothL2_38 (iteratedDeriv j g) (contDiff_iteratedDeriv_smooth g hg j)
          (NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff g hg hper j) := by
  induction j with
  | zero =>
    intro g hg hper
    exact smoothL2_38_congr (iteratedDeriv_zero).symm _ _ _ _
  | succ j ih =>
    intro g hg hper
    rw [Function.iterate_succ_apply, weakDerivative_smoothL2_38, ih]
    exact smoothL2_38_congr (by rw [iteratedDeriv_one, iteratedDeriv_succ']) _ _ _ _

theorem contDiff_star_smooth (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x => star (g x)) :=
  ((starL ℝ : ℂ ≃L⋆[ℝ] ℂ).toContinuousLinearMap).contDiff.comp hg

theorem periodic_star_smooth (g : ℝ → ℂ) (hper : Function.Periodic g 1) :
    Function.Periodic (fun x => star (g x)) 1 := fun x => congrArg star (hper x)

theorem star_smoothL2_38 (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hper : Function.Periodic g 1) :
    star (smoothL2_38 g hg hper) =
      smoothL2_38 (fun x => star (g x)) (contDiff_star_smooth g hg) (periodic_star_smooth g hper) := by
  apply Lp.ext
  have h1 := Lp.coeFn_star (smoothL2_38 g hg hper)
  have h2 : ⇑(smoothL2_38 g hg hper) =ᵐ[spatialMeasure]
      ⇑(riccatiSmoothPeriodicLiftContinuousMapRecovery30First g hg.continuous hper) :=
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure _
  have h3 : ⇑(smoothL2_38 (fun x => star (g x)) (contDiff_star_smooth g hg)
      (periodic_star_smooth g hper)) =ᵐ[spatialMeasure]
      ⇑(riccatiSmoothPeriodicLiftContinuousMapRecovery30First (fun x => star (g x))
        (contDiff_star_smooth g hg).continuous (periodic_star_smooth g hper)) :=
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure _
  filter_upwards [h1, h2, h3] with x e1 e2 e3
  rw [e1, Pi.star_apply, e2, e3]
  rfl

/-- The cover representative of a smooth lift is the function itself a.e. on `(0,1]`. -/
theorem coverRep38_smoothL2_38 (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hper : Function.Periodic g 1) :
    coverRep38 (smoothL2_38 g hg hper) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] g :=
  ae_restrict_of_ae_restrict_of_subset (Set.Ioc_subset_Ioc_right (by norm_num))
    (smoothL2_38_cover_ae g hg hper)

/-- The weak-derivative jets of a pair on the real slice of a smooth lift are the classical jets. -/
theorem coverRep38_hierarchyJetL2_smooth {N : ℕ} (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hper : Function.Periodic f 1)
    (hpair : NlsGge.ThirdConsultation.KSPS.toPotPair φ = realSlice (smoothL2_38 f hf hper)) (v : Jet) :
    coverRep38 (NlsGge.ThirdConsultation.M.hierarchyJetL2 φ v)
      =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] riccatiJetFunction f v := by
  obtain ⟨b, j⟩ := v
  cases b with
  | false =>
    have e : NlsGge.ThirdConsultation.M.hierarchyJetL2 φ (false, j) =
        weakDerivative^[j] (smoothL2_38 f hf hper) := by
      simp only [NlsGge.ThirdConsultation.M.hierarchyJetL2, hpair, realSlice_apply]
      rfl
    rw [e, weakDerivative_iterate_smoothL2_38]
    exact coverRep38_smoothL2_38 _ _ _
  | true =>
    have e : NlsGge.ThirdConsultation.M.hierarchyJetL2 φ (true, j) =
        weakDerivative^[j] (smoothL2_38 (fun x => star (f x)) (contDiff_star_smooth f hf)
          (periodic_star_smooth f hper)) := by
      simp only [NlsGge.ThirdConsultation.M.hierarchyJetL2, hpair, realSlice_apply]
      rw [← star_smoothL2_38]
      rfl
    rw [e, weakDerivative_iterate_smoothL2_38]
    exact coverRep38_smoothL2_38 _ _ _

/-- Smooth case: the source odd hierarchy charge is the signed smooth local charge. -/
theorem hierarchyCharge_odd_smooth (m : ℕ) (hm : 1 ≤ m) (φ : NlsGge.ThirdConsultation.KSPS.SobolevC (2 * m))
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hper : Function.Periodic f 1)
    (hpair : NlsGge.ThirdConsultation.KSPS.toPotPair φ = realSlice (smoothL2_38 f hf hper)) :
    NlsGge.ThirdConsultation.M.hierarchyCharge φ ⟨2 * m + 1, by omega, by omega⟩ =
      (((-1 : ℝ) ^ (m + 1) * NlsGge.ThirdConsultation.M.smoothSignedCharge m f : ℝ) : ℂ) := by
  have h1 := NlsGge.ThirdConsultation.M.WKB_hierarchy_coefficients_complex (2 * m) φ (2 * m + 1)
    (by omega) (by omega)
  rw [if_neg (by omega)] at h1
  have h2 : NlsGge.ThirdConsultation.M.hierarchyCharge φ ⟨2 * m + 1, by omega, by omega⟩ =
      NlsGge.ThirdConsultation.KSPS.integralRiccatiCoefficient φ (2 * m + 1) := by
    rw [h1]
    rfl
  rw [h2, NlsGge.ThirdConsultation.M.integralRiccatiCoefficient_eq_polyIntegral (2 * m) φ (2 * m + 1)
    (by omega) (by omega)]
  have hall : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      ∀ v : Jet, coverRep38 (NlsGge.ThirdConsultation.M.hierarchyJetL2 φ v) x = riccatiJetFunction f v x :=
    ae_all_iff.2 (fun v => coverRep38_hierarchyJetL2_smooth φ f hf hper hpair v)
  have h0 : coverRep38 (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1
      =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] f := by
    rw [hpair, realSlice_fst]
    exact coverRep38_smoothL2_38 f hf hper
  have hae : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      coverRep38 (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1 x *
          polynomialEvaluation (fun v => coverRep38 (NlsGge.ThirdConsultation.M.hierarchyJetL2 φ v) x)
            (p (2 * m + 1)) =
        riccatiJetEvaluation f x (MvPolynomial.X (false, 0) * p (2 * m + 1)) := by
    filter_upwards [hall, h0] with x hx hx0
    rw [hx0, show (fun v => coverRep38 (NlsGge.ThirdConsultation.M.hierarchyJetL2 φ v) x) =
      fun v => riccatiJetFunction f v x from funext hx]
    simp only [riccatiJetEvaluation, map_mul, polynomialEvaluation_X]
    rfl
  rw [ae_restrict_iff' measurableSet_Ioc] at hae
  rw [intervalIntegral.integral_congr_ae (hae.mono fun x hx hmem =>
    hx (by rwa [Set.uIoc_of_le zero_le_one] at hmem))]
  have hs : ((-1 : ℂ) ^ (m + 1)) * (-1) ^ (m + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  have hpt : ∀ x : ℝ, riccatiJetEvaluation f x (MvPolynomial.X (false, 0) * p (2 * m + 1)) =
      (-1 : ℂ) ^ (m + 1) * riccatiJetEvaluation f x (formalChargeIntegrand m) := by
    intro x
    unfold formalChargeIntegrand
    simp only [riccatiJetEvaluation, map_mul, polynomialEvaluation_C]
    push_cast
    linear_combination
      (-(polynomialEvaluation (fun v => riccatiJetFunction f v x) (MvPolynomial.X (false, 0)) *
        polynomialEvaluation (fun v => riccatiJetFunction f v x) (p (2 * m + 1)))) * hs
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, formalChargeIntegrand_integral_eq_re38 m f hf hper]
  unfold NlsGge.ThirdConsultation.M.smoothSignedCharge
  push_cast
  rfl

/-- Pro's head in the smooth case: `u` represented by a smooth periodic `f` (M006 `RepresentsSmoothField`). -/
theorem odd_hierarchy_charge_eq_signedCharge_smooth (m : ℕ) (hm : 1 ≤ m)
    (u : NlsGge.ThirdConsultation.M.SobolevR m)
    (φ : NlsGge.ThirdConsultation.KSPS.SobolevC (2 * m))
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hper : Function.Periodic f 1)
    (hrep : NlsGge.ThirdConsultation.M.RepresentsSmoothField u f hf hper)
    (hpair : NlsGge.ThirdConsultation.KSPS.toPotPair φ =
      realSlice (NlsGge.ThirdConsultation.M.physicalOfSobolev u)) :
    NlsGge.ThirdConsultation.M.hierarchyCharge φ ⟨2 * m + 1, by omega, by omega⟩ =
      (((-1 : ℝ) ^ (m + 1) * NlsGge.ThirdConsultation.M.signedCharge m u : ℝ) : ℂ) := by
  have hpair' : NlsGge.ThirdConsultation.KSPS.toPotPair φ = realSlice (smoothL2_38 f hf hper) := by
    rw [hpair, hrep]
    rfl
  rw [hierarchyCharge_odd_smooth m hm φ f hf hper hpair',
    NlsGge.ThirdConsultation.M.signedCharge_smooth m hm f hf hper u hrep]

end
end NlsGge.ThirdConsultation.MOdd
