import Mathlib
import NlsGge.Atomic.F.F034
import NlsGge.Atomic.F.F027
import NlsGge.Atomic.F.F035
import NlsGge.Hierarchy.RiccatiMonomialSobolevCMM38
import NlsGge.Hierarchy.GaussianTailContractionsF06C2_38
import NlsGge.Hierarchy.RiccatiQ6CuspNegative38
import NlsGge.Hierarchy.RiccatiRealTrigApproxC2_38
import NlsGge.Hierarchy.RiccatiSmoothDenseSobolev38
import NlsGge.Schur.ActualSchurRealTypeSymmetry38V1

                                                                                                                               
                                                                                                                                                                   
                                                                                                                                                             
                                                                                                                                                                 


                                                                                                                                  
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.F

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance


abbrev RealH2 := {y : SobolevHilbert (2 : ℝ) //
  ∀ n : ℤ, sobolevCoe 2 y (-n) = star (sobolevCoe 2 y n)}

def quarticH2 (y : RealH2) : ℝ :=
  ∫ t : PhysicalCircle,
    14 * ((lowerJetLinfty38 2 (false, 0) (toCarrier38 2 y.val) :
      PhysicalCircle → ℂ) t).re ^ 2 *
      ((topJetL2_38 2 (false, 2) (toCarrier38 2 y.val) :
        PhysicalCircle → ℂ) t).re ^ 2 -
    7 * ((lowerJetLinfty38 2 (false, 1) (toCarrier38 2 y.val) :
      PhysicalCircle → ℂ) t).re ^ 4 ∂spatialMeasure

namespace F036Aux

abbrev E2 : Type := SobolevCarrier38 ((2 : ℕ) : ℝ)

def reC : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM

def reLp (p : ℝ≥0∞) [Fact (1 ≤ p)] : Lp ℂ p spatialMeasure →L[ℝ] Lp ℂ p spatialMeasure :=
  reC.compLpL p spatialMeasure

theorem reLp_ae (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : Lp ℂ p spatialMeasure) :
    (reLp p f : PhysicalCircle → ℂ) =ᵐ[spatialMeasure] fun t => (((f t).re : ℝ) : ℂ) :=
  reC.coeFn_compLpL f

def T2 : E2 →L[ℝ] Lp ℂ 2 spatialMeasure := (reLp 2).comp (topJetL2_38 2 (false, 2))
def L0 : E2 →L[ℝ] Lp ℂ ∞ spatialMeasure := (reLp ∞).comp (lowerJetLinfty38 2 (false, 0))
def L1 : E2 →L[ℝ] Lp ℂ ∞ spatialMeasure := (reLp ∞).comp (lowerJetLinfty38 2 (false, 1))

def b1 : Fin 4 → Bool := ![false, false, true, true]
def b2 : Fin 4 → Bool := fun _ => false

theorem hc1 : highCount38 b1 ≤ 2 := by
  simp [highCount38, b1]

theorem hc2 : highCount38 b2 ≤ 2 := by
  simp [highCount38, b2]

def A1 : (i : Fin 4) → E2 →L[ℝ] Lp ℂ (slotExponent38 (b1 i)) spatialMeasure :=
  fun i => slotMapOfBool38 (b1 i) T2 L0

def A2 : (i : Fin 4) → E2 →L[ℝ] Lp ℂ (slotExponent38 (b2 i)) spatialMeasure :=
  fun i => slotMapOfBool38 (b2 i) T2 L1

def Q1 (x : E2) : ℝ :=
  (integrateProductLp38 (highCount38 b1) hc1 (mixedProduct38 b1 hc1 A1 (fun _ => x))).re

def Q2 (x : E2) : ℝ :=
  (integrateProductLp38 (highCount38 b2) hc2 (mixedProduct38 b2 hc2 A2 (fun _ => x))).re

theorem continuous_Q1 : Continuous Q1 := by
  unfold Q1
  exact Complex.continuous_re.comp ((integrateProductLp38 (highCount38 b1) hc1).continuous.comp
    ((mixedProduct38 b1 hc1 A1).cont.comp (continuous_pi fun _ => continuous_id)))

theorem continuous_Q2 : Continuous Q2 := by
  unfold Q2
  exact Complex.continuous_re.comp ((integrateProductLp38 (highCount38 b2) hc2).continuous.comp
    ((mixedProduct38 b2 hc2 A2).cont.comp (continuous_pi fun _ => continuous_id)))

theorem Q1_eq (x : E2) :
    Q1 x = ∫ t : PhysicalCircle,
      ((lowerJetLinfty38 2 (false, 0) x : PhysicalCircle → ℂ) t).re ^ 2 *
        ((topJetL2_38 2 (false, 2) x : PhysicalCircle → ℂ) t).re ^ 2 ∂spatialMeasure := by
  unfold Q1
  rw [integrateProductLp_eq_integral38]
  have hre := integral_re (𝕜 := ℂ) (productLp_integrable38 (highCount38 b1) hc1
    (mixedProduct38 b1 hc1 A1 (fun _ => x)))
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  apply integral_congr_ae
  filter_upwards [mixedProduct_ae38 4 b1 hc1 A1 (fun _ => x),
    reLp_ae ∞ (lowerJetLinfty38 2 (false, 0) x), reLp_ae 2 (topJetL2_38 2 (false, 2) x)] with t h1 h2 h3
  have e0 : (A1 0) x = L0 x := rfl
  have e1 : (A1 1) x = L0 x := rfl
  have e2 : (A1 2) x = T2 x := rfl
  have e3 : (A1 3) x = T2 x := rfl
  have h2' : (L0 x : PhysicalCircle → ℂ) t = (((lowerJetLinfty38 2 (false, 0) x : PhysicalCircle → ℂ) t).re : ℂ) := h2
  have h3' : (T2 x : PhysicalCircle → ℂ) t = (((topJetL2_38 2 (false, 2) x : PhysicalCircle → ℂ) t).re : ℂ) := h3
  rw [h1, Fin.prod_univ_four, e0, e1, e2, e3, h2', h3']
  norm_cast
  ring

theorem Q2_eq (x : E2) :
    Q2 x = ∫ t : PhysicalCircle,
      ((lowerJetLinfty38 2 (false, 1) x : PhysicalCircle → ℂ) t).re ^ 4 ∂spatialMeasure := by
  unfold Q2
  rw [integrateProductLp_eq_integral38]
  have hre := integral_re (𝕜 := ℂ) (productLp_integrable38 (highCount38 b2) hc2
    (mixedProduct38 b2 hc2 A2 (fun _ => x)))
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  apply integral_congr_ae
  filter_upwards [mixedProduct_ae38 4 b2 hc2 A2 (fun _ => x),
    reLp_ae ∞ (lowerJetLinfty38 2 (false, 1) x)] with t h1 h2
  have e : ∀ i : Fin 4, (A2 i) x = L1 x := fun i => rfl
  have h2' : (L1 x : PhysicalCircle → ℂ) t = (((lowerJetLinfty38 2 (false, 1) x : PhysicalCircle → ℂ) t).re : ℂ) := h2
  rw [h1]
  simp only [e, Finset.prod_const, Finset.card_univ, Fintype.card_fin, h2']
  norm_cast

theorem integrable_first (x : E2) :
    Integrable (fun t : PhysicalCircle =>
      ((lowerJetLinfty38 2 (false, 0) x : PhysicalCircle → ℂ) t).re ^ 2 *
        ((topJetL2_38 2 (false, 2) x : PhysicalCircle → ℂ) t).re ^ 2) spatialMeasure := by
  have hi := (mixedProduct_integrable38 b1 hc1 A1 (fun _ => x)).re
  refine hi.congr ?_
  filter_upwards [reLp_ae ∞ (lowerJetLinfty38 2 (false, 0) x),
    reLp_ae 2 (topJetL2_38 2 (false, 2) x)] with t h2 h3
  have e0 : (A1 0) x = L0 x := rfl
  have e1 : (A1 1) x = L0 x := rfl
  have e2 : (A1 2) x = T2 x := rfl
  have e3 : (A1 3) x = T2 x := rfl
  have h2' : (L0 x : PhysicalCircle → ℂ) t = (((lowerJetLinfty38 2 (false, 0) x : PhysicalCircle → ℂ) t).re : ℂ) := h2
  have h3' : (T2 x : PhysicalCircle → ℂ) t = (((topJetL2_38 2 (false, 2) x : PhysicalCircle → ℂ) t).re : ℂ) := h3
  show (∏ i, (A1 i) x t).re = _
  rw [Fin.prod_univ_four, e0, e1, e2, e3, h2', h3']
  norm_cast
  ring

theorem integrable_second (x : E2) :
    Integrable (fun t : PhysicalCircle =>
      ((lowerJetLinfty38 2 (false, 1) x : PhysicalCircle → ℂ) t).re ^ 4) spatialMeasure := by
  have hi := (mixedProduct_integrable38 b2 hc2 A2 (fun _ => x)).re
  refine hi.congr ?_
  filter_upwards [reLp_ae ∞ (lowerJetLinfty38 2 (false, 1) x)] with t h2
  have e : ∀ i : Fin 4, (A2 i) x = L1 x := fun i => rfl
  have h2' : (L1 x : PhysicalCircle → ℂ) t = (((lowerJetLinfty38 2 (false, 1) x : PhysicalCircle → ℂ) t).re : ℂ) := h2
  show (∏ i, (A2 i) x t).re = _
  simp only [e, Finset.prod_const, Finset.card_univ, Fintype.card_fin, h2']
  norm_cast

theorem quarticH2_eq (y : RealH2) :
    quarticH2 y = 14 * Q1 (toCarrier38 2 y.val) - 7 * Q2 (toCarrier38 2 y.val) := by
  unfold quarticH2
  rw [Q1_eq, Q2_eq, ← integral_const_mul, ← integral_const_mul, ← integral_sub]
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by ring
  · exact (integrable_first _).const_mul 14
  · exact (integrable_second _).const_mul 7

theorem low_ae (k : ℕ) (hk : k + 1 ≤ 2) (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) (x : SobolevHilbert ((2 : ℕ) : ℝ))
    (hsource : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight ((2 : ℕ) : ℝ)) from x) n =
        physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)) n) :
    (lowerJetLinfty38 2 (false, k) (toCarrier38 ((2 : ℕ) : ℝ) x) : PhysicalCircle → ℂ)
      =ᵐ[spatialMeasure] AddCircle.liftIoc 1 0 (iteratedDeriv k u) := by
  have hL := lowerJetCLM_smooth38 2 k hk u hu hper x hsource
  simp only [lowerJetLinfty38, hk, dite_true]
  change (conjugateIfLp38 false ∞
      (ContinuousMap.toLp ∞ spatialMeasure ℝ (E := ℂ)
        (riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth 2 k hk x)) :
        PhysicalCircle → ℂ) =ᵐ[spatialMeasure] _
  filter_upwards [conjugateIfLp38_ae false ∞ _, ContinuousMap.coeFn_toLp
    (p := ∞) (𝕜 := ℝ) spatialMeasure
    (riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth 2 k hk x)]
    with t ht hl
  rw [ht, hl, hL]
  rfl

theorem top_ae (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) (x : SobolevHilbert ((2 : ℕ) : ℝ))
    (hsource : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight ((2 : ℕ) : ℝ)) from x) n =
        physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)) n) :
    (topJetL2_38 2 (false, 2) (toCarrier38 ((2 : ℕ) : ℝ) x) : PhysicalCircle → ℂ)
      =ᵐ[spatialMeasure] AddCircle.liftIoc 1 0 (iteratedDeriv 2 u) := by
  have hD := riccatiSobolevIteratedDerivativeL2_agrees_classicalRecovery30First
    2 2 le_rfl x u hu hper hsource
  change (conjugateIfLp38 false 2
      (riccatiSobolevIteratedDerivativeL2CLMRecovery30First 2 2 le_rfl x) :
        PhysicalCircle → ℂ) =ᵐ[spatialMeasure] _
  rw [hD]
  filter_upwards [conjugateIfLp38_ae false 2 _, ContinuousMap.coeFn_toLp
    (p := 2) (𝕜 := ℂ) spatialMeasure
    (riccatiSmoothPeriodicLiftContinuousMapRecovery30First (iteratedDeriv 2 u)
      (by
        rw [iteratedDeriv_eq_iterate]
        exact (ContDiff.iterate_deriv 2 hu).continuous)
      (NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff u hu hper 2))]
    with t ht hl
  rw [ht, hl]
  rfl

theorem deriv_re_of_diff (v : ℝ → ℂ) (hv : Differentiable ℝ v) :
    deriv (fun r => (v r).re) = fun r => (deriv v r).re := by
  funext r
  have h := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt r (hv r).hasDerivAt)
  exact h.deriv

theorem iteratedDeriv_re_one (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) :
    deriv (fun r => (u r).re) = fun r => (iteratedDeriv 1 u r).re := by
  rw [deriv_re_of_diff u (hu.differentiable (by simp))]
  simp [iteratedDeriv_one]

theorem iteratedDeriv_re_two (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) :
    iteratedDeriv 2 (fun r => (u r).re) = fun r => (iteratedDeriv 2 u r).re := by
  have hdu : Differentiable ℝ (deriv u) := by
    exact ((contDiff_infty_iff_deriv.1 hu).2).differentiable (by simp)
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_re_of_diff u (hu.differentiable (by simp))]
  rw [deriv_re_of_diff (deriv u) hdu]
  funext r
  simp [iteratedDeriv_succ, iteratedDeriv_one]

theorem smooth_integral (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) (x : SobolevHilbert ((2 : ℕ) : ℝ))
    (hsource : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight ((2 : ℕ) : ℝ)) from x) n =
        physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)) n) :
    (∫ t : PhysicalCircle,
      14 * ((lowerJetLinfty38 2 (false, 0) (toCarrier38 ((2 : ℕ) : ℝ) x) :
        PhysicalCircle → ℂ) t).re ^ 2 *
        ((topJetL2_38 2 (false, 2) (toCarrier38 ((2 : ℕ) : ℝ) x) :
          PhysicalCircle → ℂ) t).re ^ 2 -
      7 * ((lowerJetLinfty38 2 (false, 1) (toCarrier38 ((2 : ℕ) : ℝ) x) :
        PhysicalCircle → ℂ) t).re ^ 4 ∂spatialMeasure) =
    q6QuarticF38 (fun r => (u r).re) := by
  have h0 := low_ae 0 (by norm_num) u hu hper x hsource
  have h1 := low_ae 1 (by norm_num) u hu hper x hsource
  have h2 := top_ae u hu hper x hsource
  have hu1 := NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff u hu hper 1
  have hu2 := NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff u hu hper 2
  rw [integral_congr_ae (g := fun t : PhysicalCircle =>
      14 * ((AddCircle.liftIoc 1 0 (iteratedDeriv 0 u) t).re) ^ 2 *
        ((AddCircle.liftIoc 1 0 (iteratedDeriv 2 u) t).re) ^ 2 -
      7 * ((AddCircle.liftIoc 1 0 (iteratedDeriv 1 u) t).re) ^ 4)
    (by filter_upwards [h0, h1, h2] with t a b c; rw [a, b, c])]
  rw [← NlsGge.HierarchyRiccati.unitIntervalIntegral_lift_eq_spatialHaar (fun t : PhysicalCircle =>
      14 * ((AddCircle.liftIoc 1 0 (iteratedDeriv 0 u) t).re) ^ 2 *
        ((AddCircle.liftIoc 1 0 (iteratedDeriv 2 u) t).re) ^ 2 -
      7 * ((AddCircle.liftIoc 1 0 (iteratedDeriv 1 u) t).re) ^ 4)]
  unfold q6QuarticF38
  apply intervalIntegral.integral_congr
  intro r hr
  rw [Set.uIcc_of_le zero_le_one] at hr
  simp only
  rw [liftIoc_unit_eq38 _ (by simpa using hper) hr, liftIoc_unit_eq38 _ hu2 hr,
    liftIoc_unit_eq38 _ hu1 hr, iteratedDeriv_re_two u hu, iteratedDeriv_re_one u hu]
  simp only [iteratedDeriv_zero]

end F036Aux

open F036Aux in
theorem F036_continuous : Continuous quarticH2 := by
  have h : quarticH2 = fun y : RealH2 => 14 * Q1 (toCarrier38 2 y.val) - 7 * Q2 (toCarrier38 2 y.val) :=
    funext quarticH2_eq
  rw [h]
  have hc : Continuous (fun y : RealH2 => (toCarrier38 2 y.val : E2)) := continuous_subtype_val
  exact (continuous_const.mul (continuous_Q1.comp hc)).sub (continuous_const.mul (continuous_Q2.comp hc))

open F036Aux in
theorem F036_integrable (y : RealH2) :
    Integrable (fun t : PhysicalCircle =>
        ((lowerJetLinfty38 2 (false, 0) (toCarrier38 2 y.val) :
          PhysicalCircle → ℂ) t).re ^ 2 *
        ((topJetL2_38 2 (false, 2) (toCarrier38 2 y.val) :
          PhysicalCircle → ℂ) t).re ^ 2) spatialMeasure ∧
      Integrable (fun t : PhysicalCircle =>
        ((lowerJetLinfty38 2 (false, 1) (toCarrier38 2 y.val) :
          PhysicalCircle → ℂ) t).re ^ 4) spatialMeasure :=
  ⟨integrable_first _, integrable_second _⟩

open F036Aux in
theorem F036_plane (y : RealH2) (N : ℕ) (z : FourierPlane N)
    (h : y.val = planeElement38 (2 : ℝ) N z) :
    quarticH2 y = q6QuarticF38 (fun x => (planeReal N z x).re) := by
  have hs : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight ((2 : ℕ) : ℝ)) from y.val) n =
        physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First (planeReal N z)
            (planeReal_smooth38 N z).continuous (planeReal_periodic N z))) n := by
    intro n
    rw [h]
    exact planeElement_hsource38 2 N z n
  exact smooth_integral (planeReal N z) (planeReal_smooth38 N z) (planeReal_periodic N z) y.val hs

theorem planeReal_trig (d : ℤ → ℂ) (N : ℕ) (x : ℝ) :
    planeReal N (fun i => d (modeIndex N i)) x = trigSum38 d N x := by
  unfold planeReal planeField trigSum38
  have himg : Finset.Icc (-(N : ℤ)) N = Finset.univ.image (modeIndex N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro h; exact modeIndex_covers N n h.1 h.2
    · rintro ⟨i, rfl⟩; exact modeIndex_bounds N i
  rw [himg, Finset.sum_image (fun a _ b _ h => modeIndex_injective N h)]
  rfl

theorem trigSum_im_zero (d : ℤ → ℂ) (hd : ∀ n, d (-n) = star (d n)) (N : ℕ) (x : ℝ) :
    (trigSum38 d N x).im = 0 := by
  have ht : ∀ n : ℤ, star (fourierRealTerm n (d n) x) = fourierRealTerm (-n) (d (-n)) x := by
    intro n
    rw [fourierRealTerm_eq_exp38, fourierRealTerm_eq_exp38, hd, star_mul']
    congr 1
    rw [Complex.star_def, ← Complex.exp_conj]
    apply congrArg
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hstar : star (trigSum38 d N x) = trigSum38 d N x := by
    unfold trigSum38
    rw [star_sum]
    simp only [ht]
    exact Finset.sum_equiv (Equiv.neg ℤ) (fun n => by simp only [Finset.mem_Icc, Equiv.neg_apply]; omega) (fun n _ => rfl)
  have := Complex.conj_eq_iff_im.1 (by simpa [Complex.star_def] using hstar)
  exact this

theorem finiteSeq_zero_off (N : ℕ) (z : FourierPlane N) (n : ℤ)
    (hn : n ∉ Finset.univ.image (modeIndex N)) : finiteSeq38 (modeIndex N) z n = 0 := by
  unfold finiteSeq38
  refine Finset.sum_eq_zero fun k _ => ?_
  have hne : modeIndex N k ≠ n := fun h => hn (Finset.mem_image.2 ⟨k, Finset.mem_univ _, h⟩)
  simp [hne]

theorem trunc_eq_plane (y : SobolevHilbert (2 : ℝ)) (N : ℕ) :
    truncSobolev38 2 N y = planeElement38 (2 : ℝ) N (fun i => sobolevCoe 2 y (modeIndex N i)) := by
  apply Subtype.ext
  funext n
  by_cases hn : n ∈ Finset.Icc (-(N : ℤ)) N
  · rw [Finset.mem_Icc] at hn
    obtain ⟨i, hi⟩ := modeIndex_covers N n hn.1 hn.2
    subst hi
    have h1 := truncSobolev38_apply 2 N y (modeIndex N i)
    have h2 := finiteElement_apply38 (2 : ℝ) (modeIndex N) (fun i => sobolevCoe 2 y (modeIndex N i)) (modeIndex_injective N) (modeIndex N i)
    rw [if_pos (Finset.mem_Icc.2 (modeIndex_bounds N i))] at h1
    rw [finiteSeq_of_inj38 _ _ (modeIndex_injective N)] at h2
    exact h1.trans h2.symm
  · have h1 := truncSobolev38_apply 2 N y n
    have h2 := finiteElement_apply38 (2 : ℝ) (modeIndex N) (fun i => sobolevCoe 2 y (modeIndex N i)) (modeIndex_injective N) n
    rw [if_neg hn] at h1
    have hn' : n ∉ Finset.univ.image (modeIndex N) := by
      intro h
      obtain ⟨i, _, hi⟩ := Finset.mem_image.1 h
      exact hn (hi ▸ Finset.mem_Icc.2 (modeIndex_bounds N i))
    rw [finiteSeq_zero_off N _ n hn'] at h2
    exact h1.trans h2.symm

theorem trunc_sym (y : RealH2) (N : ℕ) (n : ℤ) :
    sobolevCoe 2 (truncSobolev38 2 N y.val) (-n) = star (sobolevCoe 2 (truncSobolev38 2 N y.val) n) := by
  unfold sobolevCoe
  rw [truncSobolev38_apply, truncSobolev38_apply]
  have hiff : (-n ∈ Finset.Icc (-(N : ℤ)) N) ↔ (n ∈ Finset.Icc (-(N : ℤ)) N) := by
    simp only [Finset.mem_Icc]; omega
  by_cases h : n ∈ Finset.Icc (-(N : ℤ)) N
  · rw [if_pos (hiff.2 h), if_pos h]
    exact y.2 n
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
    simp

theorem F036_approx (y : RealH2) (hy : quarticH2 y < 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∃ z : FourierPlane N,
      (∀ x : ℝ, (planeReal N z x).im = 0) ∧
      ‖planeElement38 (2 : ℝ) N z - y.val‖ < ε ∧
      IsRealTrigPoly38 (fun x => (planeReal N z x).re) ∧
      q6QuarticF38 (fun x => (planeReal N z x).re) < 0 := by
  have hc := (F036_continuous.continuousAt (x := y)).eventually (gt_mem_nhds hy)
  obtain ⟨δ, hδ, hδy⟩ := Metric.eventually_nhds_iff.1 hc
  have ht := Metric.tendsto_atTop.1 (tendsto_truncSobolev38 2 y.val) (min ε δ) (lt_min hε hδ)
  obtain ⟨N, hN⟩ := ht
  have hNN := hN N le_rfl
  let y' : RealH2 := ⟨truncSobolev38 2 N y.val, fun n => trunc_sym y N n⟩
  have hval : y'.val = planeElement38 (2 : ℝ) N (fun i => sobolevCoe 2 y.val (modeIndex N i)) :=
    trunc_eq_plane y.val N
  have hd : dist y' y < δ := by
    have : dist y' y = dist (truncSobolev38 2 N y.val) y.val := rfl
    rw [this]; exact lt_of_lt_of_le hNN (min_le_right _ _)
  have hneg : quarticH2 y' < 0 := hδy hd
  have hq := F036_plane y' N _ hval
  have hz : ∀ i, (fun i => sobolevCoe 2 y.val (modeIndex N i)) i = sobolevCoe 2 y.val (modeIndex N i) := fun _ => rfl
  refine ⟨N, fun i => sobolevCoe 2 y.val (modeIndex N i), ?_, ?_, ?_, ?_⟩
  · intro x
    rw [planeReal_trig (sobolevCoe 2 y.val) N x]
    exact trigSum_im_zero _ y.2 N x
  · have : planeElement38 (2 : ℝ) N (fun i => sobolevCoe 2 y.val (modeIndex N i)) - y.val =
        truncSobolev38 2 N y.val - y.val := by rw [← trunc_eq_plane]
    rw [this]
    have h2 : dist (truncSobolev38 2 N y.val) y.val < ε := lt_of_lt_of_le hNN (min_le_left _ _)
    rwa [dist_eq_norm] at h2
  · have : (fun x => (planeReal N (fun i => sobolevCoe 2 y.val (modeIndex N i)) x).re) =
        fun x => (trigSum38 (sobolevCoe 2 y.val) N x).re := by
      funext x; rw [planeReal_trig]
    rw [this]
    exact isRealTrigPoly_re_trigSum38 _ N
  · rw [← hq]; exact hneg

theorem star_lift_real (f : ℝ → ℝ) (hf : Continuous f) (hper : Function.Periodic f 1)
    (hu : ContDiff ℝ ∞ (fun x => ((f x : ℝ) : ℂ))) (hper' : Function.Periodic (fun x => ((f x : ℝ) : ℂ)) 1)
    (t : PhysicalCircle) :
    star (riccatiSmoothPeriodicLiftContinuousMapRecovery30First (fun x => ((f x : ℝ) : ℂ))
      hu.continuous hper' t) =
    riccatiSmoothPeriodicLiftContinuousMapRecovery30First (fun x => ((f x : ℝ) : ℂ))
      hu.continuous hper' t := by
  change star (AddCircle.liftIoc 1 0 (fun x => ((f x : ℝ) : ℂ)) t) =
    AddCircle.liftIoc 1 0 (fun x => ((f x : ℝ) : ℂ)) t
  simp [AddCircle.liftIoc, Complex.star_def, Complex.conj_ofReal]

theorem F036_exists_of_smooth
    (hf : ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧ q6QuarticF38 f < 0) :
    ∃ f : ℝ → ℝ, IsRealTrigPoly38 f ∧ q6QuarticF38 f < 0 := by
  obtain ⟨f, hfs, hfp, hfneg⟩ := hf
  have hu : ContDiff ℝ ∞ (fun x => ((f x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hfs
  have hper : Function.Periodic (fun x => ((f x : ℝ) : ℂ)) 1 := fun x => by simp [hfp x]
  obtain ⟨x', hx', -⟩ := riccatiSmoothPeriodicJetsAgreePointwiseRecovery31Second 2
    (fun x => ((f x : ℝ) : ℂ)) hu hper
  set U := ContinuousMap.toLp 2 spatialMeasure ℂ
    (riccatiSmoothPeriodicLiftContinuousMapRecovery30First (fun x => ((f x : ℝ) : ℂ))
      hu.continuous hper) with hU
  have hstar : (star U : PhysicalL2) = U := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_star U, ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure
      (riccatiSmoothPeriodicLiftContinuousMapRecovery30First (fun x => ((f x : ℝ) : ℂ))
        hu.continuous hper)] with t h1 h2
    rw [h1]
    simp only [Pi.star_apply, Function.comp]
    rw [hU, h2]
    exact star_lift_real f hfs.continuous hfp hu hper t
  have hsym : ∀ n : ℤ, sobolevCoe 2 x' (-n) = star (sobolevCoe 2 x' n) := by
    intro n
    have h1 := NlsGge.Schur.physicalFourier_star38 U (-n)
    rw [hstar, neg_neg] at h1
    show (show WeightedHilbert (sobolevModeWeight ((2 : ℕ) : ℝ)) from x') (-n) = star ((show WeightedHilbert (sobolevModeWeight ((2 : ℕ) : ℝ)) from x') n)
    rw [hx', hx']
    exact h1
  let y : RealH2 := ⟨x', hsym⟩
  have hq : quarticH2 y = q6QuarticF38 f := by
    have := F036Aux.smooth_integral (fun x => ((f x : ℝ) : ℂ)) hu hper x' hx'
    simp only [Complex.ofReal_re] at this
    exact this
  obtain ⟨N, z, -, -, hp, hneg⟩ := F036_approx y (by rw [hq]; exact hfneg) 1 one_pos
  exact ⟨_, hp, hneg⟩

theorem exists_cusp_cutoff : ∃ η : ℝ → ℝ, IsCuspCutoff η := by
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  have hr : b.rOut = 1 / 4 := rfl
  have hi : b.rIn = 1 / 8 := rfl
  refine ⟨fun x => b x, b.contDiff, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ Function.support (fun x => b x) := hx
    rw [b.support_eq, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt, hr] at hx'
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  · intro x hx
    apply b.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, hi]
    exact hx

theorem f036 :
    Continuous quarticH2 ∧
    (∀ y : RealH2,
      Integrable (fun t : PhysicalCircle =>
        ((lowerJetLinfty38 2 (false, 0) (toCarrier38 2 y.val) :
          PhysicalCircle → ℂ) t).re ^ 2 *
        ((topJetL2_38 2 (false, 2) (toCarrier38 2 y.val) :
          PhysicalCircle → ℂ) t).re ^ 2) spatialMeasure ∧
      Integrable (fun t : PhysicalCircle =>
        ((lowerJetLinfty38 2 (false, 1) (toCarrier38 2 y.val) :
          PhysicalCircle → ℂ) t).re ^ 4) spatialMeasure) ∧
    (∀ (y : RealH2) (N : ℕ) (z : FourierPlane N),
      y.val = planeElement38 (2 : ℝ) N z →
      quarticH2 y = q6QuarticF38 (fun x => (planeReal N z x).re)) ∧
    (∀ y : RealH2, quarticH2 y < 0 → ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∃ z : FourierPlane N,
        (∀ x : ℝ, (planeReal N z x).im = 0) ∧
        ‖planeElement38 (2 : ℝ) N z - y.val‖ < ε ∧
        IsRealTrigPoly38 (fun x => (planeReal N z x).re) ∧
        q6QuarticF38 (fun x => (planeReal N z x).re) < 0) ∧
    ∃ f : ℝ → ℝ, IsRealTrigPoly38 f ∧ q6QuarticF38 f < 0 := by
  obtain ⟨η, hη⟩ := exists_cusp_cutoff
  have hf := (f035 η hη).2.2
  exact ⟨F036_continuous, fun y => F036_integrable y, fun y N z h => F036_plane y N z h,
    fun y hy ε hε => F036_approx y hy ε hε, F036_exists_of_smooth hf⟩

end NlsGge.ThirdConsultation.F
