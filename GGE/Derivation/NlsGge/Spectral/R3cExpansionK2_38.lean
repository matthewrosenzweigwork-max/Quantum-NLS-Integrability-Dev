import NlsGge.Spectral.R3cResolventCore38
import NlsGge.Spectral.R3cResolventL2_38
import NlsGge.Spectral.R3cUniformRiccati38
import NlsGge.Spectral.R3cPlaneSobolev38
import NlsGge.Spectral.R3cIdentification38
import NlsGge.Spectral.R3cQuadIdentity38
import NlsGge.Spectral.R3cK2Quartic38b
import NlsGge.Spectral.R3cK2Sextic38
import NlsGge.Spectral.R3cExpansionK1_38
import NlsGge.Spectral.PlaneMomentInequality38V1
import NlsGge.Spectral.NonlinearRemainderDensity38
import NlsGge.Hierarchy.PeriodicIntegrationByParts
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core

/-! # R3c piece P8: the `k = 2` charge, the periodic IBP identities and `NonlinRiccatiSmoothBound38 2` -/

/-! ## The nonlinear charge `N₄` -/

theorem nonlinCharge_two_r3c (N : ℕ) (z : FourierPlane N) :
    localCharge38 (planeReal N z) 2 - ∑ i : Fin (2*N+1),
      (2*Real.pi*(modeIndex N i : ℤ))^(2*2) * ‖z i‖^2 =
      ∫ x in (0:ℝ)..1, (2 * ‖planeReal N z x‖ ^ 6 +
        8 * ‖planeReal N z x‖ ^ 2 * ‖planeReal N (derivativePlane N z) x‖ ^ 2 +
        2 * (planeReal N z x ^ 2 * star (planeReal N (derivativePlane N z) x) ^ 2).re) := by
  have hU := planeReal_smooth38 N z
  have hc : Continuous (planeReal N z) := hU.continuous
  have hd : Continuous (planeReal N (derivativePlane N z)) := (planeReal_smooth38 N _).continuous
  have hdd : Continuous (planeReal N (derivativePlane N (derivativePlane N z))) :=
    (planeReal_smooth38 N _).continuous
  unfold localCharge38
  rw [complexQ4_local_formula_Q024 _ hU (planeReal_periodic N z)]
  have h2 : iteratedDeriv 2 (planeReal N z) =
      planeReal N (derivativePlane N (derivativePlane N z)) := by
    rw [iteratedDeriv_planeReal]; rfl
  rw [h2, deriv_planeReal]
  have hre : Continuous fun x => (planeReal N z x ^ 2 *
      star (planeReal N (derivativePlane N z) x) ^ 2).re :=
    Complex.continuous_re.comp ((hc.pow 2).mul (hd.star.pow 2))
  have hi1 : IntervalIntegrable (fun x => ‖planeReal N (derivativePlane N (derivativePlane N z)) x‖ ^ 2)
      MeasureTheory.volume 0 1 := (hdd.norm.pow 2).intervalIntegrable 0 1
  have hi2 : IntervalIntegrable (fun x => 2 * ‖planeReal N z x‖ ^ 6 +
        8 * ‖planeReal N z x‖ ^ 2 * ‖planeReal N (derivativePlane N z) x‖ ^ 2 +
        2 * (planeReal N z x ^ 2 * star (planeReal N (derivativePlane N z) x) ^ 2).re)
      MeasureTheory.volume 0 1 := by
    refine Continuous.intervalIntegrable ?_ 0 1
    have := hc.norm; have := hd.norm
    fun_prop
  have hsplit : (∫ x in (0:ℝ)..1, (‖planeReal N (derivativePlane N (derivativePlane N z)) x‖ ^ 2 +
        2 * ‖planeReal N z x‖ ^ 6 +
        8 * ‖planeReal N z x‖ ^ 2 * ‖planeReal N (derivativePlane N z) x‖ ^ 2 +
        2 * (planeReal N z x ^ 2 * star (planeReal N (derivativePlane N z) x) ^ 2).re)) =
      (∫ x in (0:ℝ)..1, ‖planeReal N (derivativePlane N (derivativePlane N z)) x‖ ^ 2) +
      ∫ x in (0:ℝ)..1, (2 * ‖planeReal N z x‖ ^ 6 +
        8 * ‖planeReal N z x‖ ^ 2 * ‖planeReal N (derivativePlane N z) x‖ ^ 2 +
        2 * (planeReal N z x ^ 2 * star (planeReal N (derivativePlane N z) x) ^ 2).re) := by
    rw [← intervalIntegral.integral_add hi1 hi2]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    ring
  rw [hsplit, planeReal_integral_norm_sq38]
  have : ∑ i : Fin (2 * N + 1), ‖derivativePlane N (derivativePlane N z) i‖ ^ 2 =
      ∑ i : Fin (2*N+1), (2*Real.pi*(modeIndex N i : ℤ))^(2*2) * ‖z i‖^2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [derivativePlane, norm_mul, mul_pow, Complex.norm_I, Complex.norm_ofNat,
      Complex.norm_real, Complex.norm_intCast, Real.norm_eq_abs, mul_one, sq_abs]
    ring
  rw [this]
  ring

/-! ## Periodic integration by parts -/

theorem ibp_form_r3c {f f' g g' a b : ℝ → ℂ} (hf : PerC1_38 f f') (hg : PerC1_38 g g')
    (ha : ∀ x, a x = f x * g' x) (hb : ∀ x, b x = f' x * g x) :
    (∫ x in (0:ℝ)..1, a x) = -(∫ x in (0:ℝ)..1, b x) := by
  have e1 : a = fun x => f x * g' x := funext ha
  have e2 : b = fun x => f' x * g x := funext hb
  rw [e1, e2]
  exact NlsGge.HierarchyRiccati.unitPeriod_integral_mul_deriv_eq_neg_deriv_mul hf.per hg.per
    (fun x _ => hf.deriv x) (fun x _ => hg.deriv x) (hf.cont'.intervalIntegrable 0 1)
    (hg.cont'.intervalIntegrable 0 1)

theorem integral_star_r3c (f : ℝ → ℂ) :
    (∫ x in (0:ℝ)..1, star (f x)) = star (∫ x in (0:ℝ)..1, f x) := by
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  simp only [Complex.star_def]
  exact integral_conj

theorem integral_re_r3c {f : ℝ → ℂ} (hf : Continuous f) :
    (∫ x in (0:ℝ)..1, f x).re = ∫ x in (0:ℝ)..1, (f x).re := by
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  exact (integral_re (hf.integrableOn_Ioc)).symm

theorem star_re_r3c (w : ℂ) : (star w).re = w.re := rfl

theorem mul_star_eq_r3c (w : ℂ) : w * star w = ((‖w‖ : ℝ) : ℂ) ^ 2 := by
  rw [Complex.star_def, Complex.mul_conj']

/-- The three periodic IBP identities of section 3c, abstractly. -/
theorem ibp_identities_abstract_r3c {U U₁ U₂ : ℝ → ℂ} (h1 : PerC1_38 U U₁) (h2 : PerC1_38 U₁ U₂) :
    ((∫ x in (0:ℝ)..1, U₁ x * U x * star (U x) ^ 2) -
        2 * ∫ x in (0:ℝ)..1, U x ^ 2 * star (U x) * star (U₁ x)).re = 0 ∧
    (∫ x in (0:ℝ)..1, U₂ x * U x * star (U x) ^ 2).re =
      -(∫ x in (0:ℝ)..1, U x ^ 2 * star (U₁ x) ^ 2).re -
        2 * ∫ x in (0:ℝ)..1, ‖U x‖ ^ 2 * ‖U₁ x‖ ^ 2 ∧
    (2 * ∫ x in (0:ℝ)..1, ‖U x‖ ^ 2 * U x * star (U₂ x)).re =
      -4 * (∫ x in (0:ℝ)..1, ‖U x‖ ^ 2 * ‖U₁ x‖ ^ 2) -
        2 * (∫ x in (0:ℝ)..1, U x ^ 2 * star (U₁ x) ^ 2).re := by
  have hs1 := h1.star
  have hs2 := h2.star
  have c0 := h1.cont
  have c1 := h2.cont
  have c2 := h2.cont'
  have hX : (∫ x in (0:ℝ)..1, ((‖U x‖ ^ 2 * ‖U₁ x‖ ^ 2 : ℝ) : ℂ)) =
      ((∫ x in (0:ℝ)..1, ‖U x‖ ^ 2 * ‖U₁ x‖ ^ 2 : ℝ) : ℂ) := intervalIntegral.integral_ofReal
  have hXe : ∀ x, ((‖U x‖ ^ 2 * ‖U₁ x‖ ^ 2 : ℝ) : ℂ) =
      (U x * star (U x)) * (U₁ x * star (U₁ x)) := fun x => by
    rw [mul_star_eq_r3c, mul_star_eq_r3c]; push_cast; ring
  -- identity 1
  have I21 : (∫ x in (0:ℝ)..1, U x ^ 2 * star (U x) * star (U₁ x)) =
      -(∫ x in (0:ℝ)..1, U₁ x * U x * star (U x) ^ 2) := by
    have key := ibp_form_r3c (f := fun y => U y ^ 2) (f' := fun y => 2 * U y * U₁ y)
      (g := fun y => star (U y) ^ 2) (g' := fun y => 2 * star (U y) * star (U₁ y))
      (a := fun x => 2 * (U x ^ 2 * star (U x) * star (U₁ x)))
      (b := fun x => 2 * (U₁ x * U x * star (U x) ^ 2)) h1.pow_two hs1.pow_two
      (fun x => by ring) (fun x => by ring)
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at key
    linear_combination (1/2 : ℂ) * key
  have I21s : (∫ x in (0:ℝ)..1, U x ^ 2 * star (U x) * star (U₁ x)) =
      star (∫ x in (0:ℝ)..1, U₁ x * U x * star (U x) ^ 2) := by
    rw [← integral_star_r3c]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [star_mul', star_pow, star_star]
    ring
  have R1 : (∫ x in (0:ℝ)..1, U₁ x * U x * star (U x) ^ 2).re = 0 := by
    have a := congrArg Complex.re I21
    have b := congrArg Complex.re I21s
    rw [Complex.neg_re] at a
    rw [star_re_r3c] at b
    linarith
  have R2 : (∫ x in (0:ℝ)..1, U x ^ 2 * star (U x) * star (U₁ x)).re = 0 := by
    have a := congrArg Complex.re I21
    rw [Complex.neg_re, R1] at a
    simpa using a
  refine ⟨by simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, R1, R2,
    zero_mul, sub_zero, mul_zero], ?_, ?_⟩
  · -- identity 2
    have key := ibp_form_r3c (f := fun y => U y * star (U y) ^ 2)
      (f' := fun y => U₁ y * star (U y) ^ 2 + U y * (2 * star (U y) * star (U₁ y)))
      (g := U₁) (g' := U₂)
      (a := fun x => U₂ x * U x * star (U x) ^ 2)
      (b := fun x => U₁ x ^ 2 * star (U x) ^ 2 +
        2 * ((U x * star (U x)) * (U₁ x * star (U₁ x))))
      (h1.mul hs1.pow_two) h2 (fun x => by ring) (fun x => by ring)
    have i1 : IntervalIntegrable (fun x => U₁ x ^ 2 * star (U x) ^ 2) MeasureTheory.volume 0 1 :=
      ((c1.pow 2).mul (c0.star.pow 2)).intervalIntegrable 0 1
    have i2 : IntervalIntegrable (fun x => 2 * ((U x * star (U x)) * (U₁ x * star (U₁ x))))
        MeasureTheory.volume 0 1 :=
      (continuous_const.mul ((c0.mul c0.star).mul (c1.mul c1.star))).intervalIntegrable 0 1
    rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul] at key
    simp only [← hXe] at key
    rw [hX] at key
    have hY : (∫ x in (0:ℝ)..1, U₁ x ^ 2 * star (U x) ^ 2) =
        star (∫ x in (0:ℝ)..1, U x ^ 2 * star (U₁ x) ^ 2) := by
      rw [← integral_star_r3c]
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      simp only [star_mul', star_pow, star_star]
      ring
    have a := congrArg Complex.re key
    rw [hY] at a
    simp only [Complex.neg_re, Complex.add_re, star_re_r3c, Complex.mul_re,
      Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im] at a
    linarith
  · -- identity 3
    have key := ibp_form_r3c (f := fun y => (U y * star (U y)) * U y)
      (f' := fun y => (U₁ y * star (U y) + U y * star (U₁ y)) * U y + (U y * star (U y)) * U₁ y)
      (g := fun y => star (U₁ y)) (g' := fun y => star (U₂ y))
      (a := fun x => ((‖U x‖ : ℝ) : ℂ) ^ 2 * U x * star (U₂ x))
      (b := fun x => 2 * ((U x * star (U x)) * (U₁ x * star (U₁ x))) +
        U x ^ 2 * star (U₁ x) ^ 2)
      ((h1.mul hs1).mul h1) hs2
      (fun x => by rw [← mul_star_eq_r3c (U x)]) (fun x => by ring)
    have i1 : IntervalIntegrable (fun x => 2 * ((U x * star (U x)) * (U₁ x * star (U₁ x))))
        MeasureTheory.volume 0 1 :=
      (continuous_const.mul ((c0.mul c0.star).mul (c1.mul c1.star))).intervalIntegrable 0 1
    have i2 : IntervalIntegrable (fun x => U x ^ 2 * star (U₁ x) ^ 2) MeasureTheory.volume 0 1 :=
      ((c0.pow 2).mul (c1.star.pow 2)).intervalIntegrable 0 1
    rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul] at key
    simp only [← hXe] at key
    rw [hX] at key
    have a := congrArg Complex.re key
    simp only [Complex.neg_re, Complex.add_re, Complex.mul_re,
      Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im] at a ⊢
    linarith

theorem ibp_identities_r3c (N : ℕ) (z : FourierPlane N) :
    ((∫ x in (0:ℝ)..1, planeReal N (derivativePlane N z) x * planeReal N z x *
        star (planeReal N z x) ^ 2) -
      2 * ∫ x in (0:ℝ)..1, planeReal N z x ^ 2 * star (planeReal N z x) *
        star (planeReal N (derivativePlane N z) x)).re = 0 ∧
    (∫ x in (0:ℝ)..1, planeReal N (derivativePlane N (derivativePlane N z)) x *
        planeReal N z x * star (planeReal N z x) ^ 2).re =
      -(∫ x in (0:ℝ)..1, planeReal N z x ^ 2 * star (planeReal N (derivativePlane N z) x) ^ 2).re -
        2 * ∫ x in (0:ℝ)..1, ‖planeReal N z x‖ ^ 2 * ‖planeReal N (derivativePlane N z) x‖ ^ 2 ∧
    (2 * ∫ x in (0:ℝ)..1, ‖planeReal N z x‖ ^ 2 * planeReal N z x *
        star (planeReal N (derivativePlane N (derivativePlane N z)) x)).re =
      -4 * (∫ x in (0:ℝ)..1, ‖planeReal N z x‖ ^ 2 * ‖planeReal N (derivativePlane N z) x‖ ^ 2) -
        2 * (∫ x in (0:ℝ)..1, planeReal N z x ^ 2 *
          star (planeReal N (derivativePlane N z) x) ^ 2).re :=
  ibp_identities_abstract_r3c (perC1_plane38 N z) (perC1_plane38 N (derivativePlane N z))

/-! ## The final arithmetic -/

theorem re_div_r3c (w a : ℂ) (r : ℝ) (h : a = (r : ℂ)) : (w / a).re = w.re / r := by
  rw [h]; exact Complex.div_ofReal_re w r

theorem k2_arith_r3c {η J4 J6 X : ℝ} (hη : 0 < η) (I1 I2 I3 I4 I5 Q S6 P eQ eS : ℂ)
    (hQe : Q = (((J4 : ℝ) : ℂ) / (8 * (η : ℂ) ^ 3) + I1 / (16 * (η : ℂ) ^ 4) -
      I2 / (8 * (η : ℂ) ^ 4) + ((I3 + I4) + 2 * I5) / (32 * (η : ℂ) ^ 5) -
      ((X : ℝ) : ℂ) / (16 * (η : ℂ) ^ 5)) + eQ)
    (hSe : S6 = ((J6 : ℝ) : ℂ) / (16 * (η : ℂ) ^ 5) + eS)
    (id1 : (I1 - 2 * I2).re = 0) (id2 : I3.re = -I4.re - 2 * X)
    (id3 : (2 * I5).re = -4 * X - 2 * I4.re) :
    (-Q + S6 + P).re - (-(J4 / (8 * η ^ 3)) + (2 * J6 + 8 * X + 2 * I4.re) / (32 * η ^ 5)) =
      -eQ.re + eS.re + P.re := by
  rw [hQe, hSe]
  have h1 : (8 * (η : ℂ) ^ 3) = ((8 * η ^ 3 : ℝ) : ℂ) := by push_cast; ring
  have h2 : (16 * (η : ℂ) ^ 4) = ((16 * η ^ 4 : ℝ) : ℂ) := by push_cast; ring
  have h3 : (8 * (η : ℂ) ^ 4) = ((8 * η ^ 4 : ℝ) : ℂ) := by push_cast; ring
  have h4 : (32 * (η : ℂ) ^ 5) = ((32 * η ^ 5 : ℝ) : ℂ) := by push_cast; ring
  have h5 : (16 * (η : ℂ) ^ 5) = ((16 * η ^ 5 : ℝ) : ℂ) := by push_cast; ring
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, re_div_r3c _ _ _ h1,
    re_div_r3c _ _ _ h2, re_div_r3c _ _ _ h3, re_div_r3c _ _ _ h4, re_div_r3c _ _ _ h5,
    Complex.ofReal_re]
  have i2 : (I2).re = (I1).re / 2 := by
    have := id1
    rw [Complex.sub_re] at this
    have h2' : (2 * I2).re = 2 * I2.re := by simp
    rw [h2'] at this
    linarith
  have h5' : (2 * I5).re = 2 * I5.re := by simp
  rw [h5'] at id3 ⊢
  rw [i2] at *
  field_simp
  nlinarith [id2, id3]

theorem pair38_neg_r3c (f g : ℝ → ℂ) : pair38 f (fun x => -g x) = -pair38 f g := by
  unfold pair38
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [mul_neg]

theorem pair38_add_r3c {f g h : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) : pair38 f (fun x => g x + h x) = pair38 f g + pair38 f h := by
  unfold pair38
  have := intervalIntegral.integral_add (a := (0:ℝ)) (b := 1) (μ := MeasureTheory.volume)
    (f := fun x => f x * g x) (g := fun x => f x * h x) ((hf.mul hg).intervalIntegrable 0 1)
    ((hf.mul hh).intervalIntegrable 0 1)
  rw [← this]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [mul_add]

/-! ## The final theorem -/

theorem nonlinRiccatiSmoothBound38_two : NonlinRiccatiSmoothBound38 2 := by
  intro B
  obtain ⟨η₁, hη₁, hP⟩ := r3c_im_eq_pair38 |B| (abs_nonneg B)
  obtain ⟨η₂, C₂, hη₂, hC₂, hQ⟩ := r3c_k2_quartic B
  obtain ⟨η₃, C₃, hη₃, hC₃, hS⟩ := r3c_k2_sextic B
  set A : ℝ := Real.sqrt bracketSumE02_38 * |B| with hAdef
  have hA0 : 0 ≤ A := mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  refine ⟨max (max η₁ η₂) (max η₃ (max (4 * A) 1)), C₂ + C₃ + A ^ 8,
    lt_max_of_lt_left (lt_max_of_lt_left hη₁), by positivity, ?_⟩
  intro N z hS2 η hη
  have hηa : η₁ ≤ η := (le_max_left _ _).trans ((le_max_left _ _).trans hη)
  have hηb : η₂ ≤ η := (le_max_right _ _).trans ((le_max_left _ _).trans hη)
  have hηc : η₃ ≤ η := (le_max_left _ _).trans ((le_max_right _ _).trans hη)
  have hηd : max (4 * A) 1 ≤ η := (le_max_right _ _).trans ((le_max_right _ _).trans hη)
  have hη1 : 1 ≤ η := (le_max_right _ _).trans hηd
  have hηpos : 0 < η := by linarith
  have hS1 : ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 1 * ‖z i‖ ^ 2 ≤
      |B| ^ 2 := by
    rw [sq_abs]; exact (plane_S_mono_r3c N z (by norm_num : 1 ≤ 2)).trans hS2
  have hUb : ∀ x, ‖planeReal N z x‖ ≤ A := by
    intro x
    refine (plane_sup_le_r3c N z x).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    calc Real.sqrt (∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 1 * ‖z i‖ ^ 2)
        ≤ Real.sqrt (|B| ^ 2) := Real.sqrt_le_sqrt hS1
      _ = |B| := Real.sqrt_sq (abs_nonneg _)
  obtain ⟨Γ, hΓc, hΓp, hΓd, hΓb, hΓk⟩ := hP N z hS1 η hηa
  have hU := perC1_plane38 N z
  have hG := perC1_resolv38 hηpos hU.star
  have hF := hU.mul hG.pow_two
  have hRF := perC1_resolv38 hηpos hF
  have hG3 : PerC1_38 (fun x => -resolv38 η (fun y => planeReal N z y *
      resolv38 η (fun y => star (planeReal N z y)) y ^ 2) x) _ := hRF.neg
  have hH := ((hU.const_mul 2).mul hG).mul hG3
  have hRH := perC1_resolv38 hηpos hH
  have hG5 := hRH.neg
  obtain ⟨_, _, hrem⟩ := born_remainder38 (planeReal N z) Γ hU.cont hU.per hA0 hUb hηd hΓc hΓp hΓd hΓb
  have hQ' := hQ N z hS2 η hηb
  have hS' := hS N z hS2 η hηc
  have hid := ibp_identities_r3c N z
  have hc0 : Continuous (planeReal N z) := hU.cont
  have hc1 : Continuous (planeReal N (derivativePlane N z)) := hU.cont'
  have hc2 : Continuous (planeReal N (derivativePlane N (derivativePlane N z))) :=
    (perC1_plane38 N (derivativePlane N z)).cont'
  -- the nonlinear charges
  have hN1 := nonlinCharge_one_r3c N z
  have hN2 := nonlinCharge_two_r3c N z
  have hN0 := nonlinCharge_zero_r3c N z
  set U := planeReal N z with hUdef
  set U₁ := planeReal N (derivativePlane N z) with hU₁def
  set U₂ := planeReal N (derivativePlane N (derivativePlane N z)) with hU₂def
  set G1 : ℝ → ℂ := resolv38 η (fun y => star (U y)) with hG1def
  set R3 : ℝ → ℂ := resolv38 η (fun y => U y * G1 y ^ 2) with hR3def
  set G5 : ℝ → ℂ := fun x => -resolv38 η (fun y => 2 * U y * G1 y * -R3 y) x with hG5def
  set Q : ℂ := pair38 U R3 with hQdef
  set S6 : ℂ := pair38 U G5 with hS6def
  have hG1c : Continuous G1 := hG.cont
  have hR3c : Continuous R3 := hRF.cont
  have hG5c : Continuous G5 := hG5.cont
  set rem : ℝ → ℂ := fun x => Γ x - G1 x - (-R3 x) - G5 x with hremdef
  have hremc : Continuous rem := ((hΓc.sub hG1c).sub hR3c.neg).sub hG5c
  have hremb : ∀ x, ‖rem x‖ ≤ A ^ 7 / η ^ 7 := hrem
  have hpr : ‖pair38 U rem‖ ≤ A ^ 8 / η ^ 7 := by
    unfold pair38
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0:ℝ)) (b := 1) (f := fun x => U x * rem x) (C := A ^ 8 / η ^ 7)
      (fun x _ => by
        rw [norm_mul]
        calc ‖U x‖ * ‖rem x‖ ≤ A * (A ^ 7 / η ^ 7) :=
              mul_le_mul (hUb x) (hremb x) (norm_nonneg _) hA0
          _ = A ^ 8 / η ^ 7 := by ring)
    simpa using this
  have hdec : pair38 U (fun x => Γ x - G1 x) = -Q + S6 + pair38 U rem := by
    have e : (fun x => Γ x - G1 x) = fun x => ((-R3 x) + G5 x) + rem x := by
      funext x; simp only [hremdef]; ring
    have hng : Continuous (fun x => -R3 x) := hR3c.neg
    have hsum : Continuous (fun x => -R3 x + G5 x) := hng.add hG5c
    rw [e, pair38_add_r3c hc0 hsum hremc, pair38_add_r3c hc0 hng hG5c, pair38_neg_r3c]
  have hpair : (pair38 U Γ).re - (pair38 U G1).re = (pair38 U (fun x => Γ x - G1 x)).re := by
    unfold pair38
    have hint : ∫ x in (0:ℝ)..1, U x * (Γ x - G1 x) =
        (∫ x in (0:ℝ)..1, U x * Γ x) - ∫ x in (0:ℝ)..1, U x * G1 x := by
      rw [← intervalIntegral.integral_sub
        (f := fun x => U x * Γ x) (g := fun x => U x * G1 x)
        ((hc0.mul hΓc).intervalIntegrable 0 1) ((hc0.mul hG1c).intervalIntegrable 0 1)]
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      simp only [mul_sub]
    rw [hint, Complex.sub_re]
  have hqu : quadRiccati38 (planeL2 N z) η = (pair38 U G1).re := quadRiccati38_eq_pair38 N z hηpos
  -- integrals
  set J4 : ℝ := ∫ x in (0:ℝ)..1, ‖U x‖ ^ 4 with hJ4
  set J6 : ℝ := ∫ x in (0:ℝ)..1, ‖U x‖ ^ 6 with hJ6
  set X : ℝ := ∫ x in (0:ℝ)..1, ‖U x‖ ^ 2 * ‖U₁ x‖ ^ 2 with hX
  set I4 : ℂ := ∫ x in (0:ℝ)..1, U x ^ 2 * star (U₁ x) ^ 2 with hI4
  have hN2' : (∫ x in (0:ℝ)..1, (2 * ‖U x‖ ^ 6 + 8 * ‖U x‖ ^ 2 * ‖U₁ x‖ ^ 2 +
      2 * (U x ^ 2 * star (U₁ x) ^ 2).re)) = 2 * J6 + 8 * X + 2 * I4.re := by
    have i1 : IntervalIntegrable (fun x => 2 * ‖U x‖ ^ 6) MeasureTheory.volume 0 1 :=
      (continuous_const.mul (hc0.norm.pow 6)).intervalIntegrable 0 1
    have i2 : IntervalIntegrable (fun x => 8 * ‖U x‖ ^ 2 * ‖U₁ x‖ ^ 2) MeasureTheory.volume 0 1 :=
      ((continuous_const.mul (hc0.norm.pow 2)).mul (hc1.norm.pow 2)).intervalIntegrable 0 1
    have hre : Continuous fun x => (U x ^ 2 * star (U₁ x) ^ 2).re :=
      Complex.continuous_re.comp ((hc0.pow 2).mul (hc1.star.pow 2))
    have i3 : IntervalIntegrable (fun x => 2 * (U x ^ 2 * star (U₁ x) ^ 2).re)
        MeasureTheory.volume 0 1 := (continuous_const.mul hre).intervalIntegrable 0 1
    rw [intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have h8 : (∫ x in (0:ℝ)..1, 8 * ‖U x‖ ^ 2 * ‖U₁ x‖ ^ 2) = 8 * X := by
      rw [hX, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      simp only [mul_assoc]
    have hI4re : I4.re = ∫ x in (0:ℝ)..1, (U x ^ 2 * star (U₁ x) ^ 2).re :=
      integral_re_r3c ((hc0.pow 2).mul (hc1.star.pow 2))
    rw [h8, hI4re]
  have hsum : ∑ j ∈ Finset.range (2 + 1), (-1:ℝ)^j / (2 * 4^j * η^(2*j+1)) *
      (localCharge38 U j -
        ∑ i : Fin (2*N+1), (2*Real.pi*(modeIndex N i : ℤ))^(2*j) * ‖z i‖^2) =
      -(J4 / (8 * η ^ 3)) + (2 * J6 + 8 * X + 2 * I4.re) / (32 * η ^ 5) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hN0, hN1, hN2, hN2']
    field_simp
    ring
  obtain ⟨id1, id2, id3⟩ := hid
  set I1 : ℂ := ∫ x in (0:ℝ)..1, U₁ x * U x * star (U x) ^ 2 with hI1
  set I2 : ℂ := ∫ x in (0:ℝ)..1, U x ^ 2 * star (U x) * star (U₁ x) with hI2
  set I3 : ℂ := ∫ x in (0:ℝ)..1, U₂ x * U x * star (U x) ^ 2 with hI3
  set I5 : ℂ := ∫ x in (0:ℝ)..1, ((‖U x‖ : ℝ) : ℂ) ^ 2 * U x * star (U₂ x) with hI5
  set M : ℂ := ((J4 : ℝ) : ℂ) / (8 * (η : ℂ) ^ 3) + I1 / (16 * (η : ℂ) ^ 4) -
      I2 / (8 * (η : ℂ) ^ 4) + ((I3 + I4) + 2 * I5) / (32 * (η : ℂ) ^ 5) -
      ((X : ℝ) : ℂ) / (16 * (η : ℂ) ^ 5) with hM
  have key := k2_arith_r3c hηpos I1 I2 I3 I4 I5 Q S6 (pair38 U rem) (Q - M)
    (S6 - ((J6 : ℝ) : ℂ) / (16 * (η : ℂ) ^ 5)) (by rw [add_sub_cancel]) (by rw [add_sub_cancel])
    id1 id2 id3
  have hE : (pair38 U Γ).re - (pair38 U G1).re -
      (-(J4 / (8 * η ^ 3)) + (2 * J6 + 8 * X + 2 * I4.re) / (32 * η ^ 5)) =
      -(Q - M).re + (S6 - ((J6 : ℝ) : ℂ) / (16 * (η : ℂ) ^ 5)).re + (pair38 U rem).re := by
    rw [← key, hpair, hdec]
  rw [hsum, hΓk, hqu]
  rw [hE]
  have b1 : |(Q - M).re| ≤ C₂ / η ^ 6 := (Complex.abs_re_le_norm _).trans hQ'
  have b2 : |(S6 - ((J6 : ℝ) : ℂ) / (16 * (η : ℂ) ^ 5)).re| ≤ C₃ / η ^ 6 :=
    (Complex.abs_re_le_norm _).trans hS'
  have b3 : |(pair38 U rem).re| ≤ A ^ 8 / η ^ 7 := (Complex.abs_re_le_norm _).trans hpr
  have hη5 : 0 < η ^ (2 * 2 + 1) := by positivity
  rw [abs_mul, abs_of_pos hη5]
  have hsum3 : |-(Q - M).re + (S6 - ((J6 : ℝ) : ℂ) / (16 * (η : ℂ) ^ 5)).re + (pair38 U rem).re| ≤
      C₂ / η ^ 6 + C₃ / η ^ 6 + A ^ 8 / η ^ 7 := by
    refine (abs_add_three _ _ _).trans ?_
    rw [abs_neg]
    linarith
  calc η ^ (2 * 2 + 1) * |-(Q - M).re + (S6 - ((J6 : ℝ) : ℂ) / (16 * (η : ℂ) ^ 5)).re +
          (pair38 U rem).re| ≤ η ^ (2 * 2 + 1) * (C₂ / η ^ 6 + C₃ / η ^ 6 + A ^ 8 / η ^ 7) :=
        mul_le_mul_of_nonneg_left hsum3 hη5.le
    _ = (C₂ + C₃) / η + A ^ 8 / η ^ 2 := by field_simp
    _ ≤ (C₂ + C₃ + A ^ 8) / η := by
        have h : A ^ 8 / η ^ 2 ≤ A ^ 8 / η :=
          div_le_div_of_nonneg_left (by positivity) hηpos (by nlinarith)
        rw [add_div (C₂ + C₃) (A ^ 8)]
        linarith

end NlsGge.SpectralFoundations
