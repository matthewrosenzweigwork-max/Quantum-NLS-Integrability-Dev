import NlsGge.Spectral.R3cResolventCore38
import NlsGge.Spectral.R3cResolventL2_38
import NlsGge.Spectral.R3cUniformRiccati38
import NlsGge.Spectral.R3cPlaneSobolev38
import NlsGge.Spectral.R3cIdentification38
import NlsGge.Spectral.R3cQuadIdentity38
import NlsGge.Spectral.PlaneMomentInequality38V1
import NlsGge.Spectral.NonlinearRemainderDensity38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core

/-! # R3c piece P5: the `k = 1` expansion and `NonlinRiccatiSmoothBound38 1`

Section 2 of `R3C_PROOF_NOTE.md`: with `U = planeReal N z`, `G₁ = R Ū`, `F = U G₁²`, the quartic term
`Re ⟪U, G₃⟫ = -Re ⟪U, R F⟫` equals `-∫|U|⁴/(8η³) + O(η⁻⁴)`. -/

/-! ## Elementary `L²` helpers -/

theorem sqrt_l2sq_le_r3c {f : ℝ → ℂ} {c : ℝ} (hc : 0 ≤ c) (h : l2sq38 f ≤ c ^ 2) :
    Real.sqrt (l2sq38 f) ≤ c := by
  calc Real.sqrt (l2sq38 f) ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt h
    _ = c := Real.sqrt_sq hc

theorem l2sq38_add_le_r3c {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    l2sq38 (fun x => f x + g x) ≤ 2 * l2sq38 f + 2 * l2sq38 g := by
  unfold l2sq38
  have h1 : IntervalIntegrable (fun x => 2 * ‖f x‖ ^ 2) MeasureTheory.volume 0 1 :=
    ((hf.norm.pow 2).const_mul 2).intervalIntegrable 0 1
  have h2 : IntervalIntegrable (fun x => 2 * ‖g x‖ ^ 2) MeasureTheory.volume 0 1 :=
    ((hg.norm.pow 2).const_mul 2).intervalIntegrable 0 1
  have h := intervalIntegral.integral_mono_on zero_le_one
    (((hf.add hg).norm.pow 2).intervalIntegrable 0 1) (h1.add h2) (fun x _ => by
      show ‖f x + g x‖ ^ 2 ≤ 2 * ‖f x‖ ^ 2 + 2 * ‖g x‖ ^ 2
      have := norm_add_le (f x) (g x)
      nlinarith [mul_self_le_mul_self (norm_nonneg _) this, norm_nonneg (f x), norm_nonneg (g x),
        sq_nonneg (‖f x‖ - ‖g x‖)])
  rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h
  exact h

theorem l2sq38_ofReal_mul_r3c (r : ℝ) (f : ℝ → ℂ) :
    l2sq38 (fun x => (r : ℂ) * f x) = r ^ 2 * l2sq38 f := by
  unfold l2sq38
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

/-! ## Bounds on `R F'` and the decomposition of `⟪U, F⟫` -/

/-- `‖⟪U, R F'⟫‖ ≤ A³ d / (2η³)` for `F' = U₁ G² + U (2 G G')`. -/
theorem pair_resolv_Fderiv_le_r3c {η A d : ℝ} (hη : 0 < η) (hA0 : 0 ≤ A) (hd0 : 0 ≤ d)
    {U U₁ G G' : ℝ → ℂ} (hU : PerC1_38 U U₁) (hG : PerC1_38 G G')
    (hUb : ∀ x, ‖U x‖ ≤ A) (hGb : ∀ x, ‖G x‖ ≤ A / (2 * η)) (hU₁ : l2sq38 U₁ ≤ d ^ 2)
    (hG' : l2sq38 G' ≤ d ^ 2 / (2 * η) ^ 2) :
    ‖pair38 U (resolv38 η (fun y => U₁ y * G y ^ 2 + U y * (2 * G y * G' y)))‖ ≤
      A ^ 3 * d / (2 * η ^ 3) := by
  have hη2 : 0 < 2 * η := by positivity
  set F' : ℝ → ℂ := fun y => U₁ y * G y ^ 2 + U y * (2 * G y * G' y) with hF'
  have hFc : Continuous F' := (hU.cont'.mul (hG.cont.pow 2)).add
    (hU.cont.mul ((continuous_const.mul hG.cont).mul hG.cont'))
  have hFp : Function.Periodic F' 1 := fun y => by
    simp only [hF', hU.per' y, hU.per y, hG.per y, hG.per' y]
  -- first term
  have hT1 : l2sq38 (fun y => G y ^ 2 * U₁ y) ≤ (A / (2 * η)) ^ 4 * d ^ 2 := by
    have := l2sq38_mul_le (f := fun y => G y ^ 2) (g := U₁) (hG.cont.pow 2) hU.cont'
      (M := (A / (2 * η)) ^ 2) (fun x => by
        rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hGb x) 2)
    calc _ ≤ ((A / (2 * η)) ^ 2) ^ 2 * l2sq38 U₁ := this
      _ ≤ ((A / (2 * η)) ^ 2) ^ 2 * d ^ 2 :=
        mul_le_mul_of_nonneg_left hU₁ (by positivity)
      _ = _ := by ring
  have hT2 : l2sq38 (fun y => (U y * (2 * G y)) * G' y) ≤ (A ^ 2 / η) ^ 2 * (d ^ 2 / (2 * η) ^ 2) := by
    have := l2sq38_mul_le (f := fun y => U y * (2 * G y)) (g := G') (hU.cont.mul
      (continuous_const.mul hG.cont)) hG.cont' (M := A ^ 2 / η) (fun x => by
        rw [norm_mul, norm_mul, Complex.norm_ofNat]
        have h1 := hUb x
        have h2 := hGb x
        calc ‖U x‖ * (2 * ‖G x‖) ≤ A * (2 * (A / (2 * η))) :=
              mul_le_mul h1 (by linarith) (by positivity) hA0
          _ = A ^ 2 / η := by field_simp)
    calc _ ≤ (A ^ 2 / η) ^ 2 * l2sq38 G' := this
      _ ≤ _ := mul_le_mul_of_nonneg_left hG' (by positivity)
  have hsum : l2sq38 F' ≤ A ^ 4 * d ^ 2 / η ^ 4 := by
    have hsplit : F' = fun y => G y ^ 2 * U₁ y + (U y * (2 * G y)) * G' y := by
      funext y; simp only [hF']; ring
    rw [hsplit]
    have hadd := l2sq38_add_le_r3c (f := fun y => G y ^ 2 * U₁ y)
      (g := fun y => (U y * (2 * G y)) * G' y) ((hG.cont.pow 2).mul hU.cont')
      ((hU.cont.mul (continuous_const.mul hG.cont)).mul hG.cont')
    refine hadd.trans ?_
    have e1 : (A / (2 * η)) ^ 4 * d ^ 2 = A ^ 4 * d ^ 2 / (16 * η ^ 4) := by
      field_simp; ring
    have e2 : (A ^ 2 / η) ^ 2 * (d ^ 2 / (2 * η) ^ 2) = A ^ 4 * d ^ 2 / (4 * η ^ 4) := by
      field_simp; ring
    rw [e1] at hT1
    rw [e2] at hT2
    have hpos : 0 ≤ A ^ 4 * d ^ 2 / η ^ 4 := by positivity
    have : A ^ 4 * d ^ 2 / (16 * η ^ 4) * 2 + A ^ 4 * d ^ 2 / (4 * η ^ 4) * 2 ≤
        A ^ 4 * d ^ 2 / η ^ 4 := by
      have : A ^ 4 * d ^ 2 / (16 * η ^ 4) * 2 + A ^ 4 * d ^ 2 / (4 * η ^ 4) * 2 =
          (5 / 8) * (A ^ 4 * d ^ 2 / η ^ 4) := by field_simp; ring
      rw [this]; linarith
    linarith
  have hRF : l2sq38 (resolv38 η F') ≤ (A ^ 2 * d / (2 * η ^ 3)) ^ 2 := by
    refine (resolv38_l2sq_le hη hFc hFp).trans ?_
    calc l2sq38 F' / (2 * η) ^ 2 ≤ A ^ 4 * d ^ 2 / η ^ 4 / (2 * η) ^ 2 :=
          div_le_div_of_nonneg_right hsum (by positivity)
      _ = _ := by field_simp
  have hRFc : Continuous (resolv38 η F') := (perC1_resolv38_of_cont hη hFc hFp).cont
  have hs := sqrt_l2sq_le_r3c (by positivity) hRF
  calc ‖pair38 U (resolv38 η F')‖ ≤ A * Real.sqrt (l2sq38 (resolv38 η F')) :=
        norm_pair38_le_sup hU.cont hRFc hUb
    _ ≤ A * (A ^ 2 * d / (2 * η ^ 3)) := mul_le_mul_of_nonneg_left hs hA0
    _ = _ := by ring

/-- Decomposition of `⟪U, F⟫` with `F = U G²` and `G = a + e`, `a = Ū/(2η)`. -/
theorem pair_F_decomp_r3c {η A d : ℝ} (hη : 0 < η) (hA0 : 0 ≤ A) (hd0 : 0 ≤ d)
    {U G G' : ℝ → ℂ} (hUc : Continuous U) (hGc : Continuous G) (hG'c : Continuous G')
    (hUb : ∀ x, ‖U x‖ ≤ A) (hGb : ∀ x, ‖G x‖ ≤ A / (2 * η))
    (hGeq : ∀ x, G x = ((1 / (2 * η) : ℝ) : ℂ) * star (U x) +
      ((-(1 / (2 * η)) : ℝ) : ℂ) * G' x)
    (hG' : l2sq38 G' ≤ d ^ 2 / (2 * η) ^ 2) :
    ∃ E : ℂ, pair38 U (fun y => U y * G y ^ 2) =
      (((∫ x in (0:ℝ)..1, ‖U x‖ ^ 4) / (4 * η ^ 2) : ℝ) : ℂ) + E ∧
      ‖E‖ ≤ A ^ 3 * d / (4 * η ^ 3) := by
  have hη2 : 0 < 2 * η := by positivity
  set a : ℝ → ℂ := fun x => ((1 / (2 * η) : ℝ) : ℂ) * star (U x) with ha
  set e : ℝ → ℂ := fun x => ((-(1 / (2 * η)) : ℝ) : ℂ) * G' x with he
  have hac : Continuous a := continuous_const.mul hUc.star
  have hec : Continuous e := continuous_const.mul hG'c
  set f : ℝ → ℂ := fun x => U x ^ 2 * (a x + G x) with hf
  have hfc : Continuous f := (hUc.pow 2).mul (hac.add hGc)
  have hpt : ∀ x, U x * (U x * G x ^ 2) =
      (((‖U x‖ ^ 4 / (4 * η ^ 2) : ℝ)) : ℂ) + f x * e x := by
    intro x
    have hu : U x * star (U x) = ((‖U x‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.star_def, Complex.mul_conj']
    have hGx' : G x = a x + e x := hGeq x
    have hr : (((‖U x‖ ^ 4 / (4 * η ^ 2) : ℝ)) : ℂ) =
        (((1 / (2 * η) : ℝ) : ℂ)) ^ 2 * ((‖U x‖ : ℝ) : ℂ) ^ 4 := by
      have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
      push_cast
      field_simp
      norm_num
    rw [hr]
    simp only [hf]
    rw [hGx']
    simp only [ha, he]
    linear_combination ((((1 / (2 * η) : ℝ) : ℂ)) ^ 2 *
      (U x * star (U x) + ((‖U x‖ : ℝ) : ℂ) ^ 2)) * hu
  have hfb : ∀ x, ‖f x‖ ≤ A ^ 3 / η := by
    intro x
    have hax : ‖a x‖ ≤ A / (2 * η) := by
      simp only [ha, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_star]
      rw [abs_of_pos (by positivity)]
      calc 1 / (2 * η) * ‖U x‖ ≤ 1 / (2 * η) * A :=
            mul_le_mul_of_nonneg_left (hUb x) (by positivity)
        _ = A / (2 * η) := by ring
    simp only [hf, norm_mul, norm_pow]
    calc ‖U x‖ ^ 2 * ‖a x + G x‖ ≤ A ^ 2 * (A / (2 * η) + A / (2 * η)) := by
          refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hUb x) 2) ?_ (norm_nonneg _)
            (by positivity)
          exact (norm_add_le _ _).trans (add_le_add hax (hGb x))
      _ = A ^ 3 / η := by field_simp; ring
  have hel : l2sq38 e ≤ (d / (4 * η ^ 2)) ^ 2 := by
    have h1 : l2sq38 e = (-(1 / (2 * η))) ^ 2 * l2sq38 G' := l2sq38_ofReal_mul_r3c _ _
    rw [h1]
    calc (-(1 / (2 * η))) ^ 2 * l2sq38 G' ≤ (-(1 / (2 * η))) ^ 2 * (d ^ 2 / (2 * η) ^ 2) :=
          mul_le_mul_of_nonneg_left hG' (by positivity)
      _ = _ := by field_simp; ring
  refine ⟨pair38 f e, ?_, ?_⟩
  · have h2 : (fun x => U x * (U x * G x ^ 2)) = fun x =>
        (((‖U x‖ ^ 4 / (4 * η ^ 2) : ℝ)) : ℂ) + f x * e x := funext hpt
    have : pair38 U (fun y => U y * G y ^ 2) = ∫ x in (0:ℝ)..1, U x * (U x * G x ^ 2) := by
      rfl
    have hint1 : IntervalIntegrable (fun x => (((‖U x‖ ^ 4 / (4 * η ^ 2) : ℝ)) : ℂ))
        MeasureTheory.volume 0 1 :=
      (Complex.continuous_ofReal.comp ((hUc.norm.pow 4).div_const _)).intervalIntegrable 0 1
    have hint2 : IntervalIntegrable (fun x => f x * e x) MeasureTheory.volume 0 1 :=
      (hfc.mul hec).intervalIntegrable 0 1
    rw [this, h2, intervalIntegral.integral_add hint1 hint2, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_div]
    rfl
  · have hs := sqrt_l2sq_le_r3c (by positivity) hel
    calc ‖pair38 f e‖ ≤ A ^ 3 / η * Real.sqrt (l2sq38 e) := norm_pair38_le_sup hfc hec hfb
      _ ≤ A ^ 3 / η * (d / (4 * η ^ 2)) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = A ^ 3 * d / (4 * η ^ 3) := by field_simp

/-! ## The abstract `k = 1` core -/

theorem r3c_k1_abstract38 {η A d : ℝ} {U U₁ : ℝ → ℂ} (hU : PerC1_38 U U₁)
    (hA0 : 0 ≤ A) (hA : ∀ x, ‖U x‖ ≤ A) (hd0 : 0 ≤ d) (hd : l2sq38 U₁ ≤ d ^ 2)
    (hη : max (4 * A) 1 ≤ η) (Γ : ℝ → ℂ) (hΓc : Continuous Γ) (hΓp : Function.Periodic Γ 1)
    (hΓd : ∀ x, HasDerivAt Γ (-(2*η) * Γ x + star (U x) - U x * Γ x ^ 2) x)
    (hΓb : ∀ x, ‖Γ x - resolv38 η (fun y => star (U y)) x‖ ≤ A ^ 3 / (4 * η ^ 3)) :
    |η ^ 3 * (pair38 U (fun x => Γ x - resolv38 η (fun y => star (U y)) x)).re +
        (∫ x in (0:ℝ)..1, ‖U x‖ ^ 4) / 8| ≤ (A ^ 6 + A ^ 3 * d) / η := by
  have hη1 : 1 ≤ η := (le_max_right _ _).trans hη
  have hη0 : 0 < η := by linarith
  have hη2 : 0 < 2 * η := by positivity
  set G : ℝ → ℂ := resolv38 η (fun y => star (U y)) with hGdef
  set G' : ℝ → ℂ := resolv38 η (fun y => star (U₁ y)) with hG'def
  have hUs : PerC1_38 (fun y => star (U y)) (fun y => star (U₁ y)) := hU.star
  have hG : PerC1_38 G G' := perC1_resolv38 hη0 hUs
  have hGb : ∀ x, ‖G x‖ ≤ A / (2 * η) := fun x =>
    resolv38_bound hη0 hUs.cont (fun y => by simpa using hA y) x
  have hG'l : l2sq38 G' ≤ d ^ 2 / (2 * η) ^ 2 := by
    refine (resolv38_l2sq_le hη0 hUs.cont' hUs.per').trans ?_
    rw [l2sq38_star]
    exact div_le_div_of_nonneg_right hd (by positivity)
  have hGeq : ∀ x, G x = ((1 / (2 * η) : ℝ) : ℂ) * star (U x) +
      ((-(1 / (2 * η)) : ℝ) : ℂ) * G' x := by
    intro x
    have h := resolv38_expand38 hη0 hUs x
    have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη0.ne'
    simp only [hGdef, hG'def]
    rw [h]
    push_cast
    field_simp
    ring
  obtain ⟨E, hE, hEb⟩ := pair_F_decomp_r3c hη0 hA0 hd0 hU.cont hG.cont hG.cont' hA hGb hGeq hG'l
  have hF : PerC1_38 (fun y => U y * G y ^ 2)
      (fun y => U₁ y * G y ^ 2 + U y * (2 * G y * G' y)) := hU.mul hG.pow_two
  have hTb := pair_resolv_Fderiv_le_r3c hη0 hA0 hd0 hU hG hA hGb hd hG'l
  set T : ℂ := pair38 U (resolv38 η (fun y => U₁ y * G y ^ 2 + U y * (2 * G y * G' y)))
    with hTdef
  obtain ⟨_, hrem, _⟩ := born_remainder38 U Γ hU.cont hU.per hA0 hA hη hΓc hΓp hΓd hΓb
  set R : ℝ → ℂ := resolv38 η (fun y => U y * G y ^ 2) with hRdef
  have hRc : Continuous R := (perC1_resolv38 hη0 hF).cont
  have hR'c : Continuous (resolv38 η (fun y => U₁ y * G y ^ 2 + U y * (2 * G y * G' y))) :=
    (perC1_resolv38 hη0 hF).cont'
  -- the remainder
  set rem : ℝ → ℂ := fun x => Γ x - G x - (-R x) with hremdef
  have hremc : Continuous rem := (hΓc.sub hG.cont).sub hRc.neg
  have hremb : ∀ x, ‖rem x‖ ≤ A ^ 5 / η ^ 5 := hrem
  have hpr : ‖pair38 U rem‖ ≤ A * (A ^ 5 / η ^ 5) := by
    unfold pair38
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0:ℝ)) (b := 1) (f := fun x => U x * rem x) (C := A * (A ^ 5 / η ^ 5))
      (fun x _ => by
        rw [norm_mul]; exact mul_le_mul (hA x) (hremb x) (norm_nonneg _) hA0)
    simpa using this
  -- expansion of `⟪U, R F⟫`
  have hRF : pair38 U R = pair38 U (fun y => U y * G y ^ 2) / ((2 * η : ℝ) : ℂ) -
      T / ((2 * η : ℝ) : ℂ) := by
    have h1 : ∀ x, U x * R x = U x * (U x * G x ^ 2) / ((2 * η : ℝ) : ℂ) -
        U x * resolv38 η (fun y => U₁ y * G y ^ 2 + U y * (2 * G y * G' y)) x /
          ((2 * η : ℝ) : ℂ) := by
      intro x
      have := resolv38_expand38 hη0 hF x
      simp only [hRdef]
      rw [this]
      push_cast
      ring
    unfold pair38
    simp only [hTdef, pair38]
    rw [show (fun x => U x * R x) = fun x => U x * (U x * G x ^ 2) / ((2 * η : ℝ) : ℂ) -
        U x * resolv38 η (fun y => U₁ y * G y ^ 2 + U y * (2 * G y * G' y)) x /
          ((2 * η : ℝ) : ℂ) from funext h1]
    have hi1 : IntervalIntegrable (fun x => U x * (U x * G x ^ 2) / ((2 * η : ℝ) : ℂ))
        MeasureTheory.volume 0 1 :=
      ((hU.cont.mul (hU.cont.mul (hG.cont.pow 2))).div_const _).intervalIntegrable 0 1
    have hi2 : IntervalIntegrable (fun x => U x *
        resolv38 η (fun y => U₁ y * G y ^ 2 + U y * (2 * G y * G' y)) x / ((2 * η : ℝ) : ℂ))
        MeasureTheory.volume 0 1 :=
      ((hU.cont.mul hR'c).div_const _).intervalIntegrable 0 1
    rw [intervalIntegral.integral_sub hi1 hi2,
      intervalIntegral.integral_div, intervalIntegral.integral_div]
  -- decomposition of `⟪U, Γ - G⟫`
  have hdecomp : pair38 U (fun x => Γ x - G x) = pair38 U rem - pair38 U R := by
    unfold pair38
    have h1 : ∀ x, U x * (Γ x - G x) = U x * rem x - U x * R x := by
      intro x; simp only [hremdef]; ring
    rw [show (fun x => U x * (Γ x - G x)) = fun x => U x * rem x - U x * R x from funext h1,
      intervalIntegral.integral_sub
        (f := fun x => U x * rem x) (g := fun x => U x * R x)
        ((hU.cont.mul hremc).intervalIntegrable 0 1)
        ((hU.cont.mul hRc).intervalIntegrable 0 1)]
  set J : ℝ := ∫ x in (0:ℝ)..1, ‖U x‖ ^ 4 with hJ
  have hP : pair38 U (fun x => Γ x - G x) = pair38 U rem -
      ((((J / (4 * η ^ 2) : ℝ) : ℂ) + E) / ((2 * η : ℝ) : ℂ) - T / ((2 * η : ℝ) : ℂ)) := by
    rw [hdecomp, hRF, hE]
  have hre : (pair38 U (fun x => Γ x - G x)).re = (pair38 U rem).re -
      (J / (4 * η ^ 2) + E.re) / (2 * η) + T.re / (2 * η) := by
    rw [hP]
    simp only [Complex.sub_re, Complex.div_ofReal_re, Complex.add_re, Complex.ofReal_re]
    ring
  have hkey : η ^ 3 * (pair38 U (fun x => Γ x - G x)).re + J / 8 =
      η ^ 3 * (pair38 U rem).re - η ^ 2 / 2 * E.re + η ^ 2 / 2 * T.re := by
    rw [hre]
    field_simp
    ring
  show |η ^ 3 * (pair38 U (fun x => Γ x - G x)).re + J / 8| ≤ _
  rw [hkey]
  have b1 : |(pair38 U rem).re| ≤ A * (A ^ 5 / η ^ 5) :=
    (Complex.abs_re_le_norm _).trans hpr
  have b2 : |E.re| ≤ A ^ 3 * d / (4 * η ^ 3) := (Complex.abs_re_le_norm _).trans hEb
  have b3 : |T.re| ≤ A ^ 3 * d / (2 * η ^ 3) := (Complex.abs_re_le_norm _).trans hTb
  have hη3 : 0 < η ^ 3 := by positivity
  have hη2' : 0 < η ^ 2 := by positivity
  calc |η ^ 3 * (pair38 U rem).re - η ^ 2 / 2 * E.re + η ^ 2 / 2 * T.re|
      ≤ |η ^ 3 * (pair38 U rem).re| + |η ^ 2 / 2 * E.re| + |η ^ 2 / 2 * T.re| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ = η ^ 3 * |(pair38 U rem).re| + η ^ 2 / 2 * |E.re| + η ^ 2 / 2 * |T.re| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hη3, abs_of_pos (by positivity : 0 < η ^ 2 / 2)]
    _ ≤ η ^ 3 * (A * (A ^ 5 / η ^ 5)) + η ^ 2 / 2 * (A ^ 3 * d / (4 * η ^ 3)) +
          η ^ 2 / 2 * (A ^ 3 * d / (2 * η ^ 3)) := by gcongr
    _ = A ^ 6 / η ^ 2 + 3 * (A ^ 3 * d) / (8 * η) := by field_simp; ring
    _ ≤ (A ^ 6 + A ^ 3 * d) / η := by
        have h1 : A ^ 6 / η ^ 2 ≤ A ^ 6 / η :=
          div_le_div_of_nonneg_left (by positivity) hη0 (by nlinarith)
        have h2 : 3 * (A ^ 3 * d) / (8 * η) ≤ A ^ 3 * d / η := by
          rw [div_le_div_iff₀ (by positivity) hη0]
          have : 0 ≤ A ^ 3 * d := by positivity
          nlinarith
        rw [add_div]
        linarith

/-! ## The core estimate on planes (section 2 of the note) -/

/-- section 2 of the note -/
theorem r3c_k1_core (B : ℝ) : ∃ η₀ C : ℝ, 0 < η₀ ∧ 0 ≤ C ∧ ∀ (N : ℕ) (z : FourierPlane N),
    ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 1 * ‖z i‖ ^ 2 ≤ B ^ 2 →
    ∀ η : ℝ, η₀ ≤ η → ∀ Γ : ℝ → ℂ, Continuous Γ → Function.Periodic Γ 1 →
      (∀ x, HasDerivAt Γ (-(2*η) * Γ x + star (planeReal N z x) -
          planeReal N z x * Γ x ^ 2) x) →
      (∀ x, ‖Γ x - resolv38 η (fun y => star (planeReal N z y)) x‖ ≤
          (Real.sqrt bracketSumE02_38 * |B|) ^ 3 / (4 * η ^ 3)) →
      |η ^ 3 * (pair38 (planeReal N z)
          (fun x => Γ x - resolv38 η (fun y => star (planeReal N z y)) x)).re +
        (∫ x in (0:ℝ)..1, ‖planeReal N z x‖ ^ 4) / 8| ≤ C / η := by
  set A : ℝ := Real.sqrt bracketSumE02_38 * |B| with hAdef
  set d : ℝ := 2 * Real.pi * |B| with hddef
  have hA0 : 0 ≤ A := mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hd0 : 0 ≤ d := by positivity
  refine ⟨max (4 * A) 1, A ^ 6 + A ^ 3 * d, lt_of_lt_of_le one_pos (le_max_right _ _),
    by positivity, ?_⟩
  intro N z hS η hη Γ hΓc hΓp hΓd hΓb
  have hS' : ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 1 * ‖z i‖ ^ 2 ≤
      |B| ^ 2 := by rwa [sq_abs]
  have hUb : ∀ x, ‖planeReal N z x‖ ≤ A := by
    intro x
    refine (plane_sup_le_r3c N z x).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    calc Real.sqrt (∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 1 * ‖z i‖ ^ 2)
        ≤ Real.sqrt (|B| ^ 2) := Real.sqrt_le_sqrt hS'
      _ = |B| := Real.sqrt_sq (abs_nonneg _)
  have hd : l2sq38 (planeReal N (derivativePlane N z)) ≤ d ^ 2 := by
    have h := plane_l2_le_r3c N z 1
    simp only [Function.iterate_one, mul_one] at h
    unfold l2sq38
    refine h.trans ?_
    have hd2 : d ^ 2 = (2 * Real.pi) ^ 2 * |B| ^ 2 := by rw [hddef]; ring
    rw [hd2]
    exact mul_le_mul_of_nonneg_left hS' (by positivity)
  exact r3c_k1_abstract38 (perC1_plane38 N z) hA0 hUb hd0 hd hη Γ hΓc hΓp hΓd hΓb

/-! ## Nonlinear charges for `j = 0, 1` -/

theorem nonlinCharge_zero_r3c (N : ℕ) (z : FourierPlane N) :
    localCharge38 (planeReal N z) 0 - ∑ i : Fin (2*N+1),
      (2*Real.pi*(modeIndex N i : ℤ))^(2*0) * ‖z i‖^2 = 0 := by
  rw [planeQ0_local38, planeReal_integral_norm_sq38]
  simp

theorem nonlinCharge_one_r3c (N : ℕ) (z : FourierPlane N) :
    localCharge38 (planeReal N z) 1 - ∑ i : Fin (2*N+1),
      (2*Real.pi*(modeIndex N i : ℤ))^(2*1) * ‖z i‖^2 =
      ∫ x in (0:ℝ)..1, ‖planeReal N z x‖ ^ 4 := by
  rw [planeQ2_local38]
  have hc : Continuous (planeReal N z) := (planeReal_smooth38 N z).continuous
  have hd : Continuous (planeReal N (derivativePlane N z)) := (planeReal_smooth38 N _).continuous
  rw [intervalIntegral.integral_add
    (f := fun x => ‖planeReal N (derivativePlane N z) x‖ ^ 2) (g := fun x => ‖planeReal N z x‖ ^ 4)
    ((hd.norm.pow 2).intervalIntegrable 0 1)
    ((hc.norm.pow 4).intervalIntegrable 0 1), planeReal_integral_norm_sq38]
  have : ∑ i : Fin (2 * N + 1), ‖derivativePlane N z i‖ ^ 2 =
      ∑ i : Fin (2*N+1), (2*Real.pi*(modeIndex N i : ℤ))^(2*1) * ‖z i‖^2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [derivativePlane, norm_mul, mul_pow, Complex.norm_I, Complex.norm_ofNat,
      Complex.norm_real, Complex.norm_intCast, Real.norm_eq_abs, mul_one, sq_abs]
    ring
  rw [this]
  ring

/-! ## The final theorem -/

theorem nonlinRiccatiSmoothBound38_one : NonlinRiccatiSmoothBound38 1 := by
  intro B
  obtain ⟨η₁, hη₁, hP⟩ := r3c_im_eq_pair38 |B| (abs_nonneg B)
  obtain ⟨η₂, C, hη₂, hC, hcore⟩ := r3c_k1_core B
  refine ⟨max η₁ η₂, C, lt_max_of_lt_left hη₁, hC, ?_⟩
  intro N z hS η hη
  have hS' : ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 1 * ‖z i‖ ^ 2 ≤
      |B| ^ 2 := by rwa [sq_abs]
  have hηpos : 0 < η := lt_of_lt_of_le hη₁ ((le_max_left _ _).trans hη)
  obtain ⟨Γ, hΓc, hΓp, hΓd, hΓb, hΓk⟩ := hP N z hS' η ((le_max_left _ _).trans hη)
  have hcr := hcore N z hS η ((le_max_right _ _).trans hη) Γ hΓc hΓp hΓd hΓb
  -- unfold the sum over `j ∈ range 2`
  have hsum : ∑ j ∈ Finset.range (1 + 1), (-1:ℝ)^j / (2 * 4^j * η^(2*j+1)) *
      (localCharge38 (planeReal N z) j -
        ∑ i : Fin (2*N+1), (2*Real.pi*(modeIndex N i : ℤ))^(2*j) * ‖z i‖^2) =
      -((∫ x in (0:ℝ)..1, ‖planeReal N z x‖ ^ 4) / (8 * η ^ 3)) := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, nonlinCharge_zero_r3c,
      nonlinCharge_one_r3c]
    field_simp
    ring
  have hqu := quadRiccati38_eq_pair38 N z hηpos
  have hpair : (pair38 (planeReal N z)
      (fun x => Γ x - resolv38 η (fun y => star (planeReal N z y)) x)).re =
      (pair38 (planeReal N z) Γ).re -
        (pair38 (planeReal N z) (resolv38 η (fun y => star (planeReal N z y)))).re := by
    have hUc : Continuous (planeReal N z) := (planeReal_smooth38 N z).continuous
    have hGc : Continuous (resolv38 η (fun y => star (planeReal N z y))) :=
      (perC1_resolv38 hηpos (perC1_plane38 N z).star).cont
    have hint : ∫ x in (0:ℝ)..1, planeReal N z x *
        (Γ x - resolv38 η (fun y => star (planeReal N z y)) x) =
        (∫ x in (0:ℝ)..1, planeReal N z x * Γ x) -
          ∫ x in (0:ℝ)..1, planeReal N z x * resolv38 η (fun y => star (planeReal N z y)) x := by
      rw [← intervalIntegral.integral_sub
        (f := fun x => planeReal N z x * Γ x)
        (g := fun x => planeReal N z x * resolv38 η (fun y => star (planeReal N z y)) x)
        ((hUc.mul hΓc).intervalIntegrable 0 1) ((hUc.mul hGc).intervalIntegrable 0 1)]
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      simp only [mul_sub]
    show (∫ x in (0:ℝ)..1, planeReal N z x *
        (Γ x - resolv38 η (fun y => star (planeReal N z y)) x)).re = _
    rw [hint, Complex.sub_re]
    rfl
  rw [hsum, hΓk, hqu]
  have e : η ^ (2 * 1 + 1) * ((pair38 (planeReal N z) Γ).re -
      (pair38 (planeReal N z) (resolv38 η (fun y => star (planeReal N z y)))).re -
      -((∫ x in (0:ℝ)..1, ‖planeReal N z x‖ ^ 4) / (8 * η ^ 3))) =
      η ^ 3 * (pair38 (planeReal N z)
          (fun x => Γ x - resolv38 η (fun y => star (planeReal N z y)) x)).re +
        (∫ x in (0:ℝ)..1, ‖planeReal N z x‖ ^ 4) / 8 := by
    rw [hpair]
    field_simp
    ring
  rw [e]
  exact hcr

end NlsGge.SpectralFoundations
