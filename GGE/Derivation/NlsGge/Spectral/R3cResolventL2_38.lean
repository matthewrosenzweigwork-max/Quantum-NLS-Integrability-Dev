import NlsGge.Spectral.R3cResolventCore38
import NlsGge.Hierarchy.PeriodicIntegrationByParts
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Pilot NlsGge.HierarchyRiccati.Core

/-! # R3c piece P1b: `L²` energy bounds for the resolvents, transpose identity, periodic IBP

Everything is proved from the ODEs `R g' + 2η R g = g` (no Fourier analysis, no Fubini). -/

/-! ## L6: pairing bounds -/

theorem l2sq38_nonneg (f : ℝ → ℂ) : 0 ≤ l2sq38 f :=
  intervalIntegral.integral_nonneg zero_le_one (fun x _ => by positivity)

theorem norm_pair38_le_l2 {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    ‖pair38 f g‖ ≤ Real.sqrt (l2sq38 f) * Real.sqrt (l2sq38 g) := by
  have hfc : Continuous fun x => ‖f x‖ := hf.norm
  have hgc : Continuous fun x => ‖g x‖ := hg.norm
  have h1 : ‖pair38 f g‖ ≤ ∫ x in (0:ℝ)..1, ‖f x‖ * ‖g x‖ := by
    unfold pair38
    refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans ?_
    simp only [norm_mul]
    exact le_rfl
  set A := l2sq38 f with hA
  set B := l2sq38 g with hB
  set C := ∫ x in (0:ℝ)..1, ‖f x‖ * ‖g x‖ with hC
  have hA0 : 0 ≤ A := l2sq38_nonneg f
  have hB0 : 0 ≤ B := l2sq38_nonneg g
  have hC0 : 0 ≤ C :=
    intervalIntegral.integral_nonneg zero_le_one (fun x _ => by positivity)
  have hpoly : ∀ t : ℝ, 0 ≤ A * (t * t) + (2 * C) * t + B := by
    intro t
    have hnn : 0 ≤ ∫ x in (0:ℝ)..1, (t * ‖f x‖ + ‖g x‖) ^ 2 :=
      intervalIntegral.integral_nonneg zero_le_one (fun x _ => by positivity)
    have hexp : ∫ x in (0:ℝ)..1, (t * ‖f x‖ + ‖g x‖) ^ 2 = A * (t * t) + (2 * C) * t + B := by
      have e1 : ∀ x, (t * ‖f x‖ + ‖g x‖) ^ 2
          = (t * t) * ‖f x‖ ^ 2 + (2 * t) * (‖f x‖ * ‖g x‖) + ‖g x‖ ^ 2 := fun x => by ring
      simp_rw [e1]
      have i1 : IntervalIntegrable (fun x => (t * t) * ‖f x‖ ^ 2) volume 0 1 :=
        (continuous_const.mul (hfc.pow 2)).intervalIntegrable 0 1
      have i2 : IntervalIntegrable (fun x => (2 * t) * (‖f x‖ * ‖g x‖)) volume 0 1 :=
        (continuous_const.mul (hfc.mul hgc)).intervalIntegrable 0 1
      have i3 : IntervalIntegrable (fun x => ‖g x‖ ^ 2) volume 0 1 :=
        (hgc.pow 2).intervalIntegrable 0 1
      rw [intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      simp only [hA, hB, hC, l2sq38]
      ring
    linarith
  have hdisc := discrim_le_zero hpoly
  unfold discrim at hdisc
  have hsq : C ^ 2 ≤ A * B := by nlinarith
  have : C ≤ Real.sqrt (A * B) := Real.le_sqrt_of_sq_le hsq
  rw [Real.sqrt_mul hA0] at this
  exact h1.trans this

theorem l2sq38_le_sup {f : ℝ → ℂ} (hf : Continuous f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) :
    l2sq38 f ≤ M ^ 2 := by
  unfold l2sq38
  have h : ∫ x in (0:ℝ)..1, ‖f x‖ ^ 2 ≤ ∫ x in (0:ℝ)..1, M ^ 2 :=
    intervalIntegral.integral_mono_on zero_le_one ((hf.norm.pow 2).intervalIntegrable 0 1)
      (continuous_const.intervalIntegrable 0 1)
      (fun x _ => pow_le_pow_left₀ (norm_nonneg _) (hM x) 2)
  simpa using h

theorem norm_pair38_le_sup {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) {M : ℝ}
    (hM : ∀ x, ‖f x‖ ≤ M) : ‖pair38 f g‖ ≤ M * Real.sqrt (l2sq38 g) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine (norm_pair38_le_l2 hf hg).trans ?_
  have : Real.sqrt (l2sq38 f) ≤ M := by
    calc Real.sqrt (l2sq38 f) ≤ Real.sqrt (M ^ 2) := Real.sqrt_le_sqrt (l2sq38_le_sup hf hM)
      _ = M := Real.sqrt_sq hM0
  exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)

theorem l2sq38_mul_le {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) {M : ℝ}
    (hM : ∀ x, ‖f x‖ ≤ M) : l2sq38 (fun x => f x * g x) ≤ M ^ 2 * l2sq38 g := by
  unfold l2sq38
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on zero_le_one
    (((hf.mul hg).norm.pow 2).intervalIntegrable 0 1)
    ((continuous_const.mul (hg.norm.pow 2)).intervalIntegrable 0 1) (fun x _ => ?_)
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hM x) 2) (by positivity)

/-! ## Periodic integration by parts and regularity of the resolvents -/

theorem pair38_ibp {f f' g g' : ℝ → ℂ} (hf : PerC1_38 f f') (hg : PerC1_38 g g') :
    pair38 f g' = -pair38 f' g :=
  NlsGge.HierarchyRiccati.unitPeriod_integral_mul_deriv_eq_neg_deriv_mul hf.per hg.per
    (fun x _ => hf.deriv x) (fun x _ => hg.deriv x)
    (hf.cont'.intervalIntegrable 0 1) (hg.cont'.intervalIntegrable 0 1)

theorem perC1_resolv38_of_cont {η : ℝ} (hη : 0 < η) {g : ℝ → ℂ} (hg : Continuous g)
    (hp : Function.Periodic g 1) :
    PerC1_38 (resolv38 η g) (fun x => -(2 * (η : ℂ)) * resolv38 η g x + g x) := by
  have hd := resolv38_hasDerivAt_periodic38 hη hg hp
  have hc : Continuous (resolv38 η g) :=
    continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hper : Function.Periodic (resolv38 η g) 1 := resolv38_periodic hp
  exact
    { cont := hc
      cont' := (continuous_const.mul hc).add hg
      per := hper
      per' := fun y => by simp only [hper y, hp y]
      deriv := hd }

theorem perC1_resolvT38_of_cont {η : ℝ} (hη : 0 < η) {g : ℝ → ℂ} (hg : Continuous g)
    (hp : Function.Periodic g 1) :
    PerC1_38 (resolvT38 η g) (fun x => 2 * (η : ℂ) * resolvT38 η g x - g x) := by
  have hd := resolvT38_hasDerivAt hη hg hp
  have hc : Continuous (resolvT38 η g) :=
    continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hper : Function.Periodic (resolvT38 η g) 1 := resolvT38_periodic hp
  exact
    { cont := hc
      cont' := (continuous_const.mul hc).sub hg
      per := hper
      per' := fun y => by simp only [hper y, hp y]
      deriv := hd }

/-! ## L5: IBP across `R` and transpose -/

theorem pair38_resolv_ibp {η : ℝ} (hη : 0 < η) {f f' g g' : ℝ → ℂ} (hf : PerC1_38 f f')
    (hg : PerC1_38 g g') : pair38 f (resolv38 η g') = -pair38 f' (resolv38 η g) := by
  have hG := perC1_resolv38_of_cont hη hg.cont hg.per
  have h := pair38_ibp hf hG
  have hfun : resolv38 η g' = fun x => -(2 * (η : ℂ)) * resolv38 η g x + g x :=
    funext (resolv38_of_deriv38 hη hg)
  rw [hfun]
  exact h

theorem pair38_resolv_transpose {η : ℝ} (hη : 0 < η) {f g : ℝ → ℂ} (hf : Continuous f)
    (hg : Continuous g) (hfp : Function.Periodic f 1) (hgp : Function.Periodic g 1) :
    pair38 f (resolv38 η g) = pair38 (resolvT38 η f) g := by
  have hF := perC1_resolvT38_of_cont hη hf hfp
  have hG := perC1_resolv38_of_cont hη hg hgp
  set F := resolvT38 η f
  set G := resolv38 η g
  have hibp := pair38_ibp hF hG
  -- f = 2ηF - F', g = G' + 2ηG
  have e1 : pair38 f G = 2 * (η : ℂ) * pair38 F G - pair38 (fun x => 2 * (η : ℂ) * F x - f x) G := by
    unfold pair38
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr (fun x _ => ?_)
      simp only
      ring
    · exact ((continuous_const.mul (hF.cont.mul hG.cont))).intervalIntegrable 0 1
    · exact ((((continuous_const.mul hF.cont).sub hf).mul hG.cont)).intervalIntegrable 0 1
  have e2 : pair38 F g = pair38 F (fun x => -(2 * (η : ℂ)) * G x + g x)
      + 2 * (η : ℂ) * pair38 F G := by
    unfold pair38
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add]
    · refine intervalIntegral.integral_congr (fun x _ => ?_)
      simp only
      ring
    · exact (hF.cont.mul ((continuous_const.mul hG.cont).add hg)).intervalIntegrable 0 1
    · exact ((continuous_const.mul (hF.cont.mul hG.cont))).intervalIntegrable 0 1
  rw [e1, e2, hibp]
  ring

/-! ## Energy bounds -/

theorem l2sq38_star (f : ℝ → ℂ) : l2sq38 (fun x => star (f x)) = l2sq38 f := by
  simp [l2sq38]

theorem resolv38_l2sq_le {η : ℝ} (hη : 0 < η) {g : ℝ → ℂ} (hg : Continuous g)
    (hp : Function.Periodic g 1) : l2sq38 (resolv38 η g) ≤ l2sq38 g / (2 * η) ^ 2 := by
  have hG := perC1_resolv38_of_cont hη hg hp
  set φ := resolv38 η g with hφ
  have hψd : ∀ x, HasDerivAt (fun y => φ y * star (φ y))
      ((-(2 * (η : ℂ)) * φ x + g x) * star (φ x)
        + φ x * star (-(2 * (η : ℂ)) * φ x + g x)) x :=
    fun x => (hG.deriv x).mul (hG.deriv x).star
  have hcont : Continuous fun x => (-(2 * (η : ℂ)) * φ x + g x) * star (φ x)
        + φ x * star (-(2 * (η : ℂ)) * φ x + g x) :=
    (hG.cont'.mul hG.cont.star).add (hG.cont.mul hG.cont'.star)
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hψd x)
    (hcont.intervalIntegrable 0 1)
  have hper : φ 1 * star (φ 1) = φ 0 * star (φ 0) := by
    have := hG.per 0
    rw [zero_add] at this
    rw [this]
  rw [hper, sub_self] at hint
  -- expand the integrand
  have hexp : ∀ x, (-(2 * (η : ℂ)) * φ x + g x) * star (φ x)
        + φ x * star (-(2 * (η : ℂ)) * φ x + g x)
      = -(4 * (η : ℂ)) * ((‖φ x‖ ^ 2 : ℝ) : ℂ) + (g x * star (φ x) + φ x * star (g x)) := by
    intro x
    have h1 : ((‖φ x‖ ^ 2 : ℝ) : ℂ) = φ x * star (φ x) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hs : star (-(2 * (η : ℂ)) * φ x + g x) = -(2 * (η : ℂ)) * star (φ x) + star (g x) := by
      simp [Complex.conj_ofReal]
    rw [h1, hs]
    ring
  simp_rw [hexp] at hint
  have hi1 : IntervalIntegrable (fun x => -(4 * (η : ℂ)) * ((‖φ x‖ ^ 2 : ℝ) : ℂ)) volume 0 1 :=
    (continuous_const.mul (Complex.continuous_ofReal.comp (hG.cont.norm.pow 2))).intervalIntegrable 0 1
  have hi2 : IntervalIntegrable (fun x => g x * star (φ x) + φ x * star (g x)) volume 0 1 :=
    ((hg.mul hG.cont.star).add (hG.cont.mul hg.star)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal,
    intervalIntegral.integral_add (f := fun x => g x * star (φ x))
      (g := fun x => φ x * star (g x)) ((hg.mul hG.cont.star).intervalIntegrable 0 1)
      ((hG.cont.mul hg.star).intervalIntegrable 0 1)] at hint
  have hl : (∫ x in (0:ℝ)..1, ‖φ x‖ ^ 2) = l2sq38 φ := rfl
  rw [hl] at hint
  have heq : (4 * (η : ℂ)) * ((l2sq38 φ : ℝ) : ℂ) = pair38 g (fun x => star (φ x))
      + pair38 φ (fun x => star (g x)) := by
    unfold pair38
    linear_combination (-1 : ℂ) * hint
  have hnorm : 4 * η * l2sq38 φ ≤
      Real.sqrt (l2sq38 g) * Real.sqrt (l2sq38 φ) + Real.sqrt (l2sq38 φ) * Real.sqrt (l2sq38 g) := by
    have h0 := congrArg norm heq
    have hl0 : 0 ≤ l2sq38 φ := l2sq38_nonneg φ
    have hL : ‖(4 * (η : ℂ)) * ((l2sq38 φ : ℝ) : ℂ)‖ = 4 * η * l2sq38 φ := by
      rw [norm_mul, Complex.norm_real, Complex.norm_mul]
      simp [abs_of_pos hη, abs_of_nonneg hl0]
    rw [hL] at h0
    refine h0.trans_le ((norm_add_le _ _).trans ?_)
    have e1 := norm_pair38_le_l2 hg hG.cont.star
    have e2 := norm_pair38_le_l2 hG.cont hg.star
    rw [l2sq38_star] at e1 e2
    exact add_le_add e1 e2
  set a := Real.sqrt (l2sq38 φ) with ha
  set b := Real.sqrt (l2sq38 g) with hb
  have ha2 : a ^ 2 = l2sq38 φ := Real.sq_sqrt (l2sq38_nonneg φ)
  have hb2 : b ^ 2 = l2sq38 g := Real.sq_sqrt (l2sq38_nonneg g)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have key : 2 * η * a ≤ b := by
    rcases ha0.eq_or_lt with h | h
    · rw [← h]; simpa using hb0
    · have : (2 * η * a) * a ≤ b * a := by nlinarith
      exact le_of_mul_le_mul_right this h
  rw [← ha2, ← hb2, ← div_pow]
  exact pow_le_pow_left₀ ha0 ((le_div_iff₀ (by positivity)).mpr (by linarith)) 2

theorem l2sq38_comp_neg {h : ℝ → ℂ} (hp : Function.Periodic h 1) :
    l2sq38 (fun y => h (-y)) = l2sq38 h := by
  unfold l2sq38
  have hper : Function.Periodic (fun y => ‖h y‖ ^ 2) 1 := fun y => by simp only [hp y]
  have h1 := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := 1) (fun y => ‖h y‖ ^ 2)
  rw [h1]
  have h2 := hper.intervalIntegral_add_eq (-1) 0
  simp only [neg_add_cancel, zero_add] at h2
  simpa using h2

theorem resolvT38_l2sq_le {η : ℝ} (hη : 0 < η) {g : ℝ → ℂ} (hg : Continuous g)
    (hp : Function.Periodic g 1) : l2sq38 (resolvT38 η g) ≤ l2sq38 g / (2 * η) ^ 2 := by
  have h : l2sq38 (resolv38 η fun y => g (-y)) ≤ l2sq38 (fun y => g (-y)) / (2 * η) ^ 2 :=
    resolv38_l2sq_le hη (hg.comp continuous_neg) (periodic_comp_neg38 hp)
  have e : resolvT38 η g = fun y => resolv38 η (fun y => g (-y)) (-y) := rfl
  rw [e, l2sq38_comp_neg (resolv38_periodic (periodic_comp_neg38 hp))]
  rwa [l2sq38_comp_neg hp] at h

end NlsGge.SpectralFoundations
end
