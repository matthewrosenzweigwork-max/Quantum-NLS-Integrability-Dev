import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS023Support1
import NlsGge.ThirdConsultation.KSPS.KSPSUniformU3
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform6

/- KSPS025U9 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/ThirdConsultation/KSPS/KSPS025Uniform9.lean. Pro round-15 SUPPORT (never a packet), chain B.
   UNIFORM INVERSE-PHASE GERM (input (ii) of the uniform KSPS-024 tail h24 of KSPS025U7/U8): one radius r0 > 0 and
   one constant CT ≥ 0 such that for EVERY φ in the order-N Sobolev ball of radius B₀ there is ζ solving
   ζ(y) + P_{N+1}(y/(π + y ζ(y))) = 0 with ‖ζ(y)‖ ≤ 1 and Taylor remainder ≤ CT ‖y‖^(N+2) for all ‖y‖ ≤ r0
   (the landed KSPS023T germ is per φ only).
   Route (the source's analytic inverse-phase germ, made quantitative):
   (1) generic part, for any entire P with P 0 = 0, ‖P w‖ ≤ A‖w‖ and ‖P u - P v‖ ≤ Λ‖u - v‖ on the unit disc:
       on ‖y‖ ≤ r = 1/(A + Λ + 4) the map a ↦ -P(y/(π + y a)) sends the unit disc into itself and is a
       1/2-contraction; the iterates g_j (g_0 = 0) are holomorphic on the open disc and converge geometrically,
       uniformly, to a fixed point ζ (Banach iteration written out), so ζ is holomorphic (Mathlib
       TendstoLocallyUniformlyOn.differentiableOn), ζ 0 = 0, ‖ζ‖ ≤ 1;
   (2) uniqueness of the fixed point identifies ζ near 0 with the KSPS023T germ, so the Taylor coefficients of ζ are
       the concrete spectralCoefficient φ k (k ≤ N+1);
   (3) Cauchy's estimate (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le) plus the Taylor series on the
       disc (Complex.hasSum_taylorSeries_on_ball) give the remainder bound 2 (2/r)^(N+2) ‖y‖^(N+2) on ‖y‖ ≤ r/4;
   (4) A = (N+1) L, Λ = (N+1)(N+1) L with L the landed ball-uniform bound KSPSU3.integralRiccatiLeft_uniform.
   Support-local defs Tmap/gIt/zeta are literal abbreviations of the fixed-point map, its iterates and their limit.
   Nothing assumed. -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS025U9
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation.KSPS
open Metric Filter
open scoped Topology

/-! ### Generic fixed-point germ -/

def Tmap (P : ℂ → ℂ) (y a : ℂ) : ℂ := -P (y / ((Real.pi : ℂ) + y * a))

def gIt (P : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => fun _ => 0
  | j + 1 => fun y => Tmap P y (gIt P j y)

def zeta (P : ℂ → ℂ) (y : ℂ) : ℂ := limUnder atTop (fun j => gIt P j y)

def rad (A Λ : ℝ) : ℝ := 1 / (A + Λ + 4)

theorem rad_facts (A Λ : ℝ) (hA : 0 ≤ A) (hΛ : 0 ≤ Λ) :
    0 < rad A Λ ∧ rad A Λ ≤ 1 / 4 ∧ A * rad A Λ ≤ 1 ∧ Λ * rad A Λ ≤ 1 := by
  unfold rad
  have hp : 0 < A + Λ + 4 := by linarith
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ hp (by norm_num)]; linarith
  · rw [mul_one_div, div_le_one hp]; linarith
  · rw [mul_one_div, div_le_one hp]; linarith

theorem den_ge (y a : ℂ) (hy : ‖y‖ ≤ 1 / 4) (ha : ‖a‖ ≤ 1) : 2 ≤ ‖(Real.pi : ℂ) + y * a‖ := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hya : ‖y * a‖ ≤ 1 / 4 := by
    rw [norm_mul]; nlinarith [norm_nonneg y, norm_nonneg a]
  have h1 := norm_sub_norm_le ((Real.pi : ℂ)) (-(y * a))
  rw [sub_neg_eq_add, norm_neg, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le] at h1
  linarith

theorem den_ne (y a : ℂ) (hy : ‖y‖ ≤ 1 / 4) (ha : ‖a‖ ≤ 1) : (Real.pi : ℂ) + y * a ≠ 0 := by
  intro h0
  have := den_ge y a hy ha
  rw [h0, norm_zero] at this
  linarith

theorem quot_le (y a : ℂ) (hy : ‖y‖ ≤ 1 / 4) (ha : ‖a‖ ≤ 1) :
    ‖y / ((Real.pi : ℂ) + y * a)‖ ≤ ‖y‖ / 2 := by
  rw [norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) (den_ge y a hy ha)

theorem quot_sub_le (y a b : ℂ) (hy : ‖y‖ ≤ 1 / 4) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖y / ((Real.pi : ℂ) + y * a) - y / ((Real.pi : ℂ) + y * b)‖ ≤ ‖y‖ ^ 2 / 4 * ‖a - b‖ := by
  have ha0 := den_ne y a hy ha
  have hb0 := den_ne y b hy hb
  have e : y / ((Real.pi : ℂ) + y * a) - y / ((Real.pi : ℂ) + y * b) =
      y * y * (b - a) / (((Real.pi : ℂ) + y * a) * ((Real.pi : ℂ) + y * b)) := by
    field_simp
    ring
  rw [e, norm_div, norm_mul, norm_mul, norm_mul, norm_sub_rev b a]
  have h2 : (4 : ℝ) ≤ ‖(Real.pi : ℂ) + y * a‖ * ‖(Real.pi : ℂ) + y * b‖ := by
    have := den_ge y a hy ha
    have := den_ge y b hy hb
    nlinarith
  rw [div_le_iff₀ (by linarith)]
  have h3 : 0 ≤ ‖y‖ * ‖y‖ * ‖a - b‖ := by positivity
  calc ‖y‖ * ‖y‖ * ‖a - b‖ = ‖y‖ ^ 2 / 4 * ‖a - b‖ * 4 := by ring
    _ ≤ ‖y‖ ^ 2 / 4 * ‖a - b‖ * (‖(Real.pi : ℂ) + y * a‖ * ‖(Real.pi : ℂ) + y * b‖) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

theorem g_zero (P : ℂ → ℂ) (hP0 : P 0 = 0) (j : ℕ) : gIt P j 0 = 0 := by
  induction j with
  | zero => rfl
  | succ j _ =>
    show Tmap P 0 (gIt P j 0) = 0
    unfold Tmap
    rw [zero_div, hP0, neg_zero]

theorem le_zero_of_geom {x : ℝ} (h : ∀ n : ℕ, x ≤ 2 * (1 / 2 : ℝ) ^ n) : x ≤ 0 := by
  have ht : Tendsto (fun n : ℕ => 2 * (1 / 2 : ℝ) ^ n) atTop (𝓝 (2 * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul 2
  have := ge_of_tendsto' ht h
  linarith

section generic
variable (P : ℂ → ℂ) (A Λ : ℝ) (hA : 0 ≤ A) (hΛ : 0 ≤ Λ)
  (hPA : ∀ w : ℂ, ‖w‖ ≤ 1 → ‖P w‖ ≤ A * ‖w‖)
  (hPL : ∀ u v : ℂ, ‖u‖ ≤ 1 → ‖v‖ ≤ 1 → ‖P u - P v‖ ≤ Λ * ‖u - v‖)
include hA hΛ hPA

theorem T_le (y a : ℂ) (hy : ‖y‖ ≤ rad A Λ) (ha : ‖a‖ ≤ 1) : ‖Tmap P y a‖ ≤ 1 := by
  obtain ⟨hr0, hr4, hAr, -⟩ := rad_facts A Λ hA hΛ
  have hy4 : ‖y‖ ≤ 1 / 4 := hy.trans hr4
  have hq := quot_le y a hy4 ha
  unfold Tmap
  rw [norm_neg]
  refine (hPA _ (hq.trans (by linarith))).trans ?_
  have h1 : A * ‖y / ((Real.pi : ℂ) + y * a)‖ ≤ A * (‖y‖ / 2) := mul_le_mul_of_nonneg_left hq hA
  have h2 : A * ‖y‖ ≤ A * rad A Λ := mul_le_mul_of_nonneg_left hy hA
  nlinarith

include hPL in
theorem T_lip (y a b : ℂ) (hy : ‖y‖ ≤ rad A Λ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖Tmap P y a - Tmap P y b‖ ≤ 1 / 2 * ‖a - b‖ := by
  obtain ⟨hr0, hr4, -, hΛr⟩ := rad_facts A Λ hA hΛ
  have hy4 : ‖y‖ ≤ 1 / 4 := hy.trans hr4
  have hqa := quot_le y a hy4 ha
  have hqb := quot_le y b hy4 hb
  have hqs := quot_sub_le y a b hy4 ha hb
  unfold Tmap
  rw [neg_sub_neg, norm_sub_rev]
  refine (hPL _ _ (hqa.trans (by linarith)) (hqb.trans (by linarith))).trans ?_
  have h1 : Λ * ‖y / ((Real.pi : ℂ) + y * a) - y / ((Real.pi : ℂ) + y * b)‖ ≤
      Λ * (‖y‖ ^ 2 / 4 * ‖a - b‖) := mul_le_mul_of_nonneg_left hqs hΛ
  have hy0 := norm_nonneg y
  have h2 : Λ * ‖y‖ ≤ 1 := (mul_le_mul_of_nonneg_left hy hΛ).trans hΛr
  have h3 : Λ * ‖y‖ ^ 2 ≤ 1 / 4 := by
    have : Λ * ‖y‖ ^ 2 = (Λ * ‖y‖) * ‖y‖ := by ring
    rw [this]
    nlinarith
  have hab := norm_nonneg (a - b)
  have h4 : Λ * (‖y‖ ^ 2 / 4 * ‖a - b‖) = (Λ * ‖y‖ ^ 2) / 4 * ‖a - b‖ := by ring
  rw [h4] at h1
  nlinarith

theorem g_le (j : ℕ) (y : ℂ) (hy : ‖y‖ ≤ rad A Λ) : ‖gIt P j y‖ ≤ 1 := by
  induction j with
  | zero => show ‖(0 : ℂ)‖ ≤ 1; simp
  | succ j ih => exact T_le P A Λ hA hΛ hPA y _ hy ih

include hPL in
theorem g_step (j : ℕ) (y : ℂ) (hy : ‖y‖ ≤ rad A Λ) :
    ‖gIt P (j + 1) y - gIt P j y‖ ≤ (1 / 2 : ℝ) ^ j := by
  induction j with
  | zero =>
    show ‖gIt P 1 y - 0‖ ≤ (1 / 2 : ℝ) ^ 0
    rw [sub_zero, pow_zero]
    exact g_le P A Λ hA hΛ hPA 1 y hy
  | succ j ih =>
    show ‖Tmap P y (gIt P (j + 1) y) - Tmap P y (gIt P j y)‖ ≤ (1 / 2 : ℝ) ^ (j + 1)
    refine (T_lip P A Λ hA hΛ hPA hPL y _ _ hy (g_le P A Λ hA hΛ hPA _ y hy)
      (g_le P A Λ hA hΛ hPA _ y hy)).trans ?_
    rw [pow_succ]
    linarith

theorem g_diff (hPd : Differentiable ℂ P) (j : ℕ) (y : ℂ) (hy : ‖y‖ < rad A Λ) :
    DifferentiableAt ℂ (gIt P j) y := by
  induction j with
  | zero => exact differentiableAt_const _
  | succ j ih =>
    obtain ⟨-, hr4, -, -⟩ := rad_facts A Λ hA hΛ
    have hden0 := den_ne y (gIt P j y) (hy.le.trans hr4) (g_le P A Λ hA hΛ hPA j y hy.le)
    have hinner : DifferentiableAt ℂ (fun z : ℂ => z / ((Real.pi : ℂ) + z * gIt P j z)) y :=
      differentiableAt_id.div ((differentiableAt_const _).add (differentiableAt_id.mul ih)) hden0
    exact (hPd.differentiableAt.comp y hinner).neg

include hPL in
theorem zeta_conv (y : ℂ) (hy : ‖y‖ ≤ rad A Λ) :
    Tendsto (fun j => gIt P j y) atTop (𝓝 (zeta P y)) ∧
      ∀ n : ℕ, ‖gIt P n y - zeta P y‖ ≤ 2 * (1 / 2 : ℝ) ^ n := by
  have hu : ∀ n : ℕ, dist (gIt P n y) (gIt P (n + 1) y) ≤ 1 * (1 / 2 : ℝ) ^ n := by
    intro n
    rw [dist_eq_norm, norm_sub_rev, one_mul]
    exact g_step P A Λ hA hΛ hPA hPL n y hy
  have hc := cauchySeq_of_le_geometric (1 / 2 : ℝ) 1 (by norm_num) hu
  have ht : Tendsto (fun j => gIt P j y) atTop (𝓝 (zeta P y)) := hc.tendsto_limUnder
  refine ⟨ht, fun n => ?_⟩
  have hd := dist_le_of_le_geometric_of_tendsto (1 / 2 : ℝ) 1 (by norm_num) hu ht n
  rw [dist_eq_norm] at hd
  refine hd.trans (le_of_eq ?_)
  ring

include hPL in
theorem zeta_le (y : ℂ) (hy : ‖y‖ ≤ rad A Λ) : ‖zeta P y‖ ≤ 1 :=
  le_of_tendsto' (zeta_conv P A Λ hA hΛ hPA hPL y hy).1.norm
    (fun j => g_le P A Λ hA hΛ hPA j y hy)

include hPL in
theorem zeta_fixed (y : ℂ) (hy : ‖y‖ ≤ rad A Λ) : zeta P y = Tmap P y (zeta P y) := by
  obtain ⟨-, hb⟩ := zeta_conv P A Λ hA hΛ hPA hPL y hy
  have hz := zeta_le P A Λ hA hΛ hPA hPL y hy
  have h : ∀ n : ℕ, ‖zeta P y - Tmap P y (zeta P y)‖ ≤ 2 * (1 / 2 : ℝ) ^ n := by
    intro n
    have e : zeta P y - Tmap P y (zeta P y) =
        (zeta P y - gIt P (n + 1) y) + (Tmap P y (gIt P n y) - Tmap P y (zeta P y)) := by
      show _ = (zeta P y - Tmap P y (gIt P n y)) + _
      ring
    rw [e]
    have h1 := hb (n + 1)
    rw [norm_sub_rev] at h1
    have h2 := T_lip P A Λ hA hΛ hPA hPL y _ _ hy (g_le P A Λ hA hΛ hPA n y hy) hz
    have h3 := hb n
    refine (norm_add_le _ _).trans ?_
    rw [pow_succ] at h1
    linarith
  have h0 := le_zero_of_geom h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)

include hPL in
theorem zeta_zero (hP0 : P 0 = 0) : zeta P 0 = 0 := by
  have hy : ‖(0 : ℂ)‖ ≤ rad A Λ := by rw [norm_zero]; exact (rad_facts A Λ hA hΛ).1.le
  obtain ⟨-, hb⟩ := zeta_conv P A Λ hA hΛ hPA hPL 0 hy
  have h : ∀ n : ℕ, ‖zeta P 0‖ ≤ 2 * (1 / 2 : ℝ) ^ n := by
    intro n
    have := hb n
    rwa [g_zero P hP0 n, zero_sub, norm_neg] at this
  exact norm_le_zero_iff.mp (le_zero_of_geom h)

include hPL in
theorem zeta_differentiableOn (hPd : Differentiable ℂ P) :
    DifferentiableOn ℂ (zeta P) (ball 0 (rad A Λ)) := by
  have hU : TendstoUniformlyOn (fun j => gIt P j) (zeta P) atTop (ball 0 (rad A Λ)) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have ht : Tendsto (fun n : ℕ => 2 * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul 2
      rwa [mul_zero] at this
    filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn y hy
    rw [mem_ball, dist_zero_right] at hy
    rw [dist_eq_norm, norm_sub_rev]
    exact lt_of_le_of_lt ((zeta_conv P A Λ hA hΛ hPA hPL y hy.le).2 n) hn
  refine hU.tendstoLocallyUniformlyOn.differentiableOn (Eventually.of_forall fun n => ?_) isOpen_ball
  intro y hy
  rw [mem_ball, dist_zero_right] at hy
  exact (g_diff P A Λ hA hΛ hPA hPd n y hy).differentiableWithinAt

include hPL in
/-- Uniqueness: any continuous solution germ vanishing at 0 agrees with `zeta P` near 0. -/
theorem zeta_eventuallyEq (ζ' : ℂ → ℂ) (hc : ContinuousAt ζ' 0) (h0 : ζ' 0 = 0)
    (heq : ∀ᶠ z : ℂ in 𝓝 0, ζ' z + P (z / ((Real.pi : ℂ) + z * ζ' z)) = 0) :
    zeta P =ᶠ[𝓝 0] ζ' := by
  have hr := (rad_facts A Λ hA hΛ).1
  have hs : ∀ᶠ z : ℂ in 𝓝 0, ‖ζ' z‖ ≤ 1 := by
    have h := hc.eventually (Metric.closedBall_mem_nhds (ζ' 0) one_pos)
    filter_upwards [h] with z hz
    rwa [dist_eq_norm, h0, sub_zero] at hz
  have hb : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ ≤ rad A Λ := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) hr] with z hz
    rwa [mem_closedBall, dist_zero_right] at hz
  filter_upwards [hs, hb, heq] with z h1 h2 h3
  have hf := zeta_fixed P A Λ hA hΛ hPA hPL z h2
  have hf' : ζ' z = Tmap P z (ζ' z) := by unfold Tmap; linear_combination h3
  have hl := T_lip P A Λ hA hΛ hPA hPL z _ _ h2 (zeta_le P A Λ hA hΛ hPA hPL z h2) h1
  rw [← hf, ← hf'] at hl
  have : ‖zeta P z - ζ' z‖ ≤ 0 := by nlinarith [norm_nonneg (zeta P z - ζ' z)]
  exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

end generic

/-! ### Generic Taylor remainder by Cauchy's estimate -/

theorem sum_Icc_eq_range (h : ℕ → ℂ) (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, h k = ∑ i ∈ Finset.range K, h (i + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem taylor_remainder (f : ℂ → ℂ) (r : ℝ) (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball 0 r))
    (hb : ∀ y ∈ ball (0 : ℂ) r, ‖f y‖ ≤ 1) (hf0 : f 0 = 0) (K : ℕ) (y : ℂ) (hy : ‖y‖ ≤ r / 4) :
    ‖f y - ∑ k ∈ Finset.Icc 1 K, iteratedDeriv k f 0 / ((Nat.factorial k) : ℂ) * y ^ k‖ ≤
      2 * (2 / r) ^ (K + 1) * ‖y‖ ^ (K + 1) := by
  set ρ : ℝ := r / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  clear_value ρ
  have hyb : y ∈ ball (0 : ℂ) r := by
    rw [mem_ball, dist_zero_right]; linarith
  -- Cauchy estimate on the sphere of radius ρ
  have hcau : ∀ m : ℕ, ‖iteratedDeriv m f 0‖ ≤ ((Nat.factorial m) : ℝ) * 1 / ρ ^ m := by
    intro m
    have hdc : DiffContOnCl ℂ f (ball 0 ρ) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball (0 : ℂ) hρ0.ne']
      exact hf.mono (closedBall_subset_ball (by linarith))
    refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m hρ0 hdc (fun z hz => ?_)
    refine hb z ?_
    rw [mem_sphere, dist_zero_right] at hz
    rw [mem_ball, dist_zero_right, hz]
    linarith
  set t : ℝ := ‖y‖ / ρ with ht
  clear_value t
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have ht2 : t ≤ 1 / 2 := by
    rw [ht, div_le_iff₀ hρ0]; linarith
  have hterm : ∀ m : ℕ, ‖((Nat.factorial m) : ℂ)⁻¹ • (y - 0) ^ m • iteratedDeriv m f 0‖ ≤ t ^ m := by
    intro m
    rw [sub_zero, smul_eq_mul, smul_eq_mul, norm_mul, norm_mul, norm_inv, norm_pow,
      Complex.norm_natCast]
    have hfac : (0 : ℝ) < ((Nat.factorial m) : ℝ) := by exact_mod_cast Nat.factorial_pos m
    calc ((Nat.factorial m) : ℝ)⁻¹ * (‖y‖ ^ m * ‖iteratedDeriv m f 0‖)
        ≤ ((Nat.factorial m) : ℝ)⁻¹ * (‖y‖ ^ m * (((Nat.factorial m) : ℝ) * 1 / ρ ^ m)) := by
          gcongr; exact hcau m
      _ = ‖y‖ ^ m / ρ ^ m := by field_simp
      _ = t ^ m := by rw [ht, div_pow]
  have hs := Complex.hasSum_taylorSeries_on_ball hf hyb
  have hs2 := (hasSum_nat_add_iff' (K + 1)).mpr hs
  have hg : HasSum (fun n : ℕ => t ^ (K + 1) * t ^ n) (t ^ (K + 1) * (1 - t)⁻¹) :=
    (hasSum_geometric_of_lt_one ht0 (by linarith)).mul_left _
  have hle := hs2.norm_le_of_bounded hg (fun n => by
    refine (hterm (n + (K + 1))).trans (le_of_eq ?_)
    rw [pow_add, mul_comm])
  -- identify the partial sum
  have hsum : ∑ i ∈ Finset.range (K + 1), ((Nat.factorial i) : ℂ)⁻¹ • (y - 0) ^ i • iteratedDeriv i f 0 =
      ∑ k ∈ Finset.Icc 1 K, iteratedDeriv k f 0 / ((Nat.factorial k) : ℂ) * y ^ k := by
    rw [Finset.sum_range_succ', sum_Icc_eq_range]
    simp only [sub_zero, smul_eq_mul, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul,
      iteratedDeriv_zero, hf0, add_zero]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [div_eq_mul_inv]
    ring
  rw [hsum] at hle
  refine hle.trans ?_
  have h1 : (1 - t)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have h2 : t ^ (K + 1) * (1 - t)⁻¹ ≤ t ^ (K + 1) * 2 :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  refine h2.trans (le_of_eq ?_)
  rw [ht, hρ, div_pow, div_pow, div_pow]
  field_simp

/-! ### The inverse-phase polynomial on the unit disc -/

theorem phasePoly_zero {N : ℕ} (φ : SobolevC N) (K : ℕ) :
    NlsGge.ThirdConsultation.KSPSRiccati.phasePolynomial φ K 0 = 0 := by
  unfold NlsGge.ThirdConsultation.KSPSRiccati.phasePolynomial
  rw [Finset.sum_eq_zero, mul_zero]
  intro k hk
  have hk1 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
  simp [hk1]

theorem pow_sub_pow_le (u v : ℂ) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (k : ℕ) :
    ‖u ^ k - v ^ k‖ ≤ k * ‖u - v‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : u ^ (k + 1) - v ^ (k + 1) = u * (u ^ k - v ^ k) + (u - v) * v ^ k := by ring
    rw [e]
    have hvk : ‖v ^ k‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hv
    calc ‖u * (u ^ k - v ^ k) + (u - v) * v ^ k‖
        ≤ ‖u * (u ^ k - v ^ k)‖ + ‖(u - v) * v ^ k‖ := norm_add_le _ _
      _ = ‖u‖ * ‖u ^ k - v ^ k‖ + ‖u - v‖ * ‖v ^ k‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * (k * ‖u - v‖) + ‖u - v‖ * 1 := by gcongr
      _ = ((k + 1 : ℕ) : ℝ) * ‖u - v‖ := by push_cast; ring

theorem phasePoly_lip_le {N : ℕ} (φ : SobolevC N) (K : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hI : ∀ k : ℕ, 1 ≤ k → k ≤ K → ‖integralRiccatiLeft φ k‖ ≤ L)
    (u v : ℂ) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖NlsGge.ThirdConsultation.KSPSRiccati.phasePolynomial φ K u -
      NlsGge.ThirdConsultation.KSPSRiccati.phasePolynomial φ K v‖ ≤ (K * K * L) * ‖u - v‖ := by
  unfold NlsGge.ThirdConsultation.KSPSRiccati.phasePolynomial
  rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, Complex.norm_I, one_mul]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ k ∈ Finset.Icc 1 K,
      ‖((2 * Complex.I) ^ k)⁻¹ * integralRiccatiLeft φ k * u ^ k -
        ((2 * Complex.I) ^ k)⁻¹ * integralRiccatiLeft φ k * v ^ k‖ ≤ K * L * ‖u - v‖ := by
    intro k hk
    have hk2 := (Finset.mem_Icc.mp hk).2
    have hc : ‖((2 * Complex.I) ^ k)⁻¹‖ ≤ 1 := by
      rw [norm_inv, norm_pow, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have e : ((2 * Complex.I) ^ k)⁻¹ * integralRiccatiLeft φ k * u ^ k -
        ((2 * Complex.I) ^ k)⁻¹ * integralRiccatiLeft φ k * v ^ k =
        ((2 * Complex.I) ^ k)⁻¹ * integralRiccatiLeft φ k * (u ^ k - v ^ k) := by ring
    rw [e, norm_mul, norm_mul]
    have hp := pow_sub_pow_le u v hu hv k
    have hkK : (k : ℝ) ≤ K := by exact_mod_cast hk2
    have hIk := hI k (Finset.mem_Icc.mp hk).1 hk2
    calc ‖((2 * Complex.I) ^ k)⁻¹‖ * ‖integralRiccatiLeft φ k‖ * ‖u ^ k - v ^ k‖
        ≤ 1 * L * (K * ‖u - v‖) := by
          gcongr
          exact hp.trans (mul_le_mul_of_nonneg_right hkK (norm_nonneg _))
      _ = K * L * ‖u - v‖ := by ring
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
  push_cast
  ring

/-! ### The uniform germ -/

theorem germ_of_bound {N : ℕ} (φ : SobolevC N) (L : ℝ) (hL : 0 ≤ L)
    (hI : ∀ k : ℕ, 1 ≤ k → k ≤ N + 1 → ‖integralRiccatiLeft φ k‖ ≤ L) :
    ∃ ζ : ℂ → ℂ, ∀ y : ℂ,
      ‖y‖ ≤ rad (((N + 1 : ℕ) : ℝ) * L) (((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) * L) / 4 →
      (Real.pi : ℂ) + y * ζ y ≠ 0 ∧
      ζ y + NlsGge.ThirdConsultation.KSPSRiccati.phasePolynomial φ (N + 1)
        (y / ((Real.pi : ℂ) + y * ζ y)) = 0 ∧
      ‖ζ y‖ ≤ 1 ∧
      ‖ζ y - ∑ k ∈ Finset.Icc 1 (N + 1),
          NlsGge.ThirdConsultation.KSPSRiccati.spectralCoefficient φ k * y ^ k‖ ≤
        2 * (2 / rad (((N + 1 : ℕ) : ℝ) * L) (((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) * L)) ^ (N + 2) *
          ‖y‖ ^ (N + 2) := by
  set P := NlsGge.ThirdConsultation.KSPSRiccati.phasePolynomial φ (N + 1) with hPdef
  set A : ℝ := ((N + 1 : ℕ) : ℝ) * L with hAdef
  set Λ : ℝ := ((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) * L with hΛdef
  have hA : 0 ≤ A := by positivity
  have hΛ : 0 ≤ Λ := by positivity
  have hPA : ∀ w : ℂ, ‖w‖ ≤ 1 → ‖P w‖ ≤ A * ‖w‖ := fun w hw =>
    NlsGge.ThirdConsultation.KSPS025U6.phasePoly_le φ (N + 1) L
      (fun k hk => hI k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2) w hw
  have hPL : ∀ u v : ℂ, ‖u‖ ≤ 1 → ‖v‖ ≤ 1 → ‖P u - P v‖ ≤ Λ * ‖u - v‖ := fun u v hu hv =>
    phasePoly_lip_le φ (N + 1) L hL hI u v hu hv
  have hPd : Differentiable ℂ P := NlsGge.ThirdConsultation.KSPS025U6.phasePoly_differentiable φ (N + 1)
  have hP0 : P 0 = 0 := phasePoly_zero φ (N + 1)
  obtain ⟨hr0, hr4, -, -⟩ := rad_facts A Λ hA hΛ
  -- the KSPS023T germ, to identify the Taylor coefficients
  obtain ⟨ζ', hζa, hζ0, hev, hcoef⟩ :=
    NlsGge.ThirdConsultation.KSPS023T.spectralCoefficient_consistent φ (N + 1) le_rfl
  have heq' : ∀ᶠ z : ℂ in 𝓝 0, ζ' z + P (z / ((Real.pi : ℂ) + z * ζ' z)) = 0 :=
    hev.mono fun z hz => hz.2
  have hEq := zeta_eventuallyEq P A Λ hA hΛ hPA hPL ζ' hζa.continuousAt hζ0 heq'
  have hcoef' : ∀ k ∈ Finset.Icc 1 (N + 1),
      NlsGge.ThirdConsultation.KSPSRiccati.spectralCoefficient φ k =
        iteratedDeriv k (zeta P) 0 / ((Nat.factorial k) : ℂ) := by
    intro k hk
    rw [hcoef k (Finset.mem_Icc.mp hk).2, hEq.iteratedDeriv_eq k]
  have hdiff := zeta_differentiableOn P A Λ hA hΛ hPA hPL hPd
  have hbd : ∀ y ∈ ball (0 : ℂ) (rad A Λ), ‖zeta P y‖ ≤ 1 := by
    intro y hy
    rw [mem_ball, dist_zero_right] at hy
    exact zeta_le P A Λ hA hΛ hPA hPL y hy.le
  refine ⟨zeta P, fun y hy => ?_⟩
  have hyr : ‖y‖ ≤ rad A Λ := by linarith
  have hz1 := zeta_le P A Λ hA hΛ hPA hPL y hyr
  refine ⟨den_ne y _ (hyr.trans hr4) hz1, ?_, hz1, ?_⟩
  · have hf := zeta_fixed P A Λ hA hΛ hPA hPL y hyr
    unfold Tmap at hf
    linear_combination hf
  · have htay := taylor_remainder (zeta P) (rad A Λ) hr0 hdiff hbd
      (zeta_zero P A Λ hA hΛ hPA hPL hP0) (N + 1) y hy
    have hs : ∑ k ∈ Finset.Icc 1 (N + 1),
        NlsGge.ThirdConsultation.KSPSRiccati.spectralCoefficient φ k * y ^ k =
        ∑ k ∈ Finset.Icc 1 (N + 1), iteratedDeriv k (zeta P) 0 / ((Nat.factorial k) : ℂ) * y ^ k :=
      Finset.sum_congr rfl (fun k hk => by rw [hcoef' k hk])
    rw [hs]
    exact htay

/-- UNIFORM inverse-phase germ on the order-`N` Sobolev ball (one radius, one Taylor constant). -/
theorem germ_uniform (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ r0 : ℝ, 0 < r0 ∧ ∃ CT : ℝ, 0 ≤ CT ∧
      ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∃ ζ : ℂ → ℂ, ∀ y : ℂ, ‖y‖ ≤ r0 →
        (Real.pi : ℂ) + y * ζ y ≠ 0 ∧
        ζ y + NlsGge.ThirdConsultation.KSPSRiccati.phasePolynomial φ (N + 1)
          (y / ((Real.pi : ℂ) + y * ζ y)) = 0 ∧
        ‖ζ y‖ ≤ 1 ∧
        ‖ζ y - ∑ k ∈ Finset.Icc 1 (N + 1),
            NlsGge.ThirdConsultation.KSPSRiccati.spectralCoefficient φ k * y ^ k‖ ≤
          CT * ‖y‖ ^ (N + 2) := by
  obtain ⟨L, hL, hIb⟩ := NlsGge.ThirdConsultation.KSPSU3.integralRiccatiLeft_uniform N hN B₀ hB₀
  set A : ℝ := ((N + 1 : ℕ) : ℝ) * L with hAdef
  set Λ : ℝ := ((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) * L with hΛdef
  have hA : 0 ≤ A := by positivity
  have hΛ : 0 ≤ Λ := by positivity
  have hr0 := (rad_facts A Λ hA hΛ).1
  refine ⟨rad A Λ / 4, by positivity, 2 * (2 / rad A Λ) ^ (N + 2), by positivity,
    fun φ hφ => germ_of_bound φ L hL (fun k h1 h2 => hIb φ hφ k h1 h2)⟩

end
end NlsGge.ThirdConsultation.KSPS025U9
