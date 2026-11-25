import Mathlib
import QuantumNLS.Local007AlgB
import QuantumNLS.Local007EvalS

/-! LOCAL-007 stage E2: pointwise values of the algebra elements, and the identity
`Phi c L F α t² = (4/(πL)) ∫_{-1}^{1} √(1-s²) D(α + t s) ds`, `D(z) = (L/2) (-H(z)/L²)^{1/2} Ω(f(z)/4)`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open BoundedContinuousFunction Metric Filter Topology Set MeasureTheory Complex
open scoped ENNReal NNReal
namespace QuantumNLS.Local007EvalT
open QuantumNLS.Local007AlgB

/-! ### Units and inverses -/

theorem inv_eval {g : A} {m : ℝ} (hm : 0 < m) (hg : ∀ θ, m ≤ ‖g θ‖) :
    ∃ gi : A, (∀ θ, gi θ = (g θ)⁻¹) ∧ g * gi = 1 ∧ Ring.inverse g = gi := by
  have hne : ∀ θ, g θ ≠ 0 := fun θ => norm_pos_iff.1 (lt_of_lt_of_le hm (hg θ))
  let gi : A := ofNormedAddCommGroup (fun θ => (g θ)⁻¹) (g.continuous.inv₀ hne) m⁻¹ (fun θ => by
    rw [norm_inv]; exact inv_anti₀ hm (hg θ))
  have h1 : g * gi = 1 := by
    ext θ
    change g θ * (g θ)⁻¹ = 1
    exact mul_inv_cancel₀ (hne θ)
  have hu : IsUnit g := ⟨⟨g, gi, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  refine ⟨gi, fun θ => rfl, h1, ?_⟩
  calc Ring.inverse g = Ring.inverse g * (g * gi) := by rw [h1, mul_one]
    _ = (Ring.inverse g * g) * gi := by rw [mul_assoc]
    _ = gi := by rw [Ring.inverse_mul_cancel g hu, one_mul]

/-! ### Series evaluated pointwise -/

theorem pow_apply' (y : A) (n : ℕ) (θ : ℝ) : (y ^ n) θ = (y θ) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, mul_apply, ih, pow_succ]

theorem sum_apply {c : ℕ → ℝ} (hr : 1 ≤ (FormalMultilinearSeries.ofScalars A c).radius) {y : A}
    (hy : ‖y‖ < 1) (θ : ℝ) :
    (FormalMultilinearSeries.ofScalars A c).sum y θ = ∑' n : ℕ, (c n : ℂ) * (y θ) ^ n := by
  have hmem : y ∈ Metric.eball (0 : A) (FormalMultilinearSeries.ofScalars A c).radius := by
    rw [Metric.mem_eball, edist_zero_right]
    refine lt_of_lt_of_le ?_ hr
    rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_lt_one.2 hy
  have h1 := (FormalMultilinearSeries.ofScalars A c).hasSum hmem
  have h2 := (BoundedContinuousFunction.evalCLM ℝ θ).hasSum h1
  have h3 : (fun n : ℕ => (BoundedContinuousFunction.evalCLM ℝ θ)
      (FormalMultilinearSeries.ofScalars A c n fun _ => y)) = fun n => (c n : ℂ) * (y θ) ^ n := by
    funext n
    rw [FormalMultilinearSeries.ofScalars_apply_eq]
    change (c n • y ^ n) θ = _
    rw [BoundedContinuousFunction.smul_apply, pow_apply', Complex.real_smul]
  rw [h3] at h2
  exact h2.tsum_eq.symm

theorem bsum_apply {Y : A} (hY : ‖Y‖ < 1) (θ : ℝ) :
    (binomialSeries A (1 / 2 : ℝ)).sum Y θ = (1 + Y θ) ^ (1 / 2 : ℂ) := by
  have hb : binomialSeries A (1 / 2 : ℝ) =
      FormalMultilinearSeries.ofScalars A (fun n => Ring.choose (1 / 2 : ℝ) n) := rfl
  have hYθ : ‖Y θ‖ < 1 := lt_of_le_of_lt (Y.norm_coe_le_norm θ) hY
  rw [hb, sum_apply (hb ▸ radius_binom) hY θ]
  have hmem : Y θ ∈ Metric.eball (0 : ℂ) 1 := by
    rw [Metric.mem_eball, edist_zero_right]
    rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_lt_one.2 hYθ
  have h4 := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := (1 / 2 : ℂ))).hasSum hmem
  rw [zero_add] at h4
  rw [← h4.tsum_eq]
  refine tsum_congr fun n => ?_
  have hb' : binomialSeries ℂ (1 / 2 : ℂ) =
      FormalMultilinearSeries.ofScalars ℂ (fun n => Ring.choose (1 / 2 : ℂ) n) := rfl
  rw [hb', FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  have : (Ring.choose (1 / 2 : ℂ) n) = ((Ring.choose (1 / 2 : ℝ) n : ℝ) : ℂ) := by
    rw [Complex.ofReal_choose]; push_cast; rfl
  rw [this]


/-! ### The scalar objects -/

def OmC (z : ℂ) : ℂ := ∑' j : ℕ, (cOm j : ℂ) * z ^ j

/-- `√`-factor `((-(L²)⁻¹) h)^{1/2}` (principal branch). -/
def sqF (L : ℝ) (h : ℂ) : ℂ := (((-(L ^ 2)⁻¹ : ℝ) : ℂ) * h) ^ (1 / 2 : ℂ)

/-- The analytic density factor `D = (L/2) sqF(H) Ω(f/4)`. -/
def Dtrue (L : ℝ) (H f : ℂ → ℂ) (z : ℂ) : ℂ := (((L / 2 : ℝ)) : ℂ) * sqF L (H z) * OmC (f z / 4)

section pointwise
variable {c L : ℝ}

theorem iota_eq (θ : ℝ) : iota c θ = (c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := rfl

theorem norm_iota (hc : 0 < c) (θ : ℝ) : ‖iota c θ‖ = c := by
  rw [iota_eq, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_of_nonneg hc.le, mul_one]

theorem wEl_apply (a : ℝ) (θ : ℝ) : wEl c a θ = (c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - (a : ℂ) := by
  change iota c θ - (a • (1 : A)) θ = _
  rw [BoundedContinuousFunction.smul_apply]
  simp [iota_eq]

theorem winv_apply (hc : 0 < c) {a : ℝ} (ha : |a| < c) (θ : ℝ) :
    Ring.inverse (wEl c a) θ = ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - (a : ℂ))⁻¹ := by
  obtain ⟨gi, hgi, -, hinv⟩ := inv_eval (g := wEl c a) (m := c - |a|) (by linarith) (fun θ => by
    rw [wEl_apply]
    have h1 : ‖(c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = c := norm_iota hc θ
    have := norm_sub_norm_le ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) (a : ℂ)
    rw [h1, Complex.norm_real, Real.norm_eq_abs] at this
    linarith)
  rw [hinv, hgi, wEl_apply]

theorem PEl_apply (a τ : ℝ) (θ : ℝ) :
    PEl c a τ θ = ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - (a : ℂ)) *
      ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - (a : ℂ)) - (τ : ℂ) := by
  change (wEl c a * wEl c a) θ - (τ • (1 : A)) θ = _
  rw [mul_apply, wEl_apply, BoundedContinuousFunction.smul_apply]
  simp

theorem Pinv_apply (hc : 0 < c) {a t : ℝ} (ht : 0 ≤ t) (hat : |a| + t < c) (θ : ℝ) :
    Ring.inverse (PEl c a (t ^ 2)) θ =
      (((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - (a : ℂ)) *
        ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - (a : ℂ)) - ((t ^ 2 : ℝ) : ℂ))⁻¹ := by
  have hm : 0 < (c - |a|) ^ 2 - t ^ 2 := by nlinarith [abs_nonneg a]
  obtain ⟨gi, hgi, -, hinv⟩ := inv_eval (g := PEl c a (t ^ 2)) (m := (c - |a|) ^ 2 - t ^ 2) hm (fun θ => by
    rw [PEl_apply]
    have h1 : c - |a| ≤ ‖(c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - (a : ℂ)‖ := by
      have := norm_sub_norm_le ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) (a : ℂ)
      rw [show ‖(c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = c from norm_iota hc θ, Complex.norm_real,
        Real.norm_eq_abs] at this
      linarith
    set w := (c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - (a : ℂ)
    have h2 : ‖w * w‖ - ‖((t ^ 2 : ℝ) : ℂ)‖ ≤ ‖w * w - ((t ^ 2 : ℝ) : ℂ)‖ := norm_sub_norm_le _ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h2
    nlinarith [norm_nonneg w])
  rw [hinv, hgi, PEl_apply]

theorem P_lower (hc : 0 < c) {a t : ℝ} (ht : 0 ≤ t) (hat : |a| + t < c) (θ : ℝ) :
    (c - |a|) ^ 2 - t ^ 2 ≤ ‖((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - (a : ℂ)) *
        ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - (a : ℂ)) - ((t ^ 2 : ℝ) : ℂ)‖ := by
  have h1 : c - |a| ≤ ‖(c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - (a : ℂ)‖ := by
    have := norm_sub_norm_le ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) (a : ℂ)
    rw [show ‖(c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = c from norm_iota hc θ, Complex.norm_real,
      Real.norm_eq_abs] at this
    linarith
  set w := (c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - (a : ℂ)
  have h2 : ‖w * w‖ - ‖((t ^ 2 : ℝ) : ℂ)‖ ≤ ‖w * w - ((t ^ 2 : ℝ) : ℂ)‖ := norm_sub_norm_le _ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h2
  have h0 : 0 ≤ c - |a| := by linarith [abs_nonneg a]
  nlinarith [norm_nonneg w]

theorem P_ne (hc : 0 < c) {a t : ℝ} (ht : 0 ≤ t) (hat : |a| + t < c) (θ : ℝ) :
    ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - (a : ℂ)) *
        ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - (a : ℂ)) - ((t ^ 2 : ℝ) : ℂ) ≠ 0 := by
  intro h
  have := P_lower hc ht hat θ
  rw [h, norm_zero] at this
  nlinarith [abs_nonneg a]


end pointwise

/-! ### Holomorphy of the density factor -/

theorem radius_OmC : 1 ≤ (FormalMultilinearSeries.ofScalars ℂ (fun n => (cOm n : ℂ))).radius := by
  have h1 : 1 ≤ (binomialSeries ℂ (-1 / 2 : ℂ)).radius := binomialSeries_radius_ge_one
  refine h1.trans ?_
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  obtain ⟨C, -, hC⟩ := (binomialSeries ℂ (-1 / 2 : ℂ)).norm_mul_pow_le_of_lt_radius hr
  refine FormalMultilinearSeries.le_radius_of_bound _ C fun n => ?_
  have h2 := hC n
  have hb : binomialSeries ℂ (-1 / 2 : ℂ) =
      FormalMultilinearSeries.ofScalars ℂ (fun n => Ring.choose (-1 / 2 : ℂ) n) := rfl
  rw [hb, FormalMultilinearSeries.ofScalars_norm] at h2
  rw [FormalMultilinearSeries.ofScalars_norm]
  refine le_trans (mul_le_mul_of_nonneg_right ?_ (by positivity)) h2
  have e : (Ring.choose (-1 / 2 : ℂ) n) = ((Ring.choose (-1 / 2 : ℝ) n : ℝ) : ℂ) := by
    rw [Complex.ofReal_choose]; push_cast; rfl
  rw [e]
  unfold cOm
  push_cast
  rw [norm_div]
  have : (1 : ℝ) ≤ ‖(2 * (n : ℂ) + 1)‖ := by
    have : (2 * (n : ℂ) + 1) = ((2 * (n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  exact div_le_self (norm_nonneg _) this

theorem OmC_eq (z : ℂ) :
    OmC z = (FormalMultilinearSeries.ofScalars ℂ (fun n => (cOm n : ℂ))).sum z := by
  rw [OmC]
  change _ = FormalMultilinearSeries.ofScalarsSum (E := ℂ) (fun n => (cOm n : ℂ)) z
  rw [FormalMultilinearSeries.ofScalarsSum_eq_tsum]
  simp [smul_eq_mul]

theorem differentiableAt_OmC {w : ℂ} (hw : ‖w‖ < 1) : DifferentiableAt ℂ OmC w := by
  have hB := (FormalMultilinearSeries.ofScalars ℂ (fun n => (cOm n : ℂ))).hasFPowerSeriesOnBall
    (lt_of_lt_of_le one_pos radius_OmC)
  have hmem : w ∈ Metric.eball (0 : ℂ) (FormalMultilinearSeries.ofScalars ℂ (fun n => (cOm n : ℂ))).radius := by
    rw [Metric.mem_eball, edist_zero_right]
    refine lt_of_lt_of_le ?_ radius_OmC
    rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_lt_one.2 hw
  have ha := (hB.analyticAt_of_mem hmem).differentiableAt
  have : OmC = (FormalMultilinearSeries.ofScalars ℂ (fun n => (cOm n : ℂ))).sum := funext OmC_eq
  rw [this]; exact ha

theorem differentiableAt_Dtrue {L : ℝ} (hL : 0 < L) {H f : ℂ → ℂ} {z : ℂ} (hH : DifferentiableAt ℂ H z)
    (hf : DifferentiableAt ℂ f z) (hHz : ‖H z + (L : ℂ) ^ 2‖ ≤ L ^ 2 / 4) (hfz : ‖f z / 4‖ < 1) :
    DifferentiableAt ℂ (Dtrue L H f) z := by
  have hL2 : (L : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.2 hL.ne')
  have hslit : (((-(L ^ 2)⁻¹ : ℝ) : ℂ) * H z) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    have e : (((-(L ^ 2)⁻¹ : ℝ) : ℂ) * H z) - 1 = -(H z + (L : ℂ) ^ 2) / (L : ℂ) ^ 2 := by
      have e0 : (((-(L ^ 2)⁻¹ : ℝ) : ℂ)) = -(1 / (L : ℂ) ^ 2) := by push_cast; ring
      have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
      rw [e0]; field_simp; ring
    have h1 : ‖(((-(L ^ 2)⁻¹ : ℝ) : ℂ) * H z) - 1‖ ≤ 1 / 4 := by
      rw [e, norm_div, norm_neg, norm_pow, Complex.norm_real, Real.norm_of_nonneg hL.le,
        div_le_iff₀ (by positivity)]
      nlinarith
    have h2 := Complex.abs_re_le_norm ((((-(L ^ 2)⁻¹ : ℝ) : ℂ) * H z) - 1)
    rw [Complex.sub_re, Complex.one_re] at h2
    have := (abs_le.1 (h2.trans h1)).1
    linarith
  have hsq : DifferentiableAt ℂ (fun z => sqF L (H z)) z := by
    unfold sqF
    exact ((differentiableAt_const _).mul hH).cpow (differentiableAt_const _) hslit
  have hOm : DifferentiableAt ℂ (fun z => OmC (f z / 4)) z :=
    (show DifferentiableAt ℂ (OmC ∘ fun z => f z / 4) z from
      (differentiableAt_OmC hfz).comp z (hf.div_const 4))
  unfold Dtrue
  exact ((differentiableAt_const _).mul hsq).mul hOm


/-! ### Quantitative facts for the actual cofactor -/

theorem Yscal_norm {L : ℝ} (hL : 0 < L) {h : ℂ} (hh : ‖h + (L : ℂ) ^ 2‖ ≤ L ^ 2 / 4) :
    ‖(((-(L ^ 2)⁻¹ : ℝ) : ℂ) * h) - 1‖ ≤ 1 / 4 := by
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
  have e0 : (((-(L ^ 2)⁻¹ : ℝ) : ℂ)) = -(1 / (L : ℂ) ^ 2) := by push_cast; ring
  have e : (((-(L ^ 2)⁻¹ : ℝ) : ℂ) * h) - 1 = -(h + (L : ℂ) ^ 2) / (L : ℂ) ^ 2 := by
    rw [e0]; field_simp; ring
  rw [e, norm_div, norm_neg, norm_pow, Complex.norm_real, Real.norm_of_nonneg hL.le,
    div_le_iff₀ (by positivity)]
  nlinarith

theorem f_small {L : ℝ} (hL : 0 < L) {Δ H : ℂ → ℂ} {α t : ℝ} (ht : 0 ≤ t)
    (hαt : |α| + t ≤ (1 / (16 * L)) / 40)
    (hfH : ∀ z, Δ z ^ 2 - 4 = ((z - α) ^ 2 - (t : ℂ) ^ 2) * H z)
    (hHb : ∀ z : ℂ, ‖z‖ ≤ 3 * (1 / (16 * L)) → ‖H z + (L : ℂ) ^ 2‖ ≤ L ^ 2 / 4) {z : ℂ}
    (hz : ‖z‖ ≤ 3 * (1 / (16 * L))) : ‖(Δ z ^ 2 - 4) / 4‖ ≤ 1 / 50 := by
  set d : ℝ := 1 / (16 * L) with hd
  have hd0 : 0 < d := by rw [hd]; positivity
  have hL2d2 : L ^ 2 * d ^ 2 = 1 / 256 := by
    have : L * d = 1 / 16 := by rw [hd]; field_simp
    calc L ^ 2 * d ^ 2 = (L * d) ^ 2 := by ring
      _ = 1 / 256 := by rw [this]; norm_num
  have hα : |α| ≤ d / 40 := by linarith [abs_nonneg α]
  have htd : t ≤ d / 40 := by linarith [abs_nonneg α]
  have hHn : ‖H z‖ ≤ (5 / 4) * L ^ 2 := by
    have h1 := hHb z hz
    have h2 : ‖(L : ℂ) ^ 2‖ = L ^ 2 := by rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hL.le]
    have h3 : ‖H z‖ ≤ ‖H z + (L : ℂ) ^ 2‖ + ‖(L : ℂ) ^ 2‖ := by
      calc ‖H z‖ = ‖(H z + (L : ℂ) ^ 2) - (L : ℂ) ^ 2‖ := by rw [add_sub_cancel_right]
        _ ≤ _ := norm_sub_le _ _
    rw [h2] at h3; linarith
  have hw : ‖z - (α : ℂ)‖ ≤ 3 * d + d / 40 := by
    calc ‖z - (α : ℂ)‖ ≤ ‖z‖ + ‖(α : ℂ)‖ := norm_sub_le _ _
      _ ≤ 3 * d + d / 40 := by
        rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  have hP : ‖(z - (α : ℂ)) ^ 2 - (t : ℂ) ^ 2‖ ≤ (3 * d + d / 40) ^ 2 + (d / 40) ^ 2 := by
    calc ‖(z - (α : ℂ)) ^ 2 - (t : ℂ) ^ 2‖ ≤ ‖(z - (α : ℂ)) ^ 2‖ + ‖(t : ℂ) ^ 2‖ := norm_sub_le _ _
      _ ≤ (3 * d + d / 40) ^ 2 + (d / 40) ^ 2 := by
        rw [norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht]
        have h1 : ‖z - (α : ℂ)‖ ^ 2 ≤ (3 * d + d / 40) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
        have h2 : t ^ 2 ≤ (d / 40) ^ 2 := pow_le_pow_left₀ ht htd 2
        linarith
  have hPd : (3 * d + d / 40) ^ 2 + (d / 40) ^ 2 ≤ 10 * d ^ 2 := by nlinarith [sq_nonneg d]
  rw [hfH z, norm_div, norm_mul]
  have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  rw [h4, div_le_iff₀ (by norm_num)]
  have hPn := hP.trans hPd
  calc ‖(z - (α : ℂ)) ^ 2 - (t : ℂ) ^ 2‖ * ‖H z‖ ≤ (10 * d ^ 2) * ((5 / 4) * L ^ 2) := by
        gcongr
    _ = (25 / 2) * (L ^ 2 * d ^ 2) := by ring
    _ ≤ 1 / 50 * 4 := by rw [hL2d2]; norm_num


theorem Phi_eval {L c : ℝ} (hL : 0 < L) (hc : c = 1 / (8 * L)) {Δ H : ℂ → ℂ}
    (hΔ : Differentiable ℂ Δ) (hH : Differentiable ℂ H) {α t : ℝ} (ht : 0 ≤ t)
    (hαt : |α| + t ≤ (1 / (16 * L)) / 40)
    (hfH : ∀ z, Δ z ^ 2 - 4 = ((z - α) ^ 2 - (t : ℂ) ^ 2) * H z)
    (hHb : ∀ z : ℂ, ‖z‖ ≤ 3 * (1 / (16 * L)) → ‖H z + (L : ℂ) ^ 2‖ ≤ L ^ 2 / 4)
    (F : A) (hF : ∀ θ, F θ = Δ ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) :
    Phi c L F α (t ^ 2) = ((4 / (Real.pi * L) : ℝ) : ℂ) *
      ∫ s in (-1 : ℝ)..1, ((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ) *
        Dtrue L H (fun z => Δ z ^ 2 - 4) ((α : ℂ) + (t : ℂ) * (s : ℂ)) := by
  set d : ℝ := 1 / (16 * L) with hd
  have hd0 : 0 < d := by rw [hd]; positivity
  have hcd : c = 2 * d := by rw [hc, hd]; field_simp; ring
  have hc0 : 0 < c := by rw [hcd]; positivity
  have hαc : |α| + t < c := by rw [hcd]; linarith
  have hcL : c ≤ 3 * d := by rw [hcd]; linarith
  set ξ : ℝ → ℂ := fun θ => (c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) with hξ
  have hξn : ∀ θ, ‖ξ θ‖ = c := fun θ => norm_iota hc0 θ
  have hξ3 : ∀ θ, ‖ξ θ‖ ≤ 3 * d := fun θ => by rw [hξn]; exact hcL
  have hfs := fun z (hz : ‖z‖ ≤ 3 * d) => f_small hL ht hαt hfH hHb hz
  -- the F, f relation
  have hFf : ∀ θ, F θ * F θ - 4 = Δ (ξ θ) ^ 2 - 4 := fun θ => by rw [hF θ]; ring
  -- H element
  have hHpt : ∀ θ, HEl c F α (t ^ 2) θ = H (ξ θ) := by
    intro θ
    have e1 : HEl c F α (t ^ 2) θ = (F θ * F θ - 4) * Ring.inverse (PEl c α (t ^ 2)) θ := by
      change (fEl F * Ring.inverse (PEl c α (t ^ 2))) θ = _
      rw [mul_apply]
      congr 1
      change (F * F - (4 : ℝ) • (1 : A)) θ = _
      simp
    rw [e1, Pinv_apply hc0 ht hαc θ, hFf, hfH]
    have hne := P_ne hc0 ht hαc θ
    have e2 : ((ξ θ - (α : ℂ)) ^ 2 - (t : ℂ) ^ 2) = (ξ θ - (α : ℂ)) * (ξ θ - (α : ℂ)) - ((t ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [e2]
    have hne' : (ξ θ - (α : ℂ)) * (ξ θ - (α : ℂ)) - ((t ^ 2 : ℝ) : ℂ) ≠ 0 := hne
    rw [mul_assoc, mul_comm (H (ξ θ)), ← mul_assoc, mul_inv_cancel₀ hne', one_mul]
  have hYpt : ∀ θ, YEl c L F α (t ^ 2) θ = (((-(L ^ 2)⁻¹ : ℝ) : ℂ) * H (ξ θ)) - 1 := by
    intro θ
    change ((-(L ^ 2)⁻¹ : ℝ) • HEl c F α (t ^ 2) - 1) θ = _
    rw [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.smul_apply, hHpt, Complex.real_smul]
    rfl
  have hYn : ‖YEl c L F α (t ^ 2)‖ ≤ 1 / 4 :=
    (BoundedContinuousFunction.norm_le (by norm_num)).2 fun θ => by
      rw [hYpt]; exact Yscal_norm hL (hHb (ξ θ) (hξ3 θ))
  have hYn1 : ‖YEl c L F α (t ^ 2)‖ < 1 := by linarith
  have hSpt : ∀ θ, SEl c L F α (t ^ 2) θ = (L : ℂ) * sqF L (H (ξ θ)) := by
    intro θ
    change (L • (binomialSeries A (1 / 2 : ℝ)).sum (YEl c L F α (t ^ 2))) θ = _
    rw [BoundedContinuousFunction.smul_apply, bsum_apply hYn1, hYpt, Complex.real_smul]
    unfold sqF
    congr 2
    ring
  -- f element
  have hfpt : ∀ θ, ((1 / 4 : ℝ) • fEl F) θ = (Δ (ξ θ) ^ 2 - 4) / 4 := by
    intro θ
    rw [BoundedContinuousFunction.smul_apply, Complex.real_smul]
    have : fEl F θ = F θ * F θ - 4 := by
      change (F * F - (4 : ℝ) • (1 : A)) θ = _
      simp
    rw [this, hFf]; push_cast; ring
  have hfn : ‖(1 / 4 : ℝ) • fEl F‖ ≤ 1 / 50 :=
    (BoundedContinuousFunction.norm_le (by norm_num)).2 fun θ => by
      rw [hfpt]; exact hfs (ξ θ) (hξ3 θ)
  have hfn1 : ‖(1 / 4 : ℝ) • fEl F‖ < 1 := by linarith
  have hWpt : ∀ θ, WEl F θ = OmC ((Δ (ξ θ) ^ 2 - 4) / 4) := by
    intro θ
    unfold WEl
    rw [sum_apply radius_Om hfn1 θ, hfpt]
    rfl
  have hDpt : ∀ θ, DEl c L F α (t ^ 2) θ = Dtrue L H (fun z => Δ z ^ 2 - 4) (ξ θ) := by
    intro θ
    change ((1 / 2 : ℝ) • (SEl c L F α (t ^ 2) * WEl F)) θ = _
    rw [BoundedContinuousFunction.smul_apply, mul_apply, hSpt, hWpt, Complex.real_smul]
    unfold Dtrue
    push_cast; ring
  -- K element
  have hwinv : ∀ θ, Ring.inverse (wEl c α) θ = (ξ θ - (α : ℂ))⁻¹ := fun θ => winv_apply hc0 (by linarith [abs_nonneg α, ht]) θ
  have hy : ∀ θ, ((t ^ 2 : ℝ) • (Ring.inverse (wEl c α) * Ring.inverse (wEl c α))) θ =
      ((t : ℂ) / (ξ θ - (α : ℂ))) ^ 2 := by
    intro θ
    rw [BoundedContinuousFunction.smul_apply, mul_apply, hwinv, Complex.real_smul]
    push_cast; field_simp
  have hyn : ‖(t ^ 2 : ℝ) • (Ring.inverse (wEl c α) * Ring.inverse (wEl c α))‖ < 1 := by
    have : ‖(t ^ 2 : ℝ) • (Ring.inverse (wEl c α) * Ring.inverse (wEl c α))‖ ≤ (t / (c - |α|)) ^ 2 := by
      refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun θ => ?_
      rw [hy, norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg ht]
      have h1 : c - |α| ≤ ‖ξ θ - (α : ℂ)‖ := by
        have := norm_sub_norm_le (ξ θ) (α : ℂ)
        rw [hξn, Complex.norm_real, Real.norm_eq_abs] at this
        linarith
      have h2 : 0 < c - |α| := by linarith
      have h3 : t / ‖ξ θ - (α : ℂ)‖ ≤ t / (c - |α|) := div_le_div_of_nonneg_left ht h2 h1
      exact pow_le_pow_left₀ (by positivity) h3 2
    refine lt_of_le_of_lt this ?_
    have h2 : 0 < c - |α| := by linarith
    have : t / (c - |α|) < 1 := by rw [div_lt_one h2]; linarith
    nlinarith [div_nonneg ht h2.le]
  have hKpt : ∀ θ, KEl c α (t ^ 2) θ = (ξ θ - (α : ℂ))⁻¹ *
      ∑' j : ℕ, (cM j : ℂ) * (((t : ℂ) / (ξ θ - (α : ℂ))) ^ 2) ^ j := by
    intro θ
    unfold KEl
    rw [mul_apply, hwinv, sum_apply radius_M hyn θ, hy]
  -- assemble
  have hint : intCLM (iota c * DEl c L F α (t ^ 2) * KEl c α (t ^ 2)) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), circleMap 0 c θ * Dtrue L H (fun z => Δ z ^ 2 - 4) (circleMap 0 c θ) *
        ((circleMap 0 c θ - (α : ℂ))⁻¹ *
          ∑' j : ℕ, (cM j : ℂ) * (((t : ℂ) / (circleMap 0 c θ - (α : ℂ))) ^ 2) ^ j) := by
    rw [intCLM_apply]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [mul_apply, mul_apply, hDpt, hKpt, iota_eq]
    simp [circleMap, hξ]
  have hdiff : DifferentiableOn ℂ (Dtrue L H (fun z => Δ z ^ 2 - 4)) (Metric.closedBall 0 c) := by
    intro z hz
    have hz' : ‖z‖ ≤ 3 * d := by
      have : ‖z‖ ≤ c := by simpa using hz
      linarith
    refine (differentiableAt_Dtrue hL (hH z) ((hΔ.pow 2).sub_const 4 z) (hHb z hz') ?_).differentiableWithinAt
    exact lt_of_le_of_lt (hfs z hz') (by norm_num)
  have hev := Local007EvalS.eval_scalar hc0 hdiff ht hαc
  unfold Phi
  rw [hint, hev]
  push_cast
  ring

end QuantumNLS.Local007EvalT
#print axioms QuantumNLS.Local007EvalT.Phi_eval
#print axioms QuantumNLS.Local007EvalT.differentiableAt_Dtrue

