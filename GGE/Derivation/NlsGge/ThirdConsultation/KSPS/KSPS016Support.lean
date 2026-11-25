import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS016Host
import NlsGge.ThirdConsultation.KSPS.KSPS015Support
import NlsGge.Atomic.KSPS.KSPS001

/- KSPS-016 SUPPORT (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS016Support.lean.
   Route = Pro round 14 Cluster 1 "KSPS-016" (exact matrix algebra of (30)) on top of KSPS015Support:
   * antitrace = m2 + m3 and dirichletNumerator = m4 + m3 - m2 - m1 from explicit_formula (KSPS-014 tail);
   * the off-diagonal remainders at x = 1 are replaced by their KSPS-011 expansions, the derivative Fourier
     coefficients by KSPS-001 (hat(D^N u)(m) = (2 pi i m)^N hat u(m)), the diagonal ones by KSPS-012 (+ KSPS-013);
   * exact identities: antitraceError = i(-1)^n (hat phi1(-n) - hat phi2(n)) (D^-1 (pi n/xi)^N - 1) + D^-1 eps Y_A,
     dirichletError = i(-1)^(n+1)(...)(D^-1 (pi n/xi)^N - 1) + 2(-1)^(n+1) I_(N+1) (2 i xi)^-(N+1) (D^-1 - 1)
                      + D^-1 eps Y_D;
   * weighted l2 bounds of order N+1 on the tail; finite exceptional set absorbed by an eventual bound.
   KSPS-011/012/013/014 head conclusions are explicit hypotheses of `boundary_characteristics_WKB_of` of exactly
   their landed types; KSPS-001 (landed) is imported. -/
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS016W
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.KSPS NlsGge.ThirdConsultation.KSPS015W

/-! ### Entries -/

theorem antitrace_entry {N : ℕ} (φ : SobolevC N) (lam : {z : ℂ // z ≠ 0})
    (hM : monodromyPair (toPotPair φ) lam.1 = KSPSWKB.explicitWKBMonodromy N φ lam) :
    KSPSWKB.antitrace φ lam.1 =
      (1 - KSPSWKB.beta φ lam.1 0 * KSPSWKB.alpha φ lam.1 0)⁻¹ *
        ((KSPSWKB.beta φ lam.1 0 - KSPSWKB.alpha φ lam.1 0) * (et φ lam - ef φ lam) +
          ((2 * Complex.I * lam.1) ^ N)⁻¹ *
            (rt φ lam 0 + rf φ lam 1 - KSPSWKB.beta φ lam.1 0 * rf φ lam 0 -
              KSPSWKB.alpha φ lam.1 0 * rt φ lam 1)) := by
  unfold KSPSWKB.antitrace
  rw [hM, explicit_formula]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  ring

theorem dirichlet_entry {N : ℕ} (φ : SobolevC N) (lam : {z : ℂ // z ≠ 0})
    (hM : monodromyPair (toPotPair φ) lam.1 = KSPSWKB.explicitWKBMonodromy N φ lam) :
    KSPSWKB.dirichletNumerator φ lam.1 =
      (1 - KSPSWKB.beta φ lam.1 0 * KSPSWKB.alpha φ lam.1 0)⁻¹ *
        ((et φ lam - ef φ lam) * (1 - KSPSWKB.alpha φ lam.1 0) * (1 - KSPSWKB.beta φ lam.1 0) +
          ((2 * Complex.I * lam.1) ^ N)⁻¹ *
            ((rt φ lam 1 - rf φ lam 0) + (rf φ lam 1 - rt φ lam 0) +
              KSPSWKB.beta φ lam.1 0 * (rf φ lam 0 - rf φ lam 1) +
              KSPSWKB.alpha φ lam.1 0 * (rt φ lam 0 - rt φ lam 1))) := by
  unfold KSPSWKB.dirichletNumerator
  rw [hM, explicit_formula]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  ring

/-! ### Pure algebra of the two errors -/

theorem antitrace_alg (A D ε s p G1 G2 sg sN eU eL w α β rf0 rt1 rt0 rf1 : ℂ)
    (hD : D = 1 - β * α)
    (hA : A = D⁻¹ * ((β - α) * s + ε * (rt0 + rf1 - β * rf0 - α * rt1)))
    (hrt0 : rt0 = Complex.I * sg * p * G1 + sN * eU / w)
    (hrf1 : rf1 = -(Complex.I * sg * p * G2) + eL / w) :
    A - ((β - α) / (1 - α * β) * s + Complex.I * sg * (G1 - G2)) =
      (Complex.I * sg * (G1 - G2)) * (D⁻¹ * (ε * p) - 1) +
        D⁻¹ * (ε * ((sN * eU + eL) / w - β * rf0 - α * rt1)) := by
  subst hA hrt0 hrf1
  rw [show (1 - α * β) = 1 - β * α by ring, ← hD]
  ring

theorem dirichlet_alg (N : ℕ) (Dn D ε s p G1 G2 sg sN e1 e2 eU eL w α β rf0 rt1 rt0 rf1 IL X2 : ℂ)
    (hD : D = 1 - β * α)
    (hDn : Dn = D⁻¹ * (s * (1 - α) * (1 - β) +
      ε * ((rt1 - rf0) + (rf1 - rt0) + β * (rf0 - rf1) + α * (rt0 - rt1))))
    (hε : ε = (X2 ^ N)⁻¹)
    (hrf0 : rf0 = sg / X2 * IL + e1 / w)
    (hrt1 : rt1 = sg * (-1) / X2 * IL + e2 / w)
    (hrt0 : rt0 = Complex.I * sg * p * G1 + sN * eU / w)
    (hrf1 : rf1 = -(Complex.I * sg * p * G2) + eL / w) :
    Dn - ((1 - α) * (1 - β) / (1 - α * β) * s + Complex.I * (sg * (-1)) * (G1 + G2) +
        2 * (sg * (-1)) / X2 ^ (N + 1) * IL) =
      (Complex.I * (sg * (-1)) * (G1 + G2)) * (D⁻¹ * (ε * p) - 1) +
        (2 * (sg * (-1)) * IL) * ((X2 ^ (N + 1))⁻¹ * (D⁻¹ - 1)) +
        D⁻¹ * (ε * ((e2 - e1 + eL - sN * eU) / w + β * (rf0 - rf1) + α * (rt0 - rt1))) := by
  subst hDn hε hrf0 hrt1 hrt0 hrf1
  rw [show (1 - α * β) = 1 - β * α by ring, ← hD]
  ring

/-! ### Real estimates -/

theorem norm_pow_sub_one_le (z : ℂ) (M : ℝ) (hM : 1 ≤ M) (hz : ‖z‖ ≤ M) (N : ℕ) :
    ‖z ^ N - 1‖ ≤ (N : ℝ) * M ^ N * ‖z - 1‖ := by
  induction N with
  | zero => simp
  | succ k ih =>
    have h1 : z ^ (k + 1) - 1 = z * (z ^ k - 1) + (z - 1) := by ring
    rw [h1]
    have hMk : 1 ≤ M ^ (k + 1) := one_le_pow₀ hM
    have hz1 := norm_nonneg (z - 1)
    have hzk := norm_nonneg (z ^ k - 1)
    have hM0 : 0 ≤ M := by linarith
    have e1 : ‖z * (z ^ k - 1) + (z - 1)‖ ≤ ‖z‖ * ‖z ^ k - 1‖ + ‖z - 1‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
    have e2 : ‖z‖ * ‖z ^ k - 1‖ ≤ M * ((k : ℝ) * M ^ k * ‖z - 1‖) :=
      mul_le_mul hz ih hzk hM0
    have e3 : M * ((k : ℝ) * M ^ k * ‖z - 1‖) = (k : ℝ) * M ^ (k + 1) * ‖z - 1‖ := by ring
    have e4 : 1 * ‖z - 1‖ ≤ M ^ (k + 1) * ‖z - 1‖ := mul_le_mul_of_nonneg_right hMk hz1
    push_cast
    linarith

theorem lead_bound (N : ℕ) (w A A' h : ℝ) (G Dinv q : ℂ) (hw : 1 ≤ w) (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (hD : ‖Dinv‖ ≤ 2) (hq : ‖q - 1‖ ≤ A / (w * w)) (hD1 : ‖Dinv - 1‖ ≤ A' / (w * w))
    (hG : w ^ N * ‖G‖ ≤ h) :
    w ^ (N + 1) * ‖G * (Dinv * q - 1)‖ ≤ (2 * A + A') * h := by
  have hw0 : 0 < w := by linarith
  have hww : 0 < w * w := by positivity
  have e : Dinv * q - 1 = Dinv * (q - 1) + (Dinv - 1) := by ring
  have hb : ‖Dinv * q - 1‖ ≤ (2 * A + A') / (w * w) := by
    rw [e]
    have h1 : ‖Dinv * (q - 1) + (Dinv - 1)‖ ≤ ‖Dinv‖ * ‖q - 1‖ + ‖Dinv - 1‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
    have h2 : ‖Dinv‖ * ‖q - 1‖ ≤ 2 * (A / (w * w)) :=
      mul_le_mul hD hq (norm_nonneg _) (by norm_num)
    have h3 : 2 * (A / (w * w)) + A' / (w * w) = (2 * A + A') / (w * w) := by ring
    linarith
  have hGn := norm_nonneg G
  have hwN : 0 ≤ w ^ N := pow_nonneg hw0.le N
  have hh : 0 ≤ h := le_trans (mul_nonneg hwN hGn) hG
  have hK : 0 ≤ 2 * A + A' := by linarith
  have k1 : w ^ (N + 1) * (‖G‖ * ((2 * A + A') / (w * w))) = (2 * A + A') * (w ^ N * ‖G‖) / w := by
    field_simp
    ring
  calc w ^ (N + 1) * ‖G * (Dinv * q - 1)‖
      = w ^ (N + 1) * (‖G‖ * ‖Dinv * q - 1‖) := by rw [norm_mul]
    _ ≤ w ^ (N + 1) * (‖G‖ * ((2 * A + A') / (w * w))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hGn) (pow_nonneg hw0.le _)
    _ = (2 * A + A') * (w ^ N * ‖G‖) / w := k1
    _ ≤ (2 * A + A') * h / w :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hG hK) hw0.le
    _ ≤ (2 * A + A') * h := div_le_self (mul_nonneg hK hh) hw

theorem bracket_bound (N : ℕ) (w X : ℝ) (Dinv ε Y : ℂ) (hw : 0 < w) (hwX : w ≤ 2 * X)
    (hD : ‖Dinv‖ ≤ 2) (hε : ‖ε‖ = ((2 * X) ^ N)⁻¹) :
    w ^ (N + 1) * ‖Dinv * (ε * Y)‖ ≤ 2 * (w * ‖Y‖) := by
  have h2X : 0 < 2 * X := by linarith
  have hr0 : 0 ≤ w / (2 * X) := div_nonneg hw.le h2X.le
  have hr1 : w / (2 * X) ≤ 1 := by rw [div_le_one h2X]; exact hwX
  have hrN : (w / (2 * X)) ^ N ≤ 1 := pow_le_one₀ hr0 hr1
  have hY := norm_nonneg Y
  have hεn : 0 ≤ ((2 * X) ^ N)⁻¹ := inv_nonneg.mpr (pow_nonneg h2X.le N)
  have hb : ‖Dinv * (ε * Y)‖ ≤ 2 * (((2 * X) ^ N)⁻¹ * ‖Y‖) := by
    rw [norm_mul, norm_mul, hε]
    exact mul_le_mul hD le_rfl (mul_nonneg hεn hY) (by norm_num)
  have k1 : w ^ (N + 1) * (2 * (((2 * X) ^ N)⁻¹ * ‖Y‖)) = 2 * ((w / (2 * X)) ^ N * (w * ‖Y‖)) := by
    rw [div_pow]
    field_simp
    ring
  have hwY : 0 ≤ w * ‖Y‖ := mul_nonneg hw.le hY
  calc w ^ (N + 1) * ‖Dinv * (ε * Y)‖ ≤ w ^ (N + 1) * (2 * (((2 * X) ^ N)⁻¹ * ‖Y‖)) :=
        mul_le_mul_of_nonneg_left hb (pow_nonneg hw.le _)
    _ = 2 * ((w / (2 * X)) ^ N * (w * ‖Y‖)) := k1
    _ ≤ 2 * (1 * (w * ‖Y‖)) := by
        have := mul_le_mul_of_nonneg_right hrN hwY
        linarith
    _ = 2 * (w * ‖Y‖) := by ring

theorem riccati_bound (N : ℕ) (w X A' : ℝ) (J Z Dinv : ℂ) (hw : 1 ≤ w) (hwX : w ≤ 2 * X)
    (hZ : ‖Z‖ = ((2 * X) ^ (N + 1))⁻¹) (hA' : 0 ≤ A') (hD1 : ‖Dinv - 1‖ ≤ A' / (w * w)) :
    w ^ (N + 1) * ‖J * (Z * (Dinv - 1))‖ ≤ ‖J‖ * A' * (1 / w) := by
  have hw0 : 0 < w := by linarith
  have h2X : 0 < 2 * X := by linarith
  have hr0 : 0 ≤ w / (2 * X) := div_nonneg hw0.le h2X.le
  have hr1 : w / (2 * X) ≤ 1 := by rw [div_le_one h2X]; exact hwX
  have hrN : (w / (2 * X)) ^ (N + 1) ≤ 1 := pow_le_one₀ hr0 hr1
  have hJ := norm_nonneg J
  have hZn : 0 ≤ ((2 * X) ^ (N + 1))⁻¹ := inv_nonneg.mpr (pow_nonneg h2X.le _)
  have hAw : 0 ≤ A' / (w * w) := div_nonneg hA' (by positivity)
  have hb : ‖J * (Z * (Dinv - 1))‖ ≤ ‖J‖ * (((2 * X) ^ (N + 1))⁻¹ * (A' / (w * w))) := by
    rw [norm_mul, norm_mul, hZ]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD1 hZn) hJ
  have k1 : w ^ (N + 1) * (‖J‖ * (((2 * X) ^ (N + 1))⁻¹ * (A' / (w * w)))) =
      (w / (2 * X)) ^ (N + 1) * (‖J‖ * A' * (1 / w) * (1 / w)) := by
    rw [div_pow]
    field_simp <;> ring
  have hJA : 0 ≤ ‖J‖ * A' * (1 / w) := by positivity
  have hiw : 1 / w ≤ 1 := by rw [div_le_one hw0]; exact hw
  calc w ^ (N + 1) * ‖J * (Z * (Dinv - 1))‖
      ≤ w ^ (N + 1) * (‖J‖ * (((2 * X) ^ (N + 1))⁻¹ * (A' / (w * w)))) :=
        mul_le_mul_of_nonneg_left hb (pow_nonneg hw0.le _)
    _ = (w / (2 * X)) ^ (N + 1) * (‖J‖ * A' * (1 / w) * (1 / w)) := k1
    _ ≤ 1 * (‖J‖ * A' * (1 / w) * 1) := by
        have h1 : ‖J‖ * A' * (1 / w) * (1 / w) ≤ ‖J‖ * A' * (1 / w) * 1 :=
          mul_le_mul_of_nonneg_left hiw hJA
        have h2 : 0 ≤ ‖J‖ * A' * (1 / w) * (1 / w) := by positivity
        have h3 := mul_le_mul_of_nonneg_right hrN h2
        linarith
    _ = ‖J‖ * A' * (1 / w) := by ring

theorem sq_summable_inv_w : Summable (fun n : ℤ => (1 / indexWeight n) ^ 2) := by
  have hg : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) := Real.summable_one_div_int_pow.mpr one_lt_two
  refine Summable.of_norm_bounded_eventually hg ?_
  filter_upwards [eventually_natAbs 1] with n hn
  beta_reduce
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast hn
  have hn2 : 0 < (n : ℝ) ^ 2 := by
    have : (n : ℝ) ^ 2 = |(n : ℝ)| ^ 2 := (sq_abs _).symm
    rw [this]; positivity
  have hw := one_le_w n
  have hw2 : (n : ℝ) ^ 2 ≤ indexWeight n ^ 2 := by
    unfold indexWeight
    rw [Real.sq_sqrt (by positivity)]
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), div_pow, one_pow]
  exact one_div_le_one_div_of_le hn2 hw2

theorem tail_nat (a T : ℝ) (n : ℤ) (hn : ((⌈a⌉₊ + ⌈T⌉₊ + 1 : ℕ) : ℤ) ≤ |n|) :
    1 ≤ |(n : ℝ)| ∧ a ≤ |(n : ℝ)| := by
  have hnR : ((⌈a⌉₊ + ⌈T⌉₊ + 1 : ℕ) : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast hn
  push_cast at hnR
  have hca := Nat.le_ceil a
  have hc0 : (0 : ℝ) ≤ (⌈a⌉₊ : ℝ) := Nat.cast_nonneg _
  have hc1 : (0 : ℝ) ≤ (⌈T⌉₊ : ℝ) := Nat.cast_nonneg _
  constructor <;> linarith

/-! ### Pure per-index bounds (small contexts) -/

theorem rem_bounds_pure (w X c1 : ℝ) (ξ sg sN IL DF1 DF2 e1 e2 eU eL rf0 rt1 rt0 rf1 : ℂ)
    (hw1 : 1 ≤ w) (hwX : w ≤ 2 * X) (hX : ‖ξ‖ = X) (hsg : ‖sg‖ = 1) (hsN : ‖sN‖ = 1) (hIL : ‖IL‖ = c1)
    (hc1 : 0 ≤ c1)
    (hrf0 : rf0 = sg / (2 * Complex.I * ξ) * IL + e1 / (w : ℂ))
    (hrt1 : rt1 = sg * (-1) / (2 * Complex.I * ξ) * IL + e2 / (w : ℂ))
    (hrt0 : sN * rt0 = Complex.I * sg * DF1 + eU / (w : ℂ))
    (hrf1 : rf1 = Complex.I * (sg * (-1)) * DF2 + eL / (w : ℂ)) :
    ‖rf0‖ ≤ c1 * (1 / w) + ‖e1‖ ∧ ‖rt1‖ ≤ c1 * (1 / w) + ‖e2‖ ∧
      ‖rt0‖ ≤ ‖DF1‖ + ‖eU‖ ∧ ‖rf1‖ ≤ ‖DF2‖ + ‖eL‖ := by
  have hw0 : 0 < w := by linarith
  have hdivw : ∀ e : ℂ, ‖e / (w : ℂ)‖ ≤ ‖e‖ := by
    intro e
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hw0.le]
    exact div_le_self (norm_nonneg _) hw1
  have hsg1 : ‖sg * (-1)‖ = 1 := by rw [norm_mul, hsg, norm_neg, norm_one, one_mul]
  have hlead : ∀ s : ℂ, ‖s‖ = 1 → ‖s / (2 * Complex.I * ξ) * IL‖ ≤ c1 * (1 / w) := by
    intro s hs
    rw [norm_mul, norm_div, hs, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one, hX, hIL]
    have h1 : 1 / (2 * X) ≤ 1 / w := div_le_div_of_nonneg_left zero_le_one hw0 hwX
    rw [mul_comm c1]
    exact mul_le_mul_of_nonneg_right h1 hc1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrf0]
    exact (norm_add_le _ _).trans (add_le_add (hlead _ hsg) (hdivw _))
  · rw [hrt1]
    exact (norm_add_le _ _).trans (add_le_add (hlead _ hsg1) (hdivw _))
  · have h1 : ‖rt0‖ = ‖sN * rt0‖ := by rw [norm_mul, hsN, one_mul]
    rw [h1, hrt0]
    refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) (hdivw _))
    rw [norm_mul, norm_mul, Complex.norm_I, hsg, one_mul, one_mul]
  · rw [hrf1]
    refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) (hdivw _))
    rw [norm_mul, norm_mul, Complex.norm_I, hsg1, one_mul, one_mul]

theorem antitrace_pure (N : ℕ) (w X S c1 A A' F1 F2 : ℝ)
    (Dinv ε p G1 G2 sg sN eU eL e1 e2 α β rf0 rt1 : ℂ)
    (hw1 : 1 ≤ w) (hwX : w ≤ 2 * X) (hS0 : 0 ≤ S) (hc1 : 0 ≤ c1) (hA0 : 0 ≤ A) (hA'0 : 0 ≤ A')
    (hDinv : ‖Dinv‖ ≤ 2) (hDinv1 : ‖Dinv - 1‖ ≤ A' / (w * w)) (hε : ‖ε‖ = ((2 * X) ^ N)⁻¹)
    (hq : ‖ε * p - 1‖ ≤ A / (w * w)) (hsg : ‖sg‖ = 1) (hsN : ‖sN‖ = 1)
    (hG1 : w ^ N * ‖G1‖ ≤ F1) (hG2 : w ^ N * ‖G2‖ ≤ F2)
    (hα : ‖α‖ ≤ S / (2 * X)) (hβ : ‖β‖ ≤ S / (2 * X))
    (hrf0 : ‖rf0‖ ≤ c1 * (1 / w) + ‖e1‖) (hrt1 : ‖rt1‖ ≤ c1 * (1 / w) + ‖e2‖) :
    w ^ (N + 1) * ‖(Complex.I * sg * (G1 - G2)) * (Dinv * (ε * p) - 1) +
        Dinv * (ε * ((sN * eU + eL) / (w : ℂ) - β * rf0 - α * rt1))‖ ≤
      (2 * A + A') * (F1 + F2) +
        2 * (‖eU‖ + ‖eL‖ + S * ((c1 * (1 / w) + ‖e1‖) + (c1 * (1 / w) + ‖e2‖))) := by
  have hw0 : 0 < w := by linarith
  have hX0 : 0 < X := by linarith
  have hGA : w ^ N * ‖Complex.I * sg * (G1 - G2)‖ ≤ F1 + F2 := by
    rw [norm_mul, norm_mul, Complex.norm_I, hsg, one_mul, one_mul]
    have h1 := norm_sub_le G1 G2
    have h2 := mul_le_mul_of_nonneg_left h1 (pow_nonneg hw0.le N)
    linarith
  have LA := lead_bound N w A A' _ _ _ _ hw1 hA0 hA'0 hDinv hq hDinv1 hGA
  have BA := bracket_bound N w X Dinv ε ((sN * eU + eL) / (w : ℂ) - β * rf0 - α * rt1) hw0 hwX hDinv hε
  have hiwn : 0 ≤ 1 / w := div_nonneg zero_le_one hw0.le
  have hQ1 : 0 ≤ c1 * (1 / w) + ‖e1‖ := add_nonneg (mul_nonneg hc1 hiwn) (norm_nonneg _)
  have hQ4 : 0 ≤ c1 * (1 / w) + ‖e2‖ := add_nonneg (mul_nonneg hc1 hiwn) (norm_nonneg _)
  have hSX0 : 0 ≤ S / (2 * X) := div_nonneg hS0 (by linarith)
  have hwS : w * (S / (2 * X)) ≤ S := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  have hY : w * ‖(sN * eU + eL) / (w : ℂ) - β * rf0 - α * rt1‖ ≤
      ‖eU‖ + ‖eL‖ + S * ((c1 * (1 / w) + ‖e1‖) + (c1 * (1 / w) + ‖e2‖)) := by
    have t1 : ‖(sN * eU + eL) / (w : ℂ)‖ ≤ (‖eU‖ + ‖eL‖) / w := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hw0.le]
      refine div_le_div_of_nonneg_right ((norm_add_le _ _).trans ?_) hw0.le
      rw [norm_mul, hsN, one_mul]
    have t2 : ‖β * rf0‖ ≤ S / (2 * X) * (c1 * (1 / w) + ‖e1‖) := by
      rw [norm_mul]; exact mul_le_mul hβ hrf0 (norm_nonneg _) hSX0
    have t3 : ‖α * rt1‖ ≤ S / (2 * X) * (c1 * (1 / w) + ‖e2‖) := by
      rw [norm_mul]; exact mul_le_mul hα hrt1 (norm_nonneg _) hSX0
    have t4 := norm_sub_le ((sN * eU + eL) / (w : ℂ) - β * rf0) (α * rt1)
    have t5 := norm_sub_le ((sN * eU + eL) / (w : ℂ)) (β * rf0)
    have h1 : ‖(sN * eU + eL) / (w : ℂ) - β * rf0 - α * rt1‖ ≤
        (‖eU‖ + ‖eL‖) / w + S / (2 * X) * ((c1 * (1 / w) + ‖e1‖) + (c1 * (1 / w) + ‖e2‖)) := by
      have t6 : S / (2 * X) * ((c1 * (1 / w) + ‖e1‖) + (c1 * (1 / w) + ‖e2‖)) =
          S / (2 * X) * (c1 * (1 / w) + ‖e1‖) + S / (2 * X) * (c1 * (1 / w) + ‖e2‖) := by ring
      linarith
    have k1 : w * ((‖eU‖ + ‖eL‖) / w) = ‖eU‖ + ‖eL‖ := by
      rw [mul_div_assoc', mul_div_cancel_left₀ _ hw0.ne']
    have k2 : w * (S / (2 * X) * ((c1 * (1 / w) + ‖e1‖) + (c1 * (1 / w) + ‖e2‖))) ≤
        S * ((c1 * (1 / w) + ‖e1‖) + (c1 * (1 / w) + ‖e2‖)) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hwS (add_nonneg hQ1 hQ4)
    have h2 := mul_le_mul_of_nonneg_left h1 hw0.le
    rw [mul_add w] at h2
    linarith
  have tri := norm_add_le ((Complex.I * sg * (G1 - G2)) * (Dinv * (ε * p) - 1))
    (Dinv * (ε * ((sN * eU + eL) / (w : ℂ) - β * rf0 - α * rt1)))
  have h3 := mul_le_mul_of_nonneg_left tri (pow_nonneg hw0.le (N + 1))
  rw [mul_add (w ^ (N + 1))] at h3
  linarith

theorem dirichlet_pure (N : ℕ) (w X S c1 A A' F1 F2 : ℝ)
    (Dinv ε Z p G1 G2 sg sN IL eU eL e1 e2 α β rf0 rt1 rt0 rf1 : ℂ)
    (hw1 : 1 ≤ w) (hwX : w ≤ 2 * X) (hS0 : 0 ≤ S) (hc1 : 0 ≤ c1) (hA0 : 0 ≤ A) (hA'0 : 0 ≤ A')
    (hDinv : ‖Dinv‖ ≤ 2) (hDinv1 : ‖Dinv - 1‖ ≤ A' / (w * w)) (hε : ‖ε‖ = ((2 * X) ^ N)⁻¹)
    (hZ : ‖Z‖ = ((2 * X) ^ (N + 1))⁻¹)
    (hq : ‖ε * p - 1‖ ≤ A / (w * w)) (hsg : ‖sg‖ = 1) (hsN : ‖sN‖ = 1) (hIL : ‖IL‖ = c1)
    (hG1 : w ^ N * ‖G1‖ ≤ F1) (hG2 : w ^ N * ‖G2‖ ≤ F2)
    (hα : ‖α‖ ≤ S / (2 * X)) (hβ : ‖β‖ ≤ S / (2 * X))
    (hrf0 : ‖rf0‖ ≤ c1 * (1 / w) + ‖e1‖) (hrt1 : ‖rt1‖ ≤ c1 * (1 / w) + ‖e2‖)
    (hrt0 : ‖rt0‖ ≤ F1 + ‖eU‖) (hrf1 : ‖rf1‖ ≤ F2 + ‖eL‖) :
    w ^ (N + 1) * ‖(Complex.I * (sg * (-1)) * (G1 + G2)) * (Dinv * (ε * p) - 1) +
        (2 * (sg * (-1)) * IL) * (Z * (Dinv - 1)) +
        Dinv * (ε * ((e2 - e1 + eL - sN * eU) / (w : ℂ) + β * (rf0 - rf1) + α * (rt0 - rt1)))‖ ≤
      (2 * A + A') * (F1 + F2) + 2 * c1 * A' * (1 / w) +
        2 * (‖e2‖ + ‖e1‖ + ‖eL‖ + ‖eU‖ +
          S * ((c1 * (1 / w) + ‖e1‖) + (F2 + ‖eL‖) + (F1 + ‖eU‖) + (c1 * (1 / w) + ‖e2‖))) := by
  have hw0 : 0 < w := by linarith
  have hsg1 : ‖sg * (-1)‖ = 1 := by rw [norm_mul, hsg, norm_neg, norm_one, one_mul]
  have hGD : w ^ N * ‖Complex.I * (sg * (-1)) * (G1 + G2)‖ ≤ F1 + F2 := by
    rw [norm_mul, norm_mul, Complex.norm_I, hsg1, one_mul, one_mul]
    have h1 := norm_add_le G1 G2
    have h2 := mul_le_mul_of_nonneg_left h1 (pow_nonneg hw0.le N)
    linarith
  have LD := lead_bound N w A A' _ _ _ _ hw1 hA0 hA'0 hDinv hq hDinv1 hGD
  have RD := riccati_bound N w X A' (2 * (sg * (-1)) * IL) Z Dinv hw1 hwX hZ hA'0 hDinv1
  have hJ : ‖2 * (sg * (-1)) * IL‖ = 2 * c1 := by
    rw [norm_mul, norm_mul, hsg1, Complex.norm_ofNat, mul_one, hIL]
  rw [hJ] at RD
  have BD := bracket_bound N w X Dinv ε
    ((e2 - e1 + eL - sN * eU) / (w : ℂ) + β * (rf0 - rf1) + α * (rt0 - rt1)) hw0 hwX hDinv hε
  have hiwn : 0 ≤ 1 / w := div_nonneg zero_le_one hw0.le
  have hQ1 : 0 ≤ c1 * (1 / w) + ‖e1‖ := add_nonneg (mul_nonneg hc1 hiwn) (norm_nonneg _)
  have hQ4 : 0 ≤ c1 * (1 / w) + ‖e2‖ := add_nonneg (mul_nonneg hc1 hiwn) (norm_nonneg _)
  have hQ2 : 0 ≤ F2 + ‖eL‖ := le_trans (norm_nonneg _) hrf1
  have hQ3 : 0 ≤ F1 + ‖eU‖ := le_trans (norm_nonneg _) hrt0
  have hSX0 : 0 ≤ S / (2 * X) := div_nonneg hS0 (by linarith)
  have hwS : w * (S / (2 * X)) ≤ S := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  have hY : w * ‖(e2 - e1 + eL - sN * eU) / (w : ℂ) + β * (rf0 - rf1) + α * (rt0 - rt1)‖ ≤
      ‖e2‖ + ‖e1‖ + ‖eL‖ + ‖eU‖ +
        S * ((c1 * (1 / w) + ‖e1‖) + (F2 + ‖eL‖) + (F1 + ‖eU‖) + (c1 * (1 / w) + ‖e2‖)) := by
    have t1 : ‖(e2 - e1 + eL - sN * eU) / (w : ℂ)‖ ≤ (‖e2‖ + ‖e1‖ + ‖eL‖ + ‖eU‖) / w := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hw0.le]
      refine div_le_div_of_nonneg_right ?_ hw0.le
      have u1 := norm_sub_le (e2 - e1 + eL) (sN * eU)
      have u2 := norm_add_le (e2 - e1) eL
      have u3 := norm_sub_le e2 e1
      have u4 : ‖sN * eU‖ = ‖eU‖ := by rw [norm_mul, hsN, one_mul]
      linarith
    have t2 : ‖β * (rf0 - rf1)‖ ≤ S / (2 * X) * ((c1 * (1 / w) + ‖e1‖) + (F2 + ‖eL‖)) := by
      rw [norm_mul]
      exact mul_le_mul hβ ((norm_sub_le _ _).trans (add_le_add hrf0 hrf1)) (norm_nonneg _) hSX0
    have t3 : ‖α * (rt0 - rt1)‖ ≤ S / (2 * X) * ((F1 + ‖eU‖) + (c1 * (1 / w) + ‖e2‖)) := by
      rw [norm_mul]
      exact mul_le_mul hα ((norm_sub_le _ _).trans (add_le_add hrt0 hrt1)) (norm_nonneg _) hSX0
    have t4 := norm_add_le ((e2 - e1 + eL - sN * eU) / (w : ℂ) + β * (rf0 - rf1)) (α * (rt0 - rt1))
    have t5 := norm_add_le ((e2 - e1 + eL - sN * eU) / (w : ℂ)) (β * (rf0 - rf1))
    have h1 : ‖(e2 - e1 + eL - sN * eU) / (w : ℂ) + β * (rf0 - rf1) + α * (rt0 - rt1)‖ ≤
        (‖e2‖ + ‖e1‖ + ‖eL‖ + ‖eU‖) / w +
          S / (2 * X) * ((c1 * (1 / w) + ‖e1‖) + (F2 + ‖eL‖) + (F1 + ‖eU‖) + (c1 * (1 / w) + ‖e2‖)) := by
      have t6 : S / (2 * X) * ((c1 * (1 / w) + ‖e1‖) + (F2 + ‖eL‖) + (F1 + ‖eU‖) + (c1 * (1 / w) + ‖e2‖)) =
          S / (2 * X) * ((c1 * (1 / w) + ‖e1‖) + (F2 + ‖eL‖)) +
            S / (2 * X) * ((F1 + ‖eU‖) + (c1 * (1 / w) + ‖e2‖)) := by ring
      linarith
    have k1 : w * ((‖e2‖ + ‖e1‖ + ‖eL‖ + ‖eU‖) / w) = ‖e2‖ + ‖e1‖ + ‖eL‖ + ‖eU‖ := by
      rw [mul_div_assoc', mul_div_cancel_left₀ _ hw0.ne']
    have k2 : w * (S / (2 * X) * ((c1 * (1 / w) + ‖e1‖) + (F2 + ‖eL‖) + (F1 + ‖eU‖) +
        (c1 * (1 / w) + ‖e2‖))) ≤
        S * ((c1 * (1 / w) + ‖e1‖) + (F2 + ‖eL‖) + (F1 + ‖eU‖) + (c1 * (1 / w) + ‖e2‖)) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hwS (add_nonneg (add_nonneg (add_nonneg hQ1 hQ2) hQ3) hQ4)
    have h2 := mul_le_mul_of_nonneg_left h1 hw0.le
    rw [mul_add w] at h2
    linarith
  have tri1 := norm_add_le ((Complex.I * (sg * (-1)) * (G1 + G2)) * (Dinv * (ε * p) - 1) +
      (2 * (sg * (-1)) * IL) * (Z * (Dinv - 1)))
    (Dinv * (ε * ((e2 - e1 + eL - sN * eU) / (w : ℂ) + β * (rf0 - rf1) + α * (rt0 - rt1))))
  have tri2 := norm_add_le ((Complex.I * (sg * (-1)) * (G1 + G2)) * (Dinv * (ε * p) - 1))
    ((2 * (sg * (-1)) * IL) * (Z * (Dinv - 1)))
  have h1 := mul_le_mul_of_nonneg_left tri1 (pow_nonneg hw0.le (N + 1))
  have h2 := mul_le_mul_of_nonneg_left tri2 (pow_nonneg hw0.le (N + 1))
  rw [mul_add (w ^ (N + 1))] at h1 h2
  linarith

/-! ### Concrete per-index facts -/

/-- The threshold sum S (literal abbreviation). -/
def Sb {N : ℕ} (φ : SobolevC N) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N (sobolevNorm N φ) k

theorem Sb_nonneg {N : ℕ} (φ : SobolevC N) : 0 ≤ Sb φ :=
  Finset.sum_nonneg (fun k hk => KSPSWKB.endpointCoefficientBound_nonneg N (sobolevNorm N φ) k hk)

theorem dinv_facts {N : ℕ} (φ : SobolevC N) (z : ℂ) (w : ℝ)
    (hX1 : 1 ≤ ‖z‖) (hthr : WKBThreshold N (sobolevNorm N φ) z) (hw0 : 0 < w) (hwX : w ≤ 2 * ‖z‖) :
    ‖(1 - KSPSWKB.beta φ z 0 * KSPSWKB.alpha φ z 0)⁻¹‖ ≤ 2 ∧
    ‖(1 - KSPSWKB.beta φ z 0 * KSPSWKB.alpha φ z 0)⁻¹ - 1‖ ≤ 2 * Sb φ ^ 2 / (w * w) ∧
    ‖KSPSWKB.alpha φ z 0‖ ≤ Sb φ / (2 * ‖z‖) ∧ ‖KSPSWKB.beta φ z 0‖ ≤ Sb φ / (2 * ‖z‖) := by
  have hS0 := Sb_nonneg φ
  have hdet := KSPSWKB.initialColumns_det_bound N (sobolevNorm N φ) φ z le_rfl hthr
  have hdetv : Matrix.det (KSPSWKB.initialColumns φ z) =
      1 - KSPSWKB.beta φ z 0 * KSPSWKB.alpha φ z 0 := by
    simp [KSPSWKB.initialColumns, Matrix.det_fin_two]
  rw [hdetv] at hdet
  have hD : 1 - KSPSWKB.beta φ z 0 * KSPSWKB.alpha φ z 0 ≠ 0 := by
    intro h; rw [h, norm_zero] at hdet; norm_num at hdet
  have hDinv : ‖(1 - KSPSWKB.beta φ z 0 * KSPSWKB.alpha φ z 0)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have hpos : 0 < ‖1 - KSPSWKB.beta φ z 0 * KSPSWKB.alpha φ z 0‖ := by linarith
    rw [inv_le_comm₀ hpos (by norm_num)]
    linarith
  have hα : ‖KSPSWKB.alpha φ z 0‖ ≤ Sb φ / (2 * ‖z‖) :=
    KSPSWKB.endpointSum_norm_le (sobolevNorm N φ) φ le_rfl false z hX1
  have hβ : ‖KSPSWKB.beta φ z 0‖ ≤ Sb φ / (2 * ‖z‖) :=
    KSPSWKB.endpointSum_norm_le (sobolevNorm N φ) φ le_rfl true z hX1
  have hSX : Sb φ / (2 * ‖z‖) ≤ Sb φ / w := div_le_div_of_nonneg_left hS0 hw0 hwX
  refine ⟨hDinv, ?_, hα, hβ⟩
  have e : (1 - KSPSWKB.beta φ z 0 * KSPSWKB.alpha φ z 0)⁻¹ - 1 =
      (1 - KSPSWKB.beta φ z 0 * KSPSWKB.alpha φ z 0)⁻¹ *
        (KSPSWKB.beta φ z 0 * KSPSWKB.alpha φ z 0) := by
    have hinv : (1 - KSPSWKB.beta φ z 0 * KSPSWKB.alpha φ z 0)⁻¹ *
        (1 - KSPSWKB.beta φ z 0 * KSPSWKB.alpha φ z 0) = 1 := inv_mul_cancel₀ hD
    linear_combination hinv
  rw [e, norm_mul, norm_mul]
  have hb0 := norm_nonneg (KSPSWKB.beta φ z 0)
  have ha0 := norm_nonneg (KSPSWKB.alpha φ z 0)
  have hSw : 0 ≤ Sb φ / w := div_nonneg hS0 hw0.le
  have h1 : ‖KSPSWKB.beta φ z 0‖ * ‖KSPSWKB.alpha φ z 0‖ ≤ (Sb φ / w) * (Sb φ / w) :=
    mul_le_mul (hβ.trans hSX) (hα.trans hSX) ha0 hSw
  have h2 : 2 * Sb φ ^ 2 / (w * w) = 2 * ((Sb φ / w) * (Sb φ / w)) := by ring
  rw [h2]
  exact mul_le_mul hDinv h1 (mul_nonneg hb0 ha0) (by norm_num)

theorem phase_q (N : ℕ) (a : ℝ) (ha : 0 ≤ a) (xi : ℤ → ℂ)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (n : ℤ) (hν1 : 1 ≤ |(n : ℝ)|) (hνa : a ≤ |(n : ℝ)|) (hz : xi n ≠ 0) (hwX : indexWeight n ≤ 2 * ‖xi n‖) :
    ‖((2 * Complex.I * xi n) ^ N)⁻¹ * (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N - 1‖ ≤
      (N : ℝ) * 2 ^ N * (2 * a) / (indexWeight n * indexWeight n) := by
  have hX0 : 0 < ‖xi n‖ := norm_pos_iff.mpr hz
  have hw1 := one_le_w n
  have hw0 : 0 < indexWeight n := lt_of_lt_of_le one_pos hw1
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_le_four
  set z : ℂ := (n : ℂ) * (Real.pi : ℂ) / xi n with hzdef
  have hzp : ((2 * Complex.I * xi n) ^ N)⁻¹ * (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N = z ^ N := by
    rw [hzdef, div_pow]
    field_simp
    ring
  have hnorm_npi : ‖(n : ℂ) * (Real.pi : ℂ)‖ = Real.pi * |(n : ℝ)| := by
    rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]; ring
  have hX2ν : 2 * |(n : ℝ)| ≤ ‖xi n‖ := by
    have h4 := norm_sub_norm_le ((n : ℂ) * (Real.pi : ℂ)) (xi n)
    rw [norm_sub_rev, hnorm_npi] at h4
    have h2 : a / indexWeight n ≤ a := div_le_self ha hw1
    have h5 : 3 * |(n : ℝ)| ≤ Real.pi * |(n : ℝ)| := mul_le_mul_of_nonneg_right hpi3.le (by linarith)
    linarith [hxi n]
  have hz2 : ‖z‖ ≤ 2 := by
    rw [hzdef, norm_div, hnorm_npi, div_le_iff₀ hX0]
    nlinarith [mul_le_mul_of_nonneg_right hpi4 (abs_nonneg (n : ℝ))]
  have hz1 : ‖z - 1‖ ≤ 2 * a / (indexWeight n * indexWeight n) := by
    have e : z - 1 = -(xi n - (n : ℂ) * (Real.pi : ℂ)) / xi n := by
      rw [hzdef, div_sub_one hz, neg_sub]
    rw [e, norm_div, norm_neg, div_le_div_iff₀ hX0 (mul_pos hw0 hw0)]
    have h1 := hxi n
    have h2 : ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ * indexWeight n ≤ a := by
      rwa [le_div_iff₀ hw0] at h1
    have h3 : 0 ≤ ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right h2 hw0.le, mul_le_mul_of_nonneg_left hwX ha]
  rw [hzp]
  refine (norm_pow_sub_one_le z 2 (by norm_num) hz2 N).trans ?_
  have : (0 : ℝ) ≤ (N : ℝ) * 2 ^ N := by positivity
  calc (N : ℝ) * 2 ^ N * ‖z - 1‖ ≤ (N : ℝ) * 2 ^ N * (2 * a / (indexWeight n * indexWeight n)) :=
        mul_le_mul_of_nonneg_left hz1 this
    _ = (N : ℝ) * 2 ^ N * (2 * a) / (indexWeight n * indexWeight n) := by ring

theorem fourier_facts {N : ℕ} (φ : SobolevC N) (n : ℤ) (hν1 : 1 ≤ |(n : ℝ)|) :
    physicalFourier (iteratedDerivative N φ.1) (-n) =
      (-1 : ℂ) ^ N * (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N *
        physicalFourier (toPotPair φ).1 (-n) ∧
    physicalFourier (iteratedDerivative N φ.2) n =
      (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N * physicalFourier (toPotPair φ).2 n ∧
    indexWeight n ^ N * ‖physicalFourier (toPotPair φ).1 (-n)‖ ≤
      ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ ∧
    indexWeight n ^ N * ‖physicalFourier (toPotPair φ).2 n‖ ≤
      ‖physicalFourier (iteratedDerivative N φ.2) n‖ := by
  have hw0 : 0 < indexWeight n := lt_of_lt_of_le one_pos (one_le_w n)
  have hpi3 := Real.pi_gt_three
  have hDF1 : physicalFourier (iteratedDerivative N φ.1) (-n) =
      (-1 : ℂ) ^ N * (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N *
        physicalFourier (toPotPair φ).1 (-n) := by
    rw [(wkb_fourier_derivative N φ (-n)).1, ← mul_pow]
    congr 2
    push_cast
    ring
  have hDF2 : physicalFourier (iteratedDerivative N φ.2) n =
      (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N * physicalFourier (toPotPair φ).2 n :=
    (wkb_fourier_derivative N φ n).2
  have hpn : ‖(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N‖ = (2 * Real.pi * |(n : ℝ)|) ^ N := by
    rw [norm_pow, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_intCast, mul_one]
  have hwp : indexWeight n ^ N ≤ (2 * Real.pi * |(n : ℝ)|) ^ N := by
    refine pow_le_pow_left₀ hw0.le ?_ N
    have := w_le_two n hν1
    nlinarith [mul_le_mul_of_nonneg_right hpi3.le (abs_nonneg (n : ℝ))]
  have hsNn : ‖(-1 : ℂ) ^ N‖ = 1 := by rw [norm_pow, norm_neg, norm_one, one_pow]
  refine ⟨hDF1, hDF2, ?_, ?_⟩
  · rw [hDF1, norm_mul, norm_mul, hpn, hsNn, one_mul]
    exact mul_le_mul_of_nonneg_right hwp (norm_nonneg _)
  · rw [hDF2, norm_mul, hpn]
    exact mul_le_mul_of_nonneg_right hwp (norm_nonneg _)

theorem rem_formulas (N : ℕ) (φ : SobolevC N) (xi : ℤ → ℂ) (n : ℤ) (hz : xi n ≠ 0)
    (eL eU e1 e2 : ℤ → ℂ)
    (h11n : NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderLower N φ xi n =
          Complex.I * ((-1 : ℂ) ^ (n + 1)) *
            NlsGge.Pilot.physicalFourier
              (NlsGge.ThirdConsultation.KSPS.iteratedDerivative N φ.2) n +
            eL n / indexValue n ∧
        NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderUpper N φ xi n =
          Complex.I * ((-1 : ℂ) ^ n) *
            NlsGge.Pilot.physicalFourier
              (NlsGge.ThirdConsultation.KSPS.iteratedDerivative N φ.1) (-n) +
            eU n / indexValue n)
    (h12n : NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalLower N φ xi n =
          (-1 : ℂ) ^ n / (2 * Complex.I * xi n) *
            integralRiccatiLeft φ (N + 1) +
          e1 n / (indexValue n : ℂ) ∧
        NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalUpper N φ xi n =
          (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) *
            integralRiccatiRight φ (N + 1) +
          e2 n / (indexValue n : ℂ))
    (hLR : integralRiccatiLeft φ (N + 1) = integralRiccatiRight φ (N + 1)) :
    rf φ ⟨xi n, hz⟩ 0 = (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1) +
        e1 n / (indexWeight n : ℂ) ∧
    rt φ ⟨xi n, hz⟩ 1 = (-1 : ℂ) ^ n * (-1) / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1) +
        e2 n / (indexWeight n : ℂ) ∧
    (-1 : ℂ) ^ N * rt φ ⟨xi n, hz⟩ 0 = Complex.I * (-1 : ℂ) ^ n *
        physicalFourier (iteratedDerivative N φ.1) (-n) + eU n / (indexWeight n : ℂ) ∧
    rf φ ⟨xi n, hz⟩ 1 = Complex.I * ((-1 : ℂ) ^ n * (-1)) *
        physicalFourier (iteratedDerivative N φ.2) n + eL n / (indexWeight n : ℂ) := by
  have hm1 : (-1 : ℂ) ≠ 0 := by norm_num
  have hLow : rf φ ⟨xi n, hz⟩ 0 = KSPSWKB.endpointDiagonalLower N φ xi n := by
    simp only [KSPSWKB.endpointDiagonalLower, dif_neg hz]; rfl
  have hUpp : rt φ ⟨xi n, hz⟩ 1 = KSPSWKB.endpointDiagonalUpper N φ xi n := by
    simp only [KSPSWKB.endpointDiagonalUpper, dif_neg hz]; rfl
  have hRU : KSPSWKB.endpointRemainderUpper N φ xi n = (-1 : ℂ) ^ N * rt φ ⟨xi n, hz⟩ 0 := by
    simp only [KSPSWKB.endpointRemainderUpper, dif_neg hz]; rfl
  have hRL : KSPSWKB.endpointRemainderLower N φ xi n = rf φ ⟨xi n, hz⟩ 1 := by
    simp only [KSPSWKB.endpointRemainderLower, dif_neg hz]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hLow, h12n.1]; rfl
  · rw [hUpp, h12n.2, ← hLR, zpow_add_one₀ hm1]; rfl
  · rw [← hRU, h11n.2]; rfl
  · rw [← hRL, h11n.1, zpow_add_one₀ hm1]; rfl

/-! ### Per-index tail bounds -/

theorem tail_bounds
    (N : ℕ) (φ : SobolevC N) (xi : ℤ → ℂ) (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (eL eU e1 e2 : ℤ → ℂ) (n : ℤ)
    (h11n : NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderLower N φ xi n =
          Complex.I * ((-1 : ℂ) ^ (n + 1)) *
            NlsGge.Pilot.physicalFourier
              (NlsGge.ThirdConsultation.KSPS.iteratedDerivative N φ.2) n +
            eL n / indexValue n ∧
        NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderUpper N φ xi n =
          Complex.I * ((-1 : ℂ) ^ n) *
            NlsGge.Pilot.physicalFourier
              (NlsGge.ThirdConsultation.KSPS.iteratedDerivative N φ.1) (-n) +
            eU n / indexValue n)
    (h12n : NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalLower N φ xi n =
          (-1 : ℂ) ^ n / (2 * Complex.I * xi n) *
            integralRiccatiLeft φ (N + 1) +
          e1 n / (indexValue n : ℂ) ∧
        NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalUpper N φ xi n =
          (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) *
            integralRiccatiRight φ (N + 1) +
          e2 n / (indexValue n : ℂ))
    (h13 : ∀ k : ℕ, (1 ≤ k ∧ k ≤ N + 1) → integralRiccatiLeft φ k = integralRiccatiRight φ k)
    (h14 : ∀ lam : {z : ℂ // z ≠ 0}, WKBThreshold N (sobolevNorm N φ) lam.1 →
      monodromyPair (toPotPair φ) lam.1 = KSPSWKB.explicitWKBMonodromy N φ lam)
    (hn : ((⌈a⌉₊ + ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ) ≤ |n|) :
    indexWeight n ^ (N + 1) * ‖KSPSWKB.antitraceError N φ xi n‖ ≤
        (2 * ((N : ℝ) * 2 ^ N * (2 * a)) + 2 * Sb φ ^ 2) *
            (‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ +
              ‖physicalFourier (iteratedDerivative N φ.2) n‖) +
          2 * (‖eU n‖ + ‖eL n‖ + Sb φ * ((‖integralRiccatiLeft φ (N + 1)‖ * (1 / indexWeight n) + ‖e1 n‖) +
            (‖integralRiccatiLeft φ (N + 1)‖ * (1 / indexWeight n) + ‖e2 n‖))) ∧
    indexWeight n ^ (N + 1) * ‖KSPSWKB.dirichletError N φ xi n‖ ≤
        (2 * ((N : ℝ) * 2 ^ N * (2 * a)) + 2 * Sb φ ^ 2) *
            (‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ +
              ‖physicalFourier (iteratedDerivative N φ.2) n‖) +
          2 * ‖integralRiccatiLeft φ (N + 1)‖ * (2 * Sb φ ^ 2) * (1 / indexWeight n) +
          2 * (‖e2 n‖ + ‖e1 n‖ + ‖eL n‖ + ‖eU n‖ +
            Sb φ * ((‖integralRiccatiLeft φ (N + 1)‖ * (1 / indexWeight n) + ‖e1 n‖) +
              (‖physicalFourier (iteratedDerivative N φ.2) n‖ + ‖eL n‖) +
              (‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ + ‖eU n‖) +
              (‖integralRiccatiLeft φ (N + 1)‖ * (1 / indexWeight n) + ‖e2 n‖))) := by
  obtain ⟨hX1, hXT, hwX⟩ := tail_facts a _ ha xi hxi n hn
  obtain ⟨hν1, hνa⟩ := tail_nat a _ n hn
  have hz : xi n ≠ 0 := by
    intro h; rw [h, norm_zero] at hX1; norm_num at hX1
  have hX0 : 0 < ‖xi n‖ := by linarith
  have hthr : WKBThreshold N (sobolevNorm N φ) (xi n) := ⟨hX0, hXT⟩
  have hw1 := one_le_w n
  have hw0 : 0 < indexWeight n := lt_of_lt_of_le one_pos hw1
  obtain ⟨hDinv, hDinv1, hα, hβ⟩ := dinv_facts φ (xi n) (indexWeight n) hX1 hthr hw0 hwX
  have hq := phase_q N a ha xi hxi n hν1 hνa hz hwX
  obtain ⟨hDF1, hDF2, hG1, hG2⟩ := fourier_facts φ n hν1
  have hLR := h13 (N + 1) ⟨by omega, le_rfl⟩
  obtain ⟨hrf0, hrt1, hrt0', hrf1'⟩ := rem_formulas N φ xi n hz eL eU e1 e2 h11n h12n hLR
  have hsg : ‖(-1 : ℂ) ^ n‖ = 1 := by rw [norm_zpow, norm_neg, norm_one, one_zpow]
  have hsN : ‖(-1 : ℂ) ^ N‖ = 1 := by rw [norm_pow, norm_neg, norm_one, one_pow]
  obtain ⟨brf0, brt1, brt0, brf1⟩ := rem_bounds_pure (indexWeight n) ‖xi n‖ ‖integralRiccatiLeft φ (N + 1)‖
    (xi n) ((-1 : ℂ) ^ n) ((-1 : ℂ) ^ N) (integralRiccatiLeft φ (N + 1))
    (physicalFourier (iteratedDerivative N φ.1) (-n)) (physicalFourier (iteratedDerivative N φ.2) n)
    (e1 n) (e2 n) (eU n) (eL n) _ _ _ _ hw1 hwX rfl hsg hsN rfl (norm_nonneg _) hrf0 hrt1 hrt0' hrf1'
  have hsNN : ((-1 : ℂ) ^ N) * ((-1 : ℂ) ^ N) = 1 := by rw [← mul_pow]; norm_num
  have hrt0 : rt φ ⟨xi n, hz⟩ 0 = Complex.I * (-1 : ℂ) ^ n * (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N *
      physicalFourier (toPotPair φ).1 (-n) + (-1 : ℂ) ^ N * eU n / (indexWeight n : ℂ) := by
    rw [hDF1] at hrt0'
    linear_combination (-1 : ℂ) ^ N * hrt0' - (rt φ ⟨xi n, hz⟩ 0 - Complex.I * (-1 : ℂ) ^ n *
      (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N * physicalFourier (toPotPair φ).1 (-n)) * hsNN
  have hrf1 : rf φ ⟨xi n, hz⟩ 1 = -(Complex.I * (-1 : ℂ) ^ n * (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N *
      physicalFourier (toPotPair φ).2 n) + eL n / (indexWeight n : ℂ) := by
    rw [hrf1', hDF2]
    ring
  have hM := h14 ⟨xi n, hz⟩ hthr
  have hsin := et_sub_ef φ ⟨xi n, hz⟩ h13
  have hAe := antitrace_entry φ ⟨xi n, hz⟩ hM
  have hDe := dirichlet_entry φ ⟨xi n, hz⟩ hM
  rw [hsin] at hAe hDe
  have hε : ‖((2 * Complex.I * xi n) ^ N)⁻¹‖ = ((2 * ‖xi n‖) ^ N)⁻¹ := by
    rw [norm_inv, norm_pow, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
  have hε1 : ‖((2 * Complex.I * xi n) ^ (N + 1))⁻¹‖ = ((2 * ‖xi n‖) ^ (N + 1))⁻¹ := by
    rw [norm_inv, norm_pow, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
  have hA0 : (0 : ℝ) ≤ (N : ℝ) * 2 ^ N * (2 * a) := by positivity
  have hA'0 : (0 : ℝ) ≤ 2 * Sb φ ^ 2 := by positivity
  constructor
  · have hEA := antitrace_alg (KSPSWKB.antitrace φ (xi n))
      (1 - KSPSWKB.beta φ (xi n) 0 * KSPSWKB.alpha φ (xi n) 0) ((2 * Complex.I * xi n) ^ N)⁻¹
      (2 * Complex.I * Complex.sin (wkbPhase φ (xi n))) ((2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N)
      (physicalFourier (toPotPair φ).1 (-n)) (physicalFourier (toPotPair φ).2 n)
      ((-1 : ℂ) ^ n) ((-1 : ℂ) ^ N) (eU n) (eL n) (indexWeight n : ℂ)
      (KSPSWKB.alpha φ (xi n) 0) (KSPSWKB.beta φ (xi n) 0)
      (rf φ ⟨xi n, hz⟩ 0) (rt φ ⟨xi n, hz⟩ 1) (rt φ ⟨xi n, hz⟩ 0) (rf φ ⟨xi n, hz⟩ 1) rfl hAe hrt0 hrf1
    have hE : KSPSWKB.antitraceError N φ xi n = _ := hEA
    rw [hE]
    exact antitrace_pure N (indexWeight n) ‖xi n‖ (Sb φ) ‖integralRiccatiLeft φ (N + 1)‖
      ((N : ℝ) * 2 ^ N * (2 * a)) (2 * Sb φ ^ 2) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      hw1 hwX (Sb_nonneg φ) (norm_nonneg _) hA0 hA'0 hDinv hDinv1 hε hq hsg hsN hG1 hG2 hα hβ brf0 brt1
  · have hm1 : (-1 : ℂ) ≠ 0 := by norm_num
    have hED := dirichlet_alg N (KSPSWKB.dirichletNumerator φ (xi n))
      (1 - KSPSWKB.beta φ (xi n) 0 * KSPSWKB.alpha φ (xi n) 0) ((2 * Complex.I * xi n) ^ N)⁻¹
      (2 * Complex.I * Complex.sin (wkbPhase φ (xi n))) ((2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N)
      (physicalFourier (toPotPair φ).1 (-n)) (physicalFourier (toPotPair φ).2 n)
      ((-1 : ℂ) ^ n) ((-1 : ℂ) ^ N) (e1 n) (e2 n) (eU n) (eL n) (indexWeight n : ℂ)
      (KSPSWKB.alpha φ (xi n) 0) (KSPSWKB.beta φ (xi n) 0)
      (rf φ ⟨xi n, hz⟩ 0) (rt φ ⟨xi n, hz⟩ 1) (rt φ ⟨xi n, hz⟩ 0) (rf φ ⟨xi n, hz⟩ 1)
      (integralRiccatiLeft φ (N + 1)) (2 * Complex.I * xi n)
      rfl hDe rfl hrf0 hrt1 hrt0 hrf1
    unfold KSPSWKB.dirichletError
    rw [zpow_add_one₀ hm1, hED]
    exact dirichlet_pure N (indexWeight n) ‖xi n‖ (Sb φ) ‖integralRiccatiLeft φ (N + 1)‖
      ((N : ℝ) * 2 ^ N * (2 * a)) (2 * Sb φ ^ 2) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      hw1 hwX (Sb_nonneg φ) (norm_nonneg _) hA0 hA'0 hDinv hDinv1 hε hε1 hq hsg hsN rfl hG1 hG2 hα hβ
      brf0 brt1 brt0 brf1

/-! ### The weighted estimates (conditional on the KSPS-011/012/013/014 head conclusions) -/

theorem boundary_characteristics_WKB_of
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (xi : ℤ → ℂ) (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (h11 : ∃ eLower eUpper : ℤ → ℂ,
      SquareSummable eLower ∧ SquareSummable eUpper ∧
      ∀ n : ℤ,
        NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderLower N φ xi n =
          Complex.I * ((-1 : ℂ) ^ (n + 1)) *
            NlsGge.Pilot.physicalFourier
              (NlsGge.ThirdConsultation.KSPS.iteratedDerivative N φ.2) n +
            eLower n / indexValue n ∧
        NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderUpper N φ xi n =
          Complex.I * ((-1 : ℂ) ^ n) *
            NlsGge.Pilot.physicalFourier
              (NlsGge.ThirdConsultation.KSPS.iteratedDerivative N φ.1) (-n) +
            eUpper n / indexValue n)
    (h12 : ∃ e1 e2 : ℤ → ℂ,
      SquareSummable e1 ∧ SquareSummable e2 ∧
      ∀ n : ℤ,
        NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalLower N φ xi n =
          (-1 : ℂ) ^ n / (2 * Complex.I * xi n) *
            integralRiccatiLeft φ (N + 1) +
          e1 n / (indexValue n : ℂ) ∧
        NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalUpper N φ xi n =
          (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) *
            integralRiccatiRight φ (N + 1) +
          e2 n / (indexValue n : ℂ))
    (h13 : ∀ k : ℕ, (1 ≤ k ∧ k ≤ N + 1) → integralRiccatiLeft φ k = integralRiccatiRight φ k)
    (h14 : ∀ lam : {z : ℂ // z ≠ 0}, WKBThreshold N (sobolevNorm N φ) lam.1 →
      monodromyPair (toPotPair φ) lam.1 = KSPSWKB.explicitWKBMonodromy N φ lam) :
    AntiTraceDirichletWKB N φ xi := by
  obtain ⟨eL, eU, hL, hU, h11'⟩ := h11
  obtain ⟨e1, e2, hs1, hs2, h12'⟩ := h12
  have hF2 : Summable (fun n : ℤ => ‖physicalFourier (iteratedDerivative N φ.2) n‖ ^ 2) :=
    (hasSum_physicalFourier_sq _).summable
  have hF1 : Summable (fun n : ℤ => ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ ^ 2) :=
    (hasSum_physicalFourier_sq (iteratedDerivative N φ.1)).summable.comp_injective neg_injective
  have hiw := sq_summable_inv_w
  have hbound := fun n hn => tail_bounds N φ xi a ha hxi eL eU e1 e2 n (h11' n) (h12' n) h13 h14 hn
  have hrp : ∀ n : ℤ, indexWeight n ^ (2 * ((N + 1 : ℕ) : ℝ)) =
      (indexWeight n ^ (N + 1)) ^ 2 := by
    intro n
    rw [show (2 * ((N + 1 : ℕ) : ℝ)) = ((2 * (N + 1) : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    ring
  have hnn : ∀ n : ℤ, 0 ≤ indexWeight n ^ (N + 1) :=
    fun n => pow_nonneg (le_trans zero_le_one (one_le_w n)) _
  unfold AntiTraceDirichletWKB
  refine ⟨?_, ?_⟩
  · unfold WeightedL2Error
    have ht : Summable (fun n : ℤ => ((2 * ((N : ℝ) * 2 ^ N * (2 * a)) + 2 * Sb φ ^ 2) *
            (‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ +
              ‖physicalFourier (iteratedDerivative N φ.2) n‖) +
          2 * (‖eU n‖ + ‖eL n‖ + Sb φ * ((‖integralRiccatiLeft φ (N + 1)‖ * (1 / indexWeight n) + ‖e1 n‖) +
            (‖integralRiccatiLeft φ (N + 1)‖ * (1 / indexWeight n) + ‖e2 n‖)))) ^ 2) := by
      refine sq_summable_add (sq_summable_mul_left _ (sq_summable_add hF1 hF2)) (sq_summable_mul_left _ ?_)
      refine sq_summable_add (sq_summable_add hU hL) (sq_summable_mul_left _ ?_)
      exact sq_summable_add (sq_summable_add (sq_summable_mul_left _ hiw) hs1)
        (sq_summable_add (sq_summable_mul_left _ hiw) hs2)
    refine Summable.of_norm_bounded_eventually ht ?_
    filter_upwards [eventually_natAbs (⌈a⌉₊ + ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1)]
      with n hn
    beta_reduce
    rw [hrp n, ← mul_pow, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (mul_nonneg (hnn n) (norm_nonneg _)) (hbound n hn).1 2
  · unfold WeightedL2Error
    have ht : Summable (fun n : ℤ => ((2 * ((N : ℝ) * 2 ^ N * (2 * a)) + 2 * Sb φ ^ 2) *
            (‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ +
              ‖physicalFourier (iteratedDerivative N φ.2) n‖) +
          2 * ‖integralRiccatiLeft φ (N + 1)‖ * (2 * Sb φ ^ 2) * (1 / indexWeight n) +
          2 * (‖e2 n‖ + ‖e1 n‖ + ‖eL n‖ + ‖eU n‖ +
            Sb φ * ((‖integralRiccatiLeft φ (N + 1)‖ * (1 / indexWeight n) + ‖e1 n‖) +
              (‖physicalFourier (iteratedDerivative N φ.2) n‖ + ‖eL n‖) +
              (‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ + ‖eU n‖) +
              (‖integralRiccatiLeft φ (N + 1)‖ * (1 / indexWeight n) + ‖e2 n‖)))) ^ 2) := by
      refine sq_summable_add (sq_summable_add (sq_summable_mul_left _ (sq_summable_add hF1 hF2))
        (sq_summable_mul_left _ hiw)) (sq_summable_mul_left _ ?_)
      refine sq_summable_add (sq_summable_add (sq_summable_add (sq_summable_add hs2 hs1) hL) hU)
        (sq_summable_mul_left _ ?_)
      exact sq_summable_add (sq_summable_add (sq_summable_add
        (sq_summable_add (sq_summable_mul_left _ hiw) hs1) (sq_summable_add hF2 hL))
        (sq_summable_add hF1 hU)) (sq_summable_add (sq_summable_mul_left _ hiw) hs2)
    refine Summable.of_norm_bounded_eventually ht ?_
    filter_upwards [eventually_natAbs (⌈a⌉₊ + ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1)]
      with n hn
    beta_reduce
    rw [hrp n, ← mul_pow, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (mul_nonneg (hnn n) (norm_nonneg _)) (hbound n hn).2 2

end
end NlsGge.ThirdConsultation.KSPS016W
