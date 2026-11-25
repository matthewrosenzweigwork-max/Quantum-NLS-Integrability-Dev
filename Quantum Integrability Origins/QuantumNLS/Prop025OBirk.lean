import QuantumNLS.ActionTorus

/-! PROP-025 (thm:MP-mixed, mixed_propagation.tex sha256 24ab083b...), stage O4c:
the phase-torus argument for eq:MP-physical-P, generic part on `ℓ²(ℤ)` (source lines 446-532,
"Let `𝒫` be the full coordinatewise phase torus through `Z(u)` ... The frequencies are constant on each
full phase torus.  Its flow has coordinates `e^{-iτω_j(z)} z_j` ... It has operator norm at most
`1 + C|τ| W_a ‖z‖`").

For a vector field `Y` on `ℓ²(ℤ)` that is EQUIVARIANT under every coordinatewise phase rotation and whose
coordinates satisfy `Re(conj z_n · Y_n(z)) = 0` (the infinitesimal phase invariance of the chart Hamiltonian):
* `Y_eq`: `Y_n(z) = -i Ω_n(z) z_n` with the real frequency `Ω_n(z) = -Im(conj z_n Y_n(z))/|z_n|²`, valid also at a
  zero coordinate (`Y_apply_zero`); `freq_rotate`: `Ω` is constant on every full phase torus;
* `freq_le`: if `Y` is `C`-Lipschitz on a ball, then `|Ω_n(z)| ≤ C` on that ball, uniformly in `n` (a single small
  rotation of the `n`th coordinate; this replaces the division-free frequency formula eq:MP-frequency, and uses
  only the Lipschitz bound of `Y`, i.e. one derivative of the vector field);
* `flowR_hasDerivAt`: `R_τ(z) = (e^{-iτΩ_n(z)} z_n)_n` solves `ż = Y(z)`;
* **`flowR_lip`**: `‖R_τ(z') - R_τ(z)‖ ≤ (1 + 2|τ|C)‖z' - z‖` for `z, z'` in a ball on which `Y` is `C`-Lipschitz
  (the source's differential bound `1 + C|τ|W_a‖z‖`, here in Lipschitz form);
* `unif_lip`: a `C¹` map has ONE Lipschitz constant and derivative bound on balls of ONE radius around every
  point of a compact set ("Compactness supplies common local neighborhoods").
No hypothesis is added; all inherited modules are read-only.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped ComplexConjugate Topology NNReal ENNReal
open Filter Set Metric Asymptotics

namespace QuantumNLS.Prop025OBirk
open QuantumNLS.ActionTorus QuantumNLS.ResetNormalizationUniqueness

/-! ### `ℓ²` norm comparisons -/

theorem norm_le_of_pointwise (f g : S2 ℤ) {c : ℝ} (hc : 0 ≤ c) (h : ∀ n, ‖f n‖ ≤ c * ‖g n‖) :
    ‖f‖ ≤ c * ‖g‖ := by
  have h2 : ‖f‖ ^ 2 ≤ (c * ‖g‖) ^ 2 := by
    rw [tsum_sq_eq, mul_pow, tsum_sq_eq, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun n => ?_) (summable_sq f) ((summable_sq g).mul_left _)
    calc ‖f n‖ ^ 2 ≤ (c * ‖g n‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (h n) 2
      _ = c ^ 2 * ‖g n‖ ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

theorem norm_sq_le_of_pointwise2 (f g k : S2 ℤ) {a b : ℝ} (_ha : 0 ≤ a) (_hb : 0 ≤ b)
    (h : ∀ n, ‖f n‖ ≤ a * ‖g n‖ + b * ‖k n‖) :
    ‖f‖ ^ 2 ≤ 2 * a ^ 2 * ‖g‖ ^ 2 + 2 * b ^ 2 * ‖k‖ ^ 2 := by
  have e : ∑' n, (2 * a ^ 2 * ‖g n‖ ^ 2 + 2 * b ^ 2 * ‖k n‖ ^ 2) =
      2 * a ^ 2 * ∑' n, ‖g n‖ ^ 2 + 2 * b ^ 2 * ∑' n, ‖k n‖ ^ 2 := by
    rw [Summable.tsum_add ((summable_sq g).mul_left _) ((summable_sq k).mul_left _), tsum_mul_left,
      tsum_mul_left]
  rw [tsum_sq_eq f, tsum_sq_eq g, tsum_sq_eq k, ← e]
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_sq f)
    (((summable_sq g).mul_left _).add ((summable_sq k).mul_left _))
  have h2 : ‖f n‖ ^ 2 ≤ (a * ‖g n‖ + b * ‖k n‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (h n) 2
  nlinarith [sq_nonneg (a * ‖g n‖ - b * ‖k n‖)]

theorem norm_apply_le (f : S2 ℤ) (n : ℤ) : ‖f n‖ ≤ ‖f‖ :=
  lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) f n

/-! ### Single-coordinate rotations -/

/-- Rotation of the `n`th coordinate only. -/
def rotj (n : ℤ) (c : Circle) : ℤ → Circle := Pi.mulSingle n c

theorem rotj_self (n : ℤ) (c : Circle) : rotj n c n = c := by
  unfold rotj; simp

theorem norm_rotj_sub (n : ℤ) (c : Circle) (z : S2 ℤ) :
    ‖rotate (rotj n c) z - z‖ ≤ ‖(c : ℂ) - 1‖ * ‖z n‖ := by
  have h := norm_le_of_pointwise (rotate (rotj n c) z - z) (lp.single 2 n (z n))
    (norm_nonneg ((c : ℂ) - 1)) (fun m => ?_)
  · rwa [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)] at h
  · rw [lp.coeFn_sub, Pi.sub_apply, rotate_apply, lp.single_apply]
    unfold rotj
    rw [Pi.mulSingle_apply]
    by_cases hm : m = n
    · subst hm
      rw [if_pos rfl, Pi.single_eq_same,
        show (c : ℂ) * z m - z m = ((c : ℂ) - 1) * z m by ring, norm_mul]
    · rw [if_neg hm, Pi.single_eq_of_ne hm]
      simp

/-! ### Equivariant phase-invariant vector fields -/

variable (Y : S2 ℤ → S2 ℤ)

/-- The frequency `Ω_n(z) = -Im(conj z_n · Y_n(z)) / |z_n|²` (zero at a zero coordinate). -/
def freq (z : S2 ℤ) (n : ℤ) : ℝ := -((conj (z n) * Y z n).im) / ‖z n‖ ^ 2

variable {Y}

theorem Y_apply_zero (hY : ∀ (ψ : ℤ → Circle) (z : S2 ℤ), Y (rotate ψ z) = rotate ψ (Y z))
    {z : S2 ℤ} {n : ℤ} (hz : z n = 0) : Y z n = 0 := by
  have hr : rotate (rotj n (Circle.exp Real.pi)) z = z := by
    refine lp.ext (funext fun m => ?_)
    rw [rotate_apply]
    unfold rotj
    rw [Pi.mulSingle_apply]
    by_cases hm : m = n
    · subst hm; rw [hz, mul_zero]
    · rw [if_neg hm]; simp
  have h1 := congrArg (fun w : S2 ℤ => w n) (hY (rotj n (Circle.exp Real.pi)) z)
  simp only [hr, rotate_apply, rotj_self, Circle.coe_exp] at h1
  have he : Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := Complex.exp_pi_mul_I
  rw [he] at h1
  linear_combination (1 / 2 : ℂ) * h1

theorem Y_eq (hY : ∀ (ψ : ℤ → Circle) (z : S2 ℤ), Y (rotate ψ z) = rotate ψ (Y z))
    (hre : ∀ (z : S2 ℤ) (n : ℤ), (conj (z n) * Y z n).re = 0) (z : S2 ℤ) (n : ℤ) :
    Y z n = -Complex.I * (freq Y z n : ℂ) * z n := by
  by_cases hz : z n = 0
  · rw [Y_apply_zero hY hz, hz, mul_zero]
  · have hn : (‖z n‖ ^ 2 : ℝ) ≠ 0 := by positivity
    have hnc : (((‖z n‖ ^ 2 : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
    have hw : conj (z n) * Y z n = Complex.I * (((conj (z n) * Y z n).im : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hre z n]
    have hzz : z n * conj (z n) = (((‖z n‖ ^ 2 : ℝ)) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hY' : Y z n = z n * (conj (z n) * Y z n) / (((‖z n‖ ^ 2 : ℝ)) : ℂ) := by
      rw [← mul_assoc, hzz]; field_simp
    rw [hY', hw]
    unfold freq
    push_cast
    field_simp

theorem freq_rotate (hY : ∀ (ψ : ℤ → Circle) (z : S2 ℤ), Y (rotate ψ z) = rotate ψ (Y z))
    (ψ : ℤ → Circle) (z : S2 ℤ) (n : ℤ) : freq Y (rotate ψ z) n = freq Y z n := by
  unfold freq
  rw [hY, rotate_apply, rotate_apply]
  have hψ : conj ((ψ n : ℂ)) * (ψ n : ℂ) = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]; simp
  have e1 : conj ((ψ n : ℂ) * z n) * ((ψ n : ℂ) * Y z n) = conj (z n) * Y z n := by
    rw [map_mul]; linear_combination (conj (z n) * Y z n) * hψ
  rw [e1, norm_mul, Circle.norm_coe, one_mul]

/-- **Uniform frequency bound**: `|Ω_n(z)| ≤ C` on any ball where `Y` is `C`-Lipschitz. -/
theorem freq_le (hY : ∀ (ψ : ℤ → Circle) (z : S2 ℤ), Y (rotate ψ z) = rotate ψ (Y z))
    (hre : ∀ (z : S2 ℤ) (n : ℤ), (conj (z n) * Y z n).re = 0)
    {C : ℝ≥0} {p : S2 ℤ} {δ : ℝ} (hL : LipschitzOnWith C Y (ball p δ))
    {z : S2 ℤ} (hz : z ∈ ball p δ) (n : ℤ) : |freq Y z n| ≤ C := by
  by_cases h0 : z n = 0
  · unfold freq; rw [h0]; simp
  have hzn : 0 < ‖z n‖ := norm_pos_iff.mpr h0
  have hεpos : 0 < δ - dist z p := by rw [mem_ball] at hz; linarith
  set φ : ℝ := min 1 ((δ - dist z p) / (2 * (‖z n‖ + 1))) with hφ
  have hφpos : 0 < φ := lt_min one_pos (by positivity)
  have hφ1 : φ ≤ 1 := min_le_left _ _
  have hφε : φ ≤ (δ - dist z p) / (2 * (‖z n‖ + 1)) := min_le_right _ _
  set c : Circle := Circle.exp φ with hcdef
  have hcexp : (c : ℂ) = Complex.exp (Complex.I * (φ : ℂ)) := by
    rw [hcdef, Circle.coe_exp, mul_comm]
  have hc1 : ‖(c : ℂ) - 1‖ ≤ φ := by
    have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := φ)
    rwa [Real.norm_eq_abs, abs_of_pos hφpos, ← hcexp] at this
  have hcpos : 0 < ‖(c : ℂ) - 1‖ := by
    rw [hcexp, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
    have hs : 0 < Real.sin (φ / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_gt_three])
    rw [abs_of_pos (by linarith)]
    linarith
  set w := rotate (rotj n c) z with hwdef
  have hwz : ‖w - z‖ ≤ ‖(c : ℂ) - 1‖ * ‖z n‖ := norm_rotj_sub n c z
  have hw : w ∈ ball p δ := by
    rw [mem_ball]
    have h1 : ‖(c : ℂ) - 1‖ * ‖z n‖ < δ - dist z p := by
      have e1 : ‖(c : ℂ) - 1‖ * ‖z n‖ ≤ φ * ‖z n‖ := mul_le_mul_of_nonneg_right hc1 hzn.le
      have e2 : φ * ‖z n‖ ≤ (δ - dist z p) / (2 * (‖z n‖ + 1)) * ‖z n‖ :=
        mul_le_mul_of_nonneg_right hφε hzn.le
      have e3 : (δ - dist z p) / (2 * (‖z n‖ + 1)) * ‖z n‖ < δ - dist z p := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
    calc dist w p ≤ dist w z + dist z p := dist_triangle _ _ _
      _ < δ := by rw [dist_eq_norm]; linarith
  have hlip := hL.dist_le_mul w hw z hz
  rw [dist_eq_norm, dist_eq_norm] at hlip
  have hn := norm_apply_le (Y w - Y z) n
  have hcoord : (Y w - Y z) n = ((c : ℂ) - 1) * Y z n := by
    rw [lp.coeFn_sub, Pi.sub_apply, hwdef, hY, rotate_apply, rotj_self]; ring
  rw [hcoord, norm_mul] at hn
  have key : ‖(c : ℂ) - 1‖ * ‖Y z n‖ ≤ ‖(c : ℂ) - 1‖ * ((C : ℝ) * ‖z n‖) := by
    calc ‖(c : ℂ) - 1‖ * ‖Y z n‖ ≤ (C : ℝ) * ‖w - z‖ := hn.trans hlip
      _ ≤ (C : ℝ) * (‖(c : ℂ) - 1‖ * ‖z n‖) := mul_le_mul_of_nonneg_left hwz C.2
      _ = ‖(c : ℂ) - 1‖ * ((C : ℝ) * ‖z n‖) := by ring
  have hYn : ‖Y z n‖ ≤ (C : ℝ) * ‖z n‖ := le_of_mul_le_mul_left key hcpos
  rw [Y_eq hY hre z n, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs] at hYn
  exact le_of_mul_le_mul_right hYn hzn

/-! ### The torus flow -/

/-- `R_τ(z) = (e^{-iτΩ_n} z_n)_n` for real frequencies `Ω`. -/
def flowR (Ω : ℤ → ℝ) (τ : ℝ) (z : S2 ℤ) : S2 ℤ := rotate (fun n => Circle.exp (-(τ * Ω n))) z

theorem flowR_apply (Ω : ℤ → ℝ) (τ : ℝ) (z : S2 ℤ) (n : ℤ) :
    flowR Ω τ z n = Complex.exp (((-(τ * Ω n) : ℝ) : ℂ) * Complex.I) * z n := by
  unfold flowR; rw [rotate_apply, Circle.coe_exp]

theorem flowR_zero (Ω : ℤ → ℝ) (z : S2 ℤ) : flowR Ω 0 z = z := by
  refine lp.ext (funext fun n => ?_)
  rw [flowR_apply]; simp

theorem norm_flowR (Ω : ℤ → ℝ) (τ : ℝ) (z : S2 ℤ) : ‖flowR Ω τ z‖ = ‖z‖ := by
  have h := norm_rotate_sub (fun n => Circle.exp (-(τ * Ω n))) z 0
  have h0 : rotate (fun n => Circle.exp (-(τ * Ω n))) (0 : S2 ℤ) = 0 :=
    lp.ext (funext fun n => by simp)
  rw [h0, sub_zero, sub_zero] at h
  exact h

/-- **The flow of `Y` through a point with bounded frequencies is the torus rotation `R_τ`.** -/
theorem flowR_hasDerivAt (hY : ∀ (ψ : ℤ → Circle) (z : S2 ℤ), Y (rotate ψ z) = rotate ψ (Y z))
    (hre : ∀ (z : S2 ℤ) (n : ℤ), (conj (z n) * Y z n).re = 0) {z : S2 ℤ} {C : ℝ}
    (hC : ∀ n, |freq Y z n| ≤ C) (τ : ℝ) :
    HasDerivAt (fun s => flowR (freq Y z) s z) (Y (flowR (freq Y z) τ z)) τ := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine IsBigO.trans_isLittleO (g := fun s : ℝ => s ^ 2) ?_ (isLittleO_pow_id (by norm_num))
  refine IsBigO.of_bound (C ^ 2 * ‖z‖) ?_
  have hev : ∀ᶠ s : ℝ in 𝓝 0, |s| * C ≤ 1 := by
    have h1 : Tendsto (fun s : ℝ => |s| * C) (𝓝 0) (𝓝 (|0| * C)) :=
      (continuous_abs.tendsto 0).mul_const C
    rw [abs_zero, zero_mul] at h1
    exact h1.eventually (ge_mem_nhds one_pos)
  filter_upwards [hev] with s hs
  rw [Real.norm_eq_abs, abs_pow, sq_abs]
  have hpt : ∀ n, ‖(flowR (freq Y z) (τ + s) z - flowR (freq Y z) τ z - s • Y (flowR (freq Y z) τ z)) n‖ ≤
      (C ^ 2 * s ^ 2) * ‖z n‖ := by
    intro n
    have hYn := Y_eq hY hre (flowR (freq Y z) τ z) n
    have hfr : freq Y (flowR (freq Y z) τ z) n = freq Y z n := by
      unfold flowR; rw [freq_rotate hY]
    rw [hfr, flowR_apply] at hYn
    set Ω := freq Y z n with hΩ
    set x : ℂ := ((-(s * Ω) : ℝ) : ℂ) * Complex.I with hx
    have hcoord : (flowR (freq Y z) (τ + s) z - flowR (freq Y z) τ z - s • Y (flowR (freq Y z) τ z)) n =
        (Complex.exp (((-(τ * Ω) : ℝ) : ℂ) * Complex.I) * z n) * (Complex.exp x - 1 - x) := by
      rw [lp.coeFn_sub, lp.coeFn_sub, Pi.sub_apply, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, hYn,
        flowR_apply, flowR_apply]
      have he : Complex.exp ((((-((τ + s) * freq Y z n)) : ℝ) : ℂ) * Complex.I) =
          Complex.exp (((-(τ * Ω) : ℝ) : ℂ) * Complex.I) * Complex.exp x := by
        rw [← Complex.exp_add, hx, hΩ]; congr 1; push_cast; ring
      rw [he, hx, Complex.real_smul, hΩ]
      push_cast
      ring
    rw [hcoord, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    have hxn : ‖x‖ = |s| * |Ω| := by
      rw [hx, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul]
    have hx1 : ‖x‖ ≤ 1 := by
      rw [hxn]; exact (mul_le_mul_of_nonneg_left (hC n) (abs_nonneg s)).trans hs
    have hb := Complex.norm_exp_sub_one_sub_id_le hx1
    have hx2 : ‖x‖ ^ 2 ≤ C ^ 2 * s ^ 2 := by
      have hΩ2 : |Ω| ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hC n) 2
      rw [hxn, mul_pow, sq_abs s, mul_comm]
      exact mul_le_mul_of_nonneg_right hΩ2 (sq_nonneg s)
    calc ‖z n‖ * ‖Complex.exp x - 1 - x‖ ≤ ‖z n‖ * (C ^ 2 * s ^ 2) :=
          mul_le_mul_of_nonneg_left (hb.trans hx2) (norm_nonneg _)
      _ = C ^ 2 * s ^ 2 * ‖z n‖ := by ring
  have := norm_le_of_pointwise _ z (by positivity) hpt
  calc _ ≤ C ^ 2 * s ^ 2 * ‖z‖ := by simpa [add_comm] using this
    _ = C ^ 2 * ‖z‖ * s ^ 2 := by ring

/-- **Lipschitz bound of the torus flow** (the source's `‖dR_τ‖ ≤ 1 + C|τ|W_a‖z‖`). -/
theorem flowR_lip (hY : ∀ (ψ : ℤ → Circle) (z : S2 ℤ), Y (rotate ψ z) = rotate ψ (Y z))
    (hre : ∀ (z : S2 ℤ) (n : ℤ), (conj (z n) * Y z n).re = 0)
    {C : ℝ≥0} {p : S2 ℤ} {δ : ℝ} (hL : LipschitzOnWith C Y (ball p δ))
    {z z' : S2 ℤ} (hz : z ∈ ball p δ) (hz' : z' ∈ ball p δ) (τ : ℝ) :
    ‖flowR (freq Y z') τ z' - flowR (freq Y z) τ z‖ ≤ (1 + 2 * |τ| * C) * ‖z' - z‖ := by
  have hA : ‖flowR (freq Y z') τ z' - flowR (freq Y z') τ z‖ = ‖z' - z‖ := by
    unfold flowR; exact norm_rotate_sub _ _ _
  have hlip := hL.dist_le_mul z' hz' z hz
  rw [dist_eq_norm, dist_eq_norm] at hlip
  have hpt : ∀ n, ‖(flowR (freq Y z') τ z - flowR (freq Y z) τ z) n‖ ≤
      (|τ| * C) * ‖(z - z') n‖ + |τ| * ‖(Y z' - Y z) n‖ := by
    intro n
    rw [lp.coeFn_sub, Pi.sub_apply, flowR_apply, flowR_apply, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_sub,
      Pi.sub_apply]
    set Ω' := freq Y z' n
    set Ω := freq Y z n
    have hdiff : Complex.exp (((-(τ * Ω') : ℝ) : ℂ) * Complex.I) - Complex.exp (((-(τ * Ω) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((-(τ * Ω) : ℝ) : ℂ) * Complex.I) *
          (Complex.exp (Complex.I * ((-(τ * (Ω' - Ω)) : ℝ) : ℂ)) - 1) := by
      rw [mul_sub, mul_one, ← Complex.exp_add]; congr 2; push_cast; ring
    have he : ‖Complex.exp (Complex.I * ((-(τ * (Ω' - Ω)) : ℝ) : ℂ)) - 1‖ ≤ |τ| * |Ω' - Ω| := by
      have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(τ * (Ω' - Ω)))
      rwa [Real.norm_eq_abs, abs_neg, abs_mul] at this
    -- `(Ω' - Ω) z_n = Ω'(z_n - z'_n) + i(Y_n z' - Y_n z)`
    have hYz := Y_eq hY hre z n
    have hYz' := Y_eq hY hre z' n
    have hkey : ((Ω' - Ω : ℝ) : ℂ) * z n = (Ω' : ℂ) * (z n - z' n) + Complex.I * (Y z' n - Y z n) := by
      rw [hYz, hYz']; push_cast; ring_nf; rw [Complex.I_sq]; ring
    have hk : |Ω' - Ω| * ‖z n‖ ≤ C * ‖z n - z' n‖ + ‖Y z' n - Y z n‖ := by
      have h1 : ‖((Ω' - Ω : ℝ) : ℂ) * z n‖ = |Ω' - Ω| * ‖z n‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [← h1, hkey]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (freq_le hY hre hL hz' n) (norm_nonneg _)
      · rw [norm_mul, Complex.norm_I, one_mul]
    rw [← sub_mul, hdiff, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    calc ‖Complex.exp (Complex.I * ((-(τ * (Ω' - Ω)) : ℝ) : ℂ)) - 1‖ * ‖z n‖
        ≤ |τ| * |Ω' - Ω| * ‖z n‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
      _ = |τ| * (|Ω' - Ω| * ‖z n‖) := by ring
      _ ≤ |τ| * (C * ‖z n - z' n‖ + ‖Y z' n - Y z n‖) := mul_le_mul_of_nonneg_left hk (abs_nonneg τ)
      _ = (|τ| * C) * ‖z n - z' n‖ + |τ| * ‖Y z' n - Y z n‖ := by ring
  have hB := norm_sq_le_of_pointwise2 _ _ _ (by positivity) (abs_nonneg τ) hpt
  have hzz : ‖z - z'‖ = ‖z' - z‖ := norm_sub_rev _ _
  rw [hzz] at hB
  have hB2 : ‖flowR (freq Y z') τ z - flowR (freq Y z) τ z‖ ^ 2 ≤ (2 * |τ| * C * ‖z' - z‖) ^ 2 := by
    have h3 : ‖Y z' - Y z‖ ^ 2 ≤ ((C : ℝ) * ‖z' - z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hlip 2
    nlinarith [sq_nonneg (|τ|), sq_nonneg ((C : ℝ) * ‖z' - z‖)]
  have hB3 : ‖flowR (freq Y z') τ z - flowR (freq Y z) τ z‖ ≤ 2 * |τ| * C * ‖z' - z‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hB2
  have he : flowR (freq Y z') τ z' - flowR (freq Y z) τ z =
      (flowR (freq Y z') τ z' - flowR (freq Y z') τ z) + (flowR (freq Y z') τ z - flowR (freq Y z) τ z) := by
    abel
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [hA]
  linarith

/-! ### One radius around a compact set -/

theorem unif_lip {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ 1 f) {S : Set E} (hS : IsCompact S) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ S,
      LipschitzOnWith C f (ball p δ) ∧ ∀ x ∈ ball p δ, ‖fderiv ℝ f x‖ ≤ C := by
  have hc : Continuous (fun x => ‖fderiv ℝ f x‖) := (hf.continuous_fderiv one_ne_zero).norm
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  set C : ℝ≥0 := Real.toNNReal (B + 1) with hCdef
  have hU : IsOpen {x : E | ‖fderiv ℝ f x‖ < B + 1} := isOpen_lt hc continuous_const
  have hSU : S ⊆ {x : E | ‖fderiv ℝ f x‖ < B + 1} := by
    intro x hx
    have := hB x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at this
    show ‖fderiv ℝ f x‖ < B + 1
    linarith
  obtain ⟨δ, hδ, hth⟩ := hS.exists_thickening_subset_open hU hSU
  have hbd : ∀ p ∈ S, ∀ x ∈ ball p δ, ‖fderiv ℝ f x‖ ≤ C := by
    intro p hp x hx
    have hx' := hth (ball_subset_thickening hp δ hx)
    have h1 : ‖fderiv ℝ f x‖ < B + 1 := hx'
    rw [hCdef, Real.coe_toNNReal _ (by linarith [norm_nonneg (fderiv ℝ f x)])]
    exact h1.le
  refine ⟨C, δ, hδ, fun p hp => ⟨?_, hbd p hp⟩⟩
  exact (convex_ball p δ).lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => (hf.differentiable one_ne_zero).differentiableAt)
    (fun x hx => by rw [← NNReal.coe_le_coe, coe_nnnorm]; exact hbd p hp x hx)

end QuantumNLS.Prop025OBirk

#print axioms QuantumNLS.Prop025OBirk.Y_eq
#print axioms QuantumNLS.Prop025OBirk.freq_le
#print axioms QuantumNLS.Prop025OBirk.flowR_hasDerivAt
#print axioms QuantumNLS.Prop025OBirk.flowR_lip
#print axioms QuantumNLS.Prop025OBirk.unif_lip

-- Recursive type/value audit of every own declaration: standard axioms only, and no held
-- identifier (HeldGP14Tonelli, the superseded pre-D1 `RegularCut`) in the transitive closure.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop025OBirk." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          n.components.any (fun c => c.toString == "RegularCut") then
        throwError "Held dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Prop025OBirk aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only, no held identifiers."
