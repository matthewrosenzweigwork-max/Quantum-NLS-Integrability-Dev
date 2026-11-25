import Mathlib
import QuantumNLS.RB01TraceAsym

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01-12: the uniform estimates preceding the root count
(source `collective_actions.tex:344-362`: "for any prescribed accuracy ε we may choose N and then shrink U ... on the
fixed w disks used below"; "On |w| ≤ 3d the other trace sign is nonzero"; "On small fixed real intervals around w = ±d
the free trace lies strictly between −2 and 2").  Real slice, actual DEF-014 discriminant.

* `uniform_trace_nbhd` (order of choices: `N` first, then `ρ`): for every `u₀`, `R` and `ε > 0` there are `N`, `ρ > 0`
  with `|Δ_{tu}(p_n + w) − 2(−1)^n cos(Lw/2)| < ε` for `|n| > N`, `‖u − u₀‖ < ρ`, `t ∈ [0,1]`, `|w| ≤ R`
  (RB01TraceAsym.trace_asymptotic on the compact ray `{t u₀}` plus RB01TraceLip.disc_lipschitz).
* Free objects: `freeF L w = (2cos(Lw/2))² − 4 = −4 sin²(Lw/2)` (`freeF_eq`), `|freeF w| ≥ L²|w|²/4` for `|w| ≤ 1/L`.
* Fixed radius `dd L = 1/(4L)` (the source's `d`), fixed accuracy `ε₀ = 2⁻¹⁶`, and `fn κ q n w = Δ_q(p_n + w)² − 4`.
* **`root_prep`**: for every `u₀` there are `N`, `ρ > 0` such that for `|n| > N`, `‖u − u₀‖ < ρ`, `t ∈ [0,1]`, `q = t u`:
  (a) `|fn − freeF| ≤ 6ε₀` on `|w| ≤ 4d`; (b) `|fn(w)| ≥ 10/65536 > 0` on `d/8 ≤ |w| ≤ 4d` (no zero there);
  (c) `|Δ_q(p_n + w) + 2(−1)^n| ≥ 1` on `|w| ≤ 4d` (the other trace sign); (d) `|Δ_q(p_n ± d)| < 2` (band points);
  (e) Cauchy: `|∂²_w(fn − freeF)(w)| ≤ 2·6ε₀/d²` on `|w| ≤ 3d`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set Metric
open QuantumNLS.RB01TraceLip QuantumNLS.RB01TraceAsym

namespace QuantumNLS.RB01RootPrep

variable {L : ℝ} [Fact (0 < L)]

/-- The order of choices of the source: `N` from the compact ray, then `ρ` from the Lipschitz bound. -/
theorem uniform_trace_nbhd (κ : ℝ) (u₀ : PhysicalTensor.L2T L) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| → ∀ u : PhysicalTensor.L2T L, ‖u - u₀‖ < ρ →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ w : ℂ, ‖w‖ ≤ R →
        ‖L2SpatialTransfer.discriminant κ (t • u) ((QuantumNLS.LocalSpectral.pm L n : ℂ) + w) -
          2 * (-1 : ℂ) ^ n * Complex.cos (L * w / 2)‖ < ε := by
  have hK : IsCompact ((fun t : ℝ => t • u₀) '' Icc 0 1) :=
    isCompact_Icc.image (continuous_id.smul continuous_const)
  obtain ⟨N, hN⟩ := trace_asymptotic κ hK (isCompact_closedBall (0 : ℂ) R) (half_pos hε)
  set C := lipConst κ R (‖u₀‖ + 1) L with hC
  have hC0 : 0 ≤ C := lipConst_nonneg _ _ _ _
  refine ⟨N, min 1 (ε / 2 / (C + 1)), lt_min one_pos (div_pos (half_pos hε) (by linarith)), ?_⟩
  intro n hn u hu t ht w hw
  have hu1 : ‖u - u₀‖ < 1 := lt_of_lt_of_le hu (min_le_left _ _)
  have hu2 : ‖u - u₀‖ < ε / 2 / (C + 1) := lt_of_lt_of_le hu (min_le_right _ _)
  have ht0 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hnu : ‖t • u‖ ≤ ‖u₀‖ + 1 := by
    rw [norm_smul, Real.norm_eq_abs]
    have : ‖u‖ ≤ ‖u₀‖ + 1 := by
      have := norm_le_insert' u u₀
      linarith
    calc |t| * ‖u‖ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right ht0 (norm_nonneg _)
      _ ≤ _ := by linarith
  have hnu0 : ‖t • u₀‖ ≤ ‖u₀‖ + 1 := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |t| * ‖u₀‖ ≤ 1 * ‖u₀‖ := mul_le_mul_of_nonneg_right ht0 (norm_nonneg _)
      _ ≤ _ := by linarith
  have him : |((QuantumNLS.LocalSpectral.pm L n : ℂ) + w).im| ≤ R := by
    have : ((QuantumNLS.LocalSpectral.pm L n : ℂ) + w).im = w.im := by simp
    rw [this]; exact (Complex.abs_im_le_norm w).trans hw
  have hl := disc_lipschitz κ (t • u) (t • u₀) hnu hnu0 him
  have hsub : ‖t • u - t • u₀‖ ≤ ‖u - u₀‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
    calc |t| * ‖u - u₀‖ ≤ 1 * ‖u - u₀‖ := mul_le_mul_of_nonneg_right ht0 (norm_nonneg _)
      _ = _ := one_mul _
  have hl2 : C * ‖t • u - t • u₀‖ < ε / 2 := by
    have h1 : C * ‖t • u - t • u₀‖ ≤ C * ‖u - u₀‖ := mul_le_mul_of_nonneg_left hsub hC0
    have h2 : C * ‖u - u₀‖ ≤ (C + 1) * ‖u - u₀‖ := by nlinarith [norm_nonneg (u - u₀)]
    have h3 : (C + 1) * ‖u - u₀‖ < ε / 2 := by
      rw [lt_div_iff₀ (by linarith)] at hu2; linarith
    linarith
  have ha := hN n hn (t • u₀) (mem_image_of_mem _ ht) w (by simpa using hw)
  calc _ ≤ ‖L2SpatialTransfer.discriminant κ (t • u) ((QuantumNLS.LocalSpectral.pm L n : ℂ) + w) -
          L2SpatialTransfer.discriminant κ (t • u₀) ((QuantumNLS.LocalSpectral.pm L n : ℂ) + w)‖ +
        ‖L2SpatialTransfer.discriminant κ (t • u₀) ((QuantumNLS.LocalSpectral.pm L n : ℂ) + w) -
          2 * (-1 : ℂ) ^ n * Complex.cos (L * w / 2)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (hl.trans hl2.le) ha
    _ = ε := add_halves ε

/-! ### Elementary bounds for the free trace -/

theorem sin_lower {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : ‖z‖ / 2 ≤ ‖Complex.sin z‖ := by
  have hb := Complex.sin_bound (x := z) (by linarith)
  have h3 : ‖z ^ 3 / 6‖ = ‖z‖ ^ 3 / 6 := by rw [norm_div, norm_pow]; norm_num
  set r := ‖z‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have h1 : ‖Complex.sin z - z‖ ≤ r ^ 5 / 100 + r ^ 3 / 6 := by
    have : Complex.sin z - z = (Complex.sin z - (z - z ^ 3 / 6)) + -(z ^ 3 / 6) := by ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, h3]; linarith
  have h2 : r ^ 5 / 100 + r ^ 3 / 6 ≤ r / 2 := by
    have hr2 : r ^ 2 ≤ 1 / 4 := by nlinarith
    have hr4 : r ^ 4 ≤ 1 / 16 := by nlinarith
    nlinarith
  have h4 : ‖z‖ ≤ ‖Complex.sin z‖ + ‖Complex.sin z - z‖ := by
    have := norm_sub_le (Complex.sin z) (Complex.sin z - z)
    simpa using this
  linarith

theorem cos_close {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : ‖Complex.cos z - 1‖ ≤ 1 / 4 := by
  have hb := Complex.cos_bound (x := z) (by linarith)
  have h2 : ‖z ^ 2 / 2‖ = ‖z‖ ^ 2 / 2 := by rw [norm_div, norm_pow]; norm_num
  set r := ‖z‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have : Complex.cos z - 1 = (Complex.cos z - (1 - z ^ 2 / 2)) + -(z ^ 2 / 2) := by ring
  rw [this]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg, h2]
  have hr2 : r ^ 2 ≤ 1 / 4 := by nlinarith
  have hr4 : r ^ 4 ≤ 1 / 16 := by nlinarith
  nlinarith

/-- The free numerator `f⁰(w) = Δ_0(p_n + w)² − 4`. -/
def freeF (L : ℝ) (w : ℂ) : ℂ := (2 * Complex.cos (L * w / 2)) ^ 2 - 4

theorem freeF_eq (w : ℂ) : freeF L w = -4 * Complex.sin (L * w / 2) ^ 2 := by
  have h := Complex.sin_sq_add_cos_sq (L * w / 2)
  unfold freeF; linear_combination (4 : ℂ) * h

theorem freeF_lower {w : ℂ} (hw : ‖w‖ ≤ 1 / L) : (L * ‖w‖) ^ 2 / 4 ≤ ‖freeF L w‖ := by
  have hL : 0 < L := Fact.out
  have hz : ‖(L : ℂ) * w / 2‖ = L * ‖w‖ / 2 := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]; norm_num
  have hz2 : ‖(L : ℂ) * w / 2‖ ≤ 1 / 2 := by
    rw [hz]; have := mul_le_mul_of_nonneg_left hw hL.le; rw [mul_one_div_cancel hL.ne'] at this; linarith
  have hs := sin_lower hz2
  rw [freeF_eq, norm_mul, norm_pow]
  rw [hz] at hs
  have : ‖(-4 : ℂ)‖ = 4 := by norm_num
  rw [this]
  have h0 : 0 ≤ L * ‖w‖ / 2 / 2 := by positivity
  nlinarith [pow_le_pow_left₀ h0 hs 2]

/-- The fixed radius `d` of the source. -/
def dd (L : ℝ) : ℝ := 1 / (4 * L)

/-- The fixed trace accuracy. -/
def ε₀ : ℝ := 1 / 65536

/-- `f_n(w, q) = Δ_q(p_n + w)² − 4`. -/
def fn (κ : ℝ) (q : PhysicalTensor.L2T L) (n : ℤ) (w : ℂ) : ℂ :=
  L2SpatialTransfer.discriminant κ q ((QuantumNLS.LocalSpectral.pm L n : ℂ) + w) ^ 2 - 4

theorem dd_pos : 0 < dd L := by unfold dd; have : 0 < L := Fact.out; positivity

theorem sign_sq (n : ℤ) : ((-1 : ℂ) ^ n) ^ 2 = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]; norm_num

theorem norm_sign (n : ℤ) : ‖(-1 : ℂ) ^ n‖ = 1 := by
  rw [norm_zpow, norm_neg, norm_one, one_zpow]

theorem small_arg {w : ℂ} (hw : ‖w‖ ≤ 4 * dd L) : ‖(L : ℂ) * w / 2‖ ≤ 1 / 2 := by
  have hL : 0 < L := Fact.out
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  have : L * ‖w‖ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hw hL.le
    unfold dd at h
    have : L * (4 * (1 / (4 * L))) = 1 := by field_simp
    linarith
  norm_num; linarith

/-- Pointwise algebra: closeness of the trace gives closeness of `f_n` and the other sign. -/
theorem pointwise {D : ℂ} {n : ℤ} {w : ℂ} (hw : ‖w‖ ≤ 4 * dd L)
    (hD : ‖D - 2 * (-1 : ℂ) ^ n * Complex.cos (L * w / 2)‖ < ε₀) :
    ‖(D ^ 2 - 4) - freeF L w‖ ≤ 6 * ε₀ ∧ 1 ≤ ‖D + 2 * (-1 : ℂ) ^ n‖ := by
  set c := 2 * (-1 : ℂ) ^ n * Complex.cos (L * w / 2) with hc
  have hcl := cos_close (small_arg hw)
  have hcos : ‖Complex.cos (L * w / 2)‖ ≤ 5 / 4 := by
    have := norm_le_insert' (Complex.cos (L * w / 2)) 1
    simp only [norm_one] at this; linarith
  have hcn : ‖c‖ ≤ 5 / 2 := by
    rw [hc, norm_mul, norm_mul, norm_sign]; norm_num; linarith
  have he0 : ε₀ ≤ 1 := by unfold ε₀; norm_num
  constructor
  · have hf : (D ^ 2 - 4) - freeF L w = (D - c) * (D + c) := by
      unfold freeF; rw [hc]
      have := sign_sq n
      linear_combination ((4 : ℂ) * Complex.cos (L * w / 2) ^ 2) * this
    rw [hf, norm_mul]
    have h1 : ‖D + c‖ ≤ 6 := by
      have : D + c = (D - c) + 2 * c := by ring
      rw [this]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]; norm_num; linarith
    nlinarith [norm_nonneg (D - c), norm_nonneg (D + c)]
  · have hcos1 : 7 / 4 ≤ ‖Complex.cos (L * w / 2) + 1‖ := by
      have : (2 : ℂ) = (Complex.cos (L * w / 2) + 1) - (Complex.cos (L * w / 2) - 1) := by ring
      have h2 := norm_sub_le (Complex.cos (L * w / 2) + 1) (Complex.cos (L * w / 2) - 1)
      rw [← this] at h2; norm_num at h2; linarith
    have hsum : D + 2 * (-1 : ℂ) ^ n = (D - c) + 2 * (-1 : ℂ) ^ n * (Complex.cos (L * w / 2) + 1) := by
      rw [hc]; ring
    have hb : ‖2 * (-1 : ℂ) ^ n * (Complex.cos (L * w / 2) + 1)‖ = 2 * ‖Complex.cos (L * w / 2) + 1‖ := by
      rw [norm_mul, norm_mul, norm_sign]; norm_num
    have hY : 2 * (-1 : ℂ) ^ n * (Complex.cos (L * w / 2) + 1) = (D + 2 * (-1 : ℂ) ^ n) - (D - c) := by
      rw [hsum]; ring
    have h3 := norm_sub_le (D + 2 * (-1 : ℂ) ^ n) (D - c)
    rw [← hY, hb] at h3
    linarith

theorem free_band {n : ℤ} {s : ℝ} (hs : s = 1 ∨ s = -1) :
    ‖2 * (-1 : ℂ) ^ n * Complex.cos (L * ((s * dd L : ℝ) : ℂ) / 2)‖ ≤ 2 - 1 / 128 := by
  have hL : 0 < L := Fact.out
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
  have he : (L : ℂ) * ((s * dd L : ℝ) : ℂ) / 2 = ((s / 8 : ℝ) : ℂ) := by
    unfold dd; push_cast; field_simp; ring
  rw [he, ← Complex.ofReal_cos, norm_mul, norm_mul, norm_sign, Complex.norm_real, Real.norm_eq_abs]
  have hx : |s / 8| ≤ 1 := by rcases hs with rfl | rfl <;> norm_num [abs_div]
  have hb := Real.cos_bound hx
  have hsq : (s / 8) ^ 2 = 1 / 64 := by rcases hs with rfl | rfl <;> norm_num
  have h4 : |s / 8| ^ 4 = 1 / 4096 := by rcases hs with rfl | rfl <;> norm_num [abs_div]
  rw [hsq] at hb; rw [h4] at hb
  have hpos : 0 ≤ Real.cos (s / 8) := by
    have := (abs_le.mp hb).1; linarith
  rw [abs_of_nonneg hpos]
  have := (abs_le.mp hb).2
  norm_num; linarith

/-- **Uniform root-count preparation** at the fixed radius `d = 1/(4L)` and accuracy `ε₀`. -/
theorem root_prep (κ : ℝ) (u₀ : PhysicalTensor.L2T L) :
    ∃ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| → ∀ u : PhysicalTensor.L2T L, ‖u - u₀‖ < ρ →
      ∀ t ∈ Icc (0 : ℝ) 1,
        (∀ w : ℂ, ‖w‖ ≤ 4 * dd L → ‖fn κ (t • u) n w - freeF L w‖ ≤ 6 * ε₀) ∧
        (∀ w : ℂ, dd L / 8 ≤ ‖w‖ → ‖w‖ ≤ 4 * dd L → 10 / 65536 ≤ ‖fn κ (t • u) n w‖) ∧
        (∀ w : ℂ, ‖w‖ ≤ 4 * dd L →
          1 ≤ ‖L2SpatialTransfer.discriminant κ (t • u) ((QuantumNLS.LocalSpectral.pm L n : ℂ) + w) +
            2 * (-1 : ℂ) ^ n‖) ∧
        ‖L2SpatialTransfer.discriminant κ (t • u)
            ((QuantumNLS.LocalSpectral.pm L n : ℂ) + ((dd L : ℝ) : ℂ))‖ < 2 ∧
        ‖L2SpatialTransfer.discriminant κ (t • u)
            ((QuantumNLS.LocalSpectral.pm L n : ℂ) + ((-dd L : ℝ) : ℂ))‖ < 2 ∧
        (∀ w : ℂ, ‖w‖ ≤ 3 * dd L →
          ‖iteratedDeriv 2 (fun ξ => fn κ (t • u) n ξ - freeF L ξ) w‖ ≤ 2 * (6 * ε₀) / dd L ^ 2) := by
  have hL : 0 < L := Fact.out
  have hd := dd_pos (L := L)
  have hε : (0 : ℝ) < ε₀ := by unfold ε₀; norm_num
  obtain ⟨N, ρ, hρ, h⟩ := uniform_trace_nbhd κ u₀ (R := 4 * dd L) (by positivity) hε
  refine ⟨N, ρ, hρ, fun n hn u hu t ht => ?_⟩
  have hp := fun w (hw : ‖w‖ ≤ 4 * dd L) => pointwise hw (h n hn u hu t ht w hw)
  have ha : ∀ w : ℂ, ‖w‖ ≤ 4 * dd L → ‖fn κ (t • u) n w - freeF L w‖ ≤ 6 * ε₀ :=
    fun w hw => (hp w hw).1
  refine ⟨ha, ?_, fun w hw => (hp w hw).2, ?_, ?_, ?_⟩
  · intro w hw1 hw2
    have hw3 : ‖w‖ ≤ 1 / L := by
      have : 4 * dd L = 1 / L := by unfold dd; field_simp
      linarith
    have hlow := freeF_lower hw3
    have hLw : 1 / 32 ≤ L * ‖w‖ := by
      have := mul_le_mul_of_nonneg_left hw1 hL.le
      have he : L * (dd L / 8) = 1 / 32 := by unfold dd; field_simp; ring
      linarith
    have hlow2 : 1 / 4096 ≤ ‖freeF L w‖ := by nlinarith
    have hs := norm_sub_le_norm_sub_add_norm_sub (freeF L w) (fn κ (t • u) n w) 0
    simp only [sub_zero] at hs
    rw [norm_sub_rev] at hs
    have := ha w hw2
    unfold ε₀ at this
    linarith
  · have hw : ‖((dd L : ℝ) : ℂ)‖ ≤ 4 * dd L := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]; linarith
    have h1 := h n hn u hu t ht _ hw
    have h2 := free_band (L := L) (n := n) (s := 1) (Or.inl rfl)
    simp only [one_mul] at h2
    have h3 := norm_le_insert' (L2SpatialTransfer.discriminant κ (t • u)
      ((QuantumNLS.LocalSpectral.pm L n : ℂ) + ((dd L : ℝ) : ℂ)))
      (2 * (-1 : ℂ) ^ n * Complex.cos (L * ((dd L : ℝ) : ℂ) / 2))
    unfold ε₀ at h1
    linarith
  · have hw : ‖((-dd L : ℝ) : ℂ)‖ ≤ 4 * dd L := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hd]; linarith
    have h1 := h n hn u hu t ht _ hw
    have h2 := free_band (L := L) (n := n) (s := -1) (Or.inr rfl)
    simp only [neg_one_mul] at h2
    have h3 := norm_le_insert' (L2SpatialTransfer.discriminant κ (t • u)
      ((QuantumNLS.LocalSpectral.pm L n : ℂ) + ((-dd L : ℝ) : ℂ)))
      (2 * (-1 : ℂ) ^ n * Complex.cos (L * ((-dd L : ℝ) : ℂ) / 2))
    unfold ε₀ at h1
    linarith
  · intro w hw
    have hdiff : Differentiable ℂ (fun ξ => fn κ (t • u) n ξ - freeF L ξ) := by
      have hD := PhysicalUpperTraceIdentity.entire_discriminant (L := L) κ (t • u)
      unfold fn freeF
      fun_prop
    have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := w) (R := dd L)
      (C := 6 * ε₀) 2 hd hdiff.diffContOnCl (fun ξ hξ => ha ξ (by
        rw [mem_sphere, dist_eq_norm] at hξ
        have := norm_le_insert' ξ w
        have h2 := norm_sub_le ξ (ξ - w)
        simp only [sub_sub_cancel] at h2
        linarith))
    simpa using hc

end QuantumNLS.RB01RootPrep

#print axioms QuantumNLS.RB01RootPrep.uniform_trace_nbhd
#print axioms QuantumNLS.RB01RootPrep.sin_lower
#print axioms QuantumNLS.RB01RootPrep.cos_close
#print axioms QuantumNLS.RB01RootPrep.freeF_eq
#print axioms QuantumNLS.RB01RootPrep.freeF_lower
#print axioms QuantumNLS.RB01RootPrep.pointwise
#print axioms QuantumNLS.RB01RootPrep.free_band
#print axioms QuantumNLS.RB01RootPrep.root_prep
