import Mathlib

/-!
# Second-order finite transfer product (R-509F3C0C, `stat:lem:product-correction`)

Source: `source/chapters/intrinsic/plane_foundations.tex`, Lemma
`stat:lem:product-correction` (R-509F3C0C), with the scalar notation
`eq:D-scalar-notation` (`f_z(u) = e^{iκu} + e^{izL} e^{-iκu}`) and the exact
two-product transfer expression of `eq:root-quantum-input`
(`source/chapters/foundations/ROOT_spectral_measure.tex`):
`S_N(z) = ∏_j (1 + iκ/(N(z - q_j))) + e^{izL} ∏_j (1 - iκ/(N(z - q_j)))`.

Statement formalized: for an arbitrary real root tuple `q`, with
`G_N(z) = N⁻¹ ∑_j (z - q_j)⁻¹`, at coupling `κ/N`,
`S_N(z) = f_z(G_N(z)) - (κ²/(2N)) f_z(G_N(z)) G_N'(z) + O_K(N⁻²)`,
uniformly over all real tuples and all `z` in a fixed compact `K` of the
upper half-plane. `O_K(N⁻²)` is stated literally: there are `C` and `N₀`
such that for all `N ≥ N₀`, all `q : Fin N → ℝ` and all `z ∈ K`, the
remainder has norm at most `C / N²`. `G_N'` is the actual complex
derivative `deriv (cauchyG N q)`.

Proof (as printed): principal-logarithm expansion
`∑ log(1 ± t_j) = ± iκ G_N - (κ²/(2N)) G_N' + R`, `|R| ≤ |κ|³/(N² η³)`,
from `|t_j| ≤ |κ|/(N η)`, `η = min_K Im z`; the deterministic bounds
`|G_N| ≤ η⁻¹`, `|G_N'| ≤ η⁻²`; exponentiation; and boundedness of `e^{izL}`
on `K`.
-/

set_option autoImplicit false

namespace QuantumNLS.TransferProductCorrection

open Complex Finset

noncomputable section

/-- `G_N(z) = N⁻¹ ∑_j (z - q_j)⁻¹` for a real root tuple `q`. -/
def cauchyG (N : ℕ) (q : Fin N → ℝ) (z : ℂ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ j, (z - (q j : ℂ))⁻¹

/-- `f_z(u) = e^{iκu} + e^{izL} e^{-iκu}` (`eq:D-scalar-notation`). -/
def fz (κ L : ℝ) (z u : ℂ) : ℂ :=
  exp (I * κ * u) + exp (I * z * L) * exp (-(I * κ * u))

/-- The exact two-product transfer expression at coupling `c`
(`eq:root-quantum-input`, `s_q(z)` of `periodic_basis.tex`):
`∏_j (1 + ic/(z - q_j)) + e^{izL} ∏_j (1 - ic/(z - q_j))`. -/
def transferS (c L : ℝ) {N : ℕ} (q : Fin N → ℝ) (z : ℂ) : ℂ :=
  (∏ j, (1 + I * c / (z - (q j : ℂ)))) +
    exp (I * z * L) * ∏ j, (1 - I * c / (z - (q j : ℂ)))

/-- At coupling `κ/N` the transfer expression is literally
`∏_j (1 + iκ/(N(z - q_j))) + e^{izL} ∏_j (1 - iκ/(N(z - q_j)))`. -/
theorem transferS_coupling (κ L : ℝ) (N : ℕ) (q : Fin N → ℝ) (z : ℂ) :
    transferS (κ / N) L q z =
      (∏ j, (1 + I * κ / (N * (z - (q j : ℂ))))) +
        exp (I * z * L) * ∏ j, (1 - I * κ / (N * (z - (q j : ℂ)))) := by
  unfold transferS
  simp only [Complex.ofReal_div, Complex.ofReal_natCast, ← mul_div_assoc, div_div]

/-! ### Elementary estimates -/

lemma sub_ofReal_ne_zero {z : ℂ} (hz : 0 < z.im) (r : ℝ) : z - (r : ℂ) ≠ 0 := by
  intro h
  have : (z - (r : ℂ)).im = 0 := by rw [h]; simp
  simp at this
  linarith

lemma im_le_norm_sub_ofReal (z : ℂ) (r : ℝ) : z.im ≤ ‖z - (r : ℂ)‖ := by
  have h := Complex.abs_im_le_norm (z - (r : ℂ))
  have him : (z - (r : ℂ)).im = z.im := by simp
  rw [him] at h
  exact (le_abs_self _).trans h

/-- Derivative of `G_N`: `G_N'(z) = -N⁻¹ ∑_j (z - q_j)⁻²`. -/
theorem hasDerivAt_cauchyG {N : ℕ} (q : Fin N → ℝ) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (cauchyG N q) (-(N : ℂ)⁻¹ * ∑ j, ((z - (q j : ℂ)) ^ 2)⁻¹) z := by
  have hs : HasDerivAt (fun w : ℂ => ∑ j, (w - (q j : ℂ))⁻¹)
      (∑ j, -(1 : ℂ) / (z - (q j : ℂ)) ^ 2) z := by
    have := HasDerivAt.sum (u := Finset.univ)
      (A := fun j (w : ℂ) => (w - (q j : ℂ))⁻¹) (x := z)
      (fun j _ => ((hasDerivAt_id z).sub_const (q j : ℂ)).inv
        (sub_ofReal_ne_zero hz (q j)))
    convert this using 1
    · ext w; simp
    · simp
  have := hs.const_mul ((N : ℂ)⁻¹)
  unfold cauchyG
  convert this using 1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem deriv_cauchyG {N : ℕ} (q : Fin N → ℝ) {z : ℂ} (hz : 0 < z.im) :
    deriv (cauchyG N q) z = -(N : ℂ)⁻¹ * ∑ j, ((z - (q j : ℂ)) ^ 2)⁻¹ :=
  (hasDerivAt_cauchyG q hz).deriv

/-- Cubic remainder of the principal logarithm on `‖t‖ ≤ 1/2`. -/
lemma norm_log_one_add_sub_le {t : ℂ} (ht : ‖t‖ ≤ 1 / 2) :
    ‖log (1 + t) - (t - t ^ 2 / 2)‖ ≤ ‖t‖ ^ 3 := by
  have h1 : ‖t‖ < 1 := by linarith
  have h := Complex.norm_log_sub_logTaylor_le 2 h1
  have hT : Complex.logTaylor (2 + 1) t = t - t ^ 2 / 2 := by
    simp [Complex.logTaylor, Finset.sum_range_succ]; ring
  rw [hT] at h
  refine h.trans ?_
  have hpos : 0 < 1 - ‖t‖ := by linarith
  have hinv : (1 - ‖t‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hpos (by norm_num)]; linarith
  have h3 : 0 ≤ ‖t‖ ^ 3 := by positivity
  have := mul_le_mul_of_nonneg_left hinv h3
  push_cast
  linarith

/-- Product as exponential of the quadratic logarithm expansion. -/
lemma prod_one_add_eq_exp {N : ℕ} (t : Fin N → ℂ) {ε : ℝ} (hε : ε ≤ 1 / 2)
    (ht : ∀ j, ‖t j‖ ≤ ε) :
    ∃ R : ℂ, ∏ j, (1 + t j) = exp ((∑ j, t j) - (∑ j, t j ^ 2) / 2 + R) ∧
      ‖R‖ ≤ N * ε ^ 3 := by
  refine ⟨∑ j, (log (1 + t j) - (t j - t j ^ 2 / 2)), ?_, ?_⟩
  · have hsum : (∑ j, t j) - (∑ j, t j ^ 2) / 2 +
        ∑ j, (log (1 + t j) - (t j - t j ^ 2 / 2)) = ∑ j, log (1 + t j) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_div]; ring
    rw [hsum, Complex.exp_sum]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    have h1 : 1 + t j ≠ 0 := by
      intro h0
      have : t j = -1 := by linear_combination h0
      have h2 := ht j
      rw [this, norm_neg, norm_one] at h2
      linarith
    rw [Complex.exp_log h1]
  · calc ‖∑ j, (log (1 + t j) - (t j - t j ^ 2 / 2))‖
        ≤ ∑ j, ‖log (1 + t j) - (t j - t j ^ 2 / 2)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin N, ε ^ 3 := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        refine (norm_log_one_add_sub_le ((ht j).trans hε)).trans ?_
        exact pow_le_pow_left₀ (norm_nonneg _) (ht j) 3
      _ = N * ε ^ 3 := by simp

lemma norm_exp_add_sub_le (a R : ℂ) (h : ‖a + R‖ ≤ 1) :
    ‖exp (a + R) - (1 + a)‖ ≤ ‖a + R‖ ^ 2 + ‖R‖ := by
  have h1 := Complex.norm_exp_sub_one_sub_id_le h
  calc ‖exp (a + R) - (1 + a)‖ = ‖(exp (a + R) - 1 - (a + R)) + R‖ := by
        congr 1; ring
    _ ≤ ‖exp (a + R) - 1 - (a + R)‖ + ‖R‖ := norm_add_le _ _
    _ ≤ ‖a + R‖ ^ 2 + ‖R‖ := by linarith


/-! ### The quantitative pointwise estimate -/

/-- Quantitative pointwise form of `eq:D-product-correction`: with
`x = |κ|/η`, `D = x²/2 + x³`, for `η ≤ Im z`, `‖e^{izL}‖ ≤ M` and
`N ≥ 2x + D + 1`, every real tuple `q` satisfies
`‖S_N(z) - f_z(G_N) + (κ²/(2N)) f_z(G_N) G_N'‖ ≤ e^x (1 + M)(D² + x³)/N²`. -/
theorem pointwise_bound (κ L : ℝ) {η M : ℝ} (hη : 0 < η) (hM : 0 ≤ M) {N : ℕ}
    (hN : 2 * (|κ| / η) + ((|κ| / η) ^ 2 / 2 + (|κ| / η) ^ 3) + 1 ≤ (N : ℝ))
    (q : Fin N → ℝ) {z : ℂ} (hz : η ≤ z.im) (hzM : ‖exp (I * z * L)‖ ≤ M) :
    ‖transferS (κ / N) L q z -
        (fz κ L z (cauchyG N q z) -
          (κ ^ 2 / (2 * N)) * fz κ L z (cauchyG N q z) * deriv (cauchyG N q) z)‖ ≤
      Real.exp (|κ| / η) * (1 + M) *
        (((|κ| / η) ^ 2 / 2 + (|κ| / η) ^ 3) ^ 2 + (|κ| / η) ^ 3) / (N : ℝ) ^ 2 := by
  set x : ℝ := |κ| / η with hxdef
  set D : ℝ := x ^ 2 / 2 + x ^ 3 with hD
  have hx : 0 ≤ x := by positivity
  have hD0 : 0 ≤ D := by positivity
  have hz0 : 0 < z.im := hη.trans_le hz
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hw : ∀ j, η ≤ ‖z - (q j : ℂ)‖ := fun j => hz.trans (im_le_norm_sub_ofReal z (q j))
  have hinv : ∀ j, ‖(z - (q j : ℂ))⁻¹‖ ≤ η⁻¹ := fun j => by
    rw [norm_inv]; exact inv_anti₀ hη (hw j)
  have hinv2 : ∀ j, ‖((z - (q j : ℂ)) ^ 2)⁻¹‖ ≤ η⁻¹ ^ 2 := fun j => by
    rw [norm_inv, norm_pow, ← inv_pow]
    exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hη (hw j)) 2
  have hNinv : ‖(N : ℂ)⁻¹‖ = (N : ℝ)⁻¹ := by simp
  set G : ℂ := cauchyG N q z with hG
  set S2 : ℂ := ∑ j, ((z - (q j : ℂ)) ^ 2)⁻¹ with hS2
  have hderiv : deriv (cauchyG N q) z = -(N : ℂ)⁻¹ * S2 := deriv_cauchyG q hz0
  have hGb : ‖G‖ ≤ η⁻¹ := by
    calc ‖G‖ ≤ ‖(N : ℂ)⁻¹‖ * ∑ j, ‖(z - (q j : ℂ))⁻¹‖ := by
          rw [hG, cauchyG, norm_mul]; gcongr; exact norm_sum_le _ _
      _ ≤ (N : ℝ)⁻¹ * ∑ _j : Fin N, η⁻¹ := by
          rw [hNinv]; gcongr with j; exact hinv j
      _ = η⁻¹ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have hS2b : ‖(N : ℂ)⁻¹ * S2‖ ≤ η⁻¹ ^ 2 := by
    calc ‖(N : ℂ)⁻¹ * S2‖ ≤ ‖(N : ℂ)⁻¹‖ * ∑ j, ‖((z - (q j : ℂ)) ^ 2)⁻¹‖ := by
          rw [norm_mul]; gcongr; exact norm_sum_le _ _
      _ ≤ (N : ℝ)⁻¹ * ∑ _j : Fin N, η⁻¹ ^ 2 := by
          rw [hNinv]; gcongr with j; exact hinv2 j
      _ = η⁻¹ ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  -- the individual logarithm arguments
  set t : Fin N → ℂ := fun j => I * ((κ / N : ℝ) : ℂ) / (z - (q j : ℂ)) with ht_def
  have htb : ∀ j, ‖t j‖ ≤ x / N := fun j => by
    simp only [ht_def]
    rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_div, Nat.abs_cast]
    calc |κ| / N / ‖z - (q j : ℂ)‖ ≤ |κ| / N / η :=
          div_le_div_of_nonneg_left (by positivity) hη (hw j)
      _ = x / N := by rw [hxdef]; ring
  have hε : x / N ≤ 1 / 2 := by
    rw [div_le_iff₀ hNpos]; linarith
  have hs1 : ∑ j, t j = I * κ * G := by
    simp only [ht_def, hG, cauchyG, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    push_cast; ring
  set a : ℂ := -((κ : ℂ) ^ 2 / (2 * N)) * (-(N : ℂ)⁻¹ * S2) with ha
  have hs2 : (∑ j, t j ^ 2) / 2 = -a := by
    have hT2 : ∑ j, t j ^ 2 = -((κ : ℂ) ^ 2 * ((N : ℂ)⁻¹) ^ 2) * S2 := by
      simp only [ht_def, hS2, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      push_cast
      rw [div_pow, mul_pow, I_sq]
      ring
    rw [hT2, ha]
    ring
  obtain ⟨Rp, hPp, hRp⟩ := prod_one_add_eq_exp t hε htb
  obtain ⟨Rm, hPm, hRm⟩ := prod_one_add_eq_exp (fun j => -t j) hε
    (fun j => by rw [norm_neg]; exact htb j)
  have hPp' : ∏ j, (1 + t j) = exp (I * κ * G) * exp (a + Rp) := by
    rw [hPp, ← Complex.exp_add]
    congr 1
    rw [hs1, hs2]; ring
  have hPm' : ∏ j, (1 + -t j) = exp (-(I * κ * G)) * exp (a + Rm) := by
    rw [hPm, ← Complex.exp_add]
    congr 1
    simp only [Finset.sum_neg_distrib, neg_sq]
    rw [hs1, hs2]; ring
  have hm : ∀ j, (1 - I * ((κ / N : ℝ) : ℂ) / (z - (q j : ℂ))) = 1 + -t j := fun j => by
    simp only [ht_def]; ring
  have hS : transferS (κ / N) L q z =
      (∏ j, (1 + t j)) + exp (I * z * L) * ∏ j, (1 + -t j) := by
    rw [transferS]
    simp only [hm]
    rfl
  have hid : transferS (κ / N) L q z -
        (fz κ L z G - (κ ^ 2 / (2 * N)) * fz κ L z G * deriv (cauchyG N q) z) =
      exp (I * κ * G) * (exp (a + Rp) - (1 + a)) +
        exp (I * z * L) * exp (-(I * κ * G)) * (exp (a + Rm) - (1 + a)) := by
    rw [hS, hPp', hPm', hderiv, ha]
    simp only [fz]
    ring
  -- norm bounds
  have hIκG : ‖I * κ * G‖ ≤ x := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |κ| * ‖G‖ ≤ |κ| * η⁻¹ := mul_le_mul_of_nonneg_left hGb (abs_nonneg _)
      _ = x := by rw [hxdef, div_eq_mul_inv]
  have hEp : ‖exp (I * κ * G)‖ ≤ Real.exp x :=
    (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr hIκG)
  have hEm : ‖exp (-(I * κ * G))‖ ≤ Real.exp x :=
    (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (by rw [norm_neg]; exact hIκG))
  have hab : ‖a‖ ≤ x ^ 2 / (2 * N) := by
    have h1 : ‖-((κ : ℂ) ^ 2 / (2 * N))‖ = κ ^ 2 / (2 * N) := by
      rw [norm_neg, norm_div, norm_pow, norm_mul, Complex.norm_real, Complex.norm_natCast,
        Real.norm_eq_abs, sq_abs]
      norm_num
    have h2 : ‖-(N : ℂ)⁻¹ * S2‖ ≤ η⁻¹ ^ 2 := by rw [neg_mul, norm_neg]; exact hS2b
    calc ‖a‖ = κ ^ 2 / (2 * N) * ‖-(N : ℂ)⁻¹ * S2‖ := by rw [ha, norm_mul, h1]
      _ ≤ κ ^ 2 / (2 * N) * η⁻¹ ^ 2 := by gcongr
      _ = x ^ 2 / (2 * N) := by rw [hxdef, div_pow, sq_abs]; field_simp
  have hRb : ∀ R : ℂ, ‖R‖ ≤ N * (x / N) ^ 3 → ‖R‖ ≤ x ^ 3 / (N : ℝ) ^ 2 := by
    intro R hR
    refine hR.trans (le_of_eq ?_)
    field_simp
  have hx3 : x ^ 3 / (N : ℝ) ^ 2 ≤ x ^ 3 / N :=
    div_le_div_of_nonneg_left (by positivity) hNpos (by nlinarith)
  have hDN : D / N ≤ 1 := by rw [div_le_one hNpos]; linarith
  have hsign : ∀ R : ℂ, ‖R‖ ≤ N * (x / N) ^ 3 →
      ‖exp (a + R) - (1 + a)‖ ≤ (D ^ 2 + x ^ 3) / (N : ℝ) ^ 2 := by
    intro R hR
    have hR' := hRb R hR
    have haR : ‖a + R‖ ≤ D / N := by
      calc ‖a + R‖ ≤ ‖a‖ + ‖R‖ := norm_add_le _ _
        _ ≤ x ^ 2 / (2 * N) + x ^ 3 / N := by linarith
        _ = D / N := by rw [hD]; field_simp
    have haR2 : ‖a + R‖ ^ 2 ≤ (D / N) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) haR 2
    calc ‖exp (a + R) - (1 + a)‖ ≤ ‖a + R‖ ^ 2 + ‖R‖ :=
          norm_exp_add_sub_le a R (haR.trans hDN)
      _ ≤ (D / N) ^ 2 + x ^ 3 / (N : ℝ) ^ 2 := by linarith
      _ = (D ^ 2 + x ^ 3) / (N : ℝ) ^ 2 := by field_simp
  have hp := hsign Rp hRp
  have hmb := hsign Rm hRm
  have hB : 0 ≤ (D ^ 2 + x ^ 3) / (N : ℝ) ^ 2 := by positivity
  rw [hid]
  calc ‖exp (I * κ * G) * (exp (a + Rp) - (1 + a)) +
        exp (I * z * L) * exp (-(I * κ * G)) * (exp (a + Rm) - (1 + a))‖
      ≤ ‖exp (I * κ * G)‖ * ‖exp (a + Rp) - (1 + a)‖ +
        ‖exp (I * z * L)‖ * ‖exp (-(I * κ * G))‖ * ‖exp (a + Rm) - (1 + a)‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, norm_mul, norm_mul]
    _ ≤ Real.exp x * ((D ^ 2 + x ^ 3) / (N : ℝ) ^ 2) +
        M * Real.exp x * ((D ^ 2 + x ^ 3) / (N : ℝ) ^ 2) := by
        gcongr
    _ = Real.exp x * (1 + M) * (D ^ 2 + x ^ 3) / (N : ℝ) ^ 2 := by ring

/-! ### The lemma `stat:lem:product-correction` -/

/-- **R-509F3C0C** (`stat:lem:product-correction`). For every compact `K` in the
open upper half-plane and every `κ, L`, there are `C` and `N₀` such that for all
`N ≥ N₀`, every real root tuple `q : Fin N → ℝ` and every `z ∈ K`,
`‖S_N(z) - (f_z(G_N(z)) - (κ²/(2N)) f_z(G_N(z)) G_N'(z))‖ ≤ C / N²`,
where `S_N` is the exact two-product transfer expression at coupling `κ/N`. -/
theorem product_correction (κ L : ℝ) {K : Set ℂ} (hK : IsCompact K)
    (hKup : ∀ z ∈ K, 0 < z.im) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q : Fin N → ℝ, ∀ z ∈ K,
      ‖transferS (κ / N) L q z -
          (fz κ L z (cauchyG N q z) -
            (κ ^ 2 / (2 * N)) * fz κ L z (cauchyG N q z) * deriv (cauchyG N q) z)‖ ≤
        C / (N : ℝ) ^ 2 := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, 0, fun N _ q z hz => absurd hz (Set.notMem_empty z)⟩
  obtain ⟨z₀, hz₀K, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (f := fun z : ℂ => exp (I * z * L)) (by fun_prop)
  have hη : 0 < z₀.im := hKup z₀ hz₀K
  refine ⟨Real.exp (|κ| / z₀.im) * (1 + max M 0) *
      (((|κ| / z₀.im) ^ 2 / 2 + (|κ| / z₀.im) ^ 3) ^ 2 + (|κ| / z₀.im) ^ 3),
    ⌈2 * (|κ| / z₀.im) + ((|κ| / z₀.im) ^ 2 / 2 + (|κ| / z₀.im) ^ 3)⌉₊ + 1, ?_⟩
  intro N hN q z hz
  have hN' : 2 * (|κ| / z₀.im) + ((|κ| / z₀.im) ^ 2 / 2 + (|κ| / z₀.im) ^ 3) + 1 ≤ (N : ℝ) := by
    have h1 := Nat.le_ceil (2 * (|κ| / z₀.im) + ((|κ| / z₀.im) ^ 2 / 2 + (|κ| / z₀.im) ^ 3))
    have h2 : ((⌈2 * (|κ| / z₀.im) + ((|κ| / z₀.im) ^ 2 / 2 + (|κ| / z₀.im) ^ 3)⌉₊ + 1 : ℕ) : ℝ)
        ≤ N := by exact_mod_cast hN
    push_cast at h2
    linarith
  exact pointwise_bound κ L hη (le_max_right _ _) hN' q (hmin hz)
    ((hM z hz).trans (le_max_left _ _))

/-- The same statement with the literal source products
`∏_j (1 ± iκ/(N(z - q_j)))` and the explicit derivative
`G_N'(z) = -N⁻¹ ∑_j (z - q_j)⁻²` (`eq:D-product-correction`). -/
theorem product_correction_literal (κ L : ℝ) {K : Set ℂ} (hK : IsCompact K)
    (hKup : ∀ z ∈ K, 0 < z.im) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ q : Fin N → ℝ, ∀ z ∈ K,
      ‖((∏ j, (1 + I * κ / (N * (z - (q j : ℂ))))) +
            exp (I * z * L) * ∏ j, (1 - I * κ / (N * (z - (q j : ℂ))))) -
          ((exp (I * κ * cauchyG N q z) +
              exp (I * z * L) * exp (-(I * κ * cauchyG N q z))) -
            (κ ^ 2 / (2 * N)) *
              (exp (I * κ * cauchyG N q z) +
                exp (I * z * L) * exp (-(I * κ * cauchyG N q z))) *
              (-(N : ℂ)⁻¹ * ∑ j, ((z - (q j : ℂ)) ^ 2)⁻¹))‖ ≤
        C / (N : ℝ) ^ 2 := by
  obtain ⟨C, N₀, h⟩ := product_correction κ L hK hKup
  refine ⟨C, N₀, fun N hN q z hz => ?_⟩
  have := h N hN q z hz
  rw [transferS_coupling, deriv_cauchyG q (hKup z hz)] at this
  simpa only [fz] using this

end

end QuantumNLS.TransferProductCorrection

#print axioms QuantumNLS.TransferProductCorrection.cauchyG
#print axioms QuantumNLS.TransferProductCorrection.fz
#print axioms QuantumNLS.TransferProductCorrection.transferS
#print axioms QuantumNLS.TransferProductCorrection.transferS_coupling
#print axioms QuantumNLS.TransferProductCorrection.sub_ofReal_ne_zero
#print axioms QuantumNLS.TransferProductCorrection.im_le_norm_sub_ofReal
#print axioms QuantumNLS.TransferProductCorrection.hasDerivAt_cauchyG
#print axioms QuantumNLS.TransferProductCorrection.deriv_cauchyG
#print axioms QuantumNLS.TransferProductCorrection.norm_log_one_add_sub_le
#print axioms QuantumNLS.TransferProductCorrection.prod_one_add_eq_exp
#print axioms QuantumNLS.TransferProductCorrection.norm_exp_add_sub_le
#print axioms QuantumNLS.TransferProductCorrection.pointwise_bound
#print axioms QuantumNLS.TransferProductCorrection.product_correction
#print axioms QuantumNLS.TransferProductCorrection.product_correction_literal
