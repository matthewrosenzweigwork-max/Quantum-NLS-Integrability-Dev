import NlsGge.Hierarchy.ALLaurent38
import Mathlib.Tactic

/-! Batch 38, E07-5b (`D:eq:Cquadratic`, paper/v2.tex l.1984-1993).
For an admissible `α` and real `t → 0`:
`alC38 (t•α) k = t² Σ_j α_j conj(α_{j-k}) + O(t⁴)` for every `k ≥ 1` (cyclic, all `k`) and
`alMass38 (t•α) = t² Σ_j |α_j|² + O(t⁴)`.
Route: exact Floquet product `g(ζ) = e^{M_d/2} ∏_k (1 + ζ β_k q_k)` from the exterior eigenvector
(`J`-form positivity gives `|q_k| < 1`), a cyclic contraction estimate for `q_k` against the linear
solution `q*_k = Σ_{m≥0} ζ^{2m+1} conj β_{k-m-1}`, logarithm expansion, an open-disk branch argument
and the Cauchy coefficient bound `norm_evenLogCoeff_le38`. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open Metric NlsGge.Analysis Finset

/-! ### Cyclic contraction -/

theorem cyc38 (f : ℕ → ℝ) (L : ℕ) (hL : 0 < L) (a b : ℝ) (ha0 : 0 ≤ a) (ha : a < 1)
    (hfL : f L = f 0) (hstep : ∀ k < L, f (k + 1) ≤ a * f k + b) :
    ∀ k ≤ L, f k ≤ b / (1 - a) := by
  obtain ⟨k0, hk0, hmax⟩ := Finset.exists_max_image (Finset.range L) f ⟨0, by simp [hL]⟩
  have hle : ∀ k ≤ L, f k ≤ f k0 := by
    intro k hk
    rcases Nat.lt_or_ge k L with h | h
    · exact hmax k (by simpa using h)
    · have : k = L := le_antisymm hk h
      subst this; rw [hfL]; exact hmax 0 (by simp [hL])
  have hk0L : k0 < L := by simpa using hk0
  have key : f k0 ≤ a * f k0 + b := by
    rcases Nat.eq_zero_or_pos k0 with h | h
    · have h1 := hstep (L - 1) (by omega)
      have e : L - 1 + 1 = L := by omega
      rw [e, hfL] at h1
      have h2 := hle (L - 1) (by omega)
      subst h
      nlinarith
    · obtain ⟨m, rfl⟩ : ∃ m, k0 = m + 1 := ⟨k0 - 1, by omega⟩
      have h1 := hstep m (by omega)
      have h2 := hle m (by omega)
      nlinarith
  intro k hk
  have : (1 - a) * f k0 ≤ b := by linarith
  rw [le_div_iff₀ (by linarith)]
  nlinarith [hle k hk]

/-! ### The linear solution `q*` -/

theorem summable_geom_mul38 {s : ℝ} {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1 / 2) (b : ℕ → ℂ)
    (hb : ∀ m, ‖b m‖ ≤ s) : Summable (fun m : ℕ => ζ ^ (2 * m + 1) * b m) := by
  have hs : 0 ≤ s := (norm_nonneg _).trans (hb 0)
  refine Summable.of_norm_bounded (g := fun m : ℕ => (s / 2) * (1 / 4 : ℝ) ^ m) ?_ ?_
  · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  · intro m
    rw [norm_mul, norm_pow]
    have h1 : ‖ζ‖ ^ (2 * m + 1) ≤ (1 / 2) * (1 / 4 : ℝ) ^ m := by
      have : ‖ζ‖ ^ (2 * m + 1) = ‖ζ‖ * (‖ζ‖ ^ 2) ^ m := by rw [pow_succ, pow_mul]; ring
      rw [this]
      have h2 : ‖ζ‖ ^ 2 ≤ 1 / 4 := by nlinarith [norm_nonneg ζ]
      exact mul_le_mul hζ (pow_le_pow_left₀ (sq_nonneg _) h2 m) (by positivity) (by norm_num)
    calc ‖ζ‖ ^ (2 * m + 1) * ‖b m‖ ≤ ((1 / 2) * (1 / 4 : ℝ) ^ m) * s :=
          mul_le_mul h1 (hb m) (norm_nonneg _) (by positivity)
      _ = s / 2 * (1 / 4 : ℝ) ^ m := by ring

/-- `q*_k = Σ_{m ≥ 0} ζ^{2m+1} conj β_{k-m-1}` (cyclic index), the solution of the linearised
Floquet recursion `q*_{k+1} = ζ conj β_k + ζ² q*_k`. -/
def alQStar38 {L : ℕ} (β : ZMod L → ℂ) (ζ : ℂ) (k : ℕ) : ℂ :=
  ∑' m : ℕ, ζ ^ (2 * m + 1) * (starRingEnd ℂ) (β ((k : ZMod L) - ((m + 1 : ℕ) : ZMod L)))

theorem alQStar38_succ {L : ℕ} (β : ZMod L → ℂ) {s : ℝ} (hβ : ∀ j, ‖β j‖ ≤ s) {ζ : ℂ}
    (hζ : ‖ζ‖ ≤ 1 / 2) (k : ℕ) :
    alQStar38 β ζ (k + 1) = ζ * (starRingEnd ℂ) (β (k : ZMod L)) + ζ ^ 2 * alQStar38 β ζ k := by
  have hsum : ∀ k : ℕ, Summable (fun m : ℕ => ζ ^ (2 * m + 1) *
      (starRingEnd ℂ) (β ((k : ZMod L) - ((m + 1 : ℕ) : ZMod L)))) := fun k =>
    summable_geom_mul38 hζ _ (fun m => by simpa using hβ _)
  unfold alQStar38
  rw [(hsum (k + 1)).tsum_eq_zero_add]
  congr 1
  · simp
  · rw [← tsum_mul_left]
    refine tsum_congr fun m => ?_
    have e : ((k + 1 : ℕ) : ZMod L) - ((m + 1 + 1 : ℕ) : ZMod L) =
        (k : ZMod L) - ((m + 1 : ℕ) : ZMod L) := by push_cast; ring
    rw [e]; ring

theorem alQStar38_L {L : ℕ} (β : ZMod L → ℂ) (ζ : ℂ) : alQStar38 β ζ L = alQStar38 β ζ 0 := by
  simp [alQStar38]

theorem den_lb38 {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) : 1 / 2 ≤ ‖1 + u‖ := by
  have := norm_sub_norm_le (1 : ℂ) (-u)
  rw [sub_neg_eq_add, norm_neg, norm_one] at this
  linarith

theorem q_bounds38 {L : ℕ} [NeZero L] (β : ZMod L → ℂ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hβ : ∀ j, ‖β j‖ ≤ s) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1 / 2) (q : ℕ → ℂ)
    (hq1 : ∀ k, k ≤ L → ‖q k‖ < 1) (hqL : q L = q 0)
    (hrec : ∀ k, k < L → q (k + 1) * (1 + ζ * β (k : ZMod L) * q k) =
      ζ * ((starRingEnd ℂ) (β (k : ZMod L)) + ζ * q k)) :
    (∀ k ≤ L, ‖q k‖ ≤ 2 * s) ∧ (∀ k ≤ L, ‖q k - alQStar38 β ζ k‖ ≤ 3 * s ^ 3) := by
  have hL : 0 < L := NeZero.pos L
  have hu : ∀ k < L, ‖ζ * β (k : ZMod L) * q k‖ ≤ s * ‖q k‖ / 2 := by
    intro k hk
    rw [norm_mul, norm_mul]
    have := hβ (k : ZMod L)
    calc ‖ζ‖ * ‖β (k : ZMod L)‖ * ‖q k‖ ≤ (1 / 2) * s * ‖q k‖ := by gcongr
      _ = s * ‖q k‖ / 2 := by ring
  have hu2 : ∀ k < L, ‖ζ * β (k : ZMod L) * q k‖ ≤ 1 / 2 := by
    intro k hk
    have := hq1 k hk.le
    have := hu k hk
    nlinarith [norm_nonneg (q k)]
  have step1 : ∀ k < L, ‖q (k + 1)‖ ≤ 1 / 2 * ‖q k‖ + s := by
    intro k hk
    have hd := den_lb38 (hu2 k hk)
    have h := congrArg norm (hrec k hk)
    rw [norm_mul, norm_mul] at h
    have h3 : ‖(starRingEnd ℂ) (β (k : ZMod L)) + ζ * q k‖ ≤ s + 1 / 2 * ‖q k‖ := by
      calc _ ≤ ‖(starRingEnd ℂ) (β (k : ZMod L))‖ + ‖ζ * q k‖ := norm_add_le _ _
        _ ≤ s + 1 / 2 * ‖q k‖ := by
          rw [Complex.norm_conj, norm_mul]
          have := hβ (k : ZMod L)
          gcongr
    have h4 : ‖q (k + 1)‖ * (1 / 2) ≤ 1 / 2 * (s + 1 / 2 * ‖q k‖) := by
      calc ‖q (k + 1)‖ * (1 / 2) ≤ ‖q (k + 1)‖ * ‖1 + ζ * β (k : ZMod L) * q k‖ :=
            mul_le_mul_of_nonneg_left hd (norm_nonneg _)
        _ = ‖ζ‖ * ‖(starRingEnd ℂ) (β (k : ZMod L)) + ζ * q k‖ := h
        _ ≤ 1 / 2 * (s + 1 / 2 * ‖q k‖) := by gcongr
    linarith
  have hb1 : ∀ k ≤ L, ‖q k‖ ≤ 2 * s := by
    have := cyc38 (fun k => ‖q k‖) L hL (1 / 2) s (by norm_num) (by norm_num) (by simp [hqL])
      step1
    intro k hk
    have := this k hk
    linarith [show s / (1 - 1 / 2) = 2 * s by ring]
  refine ⟨hb1, ?_⟩
  have step2 : ∀ k < L, ‖q (k + 1) - alQStar38 β ζ (k + 1)‖ ≤
      1 / 4 * ‖q k - alQStar38 β ζ k‖ + 2 * s ^ 3 := by
    intro k hk
    have hqs := alQStar38_succ β hβ hζ k
    have e : q (k + 1) - alQStar38 β ζ (k + 1) =
        ζ ^ 2 * (q k - alQStar38 β ζ k) - q (k + 1) * (ζ * β (k : ZMod L) * q k) := by
      rw [hqs]; linear_combination hrec k hk
    rw [e]
    have h1 : ‖ζ ^ 2 * (q k - alQStar38 β ζ k)‖ ≤ 1 / 4 * ‖q k - alQStar38 β ζ k‖ := by
      rw [norm_mul, norm_pow]
      have : ‖ζ‖ ^ 2 ≤ 1 / 4 := by nlinarith [norm_nonneg ζ]
      gcongr
    have h2 : ‖q (k + 1) * (ζ * β (k : ZMod L) * q k)‖ ≤ 2 * s ^ 3 := by
      rw [norm_mul]
      have a1 := hb1 (k + 1) (by omega)
      have a2 := hu k hk
      have a3 := hb1 k hk.le
      have : ‖ζ * β (k : ZMod L) * q k‖ ≤ s ^ 2 := by nlinarith
      calc ‖q (k + 1)‖ * ‖ζ * β (k : ZMod L) * q k‖ ≤ (2 * s) * s ^ 2 :=
            mul_le_mul a1 this (norm_nonneg _) (by positivity)
        _ = 2 * s ^ 3 := by ring
    calc _ ≤ ‖ζ ^ 2 * (q k - alQStar38 β ζ k)‖ + ‖q (k + 1) * (ζ * β (k : ZMod L) * q k)‖ :=
          norm_sub_le _ _
      _ ≤ _ := by linarith
  have := cyc38 (fun k => ‖q k - alQStar38 β ζ k‖) L hL (1 / 4) (2 * s ^ 3) (by norm_num)
    (by norm_num) (by simp [hqL, alQStar38_L]) step2
  intro k hk
  have h := this k hk
  have : 2 * s ^ 3 / (1 - 1 / 4) = 8 / 3 * s ^ 3 := by ring
  rw [this] at h
  nlinarith [pow_nonneg hs0 3]

/-! ### The exact Floquet product -/

theorem eigen_q38 {L : ℕ} [NeZero L] {β : ZMod L → ℂ} (hβ : IsALField38 β) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) 1) (h0 : ζ ≠ 0) :
    ∃ q : ℕ → ℂ, (∀ k, k ≤ L → ‖q k‖ < 1) ∧ q L = q 0 ∧
      (∀ k, k < L → q (k + 1) * (1 + ζ * β (k : ZMod L) * q k) =
        ζ * ((starRingEnd ℂ) (β (k : ZMod L)) + ζ * q k)) ∧
      alExteriorG38 β ζ = ((Real.exp (alMass38 L β / 2) : ℝ) : ℂ) *
        ∏ k ∈ range L, (1 + ζ * β (k : ZMod L) * q k) := by
  obtain ⟨⟨v, hv, hMv⟩, -, hw⟩ := alExteriorG38_multiplier hβ hζ h0
  set w : ℂ := (ζ ^ L)⁻¹ * alExteriorG38 β ζ with hwdef
  have hn : ‖ζ‖ < 1 := by simpa using hζ
  have hz1 : 1 < ‖ζ⁻¹‖ := by
    rw [norm_inv]; exact (one_lt_inv₀ (norm_pos_iff.mpr h0)).2 hn
  have hJ : 0 < alJForm38 v := alJForm_pos_of_one_lt_norm38 β hβ ζ⁻¹ hz1 w v hv hMv hw
  have hvk := fun k => alPartial38_ne_zero_ge β hβ ζ⁻¹ hz1 v hv k
  set vk : ℕ → (Fin 2 → ℂ) := fun k => (alPartial38 β ζ⁻¹ k).mulVec v with hvkdef
  have hJk : ∀ k, ‖vk k 1‖ < ‖vk k 0‖ := by
    intro k
    have h1 := (hvk k).2
    have h2 : ‖vk k 1‖ ^ 2 < ‖vk k 0‖ ^ 2 := by
      unfold alJForm38 at h1 hJ; simp only [hvkdef]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h2
  have hp : ∀ k, vk k 0 ≠ 0 := by
    intro k h
    have := hJk k
    rw [h, norm_zero] at this
    exact absurd this (not_lt.mpr (norm_nonneg _))
  have hw0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hw; linarith
  have hvL : vk L = w • v := hMv
  have hv0 : vk 0 = v := by
    show (alPartial38 β ζ⁻¹ 0).mulVec v = v
    simp only [alPartial38]; exact Matrix.one_mulVec v
  have hc : ∀ k : ℕ, (alScale38 β k) ≠ 0 := by
    intro k
    have : 0 < 1 - ‖β (k : ZMod L)‖ ^ 2 := by
      have := hβ (k : ZMod L); nlinarith [norm_nonneg (β (k : ZMod L))]
    unfold alScale38
    exact inv_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr this).ne')
  have hstep0 : ∀ k : ℕ, vk (k + 1) 0 = alScale38 β k * (ζ⁻¹ * vk k 0 + β (k : ZMod L) * vk k 1) := by
    intro k
    simp only [hvkdef]
    rw [alPartial38_mulVec_succ, alTransfer38_mulVec_zero]; rfl
  have hstep1 : ∀ k : ℕ, vk (k + 1) 1 =
      alScale38 β k * ((starRingEnd ℂ) (β (k : ZMod L)) * vk k 0 + ζ * vk k 1) := by
    intro k
    simp only [hvkdef]
    rw [alPartial38_mulVec_succ, alTransfer38_mulVec_one]
    simp [alScale38]
  set q : ℕ → ℂ := fun k => vk k 1 / vk k 0 with hqdef
  have hs : ∀ k, vk k 1 = q k * vk k 0 := fun k => by
    simp only [hqdef]; field_simp [hp k]
  have hpk : ∀ k : ℕ, vk (k + 1) 0 = alScale38 β k * (ζ⁻¹ + β (k : ZMod L) * q k) * vk k 0 := by
    intro k; rw [hstep0, hs k]; ring
  have hden : ∀ k : ℕ, ζ⁻¹ + β (k : ZMod L) * q k ≠ 0 := by
    intro k h
    have := hp (k + 1)
    rw [hpk k, h] at this; simp at this
  refine ⟨q, fun k _ => ?_, ?_, ?_, ?_⟩
  · simp only [hqdef]
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (hp k))]; exact hJk k
  · simp only [hqdef]
    rw [hvL]; simp only [Pi.smul_apply, smul_eq_mul, hv0]
    have : v 0 ≠ 0 := by rw [← hv0]; exact hp 0
    field_simp [hw0, this]
  · intro k _
    have e1 : q (k + 1) = ((starRingEnd ℂ) (β (k : ZMod L)) + ζ * q k) / (ζ⁻¹ + β (k : ZMod L) * q k) := by
      show vk (k + 1) 1 / vk (k + 1) 0 = _
      rw [hstep0, hstep1, hs k]
      have hc' := hc k
      have h2 := hden k
      have h3 := hp k
      have h4 : ζ⁻¹ * vk k 0 + β (k : ZMod L) * (q k * vk k 0) ≠ 0 := by
        have := mul_ne_zero h2 h3
        convert this using 1; ring
      rw [div_eq_div_iff (mul_ne_zero hc' h4) h2]
      ring
    rw [e1]
    have h2 := hden k
    have hzz : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ h0
    rw [div_mul_eq_mul_div, div_eq_iff h2]
    linear_combination (-((starRingEnd ℂ) (β (k : ZMod L)) + ζ * q k)) * hzz
  · have hprod : ∀ k : ℕ, vk k 0 = (∏ i ∈ range k, (alScale38 β i * (ζ⁻¹ + β (i : ZMod L) * q i))) * vk 0 0 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [hpk k, prod_range_succ, ih]; ring
    have hL0 : vk L 0 = w * vk 0 0 := by rw [hvL, hv0]; simp
    have hwprod : w = ∏ i ∈ range L, (alScale38 β i * (ζ⁻¹ + β (i : ZMod L) * q i)) := by
      have := hprod L
      rw [hL0] at this
      exact mul_right_cancel₀ (hp 0) this
    have hg : alExteriorG38 β ζ = ζ ^ L * w := by
      rw [hwdef]; field_simp
    rw [hg, hwprod, prod_mul_distrib, alScale38_prod hβ]
    have : ζ ^ L * (∏ i ∈ range L, (ζ⁻¹ + β (i : ZMod L) * q i)) =
        ∏ i ∈ range L, (1 + ζ * β (i : ZMod L) * q i) := by
      have hpow : ζ ^ L = ∏ _i ∈ range L, ζ := by simp
      rw [hpow, ← prod_mul_distrib]
      refine prod_congr rfl fun i _ => ?_
      field_simp
    rw [← this]; ring

/-! ### The quadratic series -/

/-- `c_k = Σ_j α_j conj(α_{j-k})` (cyclic, all `k ≥ 0`). -/
def alCoef38 {L : ℕ} [NeZero L] (α : ZMod L → ℂ) (k : ℕ) : ℂ :=
  ∑ j : ZMod L, α j * (starRingEnd ℂ) (α (j - (k : ZMod L)))

/-- `S(ζ) = Σ_{m ≥ 0} c_{m+1} ζ^{2(m+1)}`. -/
def alCS38 {L : ℕ} [NeZero L] (α : ZMod L → ℂ) (ζ : ℂ) : ℂ :=
  ∑' m : ℕ, alCoef38 α (m + 1) * ζ ^ (2 * (m + 1))

theorem sum_range_zmod38 {L : ℕ} [NeZero L] (f : ZMod L → ℂ) :
    ∑ k ∈ range L, f (k : ZMod L) = ∑ j : ZMod L, f j := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by have := NeZero.ne L; omega⟩
  rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ => f (k : ZMod (n + 1))) (n + 1)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : (((j : ℕ) : ZMod (n + 1))) = (show ZMod (n + 1) from j) := Fin.cast_val_eq_self j
  rw [hj]

theorem smul_apply38 {L : ℕ} (t : ℝ) (α : ZMod L → ℂ) (j : ZMod L) :
    (t • α) j = (t : ℂ) * α j := by
  simp [Complex.real_smul]

theorem isALField_smul38 {L : ℕ} {α : ZMod L → ℂ} (hα : IsALField38 α) {t : ℝ} (ht : |t| < 1) :
    IsALField38 (t • α) := by
  intro j
  rw [smul_apply38, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have := hα j
  calc |t| * ‖α j‖ ≤ |t| * 1 := by gcongr
    _ < 1 := by linarith

theorem norm_smul_le38 {L : ℕ} {α : ZMod L → ℂ} (hα : IsALField38 α) (t : ℝ) (j : ZMod L) :
    ‖(t • α) j‖ ≤ |t| := by
  rw [smul_apply38, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have := hα j
  calc |t| * ‖α j‖ ≤ |t| * 1 := by gcongr
    _ = |t| := mul_one _

theorem sum_qstar38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {t : ℝ}
    {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1 / 2) :
    ∑ k ∈ range L, ζ * (t • α) (k : ZMod L) * alQStar38 (t • α) ζ k =
      (t : ℂ) ^ 2 * alCS38 α ζ := by
  have hb : ∀ j, ‖(t • α) j‖ ≤ |t| := norm_smul_le38 hα t
  have hsum : ∀ (j : ZMod L), Summable (fun m : ℕ => ζ * (t • α) j * (ζ ^ (2 * m + 1) *
      (starRingEnd ℂ) ((t • α) (j - ((m + 1 : ℕ) : ZMod L))))) := fun j =>
    (summable_geom_mul38 hζ _ (fun m => by simpa using hb _)).mul_left _
  calc ∑ k ∈ range L, ζ * (t • α) (k : ZMod L) * alQStar38 (t • α) ζ k
      = ∑ k ∈ range L, (fun j : ZMod L => ∑' m : ℕ, ζ * (t • α) j * (ζ ^ (2 * m + 1) *
          (starRingEnd ℂ) ((t • α) (j - ((m + 1 : ℕ) : ZMod L))))) (k : ZMod L) := by
        refine sum_congr rfl fun k _ => ?_
        simp only [alQStar38]
        rw [tsum_mul_left]
    _ = ∑ j : ZMod L, ∑' m : ℕ, ζ * (t • α) j * (ζ ^ (2 * m + 1) *
          (starRingEnd ℂ) ((t • α) (j - ((m + 1 : ℕ) : ZMod L)))) :=
        sum_range_zmod38 (fun j : ZMod L => ∑' m : ℕ, ζ * (t • α) j * (ζ ^ (2 * m + 1) *
          (starRingEnd ℂ) ((t • α) (j - ((m + 1 : ℕ) : ZMod L)))))
    _ = ∑' m : ℕ, ∑ j : ZMod L, ζ * (t • α) j * (ζ ^ (2 * m + 1) *
          (starRingEnd ℂ) ((t • α) (j - ((m + 1 : ℕ) : ZMod L)))) :=
        (Summable.tsum_finsetSum fun j _ => hsum j).symm
    _ = ∑' m : ℕ, (t : ℂ) ^ 2 * (alCoef38 α (m + 1) * ζ ^ (2 * (m + 1))) := by
        refine tsum_congr fun m => ?_
        unfold alCoef38
        rw [Finset.sum_mul, Finset.mul_sum]
        refine sum_congr rfl fun j _ => ?_
        simp only [smul_apply38, map_mul, Complex.conj_ofReal]
        push_cast
        ring
    _ = (t : ℂ) ^ 2 * alCS38 α ζ := by
        unfold alCS38
        rw [tsum_mul_left]

/-! ### Pointwise expansion of the exterior branch -/

theorem g_expansion38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {t : ℝ}
    (ht : |t| < 1) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1 / 2) (h0 : ζ ≠ 0) :
    ∃ r : ℂ, ‖r‖ ≤ 3 * L * t ^ 4 ∧
      alExteriorG38 (t • α) ζ = ((Real.exp (alMass38 L (t • α) / 2) : ℝ) : ℂ) *
        Complex.exp ((t : ℂ) ^ 2 * alCS38 α ζ + r) := by
  have hβ : IsALField38 (t • α) := isALField_smul38 hα ht
  have hb : ∀ j, ‖(t • α) j‖ ≤ |t| := norm_smul_le38 hα t
  have hζb : ζ ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]; linarith
  obtain ⟨q, hq1, hqL, hrec, hg⟩ := eigen_q38 hβ hζb h0
  obtain ⟨hb1, hb2⟩ := q_bounds38 (t • α) (abs_nonneg t) ht.le hb hζ q hq1 hqL hrec
  set β := t • α with hβdef
  have hu : ∀ k < L, ‖ζ * β (k : ZMod L) * q k‖ ≤ 1 / 2 := by
    intro k hk
    have h1 := hq1 k hk.le
    have h2 := hb (k : ZMod L)
    rw [norm_mul, norm_mul]
    have : ‖ζ‖ * ‖β (k : ZMod L)‖ ≤ 1 / 2 * 1 := mul_le_mul hζ (h2.trans ht.le) (norm_nonneg _)
      (by norm_num)
    nlinarith [norm_nonneg (q k), norm_nonneg (β (k : ZMod L)), norm_nonneg ζ]
  have hne : ∀ k < L, 1 + ζ * β (k : ZMod L) * q k ≠ 0 := by
    intro k hk h
    have := den_lb38 (hu k hk)
    rw [h, norm_zero] at this; linarith
  set r : ℂ := ∑ k ∈ range L, (Complex.log (1 + ζ * β (k : ZMod L) * q k) -
    ζ * β (k : ZMod L) * alQStar38 β ζ k) with hr
  refine ⟨r, ?_, ?_⟩
  · have hterm : ∀ k ∈ range L, ‖Complex.log (1 + ζ * β (k : ZMod L) * q k) -
        ζ * β (k : ZMod L) * alQStar38 β ζ k‖ ≤ 3 * t ^ 4 := by
      intro k hk
      have hk' : k < L := by simpa using hk
      set u := ζ * β (k : ZMod L) * q k with hudef
      have hu1 := hu k hk'
      have hs : |t| ^ 4 = t ^ 4 := Even.pow_abs (by decide) t
      have hq2 := hb1 k hk'.le
      have hq3 := hb2 k hk'.le
      have hbk := hb (k : ZMod L)
      have hun : ‖u‖ ≤ t ^ 2 := by
        rw [hudef, norm_mul, norm_mul]
        have : ‖ζ‖ * ‖β (k : ZMod L)‖ ≤ 1 / 2 * |t| := mul_le_mul hζ hbk (norm_nonneg _)
          (by norm_num)
        calc ‖ζ‖ * ‖β (k : ZMod L)‖ * ‖q k‖ ≤ 1 / 2 * |t| * (2 * |t|) :=
              mul_le_mul this hq2 (norm_nonneg _) (by positivity)
          _ = t ^ 2 := by rw [← sq_abs t]; ring
      have hl := Complex.norm_log_one_add_sub_self_le (show ‖u‖ < 1 by linarith)
      have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      have hl2 : ‖Complex.log (1 + u) - u‖ ≤ ‖u‖ ^ 2 := by
        calc _ ≤ ‖u‖ ^ 2 * (1 - ‖u‖)⁻¹ / 2 := hl
          _ ≤ ‖u‖ ^ 2 * 2 / 2 := by gcongr
          _ = ‖u‖ ^ 2 := by ring
      have hl3 : ‖u‖ ^ 2 ≤ t ^ 4 := by
        calc ‖u‖ ^ 2 ≤ (t ^ 2) ^ 2 := by gcongr
          _ = t ^ 4 := by ring
      have hd : ‖u - ζ * β (k : ZMod L) * alQStar38 β ζ k‖ ≤ 3 / 2 * t ^ 4 := by
        have : u - ζ * β (k : ZMod L) * alQStar38 β ζ k =
            ζ * β (k : ZMod L) * (q k - alQStar38 β ζ k) := by rw [hudef]; ring
        rw [this, norm_mul, norm_mul]
        have h5 : ‖ζ‖ * ‖β (k : ZMod L)‖ ≤ 1 / 2 * |t| := mul_le_mul hζ hbk (norm_nonneg _)
          (by norm_num)
        calc ‖ζ‖ * ‖β (k : ZMod L)‖ * ‖q k - alQStar38 β ζ k‖ ≤ 1 / 2 * |t| * (3 * |t| ^ 3) :=
              mul_le_mul h5 hq3 (norm_nonneg _) (by positivity)
          _ = 3 / 2 * |t| ^ 4 := by ring
          _ = 3 / 2 * t ^ 4 := by rw [hs]
      calc _ = ‖(Complex.log (1 + u) - u) + (u - ζ * β (k : ZMod L) * alQStar38 β ζ k)‖ := by
            congr 1; ring
        _ ≤ ‖Complex.log (1 + u) - u‖ + ‖u - ζ * β (k : ZMod L) * alQStar38 β ζ k‖ :=
            norm_add_le _ _
        _ ≤ 3 * t ^ 4 := by have h4 : 0 ≤ t ^ 4 := by positivity
                            linarith
    calc ‖r‖ ≤ ∑ k ∈ range L, 3 * t ^ 4 := norm_sum_le_of_le _ hterm
      _ = 3 * L * t ^ 4 := by simp; ring
  · rw [hg]
    congr 1
    have hsumeq : (t : ℂ) ^ 2 * alCS38 α ζ + r =
        ∑ k ∈ range L, Complex.log (1 + ζ * β (k : ZMod L) * q k) := by
      rw [← sum_qstar38 hα hζ, hr, ← sum_add_distrib]
      refine sum_congr rfl fun k _ => ?_
      ring
    rw [hsumeq, Complex.exp_sum]
    refine prod_congr rfl fun k hk => ?_
    exact (Complex.exp_log (hne k (by simpa using hk))).symm

/-! ### `S` as an analytic function with known Taylor coefficients -/

theorem mem_eball_iff38 {y : ℂ} : y ∈ Metric.eball (0 : ℂ) 1 ↔ ‖y‖ < 1 := by
  rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one]

/-- Taylor coefficients of `S` in `ζ`. -/
def alCSseq38 {L : ℕ} [NeZero L] (α : ZMod L → ℂ) (n : ℕ) : ℂ :=
  if n ≠ 0 ∧ n % 2 = 0 then alCoef38 α (n / 2) else 0

theorem norm_alCoef38_le {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) (k : ℕ) :
    ‖alCoef38 α k‖ ≤ L := by
  unfold alCoef38
  calc ‖∑ j : ZMod L, α j * (starRingEnd ℂ) (α (j - (k : ZMod L)))‖
      ≤ ∑ j : ZMod L, ‖α j * (starRingEnd ℂ) (α (j - (k : ZMod L)))‖ := norm_sum_le _ _
    _ ≤ ∑ _j : ZMod L, (1 : ℝ) := by
        refine sum_le_sum fun j _ => ?_
        rw [norm_mul, Complex.norm_conj]
        have h1 := hα j
        have h2 := hα (j - (k : ZMod L))
        nlinarith [norm_nonneg (α j), norm_nonneg (α (j - (k : ZMod L)))]
    _ = L := by simp [Finset.card_univ, ZMod.card]

theorem norm_alCSseq38_le {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) (n : ℕ) :
    ‖alCSseq38 α n‖ ≤ L := by
  unfold alCSseq38
  split_ifs
  · exact norm_alCoef38_le hα _
  · simp

theorem hasFPS_alCS38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    HasFPowerSeriesOnBall (alCS38 α)
      (FormalMultilinearSeries.ofScalars ℂ (alCSseq38 α)) 0 1 := by
  refine ⟨?_, one_pos, ?_⟩
  · have := (FormalMultilinearSeries.ofScalars ℂ (alCSseq38 α)).le_radius_of_bound (r := 1)
      (L : ℝ) (fun n => by
        rw [FormalMultilinearSeries.ofScalars_norm]
        simpa using norm_alCSseq38_le hα n)
    simpa using this
  · intro y hy
    have hy1 : ‖y‖ < 1 := mem_eball_iff38.mp hy
    have hsum : HasSum (fun m : ℕ => alCoef38 α (m + 1) * y ^ (2 * (m + 1))) (alCS38 α y) := by
      have : Summable (fun m : ℕ => alCoef38 α (m + 1) * y ^ (2 * (m + 1))) := by
        refine Summable.of_norm_bounded (g := fun m : ℕ => (L : ℝ) * (‖y‖ ^ 2) ^ (m + 1)) ?_ ?_
        · have h2 : ‖y‖ ^ 2 < 1 := by nlinarith [norm_nonneg y]
          exact ((summable_geometric_of_lt_one (by positivity) h2).comp_injective
            (fun a b h => by simpa using h)).mul_left _
        · intro m
          rw [norm_mul, norm_pow, ← pow_mul]
          exact mul_le_mul_of_nonneg_right (norm_alCoef38_le hα _) (by positivity)
      exact this.hasSum
    simp only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
    have hinj : Function.Injective (fun m : ℕ => 2 * (m + 1)) := fun a b h => by
      simp only at h; omega
    rw [← hinj.hasSum_iff]
    · convert hsum using 2 with m
      simp [alCSseq38]
    · intro n hn
      have : ¬ (n ≠ 0 ∧ n % 2 = 0) := by
        rintro ⟨h1, h2⟩
        exact hn ⟨n / 2 - 1, by simp only; omega⟩
      simp [alCSseq38, this]

theorem differentiableOn_alCS38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    DifferentiableOn ℂ (alCS38 α) (ball (0 : ℂ) 1) := by
  intro y hy
  have : y ∈ Metric.eball (0 : ℂ) 1 := mem_eball_iff38.mpr (by simpa using hy)
  exact ((hasFPS_alCS38 hα).analyticAt_of_mem (by simpa using this)).differentiableAt.differentiableWithinAt

theorem iteratedDeriv_alCS38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) (n : ℕ) :
    iteratedDeriv n (alCS38 α) 0 = (Nat.factorial n : ℂ) * alCSseq38 α n := by
  have h := (hasFPS_alCS38 hα).factorial_smul (y := (1 : ℂ)) n
  rw [iteratedDeriv_eq_iteratedFDeriv, ← h]
  simp [nsmul_eq_mul]

/-! ### Branch argument on the open disk -/

theorem branch38 {H : ℂ → ℂ} {ρ δ : ℝ} (hδ : δ < 1)
    (hH : ContinuousOn H (ball (0 : ℂ) ρ)) (h0 : (0 : ℂ) ∈ ball (0 : ℂ) ρ) (hH0 : ‖H 0‖ < Real.pi)
    (hex : ∀ ζ ∈ ball (0 : ℂ) ρ, ∃ r : ℂ, ‖r‖ ≤ δ ∧ Complex.exp (H ζ) = Complex.exp r) :
    ∀ ζ ∈ ball (0 : ℂ) ρ, ‖H ζ‖ ≤ δ := by
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hdich : ∀ ζ ∈ ball (0 : ℂ) ρ, ‖H ζ‖ ≤ δ ∨ Real.pi < ‖H ζ‖ := by
    intro ζ hζ
    obtain ⟨r, hr, he⟩ := hex ζ hζ
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
    by_cases hn0 : n = 0
    · left; rw [hn, hn0]; simpa using hr
    · right
      have h1 : (2 : ℝ) * Real.pi ≤ ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ := by
        rw [norm_mul, Complex.norm_intCast]
        have : (1 : ℝ) ≤ |(n : ℝ)| := by
          have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
          exact_mod_cast this
        have h2 : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
          rw [norm_mul, norm_mul]; simp [abs_of_pos Real.pi_pos]
        rw [h2]; nlinarith
      have h3 : ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ ≤ ‖H ζ‖ + ‖r‖ := by
        have : (n : ℂ) * (2 * Real.pi * Complex.I) = H ζ - r := by rw [hn]; ring
        rw [this]; exact norm_sub_le _ _
      linarith
  have hnorm : ContinuousOn (fun ζ => ‖H ζ‖) (ball (0 : ℂ) ρ) := hH.norm
  have hu : IsOpen (ball (0 : ℂ) ρ ∩ (fun ζ => ‖H ζ‖) ⁻¹' Set.Iio Real.pi) :=
    hnorm.isOpen_inter_preimage isOpen_ball isOpen_Iio
  have hv : IsOpen (ball (0 : ℂ) ρ ∩ (fun ζ => ‖H ζ‖) ⁻¹' Set.Ioi Real.pi) :=
    hnorm.isOpen_inter_preimage isOpen_ball isOpen_Ioi
  have hsub := (convex_ball (0 : ℂ) ρ).isPreconnected.subset_left_of_subset_union hu hv
    (by
      rw [Set.disjoint_left]
      rintro ζ ⟨_, h1⟩ ⟨_, h2⟩
      exact absurd (lt_trans (show ‖H ζ‖ < Real.pi from h1) (show Real.pi < ‖H ζ‖ from h2))
        (lt_irrefl _))
    (by
      intro ζ hζ
      rcases hdich ζ hζ with h | h
      · left; exact ⟨hζ, by show ‖H ζ‖ < Real.pi; linarith⟩
      · right; exact ⟨hζ, h⟩)
    ⟨0, h0, h0, hH0⟩
  intro ζ hζ
  rcases hdich ζ hζ with h | h
  · exact h
  · exact absurd (hsub hζ).2 (not_lt.mpr h.le)

/-! ### Taylor coefficients of the comparison difference -/

/-- `H = ℓ - ℓ(0) - t² S`, the difference of the AL logarithm and its quadratic model. -/
def alDiff38 {L : ℕ} [NeZero L] (α : ZMod L → ℂ) (t : ℝ) (ζ : ℂ) : ℂ :=
  -(alLog38 (t • α) 0) + (alLog38 (t • α) ζ - (t : ℂ) ^ 2 * alCS38 α ζ)

theorem alDiff38_zero {L : ℕ} [NeZero L] (α : ZMod L → ℂ) (t : ℝ) : alDiff38 α t 0 = 0 := by
  simp [alDiff38, alCS38]

theorem differentiableOn_alDiff38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α)
    {t : ℝ} (ht : |t| < 1) : DifferentiableOn ℂ (alDiff38 α t) (ball (0 : ℂ) 1) := by
  have h1 := (alLog38_spec (isALField_smul38 hα ht)).1.differentiableOn
  have h2 := differentiableOn_alCS38 hα
  unfold alDiff38
  exact (differentiableOn_const _).add (h1.sub (h2.const_mul _))

theorem evenLogCoeff_alDiff38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α)
    {t : ℝ} (ht : |t| < 1) (m : ℕ) :
    evenLogCoeff38 (alDiff38 α t) m =
      alC38 (t • α) (m + 1) - (t : ℂ) ^ 2 * alCoef38 α (m + 1) := by
  have hℓ : AnalyticAt ℂ (alLog38 (t • α)) 0 :=
    (alLog38_spec (isALField_smul38 hα ht)).1 0 (mem_ball_self one_pos)
  have hS : AnalyticAt ℂ (alCS38 α) 0 := (hasFPS_alCS38 hα).analyticAt
  have hn : 0 < 2 * (m + 1) := by omega
  have hfac : (Nat.factorial (2 * (m + 1)) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  unfold evenLogCoeff38 alDiff38
  rw [iteratedDeriv_const_add hn, iteratedDeriv_fun_sub (hℓ.contDiffAt)
    ((contDiffAt_const.mul hS.contDiffAt)), iteratedDeriv_const_mul_field,
    iteratedDeriv_alCS38 hα]
  have hseq : alCSseq38 α (2 * (m + 1)) = alCoef38 α (m + 1) := by
    simp [alCSseq38]
  rw [hseq]
  unfold alC38
  field_simp

/-! ### Pointwise bound of the difference -/

theorem alDiff38_bound {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {t : ℝ}
    (ht : |t| < 1) (htL : 3 * (L : ℝ) * t ^ 4 < 1) :
    ∀ ζ ∈ ball (0 : ℂ) (1 / 2), ‖alDiff38 α t ζ‖ ≤ 3 * L * t ^ 4 := by
  have hβ := isALField_smul38 hα ht
  have hs := alLog38_spec hβ
  refine branch38 (ρ := 1 / 2) htL ?_ (mem_ball_self (by norm_num)) (by
      rw [alDiff38_zero, norm_zero]; exact Real.pi_pos) ?_
  · exact (differentiableOn_alDiff38 hα ht).continuousOn.mono
      (ball_subset_ball (by norm_num))
  · intro ζ hζ
    by_cases h0 : ζ = 0
    · exact ⟨0, by simp; positivity, by rw [h0, alDiff38_zero]⟩
    · have hζ' : ‖ζ‖ ≤ 1 / 2 := by
        have := mem_ball_zero_iff.mp hζ; linarith
      obtain ⟨r, hr, hg⟩ := g_expansion38 hα ht hζ' h0
      refine ⟨r, hr, ?_⟩
      have hζ1 : ζ ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff]; have := mem_ball_zero_iff.mp hζ; linarith
      have e1 := hs.2.1 ζ hζ1
      have e0 : Complex.exp (alLog38 (t • α) 0) =
          ((Real.exp (alMass38 L (t • α) / 2) : ℝ) : ℂ) := by
        rw [hs.2.2.1, Complex.ofReal_exp]
      have key : Complex.exp (alLog38 (t • α) ζ) = Complex.exp (alLog38 (t • α) 0) *
          Complex.exp ((t : ℂ) ^ 2 * alCS38 α ζ + r) := by
        rw [e1, e0, hg]
      have : alDiff38 α t ζ = alLog38 (t • α) ζ - (alLog38 (t • α) 0 +
          (t : ℂ) ^ 2 * alCS38 α ζ) := by unfold alDiff38; ring
      rw [this, Complex.exp_sub, key, Complex.exp_add (alLog38 (t • α) 0), Complex.exp_add
        ((t : ℂ) ^ 2 * alCS38 α ζ) r]
      have := Complex.exp_ne_zero (alLog38 (t • α) 0)
      have := Complex.exp_ne_zero ((t : ℂ) ^ 2 * alCS38 α ζ)
      field_simp

/-! ### Main statements -/

theorem small38 {L : ℕ} [NeZero L] {t : ℝ} (ht : |t| < 1 / (3 * (L : ℝ))) :
    |t| < 1 ∧ 3 * (L : ℝ) * t ^ 4 < 1 := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.pos L
  have hL3 : 0 < 3 * (L : ℝ) := by linarith
  have h1 : 1 / (3 * (L : ℝ)) ≤ 1 := by
    rw [div_le_one hL3]; linarith
  have ht1 : |t| < 1 := lt_of_lt_of_le ht h1
  refine ⟨ht1, ?_⟩
  have h4 : t ^ 4 ≤ |t| := by
    rw [← Even.pow_abs (by decide : Even 4) t]
    have : |t| ^ 4 ≤ |t| ^ 1 := pow_le_pow_of_le_one (abs_nonneg t) ht1.le (by norm_num)
    simpa using this
  have : 3 * (L : ℝ) * |t| < 1 := by
    rw [lt_div_iff₀ hL3] at ht; linarith
  nlinarith [pow_nonneg (sq_nonneg t) 2]

/-- `D:eq:Cquadratic` for `C_k`, every `k ≥ 1` (cyclic, including `k ≥ L`). -/
theorem alC38_quadratic38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α)
    {k : ℕ} (hk : 1 ≤ k) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ t : ℝ, 0 < |t| → |t| < δ →
      ‖alC38 (t • α) k - (t : ℂ) ^ 2 * ∑ j : ZMod L, α j * (starRingEnd ℂ) (α (j - (k : ZMod L)))‖
        ≤ C * t ^ 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.pos L
  refine ⟨3 * L * ((1 / 4 : ℝ) ^ (2 * (m + 1)))⁻¹, 1 / (3 * (L : ℝ)), by positivity,
    by positivity, fun t _ htd => ?_⟩
  obtain ⟨ht1, htL⟩ := small38 htd
  have hb := alDiff38_bound hα ht1 htL
  have hcoef := norm_evenLogCoeff_le38 (differentiableOn_alDiff38 hα ht1)
    (ρ := 1 / 4) (M := 3 * L * t ^ 4) (by norm_num) (by norm_num)
    (fun z hz => hb z (by
      have := mem_sphere_zero_iff_norm.mp hz
      rw [mem_ball_zero_iff]; linarith)) m
  rw [evenLogCoeff_alDiff38 hα ht1] at hcoef
  have e : ((t : ℂ) ^ 2 * ∑ j : ZMod L, α j * (starRingEnd ℂ) (α (j - ((m + 1 : ℕ) : ZMod L)))) =
      (t : ℂ) ^ 2 * alCoef38 α (m + 1) := rfl
  rw [e]
  calc _ ≤ 3 * L * t ^ 4 * ((1 / 4 : ℝ) ^ (2 * (m + 1)))⁻¹ := hcoef
    _ = _ := by ring

/-- `D:eq:Cquadratic` for the mass: `M_d(tα) = t² Σ_j |α_j|² + O(t⁴)`. -/
theorem alMass38_quadratic38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ t : ℝ, 0 < |t| → |t| < δ →
      |alMass38 L (t • α) - t ^ 2 * ∑ j : ZMod L, ‖α j‖ ^ 2| ≤ C * t ^ 4 := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.pos L
  refine ⟨2 * L, 1 / (3 * (L : ℝ)), by positivity, by positivity, fun t _ htd => ?_⟩
  obtain ⟨ht1, htL⟩ := small38 htd
  have ht2 : t ^ 2 ≤ 1 / 2 := by
    have h1 : |t| ≤ 1 / 3 := by
      refine htd.le.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    rw [this]; nlinarith [abs_nonneg t]
  have hterm : ∀ j : ZMod L, |-Real.log (1 - ‖(t • α) j‖ ^ 2) - t ^ 2 * ‖α j‖ ^ 2| ≤ 2 * t ^ 4 := by
    intro j
    have hn : ‖(t • α) j‖ ^ 2 = t ^ 2 * ‖α j‖ ^ 2 := by
      rw [smul_apply38, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    set x := t ^ 2 * ‖α j‖ ^ 2 with hx
    have hx0 : 0 ≤ x := by positivity
    have hx1 : x ≤ 1 / 2 := by
      have := hα j
      have : ‖α j‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (α j)]
      calc x ≤ t ^ 2 * 1 := by rw [hx]; gcongr
        _ ≤ 1 / 2 := by linarith
    have h := Real.abs_log_sub_add_sum_range_le (x := x) (by rw [abs_of_nonneg hx0]; linarith) 1
    have h' : |x + Real.log (1 - x)| ≤ |x| ^ 2 / (1 - |x|) := by simpa using h
    rw [hn]
    have hxt : x ≤ t ^ 2 := by
      have := hα j
      have : ‖α j‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (α j)]
      calc x ≤ t ^ 2 * 1 := by rw [hx]; gcongr
        _ = t ^ 2 := mul_one _
    have h2 : |x| ^ 2 / (1 - |x|) ≤ 2 * t ^ 4 := by
      rw [abs_of_nonneg hx0, div_le_iff₀ (by linarith)]
      have hxx : x ^ 2 ≤ (t ^ 2) ^ 2 := pow_le_pow_left₀ hx0 hxt 2
      have h4 : 0 ≤ t ^ 4 := by positivity
      nlinarith
    have e : -Real.log (1 - x) - x = -(x + Real.log (1 - x)) := by ring
    rw [e, abs_neg]
    exact h'.trans h2
  have : alMass38 L (t • α) - t ^ 2 * ∑ j : ZMod L, ‖α j‖ ^ 2 =
      ∑ j : ZMod L, (-Real.log (1 - ‖(t • α) j‖ ^ 2) - t ^ 2 * ‖α j‖ ^ 2) := by
    unfold alMass38
    rw [sum_sub_distrib, sum_neg_distrib, mul_sum]
  rw [this]
  calc _ ≤ ∑ j : ZMod L, |-Real.log (1 - ‖(t • α) j‖ ^ 2) - t ^ 2 * ‖α j‖ ^ 2| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : ZMod L, 2 * t ^ 4 := sum_le_sum fun j _ => hterm j
    _ = 2 * L * t ^ 4 := by simp [Finset.card_univ, ZMod.card]; ring

end NlsGge.AblowitzLadik

end
