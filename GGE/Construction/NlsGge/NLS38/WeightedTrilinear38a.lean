import NlsGge.NLS38.SeqConv38a

/-! # GWP piece A1 (part a): admissible weights, Minkowski, weighted trilinear convolution estimate

Plan: `campaign/GWP_PLAN.md` §7 Part A, piece A1.  Part b is `NlsGge.NLS38.WeightedTrilinear38`
(weights `⟨n⟩^m`, `min(⟨n⟩,K)^m`, cast bridge, corollaries in `h^m`); it imports this file.

The core (`trilinear_real38`) is a real nonnegative statement:
`‖ω · ((p * q) * r)‖₂ ≤ C (‖ωp‖₂ ‖q‖₁ ‖r‖₁ + ‖p‖₁ ‖ωq‖₂ ‖r‖₁ + ‖p‖₁ ‖q‖₁ ‖ωr‖₂)`,
proved with summability established first at every `tsum` (no totalised value is used before its
summability): Young `ℓ¹ * ℓ²` from A0 (`young_convR`, `young_convR_sq`), pointwise weight splitting
`ω(a+b+d) ≤ C (ω a + ω b + ω d)` inside the nested sums, then Minkowski.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open scoped ComplexConjugate ENNReal

/-! ## Definitions of the plan -/

/-- Admissible weight with constant `C`. -/
def AdmWeight (C : ℝ) (ω : ℤ → ℝ) : Prop :=
  (∀ n, 0 ≤ ω n) ∧ (∀ n, ω (-n) = ω n) ∧ ∀ a b c, ω (a + b - c) ≤ C * (ω a + ω b + ω c)

/-- Weighted `ℓ²` norm (meaningful when the sum converges). -/
def wl2 (ω : ℤ → ℝ) (f : ℤ → ℂ) : ℝ := Real.sqrt (∑' n, ω n ^ 2 * ‖f n‖ ^ 2)

theorem AdmWeight.add3 {C : ℝ} {ω : ℤ → ℝ} (h : AdmWeight C ω) (a b c : ℤ) :
    ω (a + b + c) ≤ C * (ω a + ω b + ω c) := by
  have := h.2.2 a b (-c)
  rw [h.2.1 c, sub_neg_eq_add] at this
  exact this

/-- If the constant is negative the weight vanishes identically. -/
theorem AdmWeight.eq_zero_of_neg {C : ℝ} {ω : ℤ → ℝ} (h : AdmWeight C ω) (hC : C < 0) :
    ∀ n, ω n = 0 := by
  have h0 : ω 0 = 0 := by
    have h3 := h.2.2 0 0 0
    simp only [add_zero, sub_zero] at h3
    nlinarith [h.1 0]
  intro n
  have h1 := h.2.2 n 0 0
  simp only [add_zero, sub_zero, h0] at h1
  have := h.1 n
  nlinarith

/-! ## Real core -/

section Real

/-- Reindexing of a slice: `k ↦ n - k`. -/
theorem summable_slice_swap38 {u v : ℤ → ℝ} (n : ℤ) :
    (Summable fun k => u k * v (n - k)) ↔ Summable fun k => v k * u (n - k) := by
  have h := (Equiv.subLeft n).summable_iff (f := fun k => v k * u (n - k))
  rw [← h]
  refine summable_congr fun k => ?_
  simp [Equiv.subLeft_apply, mul_comm]

theorem convR_comm38 (u v : ℤ → ℝ) : convR u v = convR v u := by
  funext n
  unfold convR
  rw [← (Equiv.subLeft n).tsum_eq (fun k => v k * u (n - k))]
  refine tsum_congr fun k => ?_
  simp [Equiv.subLeft_apply, mul_comm]

/-- `ℓ² * ℓ¹` slice. -/
theorem slice_l2_l1_38 {a b : ℤ → ℝ} (hb : Summable b) (hb0 : 0 ≤ b) (ha0 : 0 ≤ a)
    (ha2 : Summable fun k => a k ^ 2) (n : ℤ) : Summable fun k => a k * b (n - k) :=
  (summable_slice_swap38 n).2 (young_convR hb hb0 ha0 ha2 n).1

/-- `ℓ² * ℓ¹` in `ℓ²`, norm form. -/
theorem l2_convR_l1_38 {u v : ℤ → ℝ} (hv : Summable v) (hu0 : 0 ≤ u) (hv0 : 0 ≤ v)
    (hu2 : Summable fun k => u k ^ 2) :
    Summable (fun n => (convR u v n) ^ 2) ∧
      Real.sqrt (∑' n, (convR u v n) ^ 2) ≤ (∑' k, v k) * Real.sqrt (∑' k, u k ^ 2) := by
  rw [convR_comm38 u v]
  obtain ⟨h1, h2⟩ := young_convR_sq hv hv0 hu0 hu2
  refine ⟨h1, ?_⟩
  have hv' : 0 ≤ ∑' k, v k := tsum_nonneg hv0
  calc Real.sqrt (∑' n, (convR v u n) ^ 2)
      ≤ Real.sqrt ((∑' k, v k) ^ 2 * ∑' k, u k ^ 2) := Real.sqrt_le_sqrt h2
    _ = (∑' k, v k) * Real.sqrt (∑' k, u k ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hv']

/-- `ℓ¹ * ℓ²` in `ℓ²`, norm form. -/
theorem l2_convR_l1'_38 {a b : ℤ → ℝ} (ha : Summable a) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (hb2 : Summable fun k => b k ^ 2) :
    Summable (fun n => (convR a b n) ^ 2) ∧
      Real.sqrt (∑' n, (convR a b n) ^ 2) ≤ (∑' k, a k) * Real.sqrt (∑' k, b k ^ 2) := by
  obtain ⟨h1, h2⟩ := young_convR_sq ha ha0 hb0 hb2
  refine ⟨h1, ?_⟩
  have ha' : 0 ≤ ∑' k, a k := tsum_nonneg ha0
  calc Real.sqrt (∑' n, (convR a b n) ^ 2)
      ≤ Real.sqrt ((∑' k, a k) ^ 2 * ∑' k, b k ^ 2) := Real.sqrt_le_sqrt h2
    _ = (∑' k, a k) * Real.sqrt (∑' k, b k ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ha']

/-- Minkowski in `ℓ²` for two nonnegative sequences. -/
theorem minkowski2_38 {a b : ℤ → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha2 : Summable fun n => a n ^ 2)
    (hb2 : Summable fun n => b n ^ 2) :
    Summable (fun n => (a n + b n) ^ 2) ∧
      Real.sqrt (∑' n, (a n + b n) ^ 2) ≤
        Real.sqrt (∑' n, a n ^ 2) + Real.sqrt (∑' n, b n ^ 2) := by
  have ha2' : Summable fun n => a n ^ (2 : ℝ) := by simpa only [Real.rpow_two] using ha2
  have hb2' : Summable fun n => b n ^ (2 : ℝ) := by simpa only [Real.rpow_two] using hb2
  obtain ⟨h1, h2⟩ := Real.Lp_add_le_tsum_of_nonneg (p := 2) (by norm_num) ha hb ha2' hb2'
  simp only [Real.rpow_two] at h1 h2
  refine ⟨h1, ?_⟩
  simpa only [Real.sqrt_eq_rpow, one_div] using h2

theorem minkowski3_38 {a b c : ℤ → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ha2 : Summable fun n => a n ^ 2) (hb2 : Summable fun n => b n ^ 2)
    (hc2 : Summable fun n => c n ^ 2) :
    Summable (fun n => (a n + b n + c n) ^ 2) ∧
      Real.sqrt (∑' n, (a n + b n + c n) ^ 2) ≤
        Real.sqrt (∑' n, a n ^ 2) + Real.sqrt (∑' n, b n ^ 2) + Real.sqrt (∑' n, c n ^ 2) := by
  obtain ⟨s1, i1⟩ := minkowski2_38 ha hb ha2 hb2
  have hab : 0 ≤ fun n => a n + b n := fun n => add_nonneg (ha n) (hb n)
  obtain ⟨s2, i2⟩ := minkowski2_38 (a := fun n => a n + b n) hab hc s1 hc2
  exact ⟨s2, i2.trans (by linarith)⟩

variable {C : ℝ} {ω : ℤ → ℝ} {p q r : ℤ → ℝ}

/-- Weighted nonneg sequences stay nonneg. -/
theorem wmul_nonneg38 (hω : AdmWeight C ω) (hp0 : 0 ≤ p) : 0 ≤ fun k => ω k * p k :=
  fun k => mul_nonneg (hω.1 k) (hp0 k)

/-- The pointwise (in `n`) weight splitting inside the nested convolution. -/
theorem key_pointwise38 (hω : AdmWeight C ω) (hp0 : 0 ≤ p) (hq0 : 0 ≤ q) (hr0 : 0 ≤ r)
    (hp1 : Summable p) (hq1 : Summable q) (hr1 : Summable r)
    (hp2 : Summable fun n => (ω n * p n) ^ 2) (hq2 : Summable fun n => (ω n * q n) ^ 2)
    (hr2 : Summable fun n => (ω n * r n) ^ 2) (n : ℤ) :
    ω n * convR (convR p q) r n ≤
      C * (convR (convR (fun k => ω k * p k) q) r n + convR (convR p (fun k => ω k * q k)) r n +
        convR (convR p q) (fun k => ω k * r k) n) := by
  set wp : ℤ → ℝ := fun k => ω k * p k with hwp
  set wq : ℤ → ℝ := fun k => ω k * q k with hwq
  set wr : ℤ → ℝ := fun k => ω k * r k with hwr
  have hwp0 : 0 ≤ wp := wmul_nonneg38 hω hp0
  have hwq0 : 0 ≤ wq := wmul_nonneg38 hω hq0
  have hwr0 : 0 ≤ wr := wmul_nonneg38 hω hr0
  have hwp2 : Summable fun k => wp k ^ 2 := hp2
  have hwq2 : Summable fun k => wq k ^ 2 := hq2
  have hwr2 : Summable fun k => wr k ^ 2 := hr2
  have hω0 := hω.1
  -- ℓ² facts for the inner convolutions
  obtain ⟨hY2, -⟩ := l2_convR_l1_38 (u := wp) (v := q) hq1 hwp0 hq0 hwp2
  obtain ⟨hZ2, -⟩ := l2_convR_l1'_38 (a := p) (b := wq) hp1 hp0 hwq0 hwq2
  have hpq1 : Summable (convR p q) := summable_convR hp1 hq1 hp0 hq0
  have hpq0 : 0 ≤ convR p q := fun c => convR_nonneg hp0 hq0 c
  have hY0 : 0 ≤ convR wp q := fun c => convR_nonneg hwp0 hq0 c
  have hZ0 : 0 ≤ convR p wq := fun c => convR_nonneg hp0 hwq0 c
  -- Step A: inner sum over `a`
  have hA : ∀ c, ω n * (convR p q c * r (n - c)) ≤
      C * (convR wp q c * r (n - c) + convR p wq c * r (n - c) +
        convR p q c * wr (n - c)) := by
    intro c
    have s1 : Summable fun a => p a * q (c - a) := summable_convR_slice hp1 hq1 hp0 hq0 c
    have s2 : Summable fun a => wp a * q (c - a) := slice_l2_l1_38 hq1 hq0 hwp0 hwp2 c
    have s3 : Summable fun a => p a * wq (c - a) := (young_convR hp1 hp0 hwq0 hwq2 c).1
    have e1 : ω n * (convR p q c * r (n - c)) =
        ∑' a, ω n * (p a * q (c - a) * r (n - c)) := by
      unfold convR
      rw [← tsum_mul_right, ← tsum_mul_left]
    have e2 : convR wp q c * r (n - c) = ∑' a, wp a * q (c - a) * r (n - c) := by
      unfold convR; rw [← tsum_mul_right]
    have e3 : convR p wq c * r (n - c) = ∑' a, p a * wq (c - a) * r (n - c) := by
      unfold convR; rw [← tsum_mul_right]
    have e4 : convR p q c * wr (n - c) = ∑' a, p a * q (c - a) * wr (n - c) := by
      unfold convR; rw [← tsum_mul_right]
    have hsum : C * (convR wp q c * r (n - c) + convR p wq c * r (n - c) +
        convR p q c * wr (n - c)) =
        ∑' a, C * (wp a * q (c - a) * r (n - c) + p a * wq (c - a) * r (n - c) +
          p a * q (c - a) * wr (n - c)) := by
      rw [tsum_mul_left, ((s2.mul_right _).add (s3.mul_right _)).tsum_add (s1.mul_right _),
        (s2.mul_right _).tsum_add (s3.mul_right _), e2, e3, e4]
    rw [e1, hsum]
    refine Summable.tsum_le_tsum (fun a => ?_) ((s1.mul_right _).mul_left _)
      ((((s2.mul_right _).add (s3.mul_right _)).add (s1.mul_right _)).mul_left _)
    have hn : n = a + (c - a) + (n - c) := by ring
    have hb := hω.add3 a (c - a) (n - c)
    rw [← hn] at hb
    have hP : 0 ≤ p a * q (c - a) * r (n - c) :=
      mul_nonneg (mul_nonneg (hp0 a) (hq0 _)) (hr0 _)
    calc ω n * (p a * q (c - a) * r (n - c))
        ≤ (C * (ω a + ω (c - a) + ω (n - c))) * (p a * q (c - a) * r (n - c)) :=
          mul_le_mul_of_nonneg_right hb hP
      _ = C * (wp a * q (c - a) * r (n - c) + p a * wq (c - a) * r (n - c) +
          p a * q (c - a) * wr (n - c)) := by simp only [hwp, hwq, hwr]; ring
  -- Step B: outer sum over `c`
  have t1 : Summable fun c => convR p q c * r (n - c) :=
    summable_convR_slice hpq1 hr1 hpq0 hr0 n
  have t2 : Summable fun c => convR wp q c * r (n - c) :=
    slice_l2_l1_38 hr1 hr0 hY0 hY2 n
  have t3 : Summable fun c => convR p wq c * r (n - c) :=
    slice_l2_l1_38 hr1 hr0 hZ0 hZ2 n
  have t4 : Summable fun c => convR p q c * wr (n - c) :=
    (young_convR hpq1 hpq0 hwr0 hwr2 n).1
  have hsum2 : C * (convR (convR wp q) r n + convR (convR p wq) r n + convR (convR p q) wr n) =
      ∑' c, C * (convR wp q c * r (n - c) + convR p wq c * r (n - c) +
        convR p q c * wr (n - c)) := by
    change C * (∑' c, convR wp q c * r (n - c) + ∑' c, convR p wq c * r (n - c) +
      ∑' c, convR p q c * wr (n - c)) = _
    rw [tsum_mul_left, (t2.add t3).tsum_add t4, t2.tsum_add t3]
  rw [hsum2]
  have e0 : ω n * convR (convR p q) r n = ∑' c, ω n * (convR p q c * r (n - c)) := by
    unfold convR
    rw [← tsum_mul_left]
  rw [e0]
  exact Summable.tsum_le_tsum hA (t1.mul_left _) (((t2.add t3).add t4).mul_left _)

/-- **Weighted trilinear estimate, real form.** -/
theorem trilinear_real38 (hC : 0 ≤ C) (hω : AdmWeight C ω) (hp0 : 0 ≤ p) (hq0 : 0 ≤ q) (hr0 : 0 ≤ r)
    (hp1 : Summable p) (hq1 : Summable q) (hr1 : Summable r)
    (hp2 : Summable fun n => (ω n * p n) ^ 2) (hq2 : Summable fun n => (ω n * q n) ^ 2)
    (hr2 : Summable fun n => (ω n * r n) ^ 2) :
    Summable (fun n => (ω n * convR (convR p q) r n) ^ 2) ∧
      Real.sqrt (∑' n, (ω n * convR (convR p q) r n) ^ 2) ≤
        C * (Real.sqrt (∑' n, (ω n * p n) ^ 2) * (∑' k, q k) * (∑' k, r k) +
          (∑' k, p k) * Real.sqrt (∑' n, (ω n * q n) ^ 2) * (∑' k, r k) +
          (∑' k, p k) * (∑' k, q k) * Real.sqrt (∑' n, (ω n * r n) ^ 2)) := by
  set wp : ℤ → ℝ := fun k => ω k * p k with hwp
  set wq : ℤ → ℝ := fun k => ω k * q k with hwq
  set wr : ℤ → ℝ := fun k => ω k * r k with hwr
  have hwp0 : 0 ≤ wp := wmul_nonneg38 hω hp0
  have hwq0 : 0 ≤ wq := wmul_nonneg38 hω hq0
  have hwr0 : 0 ≤ wr := wmul_nonneg38 hω hr0
  have hwp2 : Summable fun k => wp k ^ 2 := hp2
  have hwq2 : Summable fun k => wq k ^ 2 := hq2
  have hwr2 : Summable fun k => wr k ^ 2 := hr2
  have hpq1 : Summable (convR p q) := summable_convR hp1 hq1 hp0 hq0
  have hpq0 : 0 ≤ convR p q := fun c => convR_nonneg hp0 hq0 c
  -- the three ℓ² majorants
  obtain ⟨hY2, iY⟩ := l2_convR_l1_38 (u := wp) (v := q) hq1 hwp0 hq0 hwp2
  obtain ⟨hZ2, iZ⟩ := l2_convR_l1'_38 (a := p) (b := wq) hp1 hp0 hwq0 hwq2
  have hY0 : 0 ≤ convR wp q := fun c => convR_nonneg hwp0 hq0 c
  have hZ0 : 0 ≤ convR p wq := fun c => convR_nonneg hp0 hwq0 c
  obtain ⟨hX12, iX1⟩ := l2_convR_l1_38 (u := convR wp q) (v := r) hr1 hY0 hr0 hY2
  obtain ⟨hX22, iX2⟩ := l2_convR_l1_38 (u := convR p wq) (v := r) hr1 hZ0 hr0 hZ2
  obtain ⟨hX32, iX3⟩ := l2_convR_l1'_38 (a := convR p q) (b := wr) hpq1 hpq0 hwr0 hwr2
  have hX10 : 0 ≤ convR (convR wp q) r := fun c => convR_nonneg hY0 hr0 c
  have hX20 : 0 ≤ convR (convR p wq) r := fun c => convR_nonneg hZ0 hr0 c
  have hX30 : 0 ≤ convR (convR p q) wr := fun c => convR_nonneg hpq0 hwr0 c
  obtain ⟨hM2, iM⟩ := minkowski3_38 hX10 hX20 hX30 hX12 hX22 hX32
  have hMeq : ∀ n, 0 ≤ ω n * convR (convR p q) r n := fun n =>
    mul_nonneg (hω.1 n) (convR_nonneg hpq0 hr0 n)
  have hkey : ∀ n, ω n * convR (convR p q) r n ≤ C * ((convR (convR wp q) r n +
      convR (convR p wq) r n) + convR (convR p q) wr n) := fun n =>
    key_pointwise38 hω hp0 hq0 hr0 hp1 hq1 hr1 hp2 hq2 hr2 n
  have hsq : ∀ n, (ω n * convR (convR p q) r n) ^ 2 ≤
      C ^ 2 * (convR (convR wp q) r n + convR (convR p wq) r n + convR (convR p q) wr n) ^ 2 :=
    fun n => by
      have h := pow_le_pow_left₀ (hMeq n) (hkey n) 2
      calc _ ≤ _ := h
        _ = _ := by ring
  have hsum : Summable (fun n => (ω n * convR (convR p q) r n) ^ 2) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hsq (hM2.mul_left _)
  refine ⟨hsum, ?_⟩
  have hle : Real.sqrt (∑' n, (ω n * convR (convR p q) r n) ^ 2) ≤
      C * Real.sqrt (∑' n, (convR (convR wp q) r n + convR (convR p wq) r n +
        convR (convR p q) wr n) ^ 2) := by
    calc Real.sqrt (∑' n, (ω n * convR (convR p q) r n) ^ 2)
        ≤ Real.sqrt (∑' n, C ^ 2 * (convR (convR wp q) r n + convR (convR p wq) r n +
          convR (convR p q) wr n) ^ 2) :=
          Real.sqrt_le_sqrt (hsum.tsum_le_tsum hsq (hM2.mul_left _))
      _ = C * Real.sqrt (∑' n, (convR (convR wp q) r n + convR (convR p wq) r n +
          convR (convR p q) wr n) ^ 2) := by
          rw [tsum_mul_left, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hC]
  refine hle.trans ?_
  refine mul_le_mul_of_nonneg_left (iM.trans ?_) hC
  have hq' : 0 ≤ ∑' k, q k := tsum_nonneg hq0
  have hr' : 0 ≤ ∑' k, r k := tsum_nonneg hr0
  have hp' : 0 ≤ ∑' k, p k := tsum_nonneg hp0
  have hpq : ∑' k, convR p q k = (∑' k, p k) * ∑' k, q k := tsum_convR hp1 hq1 hp0 hq0
  have b1 : Real.sqrt (∑' n, (convR (convR wp q) r n) ^ 2) ≤
      Real.sqrt (∑' n, (ω n * p n) ^ 2) * (∑' k, q k) * (∑' k, r k) := by
    refine iX1.trans ?_
    have := mul_le_mul_of_nonneg_left iY hr'
    nlinarith [this]
  have b2 : Real.sqrt (∑' n, (convR (convR p wq) r n) ^ 2) ≤
      (∑' k, p k) * Real.sqrt (∑' n, (ω n * q n) ^ 2) * (∑' k, r k) := by
    refine iX2.trans ?_
    have := mul_le_mul_of_nonneg_left iZ hr'
    nlinarith [this]
  have b3 : Real.sqrt (∑' n, (convR (convR p q) wr n) ^ 2) ≤
      (∑' k, p k) * (∑' k, q k) * Real.sqrt (∑' n, (ω n * r n) ^ 2) := by
    refine iX3.trans ?_
    rw [hpq]
  linarith

end Real

end NlsGge.NLS38
