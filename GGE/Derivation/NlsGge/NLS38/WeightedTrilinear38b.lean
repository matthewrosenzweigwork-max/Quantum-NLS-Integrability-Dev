import NlsGge.NLS38.WeightedTrilinear38a
import NlsGge.NLS38.SeqConv38

/-! # GWP piece A1 (part b): complex trilinear estimate, weights, cast bridge, `wl2` calculus

Plan: `campaign/GWP_PLAN.md` §6.0 (cast convention) and §7 Part A, piece A1.  Part a is
`NlsGge.NLS38.WeightedTrilinear38a` (admissible weights, Minkowski, real core `trilinear_real38`);
the public entry point is `NlsGge.NLS38.WeightedTrilinear38` (nonlinearity bounds).  Here: the
complex form `wl2_trilinear`, the weights `⟨n⟩^m` and `min(⟨n⟩,K)^m`, the cast bridge
`isL1_of_h1_nat`, and the `wl2` calculus (smul, domination by two or three sequences).
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open scoped ComplexConjugate ENNReal

/-! ## Complex form of the trilinear estimate -/

theorem wl2_eq_sqrt38 (ω : ℤ → ℝ) (f : ℤ → ℂ) :
    wl2 ω f = Real.sqrt (∑' n, (ω n * ‖f n‖) ^ 2) := by
  unfold wl2; simp only [mul_pow]

theorem wl2_nonneg38 (ω : ℤ → ℝ) (f : ℤ → ℂ) : 0 ≤ wl2 ω f := Real.sqrt_nonneg _

theorem l1_nonneg38 (f : ℤ → ℂ) : 0 ≤ l1 f := tsum_nonneg fun _ => norm_nonneg _

theorem summable_wsq_iff38 (ω : ℤ → ℝ) (f : ℤ → ℂ) :
    (Summable fun n => ω n ^ 2 * ‖f n‖ ^ 2) ↔ Summable fun n => (ω n * ‖f n‖) ^ 2 := by
  simp only [mul_pow]

theorem summable_wsq_cstar38 {ω : ℤ → ℝ} (hω : ∀ n, ω (-n) = ω n) {f : ℤ → ℂ}
    (hf : Summable fun n => ω n ^ 2 * ‖f n‖ ^ 2) :
    Summable fun n => ω n ^ 2 * ‖cstar f n‖ ^ 2 := by
  have h := (Equiv.neg ℤ).summable_iff.2 hf
  refine h.congr fun n => ?_
  simp [cstar, hω]

theorem wl2_cstar38 {ω : ℤ → ℝ} (hω : ∀ n, ω (-n) = ω n) (f : ℤ → ℂ) :
    wl2 ω (cstar f) = wl2 ω f := by
  unfold wl2
  congr 1
  rw [← (Equiv.neg ℤ).tsum_eq (fun n => ω n ^ 2 * ‖f n‖ ^ 2)]
  refine tsum_congr fun n => ?_
  simp [cstar, hω]

/-- `‖((f*g)*k)_n‖ ≤ ((|f|*|g|)*|k|)_n`. -/
theorem norm_conv_conv_le38 {f g k : ℤ → ℂ} (hf : IsL1 f) (hg : IsL1 g) (hk : IsL1 k) (n : ℤ) :
    ‖conv (conv f g) k n‖ ≤ convR (convR (fun a => ‖f a‖) (fun a => ‖g a‖)) (fun a => ‖k a‖) n := by
  have hP : IsL1 (conv f g) := (isL1_conv hf hg).1
  refine (norm_conv_le (summable_norm_conv_term hP hk n)).trans ?_
  have hFG1 : Summable (convR (fun a => ‖f a‖) fun a => ‖g a‖) :=
    summable_convR hf hg (norm_nonneg_fun f) (norm_nonneg_fun g)
  have hFG0 : 0 ≤ convR (fun a => ‖f a‖) fun a => ‖g a‖ :=
    fun c => convR_nonneg (norm_nonneg_fun f) (norm_nonneg_fun g) c
  have hP1 : Summable fun c => ‖conv f g c‖ := hP
  unfold convR
  refine Summable.tsum_le_tsum (fun c => ?_) ?_ ?_
  · exact mul_le_mul_of_nonneg_right (norm_conv_le (summable_norm_conv_term hf hg c))
      (norm_nonneg _)
  · exact summable_convR_slice hP1 hk (fun c => norm_nonneg _) (norm_nonneg_fun k) n
  · exact summable_convR_slice hFG1 hk hFG0 (norm_nonneg_fun k) n

/-- **Weighted trilinear estimate** (plan §7, A1). -/
theorem wl2_trilinear {C : ℝ} {ω : ℤ → ℝ} (hω : AdmWeight C ω) {f g h : ℤ → ℂ}
    (hf : IsL1 f) (hg : IsL1 g) (hh : IsL1 h)
    (hf2 : Summable fun n => ω n ^ 2 * ‖f n‖ ^ 2) (hg2 : Summable fun n => ω n ^ 2 * ‖g n‖ ^ 2)
    (hh2 : Summable fun n => ω n ^ 2 * ‖h n‖ ^ 2) :
    Summable (fun n => ω n ^ 2 * ‖conv (conv f g) (cstar h) n‖ ^ 2) ∧
    wl2 ω (conv (conv f g) (cstar h)) ≤
      C * (wl2 ω f * l1 g * l1 h + l1 f * wl2 ω g * l1 h + l1 f * l1 g * wl2 ω h) := by
  rcases lt_or_ge C 0 with hC | hC
  · have hz := hω.eq_zero_of_neg hC
    simp [wl2, hz]
  have hk : IsL1 (cstar h) := (isL1_cstar_iff h).2 hh
  have hk2 := summable_wsq_cstar38 hω.2.1 hh2
  have hR := trilinear_real38 (C := C) (ω := ω) (p := fun n => ‖f n‖) (q := fun n => ‖g n‖)
    (r := fun n => ‖cstar h n‖) hC hω (norm_nonneg_fun f) (norm_nonneg_fun g)
    (norm_nonneg_fun (cstar h)) hf hg hk ((summable_wsq_iff38 ω f).1 hf2)
    ((summable_wsq_iff38 ω g).1 hg2) ((summable_wsq_iff38 ω (cstar h)).1 hk2)
  obtain ⟨hs, hb⟩ := hR
  have hpt : ∀ n, ω n ^ 2 * ‖conv (conv f g) (cstar h) n‖ ^ 2 ≤
      (ω n * convR (convR (fun a => ‖f a‖) (fun a => ‖g a‖)) (fun a => ‖cstar h a‖) n) ^ 2 := by
    intro n
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg (hω.1 n) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (norm_conv_conv_le38 hf hg hk n) (hω.1 n)) 2
  have hsum : Summable (fun n => ω n ^ 2 * ‖conv (conv f g) (cstar h) n‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hpt hs
  refine ⟨hsum, ?_⟩
  have e2 : Real.sqrt (∑' n, (ω n * ‖cstar h n‖) ^ 2) = wl2 ω h := by
    rw [← wl2_cstar38 hω.2.1 h, wl2_eq_sqrt38]
  have l1e : l1 (cstar h) = l1 h := (l1_cstar h).1
  have e1 : Real.sqrt (∑' n, (ω n * ‖f n‖) ^ 2) = wl2 ω f := (wl2_eq_sqrt38 ω f).symm
  have e3 : Real.sqrt (∑' n, (ω n * ‖g n‖) ^ 2) = wl2 ω g := (wl2_eq_sqrt38 ω g).symm
  rw [e1, e3, e2] at hb
  have hl1 : (∑' k, ‖cstar h k‖) = l1 h := l1e
  rw [hl1] at hb
  refine (Real.sqrt_le_sqrt (hsum.tsum_le_tsum hpt hs)).trans hb

/-! ## The weights -/

theorem jb_abs_le38 (x : ℝ) : |x| ≤ Real.sqrt (1 + x ^ 2) :=
  Real.abs_le_sqrt (by nlinarith [sq_nonneg x])

theorem jb_add_abs_le38 (x y : ℝ) :
    Real.sqrt (1 + (x + y) ^ 2) ≤ Real.sqrt (1 + x ^ 2) + |y| := by
  rw [Real.sqrt_le_iff]
  have hs := Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)
  have hs0 := Real.sqrt_nonneg (1 + x ^ 2)
  have hx := jb_abs_le38 x
  refine ⟨by positivity, ?_⟩
  have h1 : x * y ≤ Real.sqrt (1 + x ^ 2) * |y| := by
    calc x * y ≤ |x * y| := le_abs_self _
      _ = |x| * |y| := abs_mul _ _
      _ ≤ Real.sqrt (1 + x ^ 2) * |y| := mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  nlinarith [sq_abs y]

theorem japaneseBracket_add_sub_le38 (a b c : ℤ) :
    japaneseBracket (a + b - c) ≤ japaneseBracket a + japaneseBracket b + japaneseBracket c := by
  have h1 : (((a + b - c : ℤ)) : ℝ) = (a : ℝ) + ((b : ℝ) - c) := by push_cast; ring
  have h2 : japaneseBracket (a + b - c) ≤ japaneseBracket a + |(b : ℝ) - c| := by
    unfold japaneseBracket
    rw [h1]
    exact jb_add_abs_le38 _ _
  have h3 : |(b : ℝ) - c| ≤ |(b : ℝ)| + |(c : ℝ)| := abs_sub _ _
  have h4 : |(b : ℝ)| ≤ japaneseBracket b := jb_abs_le38 _
  have h5 : |(c : ℝ)| ≤ japaneseBracket c := jb_abs_le38 _
  linarith

theorem three_pow_le38 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (k : ℕ) :
    (x + y + z) ^ (k + 1) ≤ 3 ^ k * (x ^ (k + 1) + y ^ (k + 1) + z ^ (k + 1)) := by
  have h := pow_sum_div_card_le_sum_pow (s := (Finset.univ : Finset (Fin 3)))
    (f := ![x, y, z]) (by intro i _; fin_cases i <;> simp [hx, hy, hz]) k
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp, Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at h
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  rw [div_le_iff₀ h3] at h
  change (x + y + z) ^ (k + 1) ≤ (x ^ (k + 1) + y ^ (k + 1) + z ^ (k + 1)) * 3 ^ k at h
  linarith

/-- Powers of a subadditive even nonnegative base are admissible. -/
theorem admWeight_of_base38 (m : ℕ) (hm : 1 ≤ m) (φ : ℤ → ℝ) (h0 : ∀ n, 0 ≤ φ n)
    (hneg : ∀ n, φ (-n) = φ n) (hsub : ∀ a b c, φ (a + b - c) ≤ φ a + φ b + φ c) :
    AdmWeight (3 ^ (m - 1)) (fun n => φ n ^ m) := by
  refine ⟨fun n => pow_nonneg (h0 n) _, fun n => by simp [hneg], fun a b c => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  calc φ (a + b - c) ^ (k + 1) ≤ (φ a + φ b + φ c) ^ (k + 1) :=
        pow_le_pow_left₀ (h0 _) (hsub a b c) _
    _ ≤ _ := three_pow_le38 _ _ _ (h0 a) (h0 b) (h0 c) k

theorem admWeight_pow (m : ℕ) (hm : 1 ≤ m) :
    AdmWeight (3 ^ (m - 1)) (fun n => japaneseBracket n ^ m) :=
  admWeight_of_base38 m hm (fun n => japaneseBracket n) (fun n => (japaneseBracket_pos n).le)
    japaneseBracket_neg japaneseBracket_add_sub_le38

theorem min_add3_le38 (s x y z K : ℝ) (hs : s ≤ x + y + z) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (hK : 0 ≤ K) : min s K ≤ min x K + min y K + min z K := by
  simp only [min_def]
  split_ifs <;> linarith

/-- The frequency-truncated weight `min(⟨n⟩, K)^m`. -/
def wK (m K : ℕ) (n : ℤ) : ℝ := (min (japaneseBracket n) (K : ℝ)) ^ m

theorem admWeight_trunc (m K : ℕ) (hm : 1 ≤ m) :
    AdmWeight (3 ^ (m - 1)) (fun n => (min (japaneseBracket n) K) ^ m) :=
  admWeight_of_base38 m hm (fun n => min (japaneseBracket n) (K : ℝ))
    (fun n => le_min (japaneseBracket_pos n).le (Nat.cast_nonneg K))
    (fun n => by rw [japaneseBracket_neg])
    (fun a b c => min_add3_le38 _ _ _ _ _ (japaneseBracket_add_sub_le38 a b c)
      (japaneseBracket_pos a).le (japaneseBracket_pos b).le (japaneseBracket_pos c).le
      (Nat.cast_nonneg K))

theorem admWeight_wK (m K : ℕ) (hm : 1 ≤ m) : AdmWeight (3 ^ (m - 1)) (wK m K) :=
  admWeight_trunc m K hm

theorem wK_le_pow (m K : ℕ) (n : ℤ) : wK m K n ≤ japaneseBracket n ^ m :=
  pow_le_pow_left₀ (le_min (japaneseBracket_pos n).le (Nat.cast_nonneg K)) (min_le_left _ _) m

theorem wK_le_K (m K : ℕ) (n : ℤ) : wK m K n ≤ (K : ℝ) ^ m :=
  pow_le_pow_left₀ (le_min (japaneseBracket_pos n).le (Nat.cast_nonneg K)) (min_le_right _ _) m

theorem wK_nonneg (m K : ℕ) (n : ℤ) : 0 ≤ wK m K n :=
  pow_nonneg (le_min (japaneseBracket_pos n).le (Nat.cast_nonneg K)) m

/-! ## `hn` as a weighted norm and cast bridges -/

theorem pow_sq_eq38 (n : ℤ) (m : ℕ) : (japaneseBracket n ^ m) ^ 2 = japaneseBracket n ^ (2 * m) := by
  rw [← pow_mul, mul_comm]

theorem hn_eq_wl2_38 (m : ℕ) (x : ℤ → ℂ) : hn m x = wl2 (fun n => japaneseBracket n ^ m) x := by
  unfold hn wl2
  simp only [pow_sq_eq38]

theorem mem_seqSobolev_nat_iff38 (m : ℕ) (x : ℤ → ℂ) :
    x ∈ seqSobolev38 (m : ℝ) ↔ Summable fun n => japaneseBracket n ^ (2 * m) * ‖x n‖ ^ 2 := by
  rw [mem_seqSobolev38_iff]
  unfold SobolevSquareSummable
  have e : ∀ n : ℤ, Real.rpow (japaneseBracket n) (2 * (m : ℝ)) = japaneseBracket n ^ (2 * m) :=
    fun n => sobolevModeWeight_natCast_eq m n
  simp only [e]

theorem mem_seqSobolev_nat_iff_wsq38 (m : ℕ) (x : ℤ → ℂ) :
    x ∈ seqSobolev38 (m : ℝ) ↔
      Summable fun n => (fun n => japaneseBracket n ^ m) n ^ 2 * ‖x n‖ ^ 2 := by
  rw [mem_seqSobolev_nat_iff38]
  simp only [pow_sq_eq38]

/-- Cast bridge (review note N4): `ℓ¹ ≤ C₁ h¹` at the cast index `((1:ℕ):ℝ)`. -/
theorem isL1_of_h1_nat (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    IsL1 x ∧ l1 x ≤ C1 * ‖carrierMk38 ((1 : ℕ) : ℝ) x hx‖ := by
  rw [norm_carrierMk38_eq_hn 1 x hx]
  exact isL1_of_hn_one x hx

/-- `h^m ⊆ h^1` at cast indices. -/
theorem mem_h1_of_mem_nat (m : ℕ) (hm : 1 ≤ m) {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 (m : ℝ)) :
    x ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
  seqSobolev38_mono (by exact_mod_cast hm) hx

/-- `h^1` data have `ω² |x|²` summable for every truncated weight. -/
theorem summable_wK_of_h1 (m K : ℕ) {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    Summable fun n => wK m K n ^ 2 * ‖x n‖ ^ 2 := by
  have h1 := (mem_seqSobolev_nat_iff38 1 x).1 hx
  have h2 : Summable fun n => ((K : ℝ) ^ m) ^ 2 * (japaneseBracket n ^ (2 * 1) * ‖x n‖ ^ 2) :=
    h1.mul_left _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h2
  have hb : 1 ≤ japaneseBracket n ^ (2 * 1) := one_le_pow₀ (japaneseBracket_one_le n)
  have hw : wK m K n ^ 2 ≤ ((K : ℝ) ^ m) ^ 2 :=
    pow_le_pow_left₀ (wK_nonneg m K n) (wK_le_K m K n) 2
  calc wK m K n ^ 2 * ‖x n‖ ^ 2 ≤ ((K : ℝ) ^ m) ^ 2 * ‖x n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ ≤ ((K : ℝ) ^ m) ^ 2 * (japaneseBracket n ^ (2 * 1) * ‖x n‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        nlinarith [sq_nonneg ‖x n‖]

/-! ## `wl2` calculus -/

theorem wl2_smul38 (ω : ℤ → ℝ) (c : ℂ) (f : ℤ → ℂ) : wl2 ω (c • f) = ‖c‖ * wl2 ω f := by
  unfold wl2
  have : ∀ n, ω n ^ 2 * ‖(c • f) n‖ ^ 2 = ‖c‖ ^ 2 * (ω n ^ 2 * ‖f n‖ ^ 2) := fun n => by
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]; ring
  simp only [this]
  rw [tsum_mul_left, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem summable_wsq_smul38 (ω : ℤ → ℝ) (c : ℂ) {f : ℤ → ℂ}
    (hf : Summable fun n => ω n ^ 2 * ‖f n‖ ^ 2) :
    Summable fun n => ω n ^ 2 * ‖(c • f) n‖ ^ 2 := by
  have := hf.mul_left (‖c‖ ^ 2)
  refine this.congr fun n => ?_
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]; ring

/-- Domination by three sequences, in `wl2`. -/
theorem wl2_of_le_add3_38 {ω : ℤ → ℝ} (hω : ∀ n, 0 ≤ ω n) {F f1 f2 f3 : ℤ → ℂ}
    (hF : ∀ n, ‖F n‖ ≤ ‖f1 n‖ + ‖f2 n‖ + ‖f3 n‖)
    (h1 : Summable fun n => ω n ^ 2 * ‖f1 n‖ ^ 2) (h2 : Summable fun n => ω n ^ 2 * ‖f2 n‖ ^ 2)
    (h3 : Summable fun n => ω n ^ 2 * ‖f3 n‖ ^ 2) :
    Summable (fun n => ω n ^ 2 * ‖F n‖ ^ 2) ∧ wl2 ω F ≤ wl2 ω f1 + wl2 ω f2 + wl2 ω f3 := by
  obtain ⟨hs, hb⟩ := minkowski3_38 (a := fun n => ω n * ‖f1 n‖) (b := fun n => ω n * ‖f2 n‖)
    (c := fun n => ω n * ‖f3 n‖) (fun n => mul_nonneg (hω n) (norm_nonneg _))
    (fun n => mul_nonneg (hω n) (norm_nonneg _)) (fun n => mul_nonneg (hω n) (norm_nonneg _))
    ((summable_wsq_iff38 ω f1).1 h1) ((summable_wsq_iff38 ω f2).1 h2) ((summable_wsq_iff38 ω f3).1 h3)
  have hpt : ∀ n, ω n ^ 2 * ‖F n‖ ^ 2 ≤
      (ω n * ‖f1 n‖ + ω n * ‖f2 n‖ + ω n * ‖f3 n‖) ^ 2 := by
    intro n
    rw [← mul_pow]
    refine pow_le_pow_left₀ (mul_nonneg (hω n) (norm_nonneg _)) ?_ 2
    calc ω n * ‖F n‖ ≤ ω n * (‖f1 n‖ + ‖f2 n‖ + ‖f3 n‖) :=
          mul_le_mul_of_nonneg_left (hF n) (hω n)
      _ = _ := by ring
  have hsum : Summable (fun n => ω n ^ 2 * ‖F n‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hpt hs
  refine ⟨hsum, ?_⟩
  calc wl2 ω F ≤ Real.sqrt (∑' n, (ω n * ‖f1 n‖ + ω n * ‖f2 n‖ + ω n * ‖f3 n‖) ^ 2) :=
        Real.sqrt_le_sqrt (hsum.tsum_le_tsum hpt hs)
    _ ≤ _ := by
        refine hb.trans (le_of_eq ?_)
        simp only [wl2_eq_sqrt38]

/-- Domination by two sequences, in `wl2`. -/
theorem wl2_of_le_add2_38 {ω : ℤ → ℝ} (hω : ∀ n, 0 ≤ ω n) {F f1 f2 : ℤ → ℂ}
    (hF : ∀ n, ‖F n‖ ≤ ‖f1 n‖ + ‖f2 n‖)
    (h1 : Summable fun n => ω n ^ 2 * ‖f1 n‖ ^ 2) (h2 : Summable fun n => ω n ^ 2 * ‖f2 n‖ ^ 2) :
    Summable (fun n => ω n ^ 2 * ‖F n‖ ^ 2) ∧ wl2 ω F ≤ wl2 ω f1 + wl2 ω f2 := by
  obtain ⟨hs, hb⟩ := minkowski2_38 (a := fun n => ω n * ‖f1 n‖) (b := fun n => ω n * ‖f2 n‖)
    (fun n => mul_nonneg (hω n) (norm_nonneg _)) (fun n => mul_nonneg (hω n) (norm_nonneg _))
    ((summable_wsq_iff38 ω f1).1 h1) ((summable_wsq_iff38 ω f2).1 h2)
  have hpt : ∀ n, ω n ^ 2 * ‖F n‖ ^ 2 ≤ (ω n * ‖f1 n‖ + ω n * ‖f2 n‖) ^ 2 := by
    intro n
    rw [← mul_pow]
    refine pow_le_pow_left₀ (mul_nonneg (hω n) (norm_nonneg _)) ?_ 2
    calc ω n * ‖F n‖ ≤ ω n * (‖f1 n‖ + ‖f2 n‖) := mul_le_mul_of_nonneg_left (hF n) (hω n)
      _ = _ := by ring
  have hsum : Summable (fun n => ω n ^ 2 * ‖F n‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hpt hs
  refine ⟨hsum, ?_⟩
  calc wl2 ω F ≤ Real.sqrt (∑' n, (ω n * ‖f1 n‖ + ω n * ‖f2 n‖) ^ 2) :=
        Real.sqrt_le_sqrt (hsum.tsum_le_tsum hpt hs)
    _ ≤ _ := by
        refine hb.trans (le_of_eq ?_)
        simp only [wl2_eq_sqrt38]

theorem summable_wsq_sub38 {ω : ℤ → ℝ} (hω : ∀ n, 0 ≤ ω n) {f g : ℤ → ℂ}
    (hf : Summable fun n => ω n ^ 2 * ‖f n‖ ^ 2) (hg : Summable fun n => ω n ^ 2 * ‖g n‖ ^ 2) :
    Summable fun n => ω n ^ 2 * ‖(f - g) n‖ ^ 2 :=
  (wl2_of_le_add2_38 hω (F := f - g) (fun n => by simpa using norm_sub_le (f n) (g n)) hf hg).1

end NlsGge.NLS38
