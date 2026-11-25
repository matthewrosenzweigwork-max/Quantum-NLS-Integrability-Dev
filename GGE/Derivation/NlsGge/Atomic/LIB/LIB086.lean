import NlsGge.Atomic.DM.DM046
import NlsGge.Atomic.LIB.LIB007

set_option autoImplicit false

open scoped ENNReal

noncomputable section

namespace NlsGge.Atomic.LIB086

lemma ofReal_rpow_two {x : ℝ} (hx : 0 ≤ x) :
    ENNReal.ofReal x ^ (2 : ℝ) = ENNReal.ofReal (x ^ 2) := by
  rw [ENNReal.ofReal_rpow_of_nonneg hx (by norm_num), Real.rpow_two]

lemma summable_of_tsum_ofReal_ne_top {f : ℤ → ℝ} (h0 : ∀ n, 0 ≤ f n)
    (h : ∑' n : ℤ, ENNReal.ofReal (f n) ≠ ⊤) : Summable f :=
  (ENNReal.summable_toReal h).congr (fun n => ENNReal.toReal_ofReal (h0 n))

lemma zero_of_weighted_eq_zero {w : ℝ} (hw : 0 < w) {z : ℂ} (h : w * ‖z‖ = 0) : z = 0 := by
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h hw.ne'
  · exact norm_eq_zero.mp h

lemma weighted_zero_of_tsum_zero {w : ℤ → ℝ} (hwpos : ∀ n, 0 < w n) {x : ℤ → ℂ}
    (h : ∑' n : ℤ, ENNReal.ofReal (w n * ‖x n‖) = 0) : ∀ n, x n = 0 := by
  intro n
  have h0 := (ENNReal.tsum_eq_zero.mp h) n
  have hle : w n * ‖x n‖ ≤ 0 := ENNReal.ofReal_eq_zero.mp h0
  have heq : w n * ‖x n‖ = 0 :=
    le_antisymm hle (mul_nonneg (hwpos n).le (norm_nonneg _))
  exact zero_of_weighted_eq_zero (hwpos n) heq

lemma tsum_eq_zero_of_rpow_half {X : ENNReal} (h : X ^ ((1 : ℝ) / 2) = 0) : X = 0 := by
  rcases ENNReal.rpow_eq_zero_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact h1
  · norm_num at h2

lemma weighted_zero_of_tsum_rpow_zero {w : ℤ → ℝ} (hwpos : ∀ n, 0 < w n) {x : ℤ → ℂ}
    (h : (∑' n : ℤ, ENNReal.ofReal (w n * ‖x n‖) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) = 0) :
    ∀ n, x n = 0 := by
  have h' := tsum_eq_zero_of_rpow_half h
  intro n
  have h0 := (ENNReal.tsum_eq_zero.mp h') n
  have hx : ENNReal.ofReal (w n * ‖x n‖) ^ (2 : ℝ) = 0 := h0
  rw [ofReal_rpow_two (mul_nonneg (hwpos n).le (norm_nonneg _))] at hx
  have hle : (w n * ‖x n‖) ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.mp hx
  have hsq : (w n * ‖x n‖) ^ 2 = 0 := le_antisymm hle (sq_nonneg _)
  have hz : w n * ‖x n‖ = 0 := pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hsq
  exact zero_of_weighted_eq_zero (hwpos n) hz

lemma conv_eq_zero_of_left {a b : ℤ → ℂ} (ha : ∀ n, a n = 0) (n : ℤ) :
    NlsGge.NLS38.conv a b n = 0 := by
  unfold NlsGge.NLS38.conv
  simp [ha]

lemma conv_eq_zero_of_right {a b : ℤ → ℂ} (hb : ∀ n, b n = 0) (n : ℤ) :
    NlsGge.NLS38.conv a b n = 0 := by
  unfold NlsGge.NLS38.conv
  simp [hb]

/-- Summability of the convolution of an l1 nonnegative sequence with a bounded
nonnegative sequence. -/
lemma summable_prod_of_l1_bdd {A B : ℤ → ℝ} (hA : Summable A) (hA0 : ∀ n, 0 ≤ A n)
    (hB0 : ∀ n, 0 ≤ B n) (M : ℝ) (hM : ∀ n, B n ≤ M) (m : ℤ) :
    Summable (fun k : ℤ => A k * B (m - k)) := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (hA0 k) (hB0 _)) (fun k => ?_)
    (hA.mul_right M)
  exact mul_le_mul_of_nonneg_left (hM _) (hA0 k)

/-- Pointwise domination of the weighted convolution by the nonnegative convolution
of the weighted sequences, using submultiplicativity of `w`. -/
lemma domination (w : ℤ → ℝ) (hwpos : ∀ n, 0 < w n)
    (hw : NlsGge.Atomic.DM046.SubmultiplicativeWeight w) (a b : ℤ → ℂ) (n : ℤ)
    (hs : Summable (fun k : ℤ => w k * ‖a k‖ * (w (n - k) * ‖b (n - k)‖))) :
    w n * ‖NlsGge.NLS38.conv a b n‖ ≤
      ∑' k : ℤ, w k * ‖a k‖ * (w (n - k) * ‖b (n - k)‖) := by
  have hterm : ∀ k : ℤ, ‖w n * (a k * b (n - k))‖ ≤
      w k * ‖a k‖ * (w (n - k) * ‖b (n - k)‖) := by
    intro k
    have hsub : w n ≤ w k * w (n - k) := by
      have h := hw k (n - k)
      simpa using h
    have h0 : 0 ≤ ‖a k‖ * ‖b (n - k)‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    rw [norm_mul, norm_mul, Complex.norm_of_nonneg (hwpos n).le]
    calc w n * (‖a k‖ * ‖b (n - k)‖)
        ≤ (w k * w (n - k)) * (‖a k‖ * ‖b (n - k)‖) :=
          mul_le_mul_of_nonneg_right hsub h0
      _ = w k * ‖a k‖ * (w (n - k) * ‖b (n - k)‖) := by ring
  have hnorm_summable : Summable (fun k : ℤ => ‖w n * (a k * b (n - k))‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hterm hs
  calc w n * ‖∑' k : ℤ, a k * b (n - k)‖
      = ‖w n * ∑' k : ℤ, a k * b (n - k)‖ := by
        rw [norm_mul, Complex.norm_of_nonneg (hwpos n).le]
    _ = ‖∑' k : ℤ, w n * (a k * b (n - k))‖ := by rw [tsum_mul_left]
    _ ≤ ∑' k : ℤ, ‖w n * (a k * b (n - k))‖ := norm_tsum_le_tsum_norm hnorm_summable
    _ ≤ ∑' k : ℤ, w k * ‖a k‖ * (w (n - k) * ‖b (n - k)‖) :=
        Summable.tsum_le_tsum hterm hnorm_summable hs

theorem weighted_young_l1_l2 :
    ∀ (w : ℤ → ℝ) (a b : ℤ → ℂ),
      (∀ n : ℤ, 0 < w n) →
      NlsGge.Atomic.DM046.SubmultiplicativeWeight w →
      let L1 : (ℤ → ℂ) → ENNReal := fun x => ∑' n : ℤ, ENNReal.ofReal (w n * ‖x n‖)
      let L2 : (ℤ → ℂ) → ENNReal := fun x =>
        (∑' n : ℤ, ENNReal.ofReal (w n * ‖x n‖) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      L2 (NlsGge.NLS38.conv a b) ≤ L1 a * L2 b := by
  intro w a b hwpos hw
  dsimp only
  by_cases h1 : (∑' n : ℤ, ENNReal.ofReal (w n * ‖a n‖)) = 0
  · have ha := weighted_zero_of_tsum_zero hwpos h1
    simp [conv_eq_zero_of_left ha]
  by_cases h2 : (∑' n : ℤ, ENNReal.ofReal (w n * ‖b n‖) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) = 0
  · have hb := weighted_zero_of_tsum_rpow_zero hwpos h2
    simp [conv_eq_zero_of_right hb]
  by_cases h3 : (∑' n : ℤ, ENNReal.ofReal (w n * ‖a n‖)) = ⊤
  · rw [h3, ENNReal.top_mul h2]
    exact le_top
  by_cases h4 : (∑' n : ℤ, ENNReal.ofReal (w n * ‖b n‖) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) = ⊤
  · rw [h4, ENNReal.mul_top h1]
    exact le_top
  -- Main case: both factors finite and nonzero.
  have hS2base : (∑' n : ℤ, ENNReal.ofReal (w n * ‖b n‖) ^ (2 : ℝ)) ≠ ⊤ := by
    intro htop
    apply h4
    rw [htop, ENNReal.top_rpow_of_pos (by norm_num)]
  have hA0 : ∀ n, 0 ≤ w n * ‖a n‖ := fun n => mul_nonneg (hwpos n).le (norm_nonneg _)
  have hB0 : ∀ n, 0 ≤ w n * ‖b n‖ := fun n => mul_nonneg (hwpos n).le (norm_nonneg _)
  have hAs : Summable (fun n : ℤ => w n * ‖a n‖) :=
    summable_of_tsum_ofReal_ne_top (f := fun n : ℤ => w n * ‖a n‖) hA0 h3
  have hsq_eq : (∑' n : ℤ, ENNReal.ofReal (w n * ‖b n‖) ^ (2 : ℝ))
      = ∑' n : ℤ, ENNReal.ofReal ((w n * ‖b n‖) ^ 2) :=
    tsum_congr (fun n => ofReal_rpow_two (hB0 n))
  have hBsq : Summable (fun n : ℤ => (w n * ‖b n‖) ^ 2) := by
    apply summable_of_tsum_ofReal_ne_top (f := fun n : ℤ => (w n * ‖b n‖) ^ 2)
      (fun n => sq_nonneg _)
    rw [← hsq_eq]
    exact hS2base
  have hM : ∀ n : ℤ, w n * ‖b n‖ ≤ Real.sqrt (∑' k : ℤ, (w k * ‖b k‖) ^ 2) :=
    fun n => le_trans (le_abs_self _)
      (Real.abs_le_sqrt (hBsq.le_tsum n (fun j _ => sq_nonneg _)))
  have hprod : ∀ m : ℤ, Summable (fun k : ℤ => w k * ‖a k‖ * (w (m - k) * ‖b (m - k)‖)) :=
    fun m => summable_prod_of_l1_bdd (A := fun n : ℤ => w n * ‖a n‖)
      (B := fun n : ℤ => w n * ‖b n‖) hAs hA0 hB0 _ hM m
  have hdom : ∀ n : ℤ, w n * ‖NlsGge.NLS38.conv a b n‖ ≤
      ∑' k : ℤ, w k * ‖a k‖ * (w (n - k) * ‖b (n - k)‖) :=
    fun n => domination w hwpos hw a b n (hprod n)
  -- Young bound for the nonnegative sequences A = w|a|, B = w|b| (accepted LIB-007).
  have hfL1 : NlsGge.NLS38.IsL1 (fun k : ℤ => ((w k * ‖a k‖ : ℝ) : ℂ)) :=
    hAs.congr (fun n => (Complex.norm_of_nonneg (hA0 n)).symm)
  have hgL2 : Summable (fun n : ℤ => ‖((w n * ‖b n‖ : ℝ) : ℂ)‖ ^ 2) :=
    hBsq.congr (fun n => by rw [Complex.norm_of_nonneg (hB0 n)])
  obtain ⟨hsumC, hYoung⟩ := NlsGge.Atomic.LIB007.convolution_l1_l2_bound hfL1 hgL2
  have hconvnorm : ∀ n : ℤ,
      ‖NlsGge.NLS38.conv (fun k : ℤ => ((w k * ‖a k‖ : ℝ) : ℂ))
          (fun k : ℤ => ((w k * ‖b k‖ : ℝ) : ℂ)) n‖
        = ∑' k : ℤ, w k * ‖a k‖ * (w (n - k) * ‖b (n - k)‖) := by
    intro n
    have hT : NlsGge.NLS38.conv (fun k : ℤ => ((w k * ‖a k‖ : ℝ) : ℂ))
        (fun k : ℤ => ((w k * ‖b k‖ : ℝ) : ℂ)) n
        = ((∑' k : ℤ, w k * ‖a k‖ * (w (n - k) * ‖b (n - k)‖) : ℝ) : ℂ) := by
      unfold NlsGge.NLS38.conv
      rw [Complex.ofReal_tsum]
      congr 1
      funext k
      simp only [Complex.ofReal_mul]
    rw [hT, Complex.norm_of_nonneg
      (tsum_nonneg (fun k : ℤ => mul_nonneg (hA0 k) (hB0 (n - k))))]
  have hdom' : ∀ n : ℤ, w n * ‖NlsGge.NLS38.conv a b n‖ ≤
      ‖NlsGge.NLS38.conv (fun k : ℤ => ((w k * ‖a k‖ : ℝ) : ℂ))
          (fun k : ℤ => ((w k * ‖b k‖ : ℝ) : ℂ)) n‖ := by
    intro n
    rw [hconvnorm n]
    exact hdom n
  have hL : (∑' n : ℤ, ENNReal.ofReal (w n * ‖NlsGge.NLS38.conv a b n‖) ^ (2 : ℝ))
      ≤ ∑' n : ℤ, ENNReal.ofReal
          (‖NlsGge.NLS38.conv (fun k : ℤ => ((w k * ‖a k‖ : ℝ) : ℂ))
            (fun k : ℤ => ((w k * ‖b k‖ : ℝ) : ℂ)) n‖) ^ (2 : ℝ) :=
    ENNReal.tsum_le_tsum (fun n =>
      ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hdom' n)) (by norm_num))
  have hR : (∑' n : ℤ, ENNReal.ofReal
          (‖NlsGge.NLS38.conv (fun k : ℤ => ((w k * ‖a k‖ : ℝ) : ℂ))
            (fun k : ℤ => ((w k * ‖b k‖ : ℝ) : ℂ)) n‖) ^ (2 : ℝ))
      = ENNReal.ofReal (∑' n : ℤ,
          ‖NlsGge.NLS38.conv (fun k : ℤ => ((w k * ‖a k‖ : ℝ) : ℂ))
            (fun k : ℤ => ((w k * ‖b k‖ : ℝ) : ℂ)) n‖ ^ 2) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hsumC]
    exact tsum_congr (fun n => ofReal_rpow_two (norm_nonneg _))
  have hl1nn : 0 ≤ NlsGge.NLS38.l1 (fun k : ℤ => ((w k * ‖a k‖ : ℝ) : ℂ)) := by
    unfold NlsGge.NLS38.l1
    exact tsum_nonneg (fun n => norm_nonneg _)
  have hl1 : NlsGge.NLS38.l1 (fun k : ℤ => ((w k * ‖a k‖ : ℝ) : ℂ))
      = ∑' n : ℤ, w n * ‖a n‖ := by
    unfold NlsGge.NLS38.l1
    exact tsum_congr (fun n => Complex.norm_of_nonneg (hA0 n))
  have hS1 : (∑' n : ℤ, ENNReal.ofReal (w n * ‖a n‖))
      = ENNReal.ofReal (∑' n : ℤ, w n * ‖a n‖) :=
    (ENNReal.ofReal_tsum_of_nonneg hA0 hAs).symm
  have hS2 : (∑' n : ℤ, ENNReal.ofReal (w n * ‖b n‖) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      = ENNReal.ofReal (Real.sqrt (∑' n : ℤ, (w n * ‖b n‖) ^ 2)) := by
    rw [hsq_eq, ← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hBsq,
      ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg (fun n => sq_nonneg _)) (by norm_num),
      Real.sqrt_eq_rpow]
  have hgsq : (∑' n : ℤ, ‖((w n * ‖b n‖ : ℝ) : ℂ)‖ ^ 2) = ∑' n : ℤ, (w n * ‖b n‖) ^ 2 :=
    tsum_congr (fun n => by rw [Complex.norm_of_nonneg (hB0 n)])
  calc (∑' n : ℤ, ENNReal.ofReal (w n * ‖NlsGge.NLS38.conv a b n‖) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      ≤ (∑' n : ℤ, ENNReal.ofReal
          (‖NlsGge.NLS38.conv (fun k : ℤ => ((w k * ‖a k‖ : ℝ) : ℂ))
            (fun k : ℤ => ((w k * ‖b k‖ : ℝ) : ℂ)) n‖) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow hL (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt (∑' n : ℤ,
          ‖NlsGge.NLS38.conv (fun k : ℤ => ((w k * ‖a k‖ : ℝ) : ℂ))
            (fun k : ℤ => ((w k * ‖b k‖ : ℝ) : ℂ)) n‖ ^ 2)) := by
        rw [hR, ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg (fun n => sq_nonneg _))
          (by norm_num), Real.sqrt_eq_rpow]
    _ ≤ ENNReal.ofReal (NlsGge.NLS38.l1 (fun k : ℤ => ((w k * ‖a k‖ : ℝ) : ℂ)) *
          Real.sqrt (∑' n : ℤ, ‖((w n * ‖b n‖ : ℝ) : ℂ)‖ ^ 2)) :=
        ENNReal.ofReal_le_ofReal hYoung
    _ = ENNReal.ofReal (NlsGge.NLS38.l1 (fun k : ℤ => ((w k * ‖a k‖ : ℝ) : ℂ))) *
          ENNReal.ofReal (Real.sqrt (∑' n : ℤ, ‖((w n * ‖b n‖ : ℝ) : ℂ)‖ ^ 2)) :=
        ENNReal.ofReal_mul hl1nn
    _ = (∑' n : ℤ, ENNReal.ofReal (w n * ‖a n‖)) *
          ((∑' n : ℤ, ENNReal.ofReal (w n * ‖b n‖) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) := by
        rw [hl1, hgsq, hS1, hS2]


end NlsGge.Atomic.LIB086
