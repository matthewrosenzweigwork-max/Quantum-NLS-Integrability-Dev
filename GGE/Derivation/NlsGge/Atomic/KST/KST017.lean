import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Int.Lemmas

-- KST-017 COMBINED candidate (proof development): Part A (proof development KST-017_PROOF08.lean.txt, request e26ff6e2 per root)
-- and Part B v2 (proof development KST017_PARTB_SPLIT02.lean.txt, default heartbeats, request 25c9796a), in one namespace.
-- Statements are the owner-approved heads from KST-017_COMMAND01.lean.txt. Not accepted; not yet independently reviewed.

set_option autoImplicit false
noncomputable section

namespace NlsGge.Atomic.KST


open scoped ENNReal

private lemma lp_sq_summable' (x : lp (fun _ : ℤ => ℝ) 2) :
    Summable (fun n : ℤ => (x n) ^ 2) := by
  have h := (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simpa [Real.norm_eq_abs, sq_abs] using h

private lemma lp_norm_sq' (x : lp (fun _ : ℤ => ℝ) 2) :
    ‖x‖ ^ 2 = ∑' n : ℤ, (x n) ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x
  simpa [Real.norm_eq_abs, sq_abs] using h

/-- Integer difference squared is at least one. -/
private lemma one_le_sq_int_cast (d : ℤ) (hd : d ≠ 0) : (1 : ℝ) ≤ ((d : ℤ) : ℝ) ^ 2 := by
  rw [one_le_sq_iff_one_le_abs]
  exact_mod_cast Int.one_le_abs hd

/-- If `|n+k| < |n|` then `|n| ≤ |n-k|` (squared form in `ℤ`). -/
private lemma sq_le_of_abs_lt {n k : ℤ} (h : (n + k).natAbs < n.natAbs) :
    n ^ 2 ≤ (n - k) ^ 2 := by
  have h2 : (n + k) ^ 2 < n ^ 2 := Int.natAbs_lt_iff_sq_lt.1 h
  have e1 : (n + k) ^ 2 = n ^ 2 + 2 * (n * k) + k ^ 2 := by ring
  have e2 : (n - k) ^ 2 = n ^ 2 - 2 * (n * k) + k ^ 2 := by ring
  rw [e2]
  rw [e1] at h2
  linarith [sq_nonneg k]

/-- Part A of the KST-017 contract (private candidate). -/
theorem coefficient_denominator_sum_le : (∀ (a : lp (fun _ : ℤ => ℝ) 2) (n : ℤ), n ≠ 0 →
  (∀ k : ℤ, 0 ≤ a k) → (∀ k : ℤ, a (-k) = a k) →
  ∑' k : ℤ, (if k = n then (0 : ℝ) else a (n + k) ^ 2 / (((n - k : ℤ) : ℝ)) ^ 2) ≤
    (∑' j : ℤ, if n.natAbs ≤ j.natAbs then a j ^ 2 else (0 : ℝ)) + ‖a‖ ^ 2 / (n : ℝ) ^ 2) := by
  intro a n hn _ _
  have hs : Summable (fun j : ℤ => a j ^ 2) := lp_sq_summable' a
  have hnorm : ‖a‖ ^ 2 = ∑' j : ℤ, a j ^ 2 := lp_norm_sq' a
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    positivity
  obtain ⟨Tj, hTj⟩ : ∃ Tj : ℤ → ℝ, Tj = fun j => if n.natAbs ≤ j.natAbs then a j ^ 2 else 0 :=
    ⟨_, rfl⟩
  obtain ⟨Bj, hBj⟩ : ∃ Bj : ℤ → ℝ, Bj = fun j => if j.natAbs < n.natAbs then a j ^ 2 else 0 :=
    ⟨_, rfl⟩
  have hTy : ∀ j : ℤ, n.natAbs ≤ j.natAbs → Tj j = a j ^ 2 := by
    intro j h; simp [hTj, h]
  have hTn : ∀ j : ℤ, ¬ n.natAbs ≤ j.natAbs → Tj j = 0 := by
    intro j h; simp [hTj, h]
  have hBy : ∀ j : ℤ, j.natAbs < n.natAbs → Bj j = a j ^ 2 := by
    intro j h; simp [hBj, h]
  have hBn : ∀ j : ℤ, ¬ j.natAbs < n.natAbs → Bj j = 0 := by
    intro j h; simp [hBj, h]
  have hT0 : ∀ j, 0 ≤ Tj j := by
    intro j
    by_cases h : n.natAbs ≤ j.natAbs
    · rw [hTy j h]; exact sq_nonneg _
    · rw [hTn j h]
  have hB0 : ∀ j, 0 ≤ Bj j := by
    intro j
    by_cases h : j.natAbs < n.natAbs
    · rw [hBy j h]; exact sq_nonneg _
    · rw [hBn j h]
  have hTle : ∀ j, Tj j ≤ a j ^ 2 := by
    intro j
    by_cases h : n.natAbs ≤ j.natAbs
    · rw [hTy j h]
    · rw [hTn j h]; exact sq_nonneg _
  have hBle1 : ∀ j, Bj j ≤ a j ^ 2 := by
    intro j
    by_cases h : j.natAbs < n.natAbs
    · rw [hBy j h]
    · rw [hBn j h]; exact sq_nonneg _
  have hT : Summable Tj := Summable.of_nonneg_of_le hT0 hTle hs
  have hB : Summable Bj := Summable.of_nonneg_of_le hB0 hBle1 hs
  have hT' : Summable (fun k : ℤ => Tj (n + k)) := (Equiv.addLeft n).summable_iff.2 hT
  have hB' : Summable (fun k : ℤ => Bj (n + k)) := (Equiv.addLeft n).summable_iff.2 hB
  have hR : Summable (fun k : ℤ => Tj (n + k) + Bj (n + k) / (n : ℝ) ^ 2) :=
    hT'.add (hB'.div_const _)
  have hpt : ∀ k : ℤ, (if k = n then (0 : ℝ) else a (n + k) ^ 2 / (((n - k : ℤ) : ℝ)) ^ 2) ≤
      Tj (n + k) + Bj (n + k) / (n : ℝ) ^ 2 := by
    intro k
    have hTk := hT0 (n + k)
    have hBk := hB0 (n + k)
    split_ifs with hk
    · exact add_nonneg hTk (div_nonneg hBk hn2.le)
    · have hd : (n - k : ℤ) ≠ 0 := sub_ne_zero.2 (Ne.symm hk)
      by_cases h1 : n.natAbs ≤ (n + k).natAbs
      · rw [hBn (n + k) (not_lt.2 h1), hTy (n + k) h1, zero_div, add_zero]
        exact div_le_self (sq_nonneg _) (one_le_sq_int_cast _ hd)
      · have h2 : (n + k).natAbs < n.natAbs := not_le.1 h1
        rw [hBy (n + k) h2, hTn (n + k) h1, zero_add]
        have hcast : (n : ℝ) ^ 2 ≤ (((n - k : ℤ) : ℤ) : ℝ) ^ 2 := by
          exact_mod_cast sq_le_of_abs_lt h2
        exact div_le_div_of_nonneg_left (sq_nonneg _) hn2 hcast
  have hL : Summable (fun k : ℤ =>
      (if k = n then (0 : ℝ) else a (n + k) ^ 2 / (((n - k : ℤ) : ℝ)) ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun k => ?_) hpt hR
    split_ifs
    · exact le_rfl
    · positivity
  have e1 : ∑' k : ℤ, Tj (n + k) = ∑' j : ℤ, Tj j := (Equiv.addLeft n).tsum_eq Tj
  have e2 : ∑' k : ℤ, Bj (n + k) = ∑' j : ℤ, Bj j := (Equiv.addLeft n).tsum_eq Bj
  have hBle : ∑' j : ℤ, Bj j ≤ ∑' j : ℤ, a j ^ 2 :=
    Summable.tsum_le_tsum hBle1 hB hs
  calc ∑' k : ℤ, (if k = n then (0 : ℝ) else a (n + k) ^ 2 / (((n - k : ℤ) : ℝ)) ^ 2)
      ≤ ∑' k : ℤ, (Tj (n + k) + Bj (n + k) / (n : ℝ) ^ 2) :=
        Summable.tsum_le_tsum hpt hL hR
    _ = (∑' j : ℤ, Tj j) + (∑' j : ℤ, Bj j) / (n : ℝ) ^ 2 := by
        rw [Summable.tsum_add hT' (hB'.div_const _), tsum_div_const, e1, e2]
    _ ≤ (∑' j : ℤ, if n.natAbs ≤ j.natAbs then a j ^ 2 else (0 : ℝ)) + ‖a‖ ^ 2 / (n : ℝ) ^ 2 := by
        have hTeq : (∑' j : ℤ, if n.natAbs ≤ j.natAbs then a j ^ 2 else (0 : ℝ)) =
            ∑' j : ℤ, Tj j := by rw [hTj]
        have hdiv : (∑' j : ℤ, Bj j) / (n : ℝ) ^ 2 ≤ (∑' j : ℤ, a j ^ 2) / (n : ℝ) ^ 2 := by
          gcongr
        rw [hTeq, hnorm]
        linarith

-- ===== Part B (v2) =====

open scoped ENNReal

private lemma lp_sq_summable'' (x : lp (fun _ : ℤ => ℝ) 2) :
    Summable (fun n : ℤ => (x n) ^ 2) := by
  have h := (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simpa [Real.norm_eq_abs, sq_abs] using h

private lemma lp_norm_sq'' (x : lp (fun _ : ℤ => ℝ) 2) :
    ‖x‖ ^ 2 = ∑' n : ℤ, (x n) ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x
  simpa [Real.norm_eq_abs, sq_abs] using h

private lemma one_le_sq_int_cast' (d : ℤ) (hd : d ≠ 0) : (1 : ℝ) ≤ ((d : ℤ) : ℝ) ^ 2 := by
  rw [one_le_sq_iff_one_le_abs]
  exact_mod_cast Int.one_le_abs hd

/-- The denominator-weighted sequence u_k = a(n+k)/|n-k| for k ≠ n, and 0 at k = n. -/
private def uSeq (a : lp (fun _ : ℤ => ℝ) 2) (n k : ℤ) : ℝ :=
  if k = n then 0 else a (n + k) / |((n - k : ℤ) : ℝ)|

private lemma uSeq_nonneg (a : lp (fun _ : ℤ => ℝ) 2) (ha0 : ∀ k : ℤ, 0 ≤ a k) (n k : ℤ) :
    0 ≤ uSeq a n k := by
  unfold uSeq
  split_ifs
  · exact le_rfl
  · exact div_nonneg (ha0 _) (abs_nonneg _)

private lemma uSeq_sq (a : lp (fun _ : ℤ => ℝ) 2) (n k : ℤ) :
    uSeq a n k ^ 2 = if k = n then (0 : ℝ) else a (n + k) ^ 2 / (((n - k : ℤ) : ℝ)) ^ 2 := by
  unfold uSeq
  split_ifs
  · simp
  · rw [div_pow, sq_abs]

private lemma uSeq_sq_le (a : lp (fun _ : ℤ => ℝ) 2) (n k : ℤ) :
    uSeq a n k ^ 2 ≤ a (n + k) ^ 2 := by
  rw [uSeq_sq]
  split_ifs with hk
  · exact sq_nonneg _
  · exact div_le_self (sq_nonneg _) (one_le_sq_int_cast' _ (sub_ne_zero.2 (Ne.symm hk)))

private lemma term_eq (a : lp (fun _ : ℤ => ℝ) 2) (n : ℤ) (H : ℤ → ℤ → ℂ) (p : ℤ × ℤ) :
    (if p.1 = n then (0 : ℝ)
    else ‖H (-p.1) (-p.2)‖ * (a (n + p.1) / |((n - p.1 : ℤ) : ℝ)|) * a (n + p.2)) =
    ‖H (-p.1) (-p.2)‖ * (uSeq a n p.1 * a (n + p.2)) := by
  unfold uSeq
  split_ifs with hk
  · simp
  · ring

private lemma holder_sq_bound (h g : ℤ × ℤ → ℝ) (hh0 : ∀ p, 0 ≤ h p) (hg0 : ∀ p, 0 ≤ g p)
    (hh : Summable (fun p => h p ^ 2)) (hg : Summable (fun p => g p ^ 2)) :
    Summable (fun p => h p * g p) ∧
      ∑' p, h p * g p ≤ (∑' p, h p ^ 2) ^ (1 / (2 : ℝ)) * (∑' p, g p ^ 2) ^ (1 / (2 : ℝ)) := by
  have hpq : Real.HolderConjugate 2 2 := by
    rw [Real.holderConjugate_iff]; norm_num
  have hh' : Summable (fun p => h p ^ (2 : ℝ)) := by simpa [Real.rpow_two] using hh
  have hg' : Summable (fun p => g p ^ (2 : ℝ)) := by simpa [Real.rpow_two] using hg
  obtain ⟨hs, hle⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hh0 hg0 hh' hg'
  refine ⟨hs, hle.trans (le_of_eq ?_)⟩
  simp only [Real.rpow_two]

private lemma final_bound (S T N : ℝ) (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hT0 : 0 ≤ T) (hN : 0 ≤ N) :
    S ^ (1 / (2 : ℝ)) * (T * N ^ 2) ^ (1 / (2 : ℝ)) ≤ N * Real.sqrt T := by
  have h1 : S ^ (1 / (2 : ℝ)) ≤ 1 := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_one.mpr hS1
  have h2 : (T * N ^ 2) ^ (1 / (2 : ℝ)) = N * Real.sqrt T := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul hT0, Real.sqrt_sq hN]
    ring
  rw [h2]
  calc S ^ (1 / (2 : ℝ)) * (N * Real.sqrt T) ≤ 1 * (N * Real.sqrt T) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg hN (Real.sqrt_nonneg _))
    _ = N * Real.sqrt T := one_mul _

private lemma neg_pair_tsum (F : ℤ × ℤ → ℝ) :
    ∑' p : ℤ × ℤ, F (-p.1, -p.2) = ∑' q : ℤ × ℤ, F q :=
  (Equiv.prodCongr (Equiv.neg ℤ) (Equiv.neg ℤ)).tsum_eq F

private lemma neg_pair_summable (F : ℤ × ℤ → ℝ) (hF : Summable F) :
    Summable (fun p : ℤ × ℤ => F (-p.1, -p.2)) :=
  (Equiv.prodCongr (Equiv.neg ℤ) (Equiv.neg ℤ)).summable_iff.2 hF

private lemma sq_neg_summable (H : ℤ → ℤ → ℂ)
    (hHs : Summable (fun p : ℤ × ℤ => ‖H p.1 p.2‖ ^ 2)) :
    Summable (fun p : ℤ × ℤ => ‖H (-p.1) (-p.2)‖ ^ 2) :=
  neg_pair_summable (fun q : ℤ × ℤ => ‖H q.1 q.2‖ ^ 2) hHs

private lemma sq_neg_tsum_le (H : ℤ → ℤ → ℂ)
    (hH1 : ∑' p : ℤ × ℤ, ‖H p.1 p.2‖ ^ 2 ≤ 1) :
    ∑' p : ℤ × ℤ, ‖H (-p.1) (-p.2)‖ ^ 2 ≤ 1 :=
  (neg_pair_tsum (fun q : ℤ × ℤ => ‖H q.1 q.2‖ ^ 2)).trans_le hH1

private lemma shift_sq_summable (a : lp (fun _ : ℤ => ℝ) 2) (n : ℤ) :
    Summable (fun j : ℤ => a (n + j) ^ 2) :=
  (Equiv.addLeft n).summable_iff.2 (lp_sq_summable'' a)

private lemma shift_sq_tsum (a : lp (fun _ : ℤ => ℝ) 2) (n : ℤ) :
    ∑' j : ℤ, a (n + j) ^ 2 = ‖a‖ ^ 2 := by
  rw [lp_norm_sq'']
  exact (Equiv.addLeft n).tsum_eq (fun j : ℤ => a j ^ 2)

private lemma uSeq_sq_summable (a : lp (fun _ : ℤ => ℝ) 2) (n : ℤ) :
    Summable (fun k : ℤ => uSeq a n k ^ 2) :=
  Summable.of_nonneg_of_le (fun k => sq_nonneg _) (uSeq_sq_le a n) (shift_sq_summable a n)

private lemma uSeq_sq_tsum (a : lp (fun _ : ℤ => ℝ) 2) (n : ℤ) :
    ∑' k : ℤ, uSeq a n k ^ 2 =
      ∑' k : ℤ, (if k = n then (0 : ℝ) else a (n + k) ^ 2 / (((n - k : ℤ) : ℝ)) ^ 2) :=
  tsum_congr (uSeq_sq a n)

private lemma uSeq_sum_nonneg (a : lp (fun _ : ℤ => ℝ) 2) (n : ℤ) :
    0 ≤ ∑' k : ℤ, (if k = n then (0 : ℝ) else a (n + k) ^ 2 / (((n - k : ℤ) : ℝ)) ^ 2) :=
  tsum_nonneg (fun k => by split_ifs <;> positivity)

private lemma g_sq_summable (a : lp (fun _ : ℤ => ℝ) 2) (n : ℤ) :
    Summable (fun p : ℤ × ℤ => (uSeq a n p.1 * a (n + p.2)) ^ 2) := by
  have hun : Summable (fun k : ℤ => ‖uSeq a n k ^ 2‖) :=
    (uSeq_sq_summable a n).abs.congr (fun k => (Real.norm_eq_abs _).symm)
  have hvn : Summable (fun j : ℤ => ‖a (n + j) ^ 2‖) :=
    (shift_sq_summable a n).abs.congr (fun j => (Real.norm_eq_abs _).symm)
  have hfun : (fun p : ℤ × ℤ => (uSeq a n p.1 * a (n + p.2)) ^ 2) =
      fun p => uSeq a n p.1 ^ 2 * a (n + p.2) ^ 2 := by
    funext p
    exact mul_pow _ _ _
  rw [hfun]
  exact summable_mul_of_summable_norm (f := fun k : ℤ => uSeq a n k ^ 2)
    (g := fun j : ℤ => a (n + j) ^ 2) hun hvn

private lemma g_sq_tsum (a : lp (fun _ : ℤ => ℝ) 2) (n : ℤ) :
    ∑' p : ℤ × ℤ, (uSeq a n p.1 * a (n + p.2)) ^ 2 =
      (∑' k : ℤ, uSeq a n k ^ 2) * ∑' j : ℤ, a (n + j) ^ 2 := by
  have hun : Summable (fun k : ℤ => ‖uSeq a n k ^ 2‖) :=
    (uSeq_sq_summable a n).abs.congr (fun k => (Real.norm_eq_abs _).symm)
  have hvn : Summable (fun j : ℤ => ‖a (n + j) ^ 2‖) :=
    (shift_sq_summable a n).abs.congr (fun j => (Real.norm_eq_abs _).symm)
  have hfun : (fun p : ℤ × ℤ => (uSeq a n p.1 * a (n + p.2)) ^ 2) =
      fun p => uSeq a n p.1 ^ 2 * a (n + p.2) ^ 2 := by
    funext p
    exact mul_pow _ _ _
  rw [hfun]
  exact (tsum_mul_tsum_of_summable_norm (f := fun k : ℤ => uSeq a n k ^ 2)
    (g := fun j : ℤ => a (n + j) ^ 2) hun hvn).symm

theorem hs_bilinear_denominator_bound : (∀ (a : lp (fun _ : ℤ => ℝ) 2) (n : ℤ) (H : ℤ → ℤ → ℂ),
  n ≠ 0 →
  (∀ k : ℤ, 0 ≤ a k) →
  Summable (fun p : ℤ × ℤ => ‖H p.1 p.2‖ ^ 2) →
  ∑' p : ℤ × ℤ, ‖H p.1 p.2‖ ^ 2 ≤ 1 →
  Summable (fun p : ℤ × ℤ =>
    if p.1 = n then (0 : ℝ)
    else ‖H (-p.1) (-p.2)‖ * (a (n + p.1) / |((n - p.1 : ℤ) : ℝ)|) * a (n + p.2)) ∧
  ∑' p : ℤ × ℤ,
    (if p.1 = n then (0 : ℝ)
    else ‖H (-p.1) (-p.2)‖ * (a (n + p.1) / |((n - p.1 : ℤ) : ℝ)|) * a (n + p.2)) ≤
    ‖a‖ * Real.sqrt (∑' k : ℤ,
      if k = n then (0 : ℝ) else a (n + k) ^ 2 / (((n - k : ℤ) : ℝ)) ^ 2)) := by
  intro a n H _ ha0 hHs hH1
  have hHolder := holder_sq_bound (fun p : ℤ × ℤ => ‖H (-p.1) (-p.2)‖)
    (fun p : ℤ × ℤ => uSeq a n p.1 * a (n + p.2)) (fun p => norm_nonneg _)
    (fun p => mul_nonneg (uSeq_nonneg a ha0 n _) (ha0 _))
    (sq_neg_summable H hHs) (g_sq_summable a n)
  obtain ⟨hsumF, hle⟩ := hHolder
  simp only [term_eq]
  refine ⟨hsumF, hle.trans ?_⟩
  rw [g_sq_tsum a n, shift_sq_tsum a n, uSeq_sq_tsum a n]
  exact final_bound _ _ _ (tsum_nonneg (fun p => sq_nonneg _))
    (sq_neg_tsum_le H hH1) (uSeq_sum_nonneg a n) (norm_nonneg _)

end NlsGge.Atomic.KST
