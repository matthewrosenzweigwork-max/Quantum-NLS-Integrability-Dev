                                                                                 
                                                                                   
                                                                             
                                                                                 
                                                                           
                                                                                  

                              
                                                                           
                                                                                  
                         
                                                                                    
                                                                     
                                                                                
                                                                      

import Mathlib

set_option autoImplicit false

open scoped BigOperators
open Filter Topology

namespace NlsGge.Atomic.KSN015

/-- Backward telescoping over the symmetric window [-N, N]. -/
lemma tele_back (w : ℤ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (w (k - 1) - w k) =
      w (-(N : ℤ) - 1) - w (N : ℤ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hI : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
        insert (-((N : ℤ) + 1)) (insert ((N : ℤ) + 1) (Finset.Icc (-(N : ℤ)) (N : ℤ))) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    have h1 : (-((N : ℤ) + 1)) ∉ insert ((N : ℤ) + 1) (Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc, not_or]
      omega
    have h2 : ((N : ℤ) + 1) ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      simp only [Finset.mem_Icc, not_and, not_le]
      intro _
      omega
    rw [hI, Finset.sum_insert h1, Finset.sum_insert h2, ih]
    push_cast
    ring_nf

/-- Forward telescoping over the symmetric window [-N, N]. -/
lemma tele_fwd (w : ℤ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (w (k + 1) - w k) =
      w ((N : ℤ) + 1) - w (-(N : ℤ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hI : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
        insert (-((N : ℤ) + 1)) (insert ((N : ℤ) + 1) (Finset.Icc (-(N : ℤ)) (N : ℤ))) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    have h1 : (-((N : ℤ) + 1)) ∉ insert ((N : ℤ) + 1) (Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc, not_or]
      omega
    have h2 : ((N : ℤ) + 1) ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      simp only [Finset.mem_Icc, not_and, not_le]
      intro _
      omega
    rw [hI, Finset.sum_insert h1, Finset.sum_insert h2, ih]
    push_cast
    ring_nf

/-- Reciprocal of (N + c), along N to +infinity. -/
lemma inv_tendsto_pos (c : ℤ) :
    Tendsto (fun N : ℕ => 1 / ((((N : ℤ) + c : ℤ)) : ℝ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => ((((N : ℤ) + c : ℤ)) : ℝ)) atTop atTop := by
    have e : (fun N : ℕ => ((((N : ℤ) + c : ℤ)) : ℝ)) = fun N : ℕ => (N : ℝ) + (c : ℝ) := by
      funext N
      push_cast
      ring
    rw [e]
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  simpa [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp h1

/-- Reciprocal of (-N + c), along N to +infinity. -/
lemma inv_tendsto_neg (c : ℤ) :
    Tendsto (fun N : ℕ => 1 / (((-(N : ℤ) + c : ℤ)) : ℝ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => (((-(N : ℤ) + c : ℤ)) : ℝ)) atTop atBot := by
    have e : (fun N : ℕ => (((-(N : ℤ) + c : ℤ)) : ℝ)) = fun N : ℕ => -(N : ℝ) + (c : ℝ) := by
      funext N
      push_cast
      ring
    rw [e]
    exact tendsto_atBot_add_const_right _ _
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  simpa [Function.comp_def, one_div] using tendsto_inv_atBot_zero.comp h1

/-- One step of the window recursion, shift i to i + 1. -/
lemma window_succ (i : ℤ) (N : ℕ) :
    ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 / (((k - (i + 1)) : ℤ) : ℝ) - 1 / (k : ℝ)) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 / (((k - i) : ℤ) : ℝ) - 1 / (k : ℝ)) +
        (1 / (((-(N : ℤ) - 1 - i) : ℤ) : ℝ) - 1 / ((((N : ℤ) - i) : ℤ) : ℝ)) := by
  have ht := tele_back (fun j : ℤ => 1 / (((j - i) : ℤ) : ℝ)) N
  rw [← ht, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro k _
  push_cast
  ring

/-- One step of the window recursion, shift -i to -i - 1. -/
lemma window_pred (i : ℤ) (N : ℕ) :
    ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 / (((k - (-i - 1)) : ℤ) : ℝ) - 1 / (k : ℝ)) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 / (((k - (-i)) : ℤ) : ℝ) - 1 / (k : ℝ)) +
        (1 / ((((N : ℤ) + 1 - (-i)) : ℤ) : ℝ) - 1 / (((-(N : ℤ) - (-i)) : ℤ) : ℝ)) := by
  have ht := tele_fwd (fun j : ℤ => 1 / (((j - (-i)) : ℤ) : ℝ)) N
  rw [← ht, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro k _
  push_cast
  ring

/-- Window sums of the shifted telescoping difference tend to zero, for every shift m. -/
lemma window_sum_tendsto (m : ℤ) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (1 / (((k - m) : ℤ) : ℝ) - 1 / (k : ℝ))) atTop (𝓝 0) := by
  induction m using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have hinc : Tendsto (fun N : ℕ =>
        1 / (((-(N : ℤ) - 1 - i) : ℤ) : ℝ) - 1 / ((((N : ℤ) - i) : ℤ) : ℝ)) atTop (𝓝 0) := by
      have a := (inv_tendsto_neg (-1 - i)).sub (inv_tendsto_pos (-i))
      refine (a.congr ?_).trans ?_
      · intro N
        congr 2 <;> ring_nf
      · simp
    have hsum := ih.add hinc
    rw [zero_add] at hsum
    refine hsum.congr ?_
    intro N
    rw [window_succ i N]
  | pred i ih =>
    have hinc : Tendsto (fun N : ℕ =>
        1 / ((((N : ℤ) + 1 - (-i)) : ℤ) : ℝ) - 1 / (((-(N : ℤ) - (-i)) : ℤ) : ℝ))
        atTop (𝓝 0) := by
      have a := (inv_tendsto_pos (1 - (-i))).sub (inv_tendsto_neg (-(-i)))
      refine (a.congr ?_).trans ?_
      · intro N
        congr 2 <;> ring_nf
      · simp
    have hsum := ih.add hinc
    rw [zero_add] at hsum
    refine hsum.congr ?_
    intro N
    rw [window_pred i N]

/-- Partial fractions away from k = 0, n. -/
lemma f_identity (n k : ℤ) (hn : n ≠ 0) :
    (if k = 0 ∨ k = n then (0 : ℝ) else 1 / ((k : ℝ) * ((k : ℝ) - (n : ℝ)))) =
      (1 / (n : ℝ)) * (1 / (((k - n) : ℤ) : ℝ) - 1 / (k : ℝ)) +
        (if k = 0 then 1 / (n : ℝ) ^ 2 else 0) + (if k = n then 1 / (n : ℝ) ^ 2 else 0) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  by_cases h0 : k = 0
  · subst h0
    have hne : (0 : ℤ) ≠ n := fun h => hn h.symm
    rw [if_pos (Or.inl rfl), if_pos rfl, if_neg hne]
    push_cast
    simp
    field_simp
    ring
  · by_cases hkn : k = n
    · subst hkn
      rw [if_pos (Or.inr rfl), if_neg h0, if_pos rfl]
      push_cast
      simp
      field_simp
      ring
    · rw [if_neg (fun h => h.elim h0 hkn), if_neg h0, if_neg hkn]
      have hk : (k : ℝ) ≠ 0 := by exact_mod_cast h0
      have hkn' : (k : ℝ) - (n : ℝ) ≠ 0 := by
        intro h1
        apply hkn
        exact_mod_cast (sub_eq_zero.mp h1)
      push_cast
      field_simp
      ring

/-- The finite window sum of the summand equals (1/n) times the telescoping window sum
plus the two boundary corrections 1/n^2, once the window contains 0 and n. -/
lemma window_identity (n : ℤ) (hn : n ≠ 0) (N : ℕ) (hN : n.natAbs ≤ N) :
    ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (if k = 0 ∨ k = n then (0 : ℝ) else 1 / ((k : ℝ) * ((k : ℝ) - (n : ℝ)))) =
      (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 / (((k - n) : ℤ) : ℝ) - 1 / (k : ℝ))
        + 2 / (n : ℝ) ^ 2 := by
  have hN' : (n.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  have hbd : -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ) := by
    rcases Int.natAbs_eq n with h | h <;> omega
  have hmem0 : (0 : ℤ) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) :=
    Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hmemn : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := Finset.mem_Icc.mpr hbd
  rw [Finset.sum_congr rfl (fun k _ => f_identity n k hn), Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_ite_eq', hmem0, hmemn, if_true]
  ring

/-- The window sums of the summand tend to 2/n^2. -/
lemma value_tendsto (n : ℤ) (hn : n ≠ 0) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (if k = 0 ∨ k = n then (0 : ℝ) else 1 / ((k : ℝ) * ((k : ℝ) - (n : ℝ)))))
      atTop (𝓝 (2 / (n : ℝ) ^ 2)) := by
  have h := ((window_sum_tendsto n).const_mul (1 / (n : ℝ))).add_const (2 / (n : ℝ) ^ 2)
  rw [mul_zero, zero_add] at h
  exact h.congr' (Filter.eventually_atTop.2 ⟨n.natAbs, fun N hN => (window_identity n hn N hN).symm⟩)

/-- Symmetric windows exhaust ℤ. -/
lemma exhaust_tendsto :
    Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) atTop atTop := by
  apply Filter.tendsto_atTop_finset_of_monotone
  · intro a b hab
    have hab' : (a : ℤ) ≤ (b : ℤ) := by exact_mod_cast hab
    exact Finset.Icc_subset_Icc (by linarith) hab'
  · intro x
    refine ⟨x.natAbs, Finset.mem_Icc.mpr ?_⟩
    rcases Int.natAbs_eq x with h | h <;> omega

/-- AM-GM comparison term. -/
lemma two_term (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    |1 / (x * y)| ≤ 1 / 2 * (1 / x ^ 2) + 1 / 2 * (1 / y ^ 2) := by
  have hx' : 0 < |x| := abs_pos.mpr hx
  have hy' : 0 < |y| := abs_pos.mpr hy
  have e1 : 1 / x ^ 2 = (1 / |x|) ^ 2 := by rw [div_pow, one_pow, sq_abs]
  have e2 : 1 / y ^ 2 = (1 / |y|) ^ 2 := by rw [div_pow, one_pow, sq_abs]
  have e3 : |1 / (x * y)| = (1 / |x|) * (1 / |y|) := by
    rw [abs_div, abs_one, abs_mul, one_div_mul_one_div]
  rw [e1, e2, e3]
  nlinarith [sq_nonneg (1 / |x| - 1 / |y|)]

/-- Summability of the kernel, by comparison with 1/k^2. -/
lemma summable_f (n : ℤ) :
    Summable (fun k : ℤ =>
      if k = 0 ∨ k = n then (0 : ℝ) else 1 / ((k : ℝ) * ((k : ℝ) - (n : ℝ)))) := by
  have hsq : Summable (fun k : ℤ => 1 / (k : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  have hsq' : Summable (fun k : ℤ => 1 / (((k - n) : ℤ) : ℝ) ^ 2) :=
    hsq.comp_injective (sub_left_injective)
  refine Summable.of_norm_bounded ((hsq.mul_left (1 / 2)).add (hsq'.mul_left (1 / 2))) ?_
  intro k
  rw [Real.norm_eq_abs]
  by_cases h : k = 0 ∨ k = n
  · rw [if_pos h, abs_zero]
    positivity
  · rw [if_neg h]
    have hx : (k : ℝ) ≠ 0 := by
      intro h1
      apply h
      left
      exact_mod_cast h1
    have hy : ((((k - n) : ℤ)) : ℝ) ≠ 0 := by
      intro h1
      apply h
      right
      have h2 : k - n = 0 := by exact_mod_cast h1
      omega
    have e : (k : ℝ) - (n : ℝ) = (((k - n) : ℤ) : ℝ) := by push_cast; ring
    rw [e]
    exact two_term _ _ hx hy

/-- Uniform bound: each summand is at most 2/|n|. -/
lemma f_bound (n k : ℤ) (hn : n ≠ 0) :
    |(if k = 0 ∨ k = n then (0 : ℝ) else 1 / ((k : ℝ) * ((k : ℝ) - (n : ℝ))))| ≤
      2 / |(n : ℝ)| := by
  by_cases h : k = 0 ∨ k = n
  · rw [if_pos h, abs_zero]
    positivity
  · rw [if_neg h]
    have hk0 : k ≠ 0 := fun h0 => h (Or.inl h0)
    have hkn : k ≠ n := fun h0 => h (Or.inr h0)
    have hA : (1 : ℝ) ≤ |(k : ℝ)| := by
      have h1 := Int.one_le_abs hk0
      rw [← Int.cast_abs]
      exact_mod_cast h1
    have hB : (1 : ℝ) ≤ |(k : ℝ) - (n : ℝ)| := by
      have h1 := Int.one_le_abs (sub_ne_zero.mpr hkn)
      have e : (k : ℝ) - (n : ℝ) = (((k - n) : ℤ) : ℝ) := by push_cast; ring
      rw [e, ← Int.cast_abs]
      exact_mod_cast h1
    have hM : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
    have htri : |(n : ℝ)| ≤ |(k : ℝ)| + |(k : ℝ) - (n : ℝ)| := by
      have h1 := abs_sub (k : ℝ) ((k : ℝ) - (n : ℝ))
      have e : (k : ℝ) - ((k : ℝ) - (n : ℝ)) = (n : ℝ) := by ring
      rw [e] at h1
      exact h1
    have hprod : |1 / ((k : ℝ) * ((k : ℝ) - (n : ℝ)))| =
        1 / (|(k : ℝ)| * |(k : ℝ) - (n : ℝ)|) := by
      rw [abs_div, abs_one, abs_mul]
    rw [hprod, div_le_div_iff₀ (by positivity) hM]
    nlinarith [mul_nonneg (sub_nonneg.2 hA) (sub_nonneg.2 hB)]

/-- The value 2/n^2 of the full kernel sum. -/
lemma tsum_value (n : ℤ) (hn : n ≠ 0) :
    ∑' k : ℤ, (if k = 0 ∨ k = n then (0 : ℝ) else 1 / ((k : ℝ) * ((k : ℝ) - (n : ℝ)))) =
      2 / (n : ℝ) ^ 2 := by
  have h1 := Tendsto.comp (summable_f n).hasSum exhaust_tendsto
  exact tendsto_nhds_unique h1 (value_tendsto n hn)

/-- Finite removal: the removed series is summable, and the change in the sum is at most
card F times the uniform bound c on each summand. -/
lemma removal_core (n : ℤ) (F : Finset ℤ) (f : ℤ → ℝ) (c : ℝ) (hf : Summable f)
    (hz : ∀ k, (k = 0 ∨ k = n) → f k = 0) (hb : ∀ k, |f k| ≤ c) :
    Summable (fun k : ℤ => if k = 0 ∨ k = n ∨ k ∈ F then (0 : ℝ) else f k) ∧
      |(∑' k : ℤ, (if k = 0 ∨ k = n ∨ k ∈ F then (0 : ℝ) else f k)) - ∑' k : ℤ, f k|
        ≤ (F.card : ℝ) * c := by
  have hg : Summable (fun k : ℤ => if k = 0 ∨ k = n ∨ k ∈ F then (0 : ℝ) else f k) := by
    refine Summable.of_norm_bounded hf.abs (fun k => ?_)
    by_cases hc : k = 0 ∨ k = n ∨ k ∈ F
    · rw [if_pos hc, norm_zero]
      exact abs_nonneg _
    · rw [if_neg hc]
      exact (Real.norm_eq_abs _).le
  have hh : Summable (fun k : ℤ => if k = 0 ∨ k = n ∨ k ∈ F then f k else 0) := by
    refine summable_of_ne_finset_zero (s := insert 0 (insert n F)) (fun b hb => ?_)
    have hb' : ¬ (b = 0 ∨ b = n ∨ b ∈ F) := by
      intro hc
      apply hb
      rcases hc with hc | hc | hc
      · exact Finset.mem_insert.mpr (Or.inl hc)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl hc)))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr hc)))
    rw [if_neg hb']
  have hfgh : ∀ k, f k = (if k = 0 ∨ k = n ∨ k ∈ F then (0 : ℝ) else f k) +
      (if k = 0 ∨ k = n ∨ k ∈ F then f k else 0) := by
    intro k
    by_cases hc : k = 0 ∨ k = n ∨ k ∈ F
    · rw [if_pos hc, if_pos hc]
      ring
    · rw [if_neg hc, if_neg hc]
      ring
  have hsplit : ∑' k : ℤ, f k =
      (∑' k : ℤ, (if k = 0 ∨ k = n ∨ k ∈ F then (0 : ℝ) else f k)) +
        ∑' k : ℤ, (if k = 0 ∨ k = n ∨ k ∈ F then f k else 0) := by
    rw [← hg.tsum_add hh]
    exact tsum_congr hfgh
  have hsum_h : ∑' k : ℤ, (if k = 0 ∨ k = n ∨ k ∈ F then f k else 0) = ∑ k ∈ F, f k := by
    rw [tsum_eq_sum (s := F)]
    · refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [if_pos (Or.inr (Or.inr hk))]
    · intro b hb
      split_ifs with h1
      · rcases h1 with h1 | h1 | h1
        · exact hz b (Or.inl h1)
        · exact hz b (Or.inr h1)
        · exact absurd h1 hb
      · rfl
  refine ⟨hg, ?_⟩
  have hdiff : (∑' k : ℤ, (if k = 0 ∨ k = n ∨ k ∈ F then (0 : ℝ) else f k)) - ∑' k : ℤ, f k
      = -(∑ k ∈ F, f k) := by
    rw [hsplit, hsum_h]
    ring
  rw [hdiff, abs_neg]
  calc |∑ k ∈ F, f k| ≤ ∑ k ∈ F, |f k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ F, c := Finset.sum_le_sum (fun k _ => hb k)
    _ = (F.card : ℝ) * c := by rw [Finset.sum_const, nsmul_eq_mul]

                                                                                      
theorem ksn015_statement :
    ((∀ n : ℤ, n ≠ 0 →
        Summable (fun k : ℤ =>
          if k = 0 ∨ k = n then (0 : ℝ) else 1 / ((k : ℝ) * ((k : ℝ) - (n : ℝ)))) ∧
        (∑' k : ℤ,
          (if k = 0 ∨ k = n then (0 : ℝ) else 1 / ((k : ℝ) * ((k : ℝ) - (n : ℝ))))) =
          2 / (n : ℝ) ^ 2)
    ∧
    (∀ F : Finset ℤ, ∃ C : ℝ, ∀ n : ℤ, n ≠ 0 →
        Summable (fun k : ℤ =>
          if k = 0 ∨ k = n ∨ k ∈ F then (0 : ℝ) else 1 / ((k : ℝ) * ((k : ℝ) - (n : ℝ)))) ∧
        |(∑' k : ℤ,
            (if k = 0 ∨ k = n ∨ k ∈ F then (0 : ℝ) else 1 / ((k : ℝ) * ((k : ℝ) - (n : ℝ))))) -
          (∑' k : ℤ,
            (if k = 0 ∨ k = n then (0 : ℝ) else 1 / ((k : ℝ) * ((k : ℝ) - (n : ℝ)))))| ≤
          C / |(n : ℝ)|)) := by
  refine ⟨fun n hn => ⟨summable_f n, tsum_value n hn⟩, fun F => ⟨2 * (F.card : ℝ), fun n hn => ?_⟩⟩
  obtain ⟨h1, h2⟩ := removal_core n F
    (fun k => if k = 0 ∨ k = n then (0 : ℝ) else 1 / ((k : ℝ) * ((k : ℝ) - (n : ℝ))))
    (2 / |(n : ℝ)|) (summable_f n)
    (fun k hk => by rw [if_pos hk])
    (fun k => f_bound n k hn)
  have hfun : ∀ k : ℤ,
      (if k = 0 ∨ k = n ∨ k ∈ F then (0 : ℝ)
        else (if k = 0 ∨ k = n then (0 : ℝ) else 1 / ((k : ℝ) * ((k : ℝ) - (n : ℝ))))) =
      (if k = 0 ∨ k = n ∨ k ∈ F then (0 : ℝ) else 1 / ((k : ℝ) * ((k : ℝ) - (n : ℝ)))) := by
    intro k
    by_cases hc : k = 0 ∨ k = n ∨ k ∈ F
    · rw [if_pos hc, if_pos hc]
    · have hc' : ¬ (k = 0 ∨ k = n) := fun h2 => hc (by tauto)
      rw [if_neg hc, if_neg hc, if_neg hc']
  simp only [hfun] at h1 h2
  refine ⟨h1, ?_⟩
  have e : (2 * (F.card : ℝ)) / |(n : ℝ)| = (F.card : ℝ) * (2 / |(n : ℝ)|) := by ring
  rw [e]
  exact h2

end NlsGge.Atomic.KSN015
