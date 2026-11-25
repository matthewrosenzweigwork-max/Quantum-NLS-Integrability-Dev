import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false

open Filter
open scoped Topology

namespace NlsGge.Atomic.KST

noncomputable section

private def pairSq (x : ℤ → ℂ) (n : ℕ) : ℝ :=
  ‖x (n + 1)‖ ^ 2 + ‖x (-(n + 1))‖ ^ 2

private def pairTail (x : ℤ → ℂ) (n : ℕ) : ℝ :=
  ∑' m : ℕ, pairSq x (m + n)

/-- The square root of the two-sided lattice tail beginning at `|k| = n`.
At zero this includes the zero mode; for positive indices it is the paired tail. -/
def tailEnergy (x : ℤ → ℂ) (n : ℕ) : ℝ :=
  if n = 0 then Real.sqrt (‖x 0‖ ^ 2 + pairTail x 0)
  else Real.sqrt (pairTail x (n - 1))

private def tailDenom (x : ℤ → ℂ) (n : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt (pairTail x n))

private def tailMultiplier (x : ℤ → ℂ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (tailDenom x n)⁻¹

private lemma pairSq_nonneg (x : ℤ → ℂ) (n : ℕ) : 0 ≤ pairSq x n := by
  unfold pairSq
  positivity

private lemma pairSq_summable {x : ℤ → ℂ} (hx : Memℓp x 2) :
    Summable (pairSq x) := by
  have hsq : Summable (fun k : ℤ => ‖x k‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hx.summable (by norm_num)
  have hsplit := hsq.nat_add_neg_add_one
  have hpos : Summable (fun n : ℕ => ‖x n‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg ‖x (n : ℤ)‖)
      (fun n => le_add_of_nonneg_right (sq_nonneg ‖x (-((n : ℤ) + 1))‖)) hsplit
  have hneg : Summable (fun n : ℕ => ‖x (-(n + 1))‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg ‖x (-((n : ℤ) + 1))‖)
      (fun n => le_add_of_nonneg_left (sq_nonneg ‖x (n : ℤ)‖)) hsplit
  have hpos' : Summable (fun n : ℕ => ‖x (n + 1)‖ ^ 2) :=
    (summable_nat_add_iff 1).2 hpos
  exact (hpos'.add hneg).congr fun n => by
    simp [pairSq, Nat.cast_add, Int.neg_add, add_comm, add_left_comm]

private lemma pairTail_succ {x : ℤ → ℂ} (hpair : Summable (pairSq x)) (n : ℕ) :
    pairTail x n = pairSq x n + pairTail x (n + 1) := by
  have hs : Summable (fun m : ℕ => pairSq x (m + n)) :=
    (summable_nat_add_iff n).2 hpair
  unfold pairTail
  rw [← hs.sum_add_tsum_nat_add 1]
  simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private lemma pairTail_tendsto_zero {x : ℤ → ℂ} :
    Tendsto (pairTail x) atTop (𝓝 0) := by
  convert tendsto_sum_nat_add (pairSq x) using 1
  funext n
  simp [pairTail, Nat.add_comm]

private lemma pairTail_nonneg (x : ℤ → ℂ) (n : ℕ) : 0 ≤ pairTail x n := by
  exact tsum_nonneg fun m => pairSq_nonneg x (m + n)

/-- The positive-index energy is the literal integer-lattice tail.  The
positive and negative rays are split at zero and their finite initial
segments vanish before reindexing to `pairTail`. -/
theorem tailEnergy_sq_int {x : ℤ → ℂ} (hx : Memℓp x 2) (n : ℕ) (hn : 0 < n) :
    tailEnergy x n ^ 2 = ∑' k : ℤ,
      (if n ≤ k.natAbs then ‖x k‖ ^ 2 else 0) := by
  have hsq : Summable (fun k : ℤ => ‖x k‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hx.summable (by norm_num)
  let f : ℤ → ℝ := fun k => if n ≤ k.natAbs then ‖x k‖ ^ 2 else 0
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le (fun k => by dsimp [f]; split_ifs <;> positivity)
      (fun k => by dsimp [f]; split_ifs <;> first | rfl | positivity) hsq
  have hp : Summable (fun m : ℕ => f ((m + 1 : ℕ) : ℤ)) :=
    hf.comp_injective (i := fun m : ℕ => ((m + 1 : ℕ) : ℤ)) (by
      intro a b hab
      exact Nat.succ.inj (Int.ofNat.inj hab))
  have hneg : Summable (fun m : ℕ => f (-((m + 1 : ℕ) : ℤ))) :=
    hf.comp_injective (i := fun m : ℕ => -((m + 1 : ℕ) : ℤ)) (by
      intro a b hab
      exact Nat.succ.inj (Int.ofNat.inj (neg_injective hab)))
  have hposTail : (∑' m : ℕ, f ((m + 1 : ℕ) : ℤ)) =
      ∑' j : ℕ, ‖x ((j + n : ℕ) : ℤ)‖ ^ 2 := by
    have htail := hp.sum_add_tsum_nat_add (n - 1)
    rw [← htail]
    have hprefix : (∑ i ∈ Finset.range (n - 1), f ((i + 1 : ℕ) : ℤ)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi' : i < n - 1 := Finset.mem_range.mp hi
      have hlt : i + 1 < n := by omega
      have hAbs : (((i + 1 : ℕ) : ℤ).natAbs) = i + 1 := by
        rw [Int.natAbs_natCast]
      have hnot : ¬ n ≤ i + 1 := by omega
      simp only [f, hAbs, if_neg hnot]
    rw [hprefix, zero_add]
    congr 1
    funext j
    have hj : (j + (n - 1)) + 1 = j + n := by omega
    have hle : n ≤ j + n := by omega
    have hidxCast : ((j + (n - 1) + 1 : ℕ) : ℤ) = (j + n : ℕ) := by exact_mod_cast hj
    have hAbs : (((j + (n - 1) + 1 : ℕ) : ℤ).natAbs) = j + n := by
      rw [Int.natAbs_natCast, hj]
    simp only [f, hAbs, if_pos hle]
    rw [hidxCast]
  have hnegTail : (∑' m : ℕ, f (-((m + 1 : ℕ) : ℤ))) =
      ∑' j : ℕ, ‖x (-((j + n : ℕ) : ℤ))‖ ^ 2 := by
    have htail := hneg.sum_add_tsum_nat_add (n - 1)
    rw [← htail]
    have hprefix : (∑ i ∈ Finset.range (n - 1), f (-((i + 1 : ℕ) : ℤ))) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi' : i < n - 1 := Finset.mem_range.mp hi
      have hlt : i + 1 < n := by omega
      have hAbs : (-((i + 1 : ℕ) : ℤ)).natAbs = i + 1 := by
        rw [Int.natAbs_neg, Int.natAbs_natCast]
      have hnot : ¬ n ≤ i + 1 := by omega
      simp only [f, hAbs, if_neg hnot]
    rw [hprefix, zero_add]
    congr 1
    funext j
    have hj : (j + (n - 1)) + 1 = j + n := by omega
    have hle : n ≤ j + n := by omega
    have hidxCast : ((j + (n - 1) + 1 : ℕ) : ℤ) = (j + n : ℕ) := by exact_mod_cast hj
    have hAbs : (-((j + (n - 1) + 1 : ℕ) : ℤ)).natAbs = j + n := by
      rw [Int.natAbs_neg, Int.natAbs_natCast, hj]
    simp only [f, hAbs, if_pos hle]
    rw [hidxCast]
  have hposMode : Summable (fun j : ℕ => ‖x ((j + n : ℕ) : ℤ)‖ ^ 2) :=
    hsq.comp_injective (i := fun j : ℕ => ((j + n : ℕ) : ℤ)) (by
      intro a b hab
      exact Nat.add_right_cancel (Int.ofNat.inj hab))
  have hnegMode : Summable (fun j : ℕ => ‖x (-((j + n : ℕ) : ℤ))‖ ^ 2) :=
    hsq.comp_injective (i := fun j : ℕ => -((j + n : ℕ) : ℤ)) (by
      intro a b hab
      exact Nat.add_right_cancel (Int.ofNat.inj (neg_injective hab)))
  have hpair : (∑' j : ℕ, ‖x ((j + n : ℕ) : ℤ)‖ ^ 2) +
      (∑' j : ℕ, ‖x (-((j + n : ℕ) : ℤ))‖ ^ 2) = pairTail x (n - 1) := by
    rw [pairTail, ← hposMode.tsum_add hnegMode]
    congr 1
    funext j
    have hidx : (j + (n - 1)) + 1 = j + n := by omega
    have hidxInt : ((j + n : ℕ) : ℤ) = ((j + (n - 1) : ℕ) : ℤ) + 1 := by
      exact_mod_cast hidx.symm
    change ‖x ((j + n : ℕ) : ℤ)‖ ^ 2 + ‖x (-((j + n : ℕ) : ℤ))‖ ^ 2 =
      ‖x (((j + (n - 1) : ℕ) : ℤ) + 1)‖ ^ 2 +
        ‖x (-(((j + (n - 1) : ℕ) : ℤ) + 1))‖ ^ 2
    rw [← hidxInt]
  have hzero : f 0 = 0 := by
    have hnot : ¬ n ≤ (0 : ℤ).natAbs := by simp; omega
    simp only [f, Int.natAbs_zero, if_neg hnot]
  rw [tsum_of_add_one_of_neg_add_one hp hneg, hzero, add_zero]
  have hposTail' : (∑' m : ℕ, f ((m : ℤ) + 1)) =
      ∑' j : ℕ, ‖x ((j + n : ℕ) : ℤ)‖ ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hposTail
  have hnegTail' : (∑' m : ℕ, f (-((m : ℤ) + 1))) =
      ∑' j : ℕ, ‖x (-((j + n : ℕ) : ℤ))‖ ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hnegTail
  rw [hposTail', hnegTail', hpair]
  rw [tailEnergy, if_neg (by omega)]
  exact Real.sq_sqrt (pairTail_nonneg x (n - 1))

/-- The positive-index energy is exactly the sum of the positive and negative
integer modes beginning at `n + 1`. -/
theorem tailEnergy_sq_shifted (x : ℤ → ℂ) (n : ℕ) :
    tailEnergy x (n + 1) ^ 2 = ∑' m : ℕ,
      (‖x ((m + n + 1 : ℕ) : ℤ)‖ ^ 2 + ‖x (-((m + n + 1 : ℕ) : ℤ))‖ ^ 2) := by
  unfold tailEnergy
  rw [if_neg (by omega), Nat.add_sub_cancel]
  rw [Real.sq_sqrt (pairTail_nonneg x n)]
  rfl

private lemma pairTail_pos_of_infinite_support {x : ℤ → ℂ}
    (hpair : Summable (pairSq x)) (hfin : ¬ (Function.support x).Finite) (n : ℕ) :
    0 < pairTail x n := by
  apply lt_of_le_of_ne (pairTail_nonneg x n)
  intro hzero
  have hs : Summable (fun m : ℕ => pairSq x (m + n)) :=
    (summable_nat_add_iff n).2 hpair
  have hsum : (∑' m : ℕ, pairSq x (m + n)) = 0 := by
    simpa [pairTail] using hzero.symm
  have hall : ∀ m : ℕ, pairSq x (m + n) = 0 := by
    intro m
    apply le_antisymm
    · have hle := hs.le_tsum m (fun j hj => pairSq_nonneg x (j + n))
      rw [hsum] at hle
      exact hle
    · exact pairSq_nonneg x (m + n)
  have hsub : Function.support x ⊆ Set.Icc (-(n : ℤ)) (n : ℤ) := by
    intro k hk
    cases k with
    | ofNat a =>
        by_cases ha : a ≤ n
        · simp only [Set.mem_Icc]
          constructor
          · change -(n : ℤ) ≤ (a : ℤ)
            omega
          · change (a : ℤ) ≤ n
            omega
        · have hgt : n < a := by omega
          obtain ⟨j, hj⟩ : ∃ j : ℕ, a = j + n + 1 := by
            refine ⟨a - n - 1, ?_⟩
            omega
          have hpa := hall j
          have hparts : ‖x (↑a : ℤ)‖ ^ 2 = 0 ∧ ‖x (-((↑(j + n) : ℤ) + 1))‖ ^ 2 = 0 := by
            have hparts' := (add_eq_zero_iff_of_nonneg
              (sq_nonneg ‖x ((↑(j + n) : ℤ) + 1)‖)
              (sq_nonneg ‖x (-((↑(j + n) : ℤ) + 1))‖)).1 hpa
            simpa [pairSq, hj, Nat.cast_add] using hparts'
          have hxzero : x (Int.ofNat a) = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hparts.1)
          by_contra hnot
          exact (Function.mem_support.mp hk) hxzero
    | negSucc a =>
        by_cases ha : a + 1 ≤ n
        · simp only [Set.mem_Icc]
          constructor <;> omega
        · have hge : n ≤ a := by omega
          obtain ⟨j, hj⟩ : ∃ j : ℕ, a = j + n := by
            refine ⟨a - n, ?_⟩
            omega
          have hpa := hall j
          have hparts : ‖x (↑(j + n + 1) : ℤ)‖ ^ 2 = 0 ∧
              ‖x (-((↑(j + n) : ℤ) + 1))‖ ^ 2 = 0 := by
            have hparts' := (add_eq_zero_iff_of_nonneg
              (sq_nonneg ‖x ((↑(j + n) : ℤ) + 1)‖)
              (sq_nonneg ‖x (-((↑(j + n) : ℤ) + 1))‖)).1 hpa
            simpa [pairSq, hj, Nat.cast_add] using hparts'
          have hxzero : x (Int.negSucc a) = 0 := by
            simpa [hj, Int.negSucc_eq] using norm_eq_zero.mp (sq_eq_zero_iff.mp hparts.2)
          by_contra hnot
          exact (Function.mem_support.mp hk) hxzero
  exact hfin ((Set.finite_Icc (-(n : ℤ)) (n : ℤ)).subset hsub)

private lemma finite_support_weighted_summable {x : ℤ → ℂ}
    (hfin : (Function.support x).Finite) :
    Summable (fun n : ℕ => (‖x (n : ℤ)‖ ^ 2 + ‖x (-(n : ℤ))‖ ^ 2) * ((n + 1 : ℕ) : ℝ) ^ 2) := by
  have hpos : ({n : ℕ | x (n : ℤ) ≠ 0}).Finite :=
    Set.Finite.preimage (f := fun n : ℕ => (n : ℤ))
      (by intro a ha b hb hab; exact Int.ofNat_injective hab) hfin
  have hneg : ({n : ℕ | x (-(n : ℤ)) ≠ 0}).Finite :=
    Set.Finite.preimage (f := fun n : ℕ => -(n : ℤ))
      (by intro a ha b hb hab; exact Int.ofNat_injective (neg_injective hab)) hfin
  have hterms : (Function.support (fun n : ℕ =>
      (‖x (n : ℤ)‖ ^ 2 + ‖x (-(n : ℤ))‖ ^ 2) * ((n + 1 : ℕ) : ℝ) ^ 2)).Finite := by
    apply (hpos.union hneg).subset
    intro n hn
    have hterm : (‖x (n : ℤ)‖ ^ 2 + ‖x (-(n : ℤ))‖ ^ 2) * ((n + 1 : ℕ) : ℝ) ^ 2 ≠ 0 := by
      simpa only [Function.mem_support] using hn
    have hcoord : x (n : ℤ) ≠ 0 ∨ x (-(n : ℤ)) ≠ 0 := by
      by_contra h
      push_neg at h
      simp [h.1, h.2] at hterm
    exact hcoord
  exact summable_of_finite_support hterms

/-- For an infinite-support sequence, the exact reciprocal square-root of its
positive-mode tail is increasing, diverges, and has the factor-two tail bound. -/
theorem exists_tail_multiplier_infinite {x : ℤ → ℂ} (hx : Memℓp x 2)
    (hfin : ¬ (Function.support x).Finite) :
    ∃ c : ℕ → ℝ, Monotone c ∧ Tendsto c atTop atTop ∧
      Antitone (tailEnergy x) ∧ Tendsto (tailEnergy x) atTop (𝓝 0) ∧
      (∀ n : ℕ, 0 < n → 0 < tailEnergy x n) ∧
      (∀ n : ℕ, 0 < n → c n = (Real.sqrt (tailEnergy x n))⁻¹) ∧
      Summable (fun n : ℕ => (‖x (n : ℤ)‖ ^ 2 + ‖x (-(n : ℤ))‖ ^ 2) * c n ^ 2) ∧
      (∑' n : ℕ, (‖x ((n + 1 : ℕ) : ℤ)‖ ^ 2 +
          ‖x (-((n + 1 : ℕ) : ℤ))‖ ^ 2) * c (n + 1) ^ 2 ≤ 2 * tailEnergy x 1) := by
  classical
  let c := tailMultiplier x
  have hpair : Summable (pairSq x) := pairSq_summable hx
  have hstep n : pairTail x n = pairSq x n + pairTail x (n + 1) := pairTail_succ hpair n
  have htail_anti : Antitone (pairTail x) := by
    apply antitone_nat_of_succ_le
    intro n
    rw [hstep n]
    exact le_add_of_nonneg_left (pairSq_nonneg x n)
  have hE_anti : Antitone (tailEnergy x) := by
    intro m n hmn
    cases m with
    | zero =>
        cases n with
        | zero => rfl
        | succ n =>
            simp only [tailEnergy, Nat.succ_sub_one, ↓reduceIte]
            apply Real.sqrt_le_sqrt
            exact (htail_anti (Nat.zero_le n)).trans
              (le_add_of_nonneg_left (sq_nonneg ‖x 0‖))
    | succ m =>
        cases n with
        | zero => omega
        | succ n =>
            simp only [tailEnergy, Nat.succ_ne_zero, ↓reduceIte]
            exact Real.sqrt_le_sqrt (htail_anti (Nat.succ_le_succ_iff.mp hmn))
  have hroot_anti : Antitone (fun n => Real.sqrt (Real.sqrt (pairTail x n))) := by
    intro m n hmn
    exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (htail_anti hmn))
  have hdenom_anti : Antitone (tailDenom x) := hroot_anti
  have hdenom_pos (n : ℕ) : 0 < tailDenom x n := by
    unfold tailDenom
    exact Real.sqrt_pos.2 (Real.sqrt_pos.2 (pairTail_pos_of_infinite_support hpair hfin n))
  have hc_mono : Monotone c := by
    apply monotone_nat_of_le_succ
    intro n
    cases n with
    | zero =>
        change 0 ≤ (tailDenom x 0)⁻¹
        exact inv_nonneg.mpr (le_of_lt (hdenom_pos 0))
    | succ n =>
        change (tailDenom x n)⁻¹ ≤ (tailDenom x (n + 1))⁻¹
        exact (inv_le_inv₀ (hdenom_pos n) (hdenom_pos (n + 1))).2
          (hdenom_anti (Nat.le_succ _))
  have htail_zero := pairTail_tendsto_zero (x := x)
  have htail_sub : Tendsto (fun n : ℕ => pairTail x (n - 1)) atTop (𝓝 0) :=
    htail_zero.comp (tendsto_sub_atTop_nat 1)
  have hE_base : Tendsto (fun n : ℕ => Real.sqrt (pairTail x (n - 1))) atTop (𝓝 0) := by
    convert Real.continuous_sqrt.continuousAt.tendsto.comp htail_sub using 1 <;>
      ext n <;> simp [Real.sqrt_zero]
  have hE_zero : Tendsto (tailEnergy x) atTop (𝓝 0) := by
    refine hE_base.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    simp [tailEnergy, Nat.ne_of_gt hn]
  have hE_pos (n : ℕ) (hn : 0 < n) : 0 < tailEnergy x n := by
    cases n with
    | zero => omega
    | succ n =>
        simpa [tailEnergy] using
          Real.sqrt_pos.2 (pairTail_pos_of_infinite_support hpair hfin n)
  have hdenom_zero : Tendsto (tailDenom x) atTop (𝓝 0) := by
    change Tendsto ((Real.sqrt ∘ Real.sqrt) ∘ pairTail x) atTop (𝓝 0)
    simpa only [Function.comp_apply, Real.sqrt_zero] using
      (Real.continuous_sqrt.comp Real.continuous_sqrt).continuousAt.tendsto.comp htail_zero
  have hdenom_within : Tendsto (tailDenom x) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.2
    exact ⟨hdenom_zero, Filter.Eventually.of_forall hdenom_pos⟩
  have hc_shift : Tendsto (fun n : ℕ => c (n + 2)) atTop atTop := by
    have h := hdenom_within.inv_tendsto_nhdsGT_zero.comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun n => (tailDenom x (n + 1))⁻¹) atTop atTop
    convert h using 1 <;> ext n <;> rfl
  have hc_tendsto : Tendsto c atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    have hEv : ∀ᶠ n : ℕ in atTop, b ≤ c (n + 2) := Filter.tendsto_atTop.1 hc_shift b
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hEv
    have hb : b ≤ c (N + 2) := hN N le_rfl
    have hlarge : ∀ᶠ n : ℕ in atTop, N + 2 ≤ n := Filter.eventually_ge_atTop _
    exact hlarge.mono fun n hn => hb.trans (hc_mono (a := N + 2) (b := n) hn)
  have hD_nonneg (n : ℕ) :
      0 ≤ 2 * (Real.sqrt (pairTail x n) - Real.sqrt (pairTail x (n + 1))) := by
    have hnext : pairTail x (n + 1) ≤ pairTail x n := by
      rw [hstep n]
      exact le_add_of_nonneg_left (pairSq_nonneg x n)
    have hroot := Real.sqrt_le_sqrt hnext
    nlinarith [Real.sqrt_nonneg (pairTail x n), Real.sqrt_nonneg (pairTail x (n + 1))]
  have hD_sum (k : ℕ) :
      ∑ n ∈ Finset.range k, 2 * (Real.sqrt (pairTail x n) - Real.sqrt (pairTail x (n + 1)))
        ≤ 2 * Real.sqrt (pairTail x 0) := by
    have htel (k : ℕ) :
        ∑ n ∈ Finset.range k, (Real.sqrt (pairTail x n) - Real.sqrt (pairTail x (n + 1)))
          = Real.sqrt (pairTail x 0) - Real.sqrt (pairTail x k) := by
      induction k with
      | zero => simp
      | succ k ih => rw [Finset.sum_range_succ, ih]; ring
    rw [← Finset.mul_sum, htel k]
    nlinarith [Real.sqrt_nonneg (pairTail x k)]
  have hD : Summable (fun n : ℕ =>
      2 * (Real.sqrt (pairTail x n) - Real.sqrt (pairTail x (n + 1)))) :=
    summable_of_sum_range_le hD_nonneg hD_sum
  have hmajor (n : ℕ) :
      pairSq x n * c (n + 1) ^ 2 ≤
        2 * (Real.sqrt (pairTail x n) - Real.sqrt (pairTail x (n + 1))) := by
    have hnext : pairTail x (n + 1) ≤ pairTail x n := by
      rw [hstep n]
      exact le_add_of_nonneg_left (pairSq_nonneg x n)
    have hroot : Real.sqrt (pairTail x (n + 1)) ≤ Real.sqrt (pairTail x n) :=
      Real.sqrt_le_sqrt hnext
    have hpos := pairTail_pos_of_infinite_support hpair hfin n
    have hroot_pos := Real.sqrt_pos.2 hpos
    have hrootSq := Real.sq_sqrt (pairTail_nonneg x n)
    have hnextSq := Real.sq_sqrt (pairTail_nonneg x (n + 1))
    have hc2 : c (n + 1) ^ 2 = (Real.sqrt (pairTail x n))⁻¹ := by
      dsimp [c, tailMultiplier, tailDenom]
      rw [inv_pow, Real.sq_sqrt (Real.sqrt_nonneg (pairTail x n))]
    have hdiff : pairSq x n =
        (Real.sqrt (pairTail x n) - Real.sqrt (pairTail x (n + 1))) *
          (Real.sqrt (pairTail x n) + Real.sqrt (pairTail x (n + 1))) := by
      calc
        pairSq x n = pairTail x n - pairTail x (n + 1) := by rw [hstep n]; ring
        _ = Real.sqrt (pairTail x n) ^ 2 - Real.sqrt (pairTail x (n + 1)) ^ 2 := by
          rw [hrootSq, hnextSq]
        _ = _ := by ring
    have hratio : pairSq x n * (Real.sqrt (pairTail x n))⁻¹ ≤
        2 * (Real.sqrt (pairTail x n) - Real.sqrt (pairTail x (n + 1))) := by
      have hsum : (Real.sqrt (pairTail x n) + Real.sqrt (pairTail x (n + 1))) /
          Real.sqrt (pairTail x n) ≤ 2 := by
        apply (div_le_iff₀ hroot_pos).2
        nlinarith [Real.sqrt_nonneg (pairTail x (n + 1)), hroot]
      rw [hdiff]
      calc
        (Real.sqrt (pairTail x n) - Real.sqrt (pairTail x (n + 1))) *
            (Real.sqrt (pairTail x n) + Real.sqrt (pairTail x (n + 1))) *
            (Real.sqrt (pairTail x n))⁻¹ =
          (Real.sqrt (pairTail x n) - Real.sqrt (pairTail x (n + 1))) *
            ((Real.sqrt (pairTail x n) + Real.sqrt (pairTail x (n + 1))) /
              Real.sqrt (pairTail x n)) := by rw [div_eq_mul_inv]; ring
        _ ≤ (Real.sqrt (pairTail x n) - Real.sqrt (pairTail x (n + 1))) * 2 :=
          mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hroot)
        _ = _ := by ring
    rw [hc2]
    exact hratio
  have hweighted : Summable (fun n : ℕ => pairSq x n * c (n + 1) ^ 2) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (pairSq_nonneg x n) (sq_nonneg _)) hmajor hD
  have hbound : ∑' n : ℕ, pairSq x n * c (n + 1) ^ 2 ≤ 2 * tailEnergy x 1 := by
    calc
      ∑' n : ℕ, pairSq x n * c (n + 1) ^ 2 ≤
          ∑' n : ℕ, 2 * (Real.sqrt (pairTail x n) - Real.sqrt (pairTail x (n + 1))) :=
        hweighted.tsum_le_tsum hmajor hD
      _ ≤ 2 * tailEnergy x 1 := by
        have h := Real.tsum_le_of_sum_range_le hD_nonneg hD_sum
        simpa [tailEnergy] using h
  have hshift : Summable (fun n : ℕ =>
      (‖x ((n + 1 : ℕ) : ℤ)‖ ^ 2 + ‖x (-((n + 1 : ℕ) : ℤ))‖ ^ 2) * c (n + 1) ^ 2) := by
    simpa [pairSq] using hweighted
  have htarget : Summable (fun n : ℕ =>
      (‖x (n : ℤ)‖ ^ 2 + ‖x (-(n : ℤ))‖ ^ 2) * c n ^ 2) :=
    (summable_nat_add_iff 1).1 (by simpa using hshift)
  have hformula (n : ℕ) (hn : 0 < n) : c n = (Real.sqrt (tailEnergy x n))⁻¹ := by
    cases n with
    | zero => omega
    | succ n => simp [c, tailMultiplier, tailDenom, tailEnergy]
  refine ⟨c, hc_mono, hc_tendsto, hE_anti, hE_zero, hE_pos, hformula, htarget, ?_⟩
  simpa [pairSq] using hbound

/-- Every square-summable complex sequence admits a monotone divergent multiplier
with a summable weighted square sequence. Finite support is handled by `c n = n + 1`;
otherwise the multiplier is the reciprocal square-root of the positive-mode tail. -/
theorem exists_diverging_tail_multiplier {x : ℤ → ℂ} (hx : Memℓp x 2) :
    ∃ c : ℕ → ℝ, Monotone c ∧ Tendsto c atTop atTop ∧
      Summable (fun n : ℕ => (‖x (n : ℤ)‖ ^ 2 + ‖x (-(n : ℤ))‖ ^ 2) * c n ^ 2) := by
  classical
  by_cases hfin : (Function.support x).Finite
  · refine ⟨fun n => ((n + 1 : ℕ) : ℝ), ?_, ?_, ?_⟩
    · intro m n hmn
      change ((m + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ)
      exact_mod_cast (Nat.add_le_add_right hmn 1)
    · exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    · exact finite_support_weighted_summable hfin
  · obtain ⟨c, hmono, htend, hEanti, hEzero, hEpos, hformula, hsum, hbound⟩ :=
      exists_tail_multiplier_infinite hx hfin
    exact ⟨c, hmono, htend, hsum⟩

end
end NlsGge.Atomic.KST
