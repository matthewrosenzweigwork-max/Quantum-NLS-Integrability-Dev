import Mathlib

/-!
Elementary reciprocal-square lattice estimates used in the KST high-frequency tails.
The positive-displacement series represents the two integer tails by symmetry.
-/

open scoped BigOperators

/-- The reciprocal-square weight at a strictly positive natural lattice distance. -/
noncomputable def reciprocalSqTerm (m : ℕ) : ℝ := 1 / ((m + 1 : ℕ) : ℝ) ^ 2

private noncomputable def reciprocalSqKernel (d : ℤ) : ℝ := 1 / (d.natAbs : ℝ) ^ 2

/-- The reciprocal-square tail at distance greater than half the label size.
The factor two accounts for the positive and negative translated lattice points. -/
noncomputable def reciprocalSqTail (n : ℤ) : ℝ :=
  2 * ∑' j : ℕ, reciprocalSqTerm (j + n.natAbs / 2)

private noncomputable def reciprocalSqTailKernel (N : ℕ) (d : ℤ) : ℝ :=
  if N < 2 * d.natAbs then reciprocalSqKernel d else 0

/-- The far tail written directly as a sum over the translated integer lattice. -/
noncomputable def reciprocalSqIntegerTail (n : ℤ) : ℝ :=
  ∑' k : ℤ, reciprocalSqTailKernel n.natAbs (k - n)

/-- The reciprocal-square sum over the integer lattice translated by `n`, paired by sign. -/
noncomputable def reciprocalSqLattice (_n : ℤ) : ℝ := 2 * (1 + ∑' j : ℕ, reciprocalSqTerm (j + 1))

/-- The same lattice sum written directly over the translated integer index. -/
noncomputable def reciprocalSqInteger (n : ℤ) : ℝ :=
  ∑' k : ℤ, 1 / ((k - n).natAbs : ℝ) ^ 2

private theorem reciprocalSqTerm_nonneg (m : ℕ) : 0 ≤ reciprocalSqTerm m := by
  unfold reciprocalSqTerm
  positivity

private theorem telescopeSq (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 / ((i + 1 : ℕ) : ℝ) - 1 / ((i + 2 : ℕ) : ℝ)) =
      1 - 1 / ((n + 1 : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hn : (n + 1 : ℝ) ≠ 0 := by positivity
      have hn' : (n + 2 : ℝ) ≠ 0 := by positivity
      field_simp
      ring_nf

private theorem telescopeSqTail (m n : ℕ) (hm : 0 < m) :
    ∑ i ∈ Finset.range n,
      (1 / ((i + m : ℕ) : ℝ) - 1 / ((i + m + 1 : ℕ) : ℝ)) =
      1 / (m : ℝ) - 1 / ((n + m : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have h₁ : (m : ℝ) ≠ 0 := by positivity
      have h₂ : ((n + m : ℕ) : ℝ) ≠ 0 := by positivity
      have h₃ : ((n + m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      ring_nf

private theorem reciprocalSqBase_partial_le (n : ℕ) :
    ∑ i ∈ Finset.range n, reciprocalSqTerm (i + 1) ≤ 1 := by
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (1 / ((i + 1 : ℕ) : ℝ) - 1 / ((i + 2 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      unfold reciprocalSqTerm
      have h₁ : (i + 1 : ℝ) ≠ 0 := by positivity
      have h₂ : (i + 2 : ℝ) ≠ 0 := by positivity
      have ha : 1 ≤ (i + 1 : ℝ) := by exact_mod_cast Nat.le_add_left 1 i
      push_cast
      field_simp
      nlinarith
    _ = 1 - 1 / ((n + 1 : ℕ) : ℝ) := telescopeSq n
    _ ≤ 1 := by
      have : 0 ≤ 1 / ((n + 1 : ℕ) : ℝ) := by positivity
      linarith

private theorem reciprocalSqTail_partial_le (m n : ℕ) (hm : 2 ≤ m) :
    ∑ i ∈ Finset.range n, reciprocalSqTerm (i + m) ≤ 1 / (m : ℝ) := by
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (1 / ((i + m : ℕ) : ℝ) - 1 / ((i + m + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      unfold reciprocalSqTerm
      have h₁ : (i + m : ℝ) ≠ 0 := by positivity
      have h₂ : (i + m + 1 : ℝ) ≠ 0 := by positivity
      have ha : 2 ≤ (i + m : ℝ) := by exact_mod_cast (show 2 ≤ i + m by omega)
      push_cast
      field_simp
      nlinarith
    _ = 1 / (m : ℝ) - 1 / ((n + m : ℕ) : ℝ) := telescopeSqTail m n (by omega)
    _ ≤ 1 / (m : ℝ) := by
      have : 0 ≤ 1 / ((n + m : ℕ) : ℝ) := by positivity
      linarith

private theorem reciprocalSqBase_summable : Summable (fun j : ℕ => reciprocalSqTerm (j + 1)) := by
  apply summable_of_sum_range_le (fun j => reciprocalSqTerm_nonneg (j + 1))
  exact reciprocalSqBase_partial_le

private theorem reciprocalSqTerm_summable : Summable reciprocalSqTerm := by
  rw [← summable_nat_add_iff (f := reciprocalSqTerm) 1]
  simpa [Nat.add_comm] using reciprocalSqBase_summable

private theorem reciprocalSqKernel_summable : Summable reciprocalSqKernel := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa [reciprocalSqKernel, Int.natAbs_natCast] using reciprocalSqTerm_summable
  · simpa [reciprocalSqKernel, Int.natAbs_neg, Int.natAbs_natCast] using reciprocalSqTerm_summable

private theorem reciprocalSqBase_tsum_le :
    ∑' j : ℕ, reciprocalSqTerm (j + 1) ≤ 1 :=
  reciprocalSqBase_summable.tsum_le_of_sum_range_le reciprocalSqBase_partial_le

private theorem reciprocalSqShift_tsum_le (m : ℕ) (hm : 2 ≤ m) :
    ∑' j : ℕ, reciprocalSqTerm (j + m) ≤ 1 / (m : ℝ) := by
  have hs : Summable (fun j : ℕ => reciprocalSqTerm (j + m)) := by
    apply summable_of_sum_range_le (fun j => reciprocalSqTerm_nonneg (j + m))
    intro n
    exact reciprocalSqTail_partial_le m n hm
  exact hs.tsum_le_of_sum_range_le (fun n => reciprocalSqTail_partial_le m n hm)

/-- Translating the integer index and pairing its positive and negative parts gives the
packet-local positive-displacement representation. -/
theorem reciprocalSqInteger_eq_lattice (n : ℤ) :
    reciprocalSqInteger n = reciprocalSqLattice n := by
  unfold reciprocalSqInteger reciprocalSqLattice
  change (∑' k : ℤ, reciprocalSqKernel (k - n)) = 2 * (1 + ∑' j : ℕ, reciprocalSqTerm (j + 1))
  have hshift : (∑' k : ℤ, reciprocalSqKernel (k - n)) = ∑' d : ℤ, reciprocalSqKernel d := by
    have h := (Equiv.addRight n).tsum_eq (fun k : ℤ => reciprocalSqKernel (k - n))
    simpa [sub_add_cancel] using h.symm
  have heven : Function.Even reciprocalSqKernel := by
    intro d
    simp [reciprocalSqKernel, Int.natAbs_neg]
  have hpair := tsum_int_eq_zero_add_two_mul_tsum_pnat heven reciprocalSqKernel_summable
  have hnat := reciprocalSqTerm_summable.tsum_eq_zero_add
  rw [hshift, hpair, tsum_pnat_eq_tsum_succ (f := fun d : ℕ => reciprocalSqKernel (d : ℤ))]
  simp only [reciprocalSqKernel, Int.natAbs_natCast, reciprocalSqTerm] at *
  rw [hnat]
  simp
  ring

/-- The integer cutoff used by the tail agrees with the real inequality in the source contract. -/
theorem reciprocalSqIntegerTail_eq_real (n : ℤ) :
    reciprocalSqIntegerTail n =
      ∑' k : ℤ,
        (if (n.natAbs : ℝ) / 2 < ((k - n).natAbs : ℝ) then
          1 / ((k - n).natAbs : ℝ) ^ 2 else 0) := by
  unfold reciprocalSqIntegerTail
  apply tsum_congr
  intro k
  have hcut : n.natAbs < 2 * (k - n).natAbs ↔
      (n.natAbs : ℝ) / 2 < ((k - n).natAbs : ℝ) := by
    constructor <;> intro h
    · have hcast : (n.natAbs : ℝ) < 2 * ((k - n).natAbs : ℝ) := by exact_mod_cast h
      linarith
    · have hcast : (n.natAbs : ℝ) < 2 * ((k - n).natAbs : ℝ) := by linarith
      exact_mod_cast hcast
  simp [reciprocalSqTailKernel, reciprocalSqKernel, hcut]

/-- The packet-local tail is exactly the translated integer sum over distances
`|k - n| > |n|/2`; the cutoff is converted to the integer condition
`|n| < 2 |k - n|`, then the two signs are paired and the tail is shifted. -/
theorem reciprocalSqIntegerTail_eq (n : ℤ) :
    reciprocalSqIntegerTail n = reciprocalSqTail n := by
  unfold reciprocalSqIntegerTail reciprocalSqTail
  let N := n.natAbs
  let f : ℕ → ℝ := fun j =>
    if N < 2 * (j + 1) then reciprocalSqTerm j else 0
  have hkernel_even : Function.Even (reciprocalSqTailKernel N) := by
    intro d
    simp [reciprocalSqTailKernel, reciprocalSqKernel, Int.natAbs_neg]
  have hkernel_summable : Summable (reciprocalSqTailKernel N) := by
    apply Summable.of_nonneg_of_le
      (fun d => by simp [reciprocalSqTailKernel, reciprocalSqKernel]; positivity)
      (fun d => by
        simp only [reciprocalSqTailKernel]
        split_ifs
        · exact le_rfl
        · unfold reciprocalSqKernel
          positivity)
    exact reciprocalSqKernel_summable
  have hshift : (∑' k : ℤ, reciprocalSqTailKernel N (k - n)) =
      ∑' d : ℤ, reciprocalSqTailKernel N d := by
    have h := (Equiv.addRight n).tsum_eq (fun k : ℤ => reciprocalSqTailKernel N (k - n))
    simpa [sub_add_cancel] using h.symm
  have hpair := tsum_int_eq_zero_add_two_mul_tsum_pnat hkernel_even hkernel_summable
  have hf_le : ∀ j, f j ≤ reciprocalSqTerm j := by
    intro j
    simp only [f]
    split_ifs with h
    · exact le_rfl
    · exact reciprocalSqTerm_nonneg j
  have hf_nonneg : ∀ j, 0 ≤ f j := by
    intro j
    simp only [f]
    split_ifs
    · exact reciprocalSqTerm_nonneg j
    · norm_num
  have hf_summable : Summable f :=
    Summable.of_nonneg_of_le hf_nonneg hf_le reciprocalSqTerm_summable
  have hpnat : (∑' d : ℕ+, reciprocalSqTailKernel N (d : ℤ)) = ∑' j : ℕ, f j := by
    convert tsum_pnat_eq_tsum_succ
        (f := fun d : ℕ => reciprocalSqTailKernel N (d : ℤ)) using 1
    congr 1
  have hsplit := hf_summable.sum_add_tsum_nat_add (N / 2)
  have hzero : (∑ i ∈ Finset.range (N / 2), f i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : i < N / 2 := Finset.mem_range.mp hi
    have hnot : ¬ N < 2 * (i + 1) := by omega
    simp [f, hnot]
  have htail_shift : (∑' j : ℕ, f (j + N / 2)) =
      ∑' j : ℕ, reciprocalSqTerm (j + N / 2) := by
    congr 1
    funext j
    have hcut : N < 2 * (j + N / 2 + 1) := by omega
    simp only [f, if_pos hcut, reciprocalSqTerm]
  have hnatshift : (∑' j : ℕ, f j) = ∑' j : ℕ, reciprocalSqTerm (j + N / 2) := by
    calc
      _ = (∑ i ∈ Finset.range (N / 2), f i) + ∑' j : ℕ, f (j + N / 2) := hsplit.symm
      _ = ∑' j : ℕ, reciprocalSqTerm (j + N / 2) := by rw [hzero, zero_add, htail_shift]
  rw [hshift, hpair, hpnat, hnatshift]
  simp [reciprocalSqTailKernel, Int.natAbs_zero, N]

/-- For every integer label, the translated nonzero lattice sum is bounded by four. -/
theorem lattice_reciprocal_sq_bound (n : ℤ) : reciprocalSqInteger n ≤ 4 := by
  rw [reciprocalSqInteger_eq_lattice]
  unfold reciprocalSqLattice
  have h := reciprocalSqBase_tsum_le
  linarith

/-- For labels of size at least five, the far reciprocal-square tail is bounded by `5/|n|`.
The integer sum is translated by `n`, and its two tails are indexed by positive distances
`j + floor(|n|/2) + 1`, exactly those strictly greater than `|n|/2`. -/
theorem lattice_reciprocal_sq_tail {n : ℤ} (hn : 5 ≤ n.natAbs) :
    reciprocalSqTail n ≤ 5 / (n.natAbs : ℝ) := by
  unfold reciprocalSqTail
  let m := n.natAbs / 2
  have hm : 2 ≤ m := by dsimp [m]; omega
  have htail := reciprocalSqShift_tsum_le m hm
  have hN : (n.natAbs : ℝ) ≤ 2 * (m : ℝ) + 1 := by
    dsimp [m]
    have hnat : n.natAbs ≤ 2 * (n.natAbs / 2) + 1 := by omega
    exact_mod_cast hnat
  have hMr : 2 ≤ (m : ℝ) := by exact_mod_cast hm
  have hM : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hNN : 0 < (n.natAbs : ℝ) := by exact_mod_cast (by omega : 0 < n.natAbs)
  calc
    2 * ∑' j : ℕ, reciprocalSqTerm (j + n.natAbs / 2) ≤ 2 / (m : ℝ) := by
      calc
        2 * ∑' j : ℕ, reciprocalSqTerm (j + n.natAbs / 2) ≤
            2 * (1 / (m : ℝ)) := by
          gcongr
        _ = 2 / (m : ℝ) := by ring
    _ ≤ 5 / (n.natAbs : ℝ) := by
      have hprod : 2 * (n.natAbs : ℝ) ≤ 5 * (m : ℝ) := by linarith
      rw [div_le_div_iff₀ hM hNN]
      nlinarith

/-- The integer-indexed far tail obeys the same uniform bound. -/
theorem lattice_reciprocal_sq_integer_tail {n : ℤ} (hn : 5 ≤ n.natAbs) :
    reciprocalSqIntegerTail n ≤ 5 / (n.natAbs : ℝ) := by
  rw [reciprocalSqIntegerTail_eq]
  exact lattice_reciprocal_sq_tail hn


/-- The far-tail estimate in the literal translated-lattice form of the source contract. -/
theorem lattice_reciprocal_sq_tail_contract {n : ℤ} (hn : 5 ≤ n.natAbs) :
    (∑' k : ℤ,
      (if (n.natAbs : ℝ) / 2 < ((k - n).natAbs : ℝ) then
        1 / ((k - n).natAbs : ℝ) ^ 2 else 0)) ≤ 5 / (n.natAbs : ℝ) := by
  rw [← reciprocalSqIntegerTail_eq_real, reciprocalSqIntegerTail_eq]
  exact lattice_reciprocal_sq_tail hn

/-- The totalized zero term makes the full series equal to the sum with the resonant index omitted. -/
theorem reciprocalSqInteger_eq_excluded_sum (n : ℤ) :
    reciprocalSqInteger n =
      ∑' k : ℤ, (if k ≠ n then 1 / ((k - n).natAbs : ℝ) ^ 2 else 0) := by
  unfold reciprocalSqInteger
  apply tsum_congr
  intro k
  by_cases h : k = n
  · simp [h]
  · simp [h]

/-- The full lattice estimate in the literal translated-index form. -/
theorem lattice_reciprocal_sq_bound_contract (n : ℤ) :
    (∑' k : ℤ,
      (if k ≠ n then 1 / ((k - n).natAbs : ℝ) ^ 2 else 0)) ≤ 4 := by
  rw [← reciprocalSqInteger_eq_excluded_sum]
  exact lattice_reciprocal_sq_bound n
