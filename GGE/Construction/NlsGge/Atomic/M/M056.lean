import NlsGge.Atomic.KST.KST005

set_option autoImplicit false
noncomputable section
namespace NlsGge.Atomic.M.M056

open scoped BigOperators

private def m056BracketKernel (d : ℤ) : ℝ :=
  1 / (1 + |(d : ℝ)|) ^ 2

private theorem m056BracketKernel_nonneg (d : ℤ) : 0 ≤ m056BracketKernel d := by
  unfold m056BracketKernel
  positivity

private theorem m056BracketKernel_summable : Summable m056BracketKernel := by
  have hhalf : Summable (fun d : ℤ => 1 / |(d : ℝ) + (1 / 2 : ℝ)| ^ (2 : ℝ)) := by
    exact (Real.summable_one_div_int_add_rpow (a := (1 / 2 : ℝ)) (s := (2 : ℝ))).2 (by norm_num)
  apply Summable.of_nonneg_of_le (fun d => m056BracketKernel_nonneg d)
  intro d
  unfold m056BracketKernel
  have hd : d ≤ -1 ∨ 0 ≤ d := by omega
  have hd' : (d : ℝ) ≤ -1 ∨ 0 ≤ (d : ℝ) := by exact_mod_cast hd
  have hpos : 0 < |(d : ℝ) + (1 / 2 : ℝ)| := by
    rcases hd' with hneg | hnonneg
    · have hle : (d : ℝ) + (1 / 2 : ℝ) ≤ -(1 / 2 : ℝ) := by linarith
      rw [abs_of_nonpos (by linarith : (d : ℝ) + (1 / 2 : ℝ) ≤ 0)]
      linarith
    · have hge : (1 / 2 : ℝ) ≤ (d : ℝ) + (1 / 2 : ℝ) := by linarith
      rw [abs_of_nonneg (by linarith : 0 ≤ (d : ℝ) + (1 / 2 : ℝ))]
      linarith
  have htri : |(d : ℝ) + (1 / 2 : ℝ)| ≤ 1 + |(d : ℝ)| := by
    calc
      |(d : ℝ) + (1 / 2 : ℝ)| ≤ |(d : ℝ)| + |(1 / 2 : ℝ)| := abs_add_le _ _
      _ = |(d : ℝ)| + (1 / 2 : ℝ) := by norm_num
      _ ≤ 1 + |(d : ℝ)| := by linarith [abs_nonneg (d : ℝ)]
  have hsq : |(d : ℝ) + (1 / 2 : ℝ)| ^ 2 ≤ (1 + |(d : ℝ)|) ^ 2 := by
    nlinarith [abs_nonneg ((d : ℝ) + (1 / 2 : ℝ)), abs_nonneg (d : ℝ), htri]
  have hden : 0 < (1 + |(d : ℝ)|) ^ 2 := by positivity
  have hden' : 0 < |(d : ℝ) + (1 / 2 : ℝ)| ^ 2 := by positivity
  have hcomp : 1 / (1 + |(d : ℝ)|) ^ 2 ≤
      1 / |(d : ℝ) + (1 / 2 : ℝ)| ^ (2 : ℝ) := by
    convert one_div_le_one_div_of_le hden' hsq using 1 <;>
      norm_num [Real.rpow_natCast]
  exact hcomp
  exact hhalf

private def m056ShiftedTerm (m n : ℤ) : ℝ :=
  if m = 0 then 0 else
    1 / ((1 + |((m + 2*n : ℤ) : ℝ)|) ^ 2 * |(m : ℝ)| ^ 2)

private theorem m056ShiftedTerm_nonneg (m n : ℤ) : 0 ≤ m056ShiftedTerm m n := by
  unfold m056ShiftedTerm
  split_ifs <;> positivity

private theorem m056ShiftedTerm_le_bracket (m n : ℤ) :
    m056ShiftedTerm m n ≤ m056BracketKernel (m + 2*n) := by
  by_cases hm : m = 0
  · simp [m056ShiftedTerm, m056BracketKernel, hm]
    positivity
  · have hmcast : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hcase : m ≤ -1 ∨ 1 ≤ m := by omega
    have hmag : 1 ≤ |(m : ℝ)| := by
      rcases hcase with hneg | hpos
      · have hneg' : (m : ℝ) ≤ -1 := by exact_mod_cast hneg
        rw [abs_of_nonpos (by linarith : (m : ℝ) ≤ 0)]
        linarith
      · have hpos' : 1 ≤ (m : ℝ) := by exact_mod_cast hpos
        rw [abs_of_nonneg (by linarith : 0 ≤ (m : ℝ))]
        linarith
    have hmag2 : 1 ≤ |(m : ℝ)| ^ 2 := by nlinarith [abs_nonneg (m : ℝ), hmag]
    have hbase : 0 < (1 + |((m + 2*n : ℤ) : ℝ)|) ^ 2 := by positivity
    have hden :
        (1 + |((m + 2*n : ℤ) : ℝ)|) ^ 2 ≤
          (1 + |((m + 2*n : ℤ) : ℝ)|) ^ 2 * |(m : ℝ)| ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hmag2 (le_of_lt hbase)
      nlinarith
    unfold m056ShiftedTerm m056BracketKernel
    rw [if_neg hm]
    exact one_div_le_one_div_of_le hbase hden

private theorem m056ShiftedTerm_summable (n : ℤ) :
    Summable (fun m : ℤ => m056ShiftedTerm m n) := by
  have hshift : Summable (fun m : ℤ => m056BracketKernel (m + 2*n)) := by
    exact m056BracketKernel_summable.comp_injective
      (i := fun m : ℤ => m + 2*n)
      (by intro a b h; exact add_right_cancel h)
  apply Summable.of_nonneg_of_le (fun m => m056ShiftedTerm_nonneg m n)
  · intro m
    exact m056ShiftedTerm_le_bracket m n
  · exact hshift

private def m056SourceTerm (l n : ℤ) : ℝ :=
  if l = n then 0 else
    1 / ((1 + |((l + n : ℤ) : ℝ)|) ^ 2 * |((n - l : ℤ) : ℝ)| ^ 2)

private theorem m056SourceTerm_eq_shift (l n : ℤ) :
    m056SourceTerm l n = m056ShiftedTerm (l - n) n := by
  by_cases h : l = n
  · simp [m056SourceTerm, m056ShiftedTerm, h]
  · have hshift : l - n ≠ 0 := sub_ne_zero.mpr h
    simp only [m056SourceTerm, m056ShiftedTerm, if_neg h, if_neg hshift]
    push_cast
    have hsum : (l : ℝ) - n + 2 * n = (l : ℝ) + n := by ring
    have hneg : (n : ℝ) - l = -((l : ℝ) - n) := by ring
    rw [← hsum, hneg, abs_neg]

private theorem m056SourceTerm_summable (n : ℤ) :
    Summable (fun l : ℤ => m056SourceTerm l n) := by
  have h : Summable (fun l : ℤ => m056ShiftedTerm (l - n) n) :=
    (m056ShiftedTerm_summable n).comp_injective (i := fun l : ℤ => l - n)
      (by intro a b hab; have h := congrArg (fun z : ℤ => z + n) hab; simpa using h)
  rcases h with ⟨s, hs⟩
  refine ⟨s, hs.congr_fun ?_⟩
  intro l
  exact m056SourceTerm_eq_shift l n

private theorem m056SourceTsum_eq_shift (n : ℤ) :
    (∑' l : ℤ, m056SourceTerm l n) = ∑' m : ℤ, m056ShiftedTerm m n := by
  calc
    ∑' l : ℤ, m056SourceTerm l n =
        ∑' l : ℤ, m056ShiftedTerm (l - n) n := by
      apply tsum_congr
      intro l
      exact m056SourceTerm_eq_shift l n
    _ = ∑' m : ℤ, m056ShiftedTerm m n := by
      have h := (Equiv.addRight n).tsum_eq
        (fun l : ℤ => m056ShiftedTerm (l - n) n)
      simpa [sub_add_cancel] using h.symm

private theorem m056ShiftedTerm_reflect (m n : ℤ) :
    m056ShiftedTerm (-m) n = m056ShiftedTerm m (-n) := by
  by_cases hm : m = 0
  · simp [m056ShiftedTerm, hm]
  · have hneg : -m ≠ 0 := by omega
    simp only [m056ShiftedTerm, if_neg hm, if_neg hneg]
    push_cast
    have hbracket :
        |(-((m : ℝ)) + 2 * (n : ℝ))| = |(m : ℝ) + 2 * (-(n : ℝ))| := by
      rw [show -((m : ℝ)) + 2 * (n : ℝ) = -((m : ℝ) + 2 * (-(n : ℝ))) by ring,
        abs_neg]
    have hnum : |(-(m : ℝ))| = |(m : ℝ)| := abs_neg _
    rw [hbracket, hnum]

private theorem m056ShiftedTsum_reflect (n : ℤ) :
    (∑' m : ℤ, m056ShiftedTerm m n) = ∑' m : ℤ, m056ShiftedTerm m (-n) := by
  calc
    ∑' m : ℤ, m056ShiftedTerm m n =
        ∑' m : ℤ, m056ShiftedTerm (-m) n := by
      simpa using (Equiv.neg ℤ).tsum_eq
        (fun m : ℤ => m056ShiftedTerm (-m) n)
    _ = ∑' m : ℤ, m056ShiftedTerm m (-n) := by
      apply tsum_congr
      intro m
      exact m056ShiftedTerm_reflect m n

private theorem m056SourceTsum_reflect (n : ℤ) :
    (∑' l : ℤ, m056SourceTerm l n) = ∑' l : ℤ, m056SourceTerm l (-n) := by
  rw [m056SourceTsum_eq_shift, m056SourceTsum_eq_shift]
  exact m056ShiftedTsum_reflect n



private theorem m056ReciprocalSqTerm_summable : Summable reciprocalSqTerm := by
  have hnat : Summable (fun j : ℕ => m056BracketKernel (j : ℤ)) :=
    m056BracketKernel_summable.comp_injective
      (i := fun j : ℕ => (j : ℤ))
      (by intro a b h; exact Int.ofNat.inj h)
  apply hnat.congr
  intro j
  unfold m056BracketKernel reciprocalSqTerm
  have hj : 0 ≤ (j : ℝ) := by positivity
  rw [Int.cast_natCast, abs_of_nonneg hj]
  push_cast
  ring_nf

private theorem m056ReciprocalSqTail15_le :
    (∑' j : ℕ, reciprocalSqTerm (j + 14)) ≤ 5 / 56 := by
  have htail : reciprocalSqTail (28 : ℤ) ≤ 5 / 28 :=
    lattice_reciprocal_sq_tail (n := 28) (by norm_num)
  have htail' : 2 * (∑' j : ℕ, reciprocalSqTerm (j + 14)) ≤ 5 / 28 := by
    simpa [reciprocalSqTail] using htail
  linarith

private theorem m056ReciprocalSqBase_tsum_lt_five_thirds :
    (∑' j : ℕ, reciprocalSqTerm j) < 5 / 3 := by
  have hs := m056ReciprocalSqTerm_summable
  have hsplit := hs.sum_add_tsum_nat_add 14
  have hprefix :
      (∑ j ∈ Finset.range 14, reciprocalSqTerm j) < (197 / 125 : ℝ) := by
    norm_num [reciprocalSqTerm, Finset.sum_range_succ]
  have htail := m056ReciprocalSqTail15_le
  rw [hsplit.symm]
  linarith

private theorem m056ReciprocalSqPositive_tsum_lt_two_thirds :
    (∑' j : ℕ, reciprocalSqTerm (j + 1)) < 2 / 3 := by
  have hs := m056ReciprocalSqTerm_summable
  have hinj : Function.Injective (fun j : ℕ => j + 1) := by
    intro a b h
    exact Nat.add_right_cancel h
  have hg : Summable (fun j : ℕ => reciprocalSqTerm (j + 1)) :=
    hs.comp_injective (i := fun j : ℕ => j + 1) hinj
  have hsplit := hg.sum_add_tsum_nat_add 13
  have hprefix :
      (∑ j ∈ Finset.range 13, reciprocalSqTerm (j + 1)) < (72 / 125 : ℝ) := by
    norm_num [reciprocalSqTerm, Finset.sum_range_succ]
  have htailShift :
      (∑' j : ℕ, reciprocalSqTerm ((j + 13) + 1)) =
        ∑' j : ℕ, reciprocalSqTerm (j + 14) := by
    apply tsum_congr
    intro j
    rfl
  have htail := m056ReciprocalSqTail15_le
  rw [hsplit.symm, htailShift]
  linarith

private def m056CoreA (N a : ℕ) : ℝ :=
  1 / ((a : ℝ) ^ 2 * ((2 : ℝ) * (N : ℝ) - (a : ℝ) + 1) ^ 2)

private def m056NormalizedA (N a : ℕ) : ℝ :=
  ((N : ℝ) + 1) ^ 2 * m056CoreA N a

private theorem m056Reciprocal_tail_telescope (M n : ℕ) (hM : 0 < M) :
    (∑ j ∈ Finset.range n,
      (1 / ((j + M : ℕ) : ℝ) - 1 / ((j + M + 1 : ℕ) : ℝ))) =
      1 / (M : ℝ) - 1 / ((n + M : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have h₁ : (M : ℝ) ≠ 0 := by positivity
      have h₂ : ((n + M : ℕ) : ℝ) ≠ 0 := by positivity
      have h₃ : ((n + M + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      ring_nf

private theorem m056Reciprocal_tail_partial_le (M n : ℕ) (hM : 0 < M) :
    (∑ j ∈ Finset.range n, 1 / ((j + M + 1 : ℕ) : ℝ) ^ 2) ≤
      1 / (M : ℝ) := by
  calc
    _ ≤ ∑ j ∈ Finset.range n,
        (1 / ((j + M : ℕ) : ℝ) - 1 / ((j + M + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have h₁ : ((j + M : ℕ) : ℝ) ≠ 0 := by positivity
      have h₂ : ((j + M + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have hx : 1 ≤ (j : ℝ) + M := by exact_mod_cast (show 1 ≤ j + M by omega)
      push_cast
      field_simp
      nlinarith
    _ = 1 / (M : ℝ) - 1 / ((n + M : ℕ) : ℝ) :=
      m056Reciprocal_tail_telescope M n hM
    _ ≤ 1 / (M : ℝ) := by
      have hnonneg : 0 ≤ 1 / ((n + M : ℕ) : ℝ) := by positivity
      linarith

private theorem m056Reciprocal_finite_tail_le (s : Finset ℕ) (M N : ℕ)
    (hM : 0 < M) (hs : s ⊆ Finset.Ico (M + 1) N) :
    (∑ a ∈ s, 1 / (a : ℝ) ^ 2) ≤ 1 / (M : ℝ) := by
  calc
    _ ≤ ∑ a ∈ Finset.Ico (M + 1) N, 1 / (a : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (by intros; positivity)
    _ = ∑ j ∈ Finset.range (N - (M + 1)),
        1 / (((M + 1) + j : ℕ) : ℝ) ^ 2 :=
      Finset.sum_Ico_eq_sum_range _ _ _
    _ ≤ 1 / (M : ℝ) := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        m056Reciprocal_tail_partial_le M (N - (M + 1)) hM

private theorem m056Reciprocal_finite_le_five_thirds (s : Finset ℕ) (N : ℕ)
    (hs : s ⊆ Finset.Ico 1 N) :
    (∑ a ∈ s, 1 / (a : ℝ) ^ 2) ≤ 5 / 3 := by
  calc
    _ ≤ ∑ a ∈ Finset.Ico 1 N, 1 / (a : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (by intros; positivity)
    _ = ∑ j ∈ Finset.range (N - 1), reciprocalSqTerm j := by
      rw [Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [reciprocalSqTerm, Nat.add_comm]
    _ ≤ ∑' j : ℕ, reciprocalSqTerm j := by
      exact Summable.sum_le_tsum (Finset.range (N - 1))
        (by intro j hj; unfold reciprocalSqTerm; positivity)
        m056ReciprocalSqTerm_summable
    _ ≤ 5 / 3 := le_of_lt m056ReciprocalSqBase_tsum_lt_five_thirds

private theorem m056NormalizedA_le_ratio (N a : ℕ) (ha : 0 < a)
    (hd : 0 < 2 * (N : ℝ) - (a : ℝ) + 1) (c : ℝ) (hc : 0 ≤ c)
    (hr : (N : ℝ) + 1 ≤ c * (2 * (N : ℝ) - (a : ℝ) + 1)) :
    m056NormalizedA N a ≤ c ^ 2 * (1 / (a : ℝ) ^ 2) := by
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  have hratio : ((N : ℝ) + 1) / (2 * (N : ℝ) - (a : ℝ) + 1) ≤ c :=
    (div_le_iff₀ hd).2 hr
  have hratioNonneg : 0 ≤ ((N : ℝ) + 1) / (2 * (N : ℝ) - (a : ℝ) + 1) :=
    div_nonneg (by positivity) (le_of_lt hd)
  have hsquare : (((N : ℝ) + 1) / (2 * (N : ℝ) - (a : ℝ) + 1)) ^ 2 ≤ c ^ 2 :=
    (sq_le_sq₀ hratioNonneg hc).2 hratio
  calc
    _ = (((N : ℝ) + 1) / (2 * (N : ℝ) - (a : ℝ) + 1)) ^ 2 *
        (1 / (a : ℝ) ^ 2) := by
      unfold m056NormalizedA m056CoreA
      field_simp [ne_of_gt ha', ne_of_gt hd]
    _ ≤ c ^ 2 * (1 / (a : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hsquare (by positivity)

private theorem m056CoreA_large_normalized (N : ℕ) (hN : 24 ≤ N) :
    ((N : ℝ) + 1) ^ 2 * (∑ a ∈ Finset.Ico 1 N, m056CoreA N a) ≤
      125 / 192 + 45 / (16 * (N : ℝ)) + 3 / (N : ℝ) := by
  classical
  let s₀ := (Finset.Ico 1 N).filter (fun a => 4 * a ≤ N)
  let s₁ := (Finset.Ico 1 N).filter (fun a => N < 4 * a ∧ 2 * a ≤ N)
  let s₂ := (Finset.Ico 1 N).filter (fun a => N < 2 * a)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNreal : 24 ≤ (N : ℝ) := by exact_mod_cast hN
  have hs₀ : s₀ ⊆ Finset.Ico 1 N := Finset.filter_subset _ _
  have hs₁ : s₁ ⊆ Finset.Ico 1 N := Finset.filter_subset _ _
  have hs₂ : s₂ ⊆ Finset.Ico 1 N := Finset.filter_subset _ _
  have hpartition :
      (∑ a ∈ Finset.Ico 1 N, m056NormalizedA N a) =
        (∑ a ∈ s₀, m056NormalizedA N a) +
        (∑ a ∈ s₁, m056NormalizedA N a) +
        (∑ a ∈ s₂, m056NormalizedA N a) := by
    simp only [s₀, s₁, s₂, Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h₄ : 4 * a ≤ N
    · have h₂ : 2 * a ≤ N := by omega
      simp [h₄, h₂, not_lt.mpr h₄, not_lt.mpr h₂]
    · have h₄' : N < 4 * a := by omega
      by_cases h₂ : 2 * a ≤ N
      · simp [h₄, h₄', h₂, not_lt.mpr h₂]
      · have h₂' : N < 2 * a := by omega
        simp [h₄, h₄', h₂, h₂']
  have hweighted₀ :
      (∑ a ∈ s₀, m056NormalizedA N a) ≤
        (25 / 64 : ℝ) * (∑ a ∈ s₀, 1 / (a : ℝ) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    have hamem := Finset.mem_Ico.mp (hs₀ ha)
    have h₄ : 4 * a ≤ N := (Finset.mem_filter.mp ha).2
    have har : (a : ℝ) < N := by exact_mod_cast hamem.2
    have h₄r : 4 * (a : ℝ) ≤ N := by exact_mod_cast h₄
    have hd : 0 < 2 * (N : ℝ) - (a : ℝ) + 1 := by linarith
    have hr : (N : ℝ) + 1 ≤ (5 / 8 : ℝ) * (2 * (N : ℝ) - (a : ℝ) + 1) := by
      nlinarith
    simpa only [show (5 / 8 : ℝ) ^ 2 = 25 / 64 by norm_num] using
      m056NormalizedA_le_ratio N a (by omega) hd (5 / 8) (by norm_num) hr
  have hweighted₁ :
      (∑ a ∈ s₁, m056NormalizedA N a) ≤
        (9 / 16 : ℝ) * (∑ a ∈ s₁, 1 / (a : ℝ) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    have hamem := Finset.mem_Ico.mp (hs₁ ha)
    have h₂ : 2 * a ≤ N := (Finset.mem_filter.mp ha).2.2
    have har : (a : ℝ) < N := by exact_mod_cast hamem.2
    have h₂r : 2 * (a : ℝ) ≤ N := by exact_mod_cast h₂
    have hd : 0 < 2 * (N : ℝ) - (a : ℝ) + 1 := by linarith
    have hr : (N : ℝ) + 1 ≤ (3 / 4 : ℝ) * (2 * (N : ℝ) - (a : ℝ) + 1) := by
      nlinarith
    simpa only [show (3 / 4 : ℝ) ^ 2 = 9 / 16 by norm_num] using
      m056NormalizedA_le_ratio N a (by omega) hd (3 / 4) (by norm_num) hr
  have hweighted₂ :
      (∑ a ∈ s₂, m056NormalizedA N a) ≤
        ∑ a ∈ s₂, 1 / (a : ℝ) ^ 2 := by
    apply Finset.sum_le_sum
    intro a ha
    have hamem := Finset.mem_Ico.mp (hs₂ ha)
    have har : (a : ℝ) < N := by exact_mod_cast hamem.2
    have hd : 0 < 2 * (N : ℝ) - (a : ℝ) + 1 := by linarith
    have hr : (N : ℝ) + 1 ≤ (1 : ℝ) * (2 * (N : ℝ) - (a : ℝ) + 1) := by
      linarith
    simpa only [one_pow, one_mul] using
      m056NormalizedA_le_ratio N a (by omega) hd 1 (by norm_num) hr
  have hsum₀ : (∑ a ∈ s₀, 1 / (a : ℝ) ^ 2) ≤ 5 / 3 :=
    m056Reciprocal_finite_le_five_thirds s₀ N hs₀
  have hsum₁ : (∑ a ∈ s₁, 1 / (a : ℝ) ^ 2) ≤ 5 / (N : ℝ) := by
    have hM : 0 < N / 4 := by omega
    have hsubset : s₁ ⊆ Finset.Ico (N / 4 + 1) N := by
      intro a ha
      have hamem := Finset.mem_Ico.mp (hs₁ ha)
      have h₄ : N < 4 * a := (Finset.mem_filter.mp ha).2.1
      exact Finset.mem_Ico.mpr ⟨by omega, hamem.2⟩
    have htail := m056Reciprocal_finite_tail_le s₁ (N / 4) N hM hsubset
    have hMpos : 0 < ((N / 4 : ℕ) : ℝ) := by exact_mod_cast hM
    have hNM : (N : ℝ) ≤ 5 * ((N / 4 : ℕ) : ℝ) := by
      exact_mod_cast (show N ≤ 5 * (N / 4) by omega)
    have hrecip : 1 / ((N / 4 : ℕ) : ℝ) ≤ 5 / (N : ℝ) := by
      apply (div_le_div_iff₀ hMpos hNpos).2
      nlinarith
    exact htail.trans hrecip
  have hsum₂ : (∑ a ∈ s₂, 1 / (a : ℝ) ^ 2) ≤ 3 / (N : ℝ) := by
    have hM : 0 < N / 2 := by omega
    have hsubset : s₂ ⊆ Finset.Ico (N / 2 + 1) N := by
      intro a ha
      have hamem := Finset.mem_Ico.mp (hs₂ ha)
      have h₂ : N < 2 * a := (Finset.mem_filter.mp ha).2
      exact Finset.mem_Ico.mpr ⟨by omega, hamem.2⟩
    have htail := m056Reciprocal_finite_tail_le s₂ (N / 2) N hM hsubset
    have hMpos : 0 < ((N / 2 : ℕ) : ℝ) := by exact_mod_cast hM
    have hNM : (N : ℝ) ≤ 3 * ((N / 2 : ℕ) : ℝ) := by
      exact_mod_cast (show N ≤ 3 * (N / 2) by omega)
    have hrecip : 1 / ((N / 2 : ℕ) : ℝ) ≤ 3 / (N : ℝ) := by
      apply (div_le_div_iff₀ hMpos hNpos).2
      nlinarith
    exact htail.trans hrecip
  calc
    _ = ∑ a ∈ Finset.Ico 1 N, m056NormalizedA N a := by
      rw [Finset.mul_sum]
      rfl
    _ = (∑ a ∈ s₀, m056NormalizedA N a) +
        (∑ a ∈ s₁, m056NormalizedA N a) +
        (∑ a ∈ s₂, m056NormalizedA N a) := hpartition
    _ ≤ (25 / 64 : ℝ) * (∑ a ∈ s₀, 1 / (a : ℝ) ^ 2) +
        (9 / 16 : ℝ) * (∑ a ∈ s₁, 1 / (a : ℝ) ^ 2) +
        (∑ a ∈ s₂, 1 / (a : ℝ) ^ 2) :=
      add_le_add (add_le_add hweighted₀ hweighted₁) hweighted₂
    _ ≤ (25 / 64 : ℝ) * (5 / 3) + (9 / 16 : ℝ) * (5 / (N : ℝ)) +
        3 / (N : ℝ) :=
      add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left hsum₀ (by norm_num))
          (mul_le_mul_of_nonneg_left hsum₁ (by norm_num)))
        hsum₂
    _ = 125 / 192 + 45 / (16 * (N : ℝ)) + 3 / (N : ℝ) := by
      field_simp [ne_of_gt hNpos]
      ring

private theorem m056_tsum_eq_zero_add_positive_pairs (f : ℤ → ℝ)
    (hf : Summable f) :
    (∑' q : ℤ, f q) = f 0 +
      ∑' j : ℕ, (f ((j + 1 : ℕ) : ℤ) + f (-((j + 1 : ℕ) : ℤ))) := by
  let pair : ℤ → ℝ := fun q => f q + f (-q)
  have hnegSummable : Summable (fun q : ℤ => f (-q)) :=
    hf.comp_injective (i := fun q : ℤ => -q) (by intro a b h; simpa using congrArg (fun z : ℤ => -z) h)
  have hpairSummable : Summable pair := by
    exact hf.add hnegSummable
  have hpairEven : Function.Even pair := by
    intro q
    simp [pair, add_comm]
  have hpairInt := tsum_int_eq_zero_add_two_mul_tsum_pnat hpairEven hpairSummable
  have hpairNat : (∑' d : ℕ+, pair (d : ℤ)) =
      ∑' j : ℕ, pair ((j + 1 : ℕ) : ℤ) :=
    tsum_pnat_eq_tsum_succ (f := fun d : ℕ => pair (d : ℤ))
  have hnegTsum : (∑' q : ℤ, f (-q)) = ∑' q : ℤ, f q := by
    simpa using (Equiv.neg ℤ).tsum_eq (fun q : ℤ => f (-q))
  have hpairAdd : (∑' q : ℤ, pair q) =
      pair 0 + (∑' d : ℕ+, pair (d : ℤ)) + (∑' d : ℕ+, pair (d : ℤ)) := by
    simpa only [two_nsmul, add_assoc] using hpairInt
  have htotal : (∑' q : ℤ, pair q) =
      (∑' q : ℤ, f q) + (∑' q : ℤ, f q) := by
    calc
      ∑' q : ℤ, pair q = (∑' q : ℤ, f q) + (∑' q : ℤ, f (-q)) := by
        simpa [pair] using hf.tsum_add hnegSummable
      _ = (∑' q : ℤ, f q) + (∑' q : ℤ, f q) := by rw [hnegTsum]
  have hcombined : (∑' q : ℤ, f q) + (∑' q : ℤ, f q) =
      (f 0 + ∑' j : ℕ, pair ((j + 1 : ℕ) : ℤ)) +
        (f 0 + ∑' j : ℕ, pair ((j + 1 : ℕ) : ℤ)) := by
    calc
      _ = ∑' q : ℤ, pair q := htotal.symm
      _ = pair 0 + (∑' d : ℕ+, pair (d : ℤ)) +
          (∑' d : ℕ+, pair (d : ℤ)) := hpairAdd
      _ = (f 0 + ∑' j : ℕ, pair ((j + 1 : ℕ) : ℤ)) +
          (f 0 + ∑' j : ℕ, pair ((j + 1 : ℕ) : ℤ)) := by
        rw [hpairNat]
        simp [pair]
        ring
  nlinarith [hcombined]

private def m056ZeroPosTerm (j : ℕ) : ℝ :=
  1 / (((j + 1 : ℕ) : ℝ) ^ 2 * ((j + 2 : ℕ) : ℝ) ^ 2)

private def m056ZeroTelescopingTerm (j : ℕ) : ℝ :=
  1 / ((j + 1 : ℕ) : ℝ) - 1 / ((j + 2 : ℕ) : ℝ)

private theorem m056ZeroPosTerm_nonneg (j : ℕ) : 0 ≤ m056ZeroPosTerm j := by
  unfold m056ZeroPosTerm
  positivity

private theorem m056ZeroPosTerm_le_telescope (j : ℕ) :
    m056ZeroPosTerm j ≤ m056ZeroTelescopingTerm j := by
  have hx : 1 ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_add_left 1 j)
  have hrel : ((j + 2 : ℕ) : ℝ) = ((j + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
  unfold m056ZeroPosTerm m056ZeroTelescopingTerm
  rw [hrel]
  have hden : 0 < ((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) + 1) := by positivity
  have hprod : 1 ≤ ((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) + 1) := by
    nlinarith [hx]
  have hdenle :
      ((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) + 1) ≤
        (((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) + 1)) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hprod (le_of_lt hden)
    simpa only [mul_one, pow_two] using hmul
  have h := one_div_le_one_div_of_le hden hdenle
  have hleft :
      ((j + 1 : ℕ) : ℝ) ^ 2 * (((j + 1 : ℕ) : ℝ) + 1) ^ 2 =
        (((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) + 1)) ^ 2 := by ring
  rw [hleft]
  have hright :
      1 / ((j + 1 : ℕ) : ℝ) - 1 / (((j + 1 : ℕ) : ℝ) + 1) =
        1 / (((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) + 1)) := by
    field_simp [ne_of_gt (by positivity : 0 < ((j + 1 : ℕ) : ℝ)),
      ne_of_gt (by positivity : 0 < ((j + 1 : ℕ) : ℝ) + 1)]
    ring
  rw [hright]
  exact h

private theorem m056ZeroTelescoping_partial (n : ℕ) :
    (∑ j ∈ Finset.range n, m056ZeroTelescopingTerm j) =
      1 - 1 / ((n + 1 : ℕ) : ℝ) := by
  induction n with
  | zero => simp [m056ZeroTelescopingTerm]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [m056ZeroTelescopingTerm]
      have h₁ : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have h₂ : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      ring_nf

private theorem m056ZeroPos_partial_le_one (n : ℕ) :
    (∑ j ∈ Finset.range n, m056ZeroPosTerm j) ≤ 1 := by
  calc
    _ ≤ ∑ j ∈ Finset.range n, m056ZeroTelescopingTerm j := by
      apply Finset.sum_le_sum
      intro j hj
      exact m056ZeroPosTerm_le_telescope j
    _ = 1 - 1 / ((n + 1 : ℕ) : ℝ) := m056ZeroTelescoping_partial n
    _ ≤ 1 := by
      have hnonneg : 0 ≤ 1 / ((n + 1 : ℕ) : ℝ) := by positivity
      linarith

private theorem m056ZeroPosTerm_summable : Summable m056ZeroPosTerm := by
  apply summable_of_sum_range_le (fun j => m056ZeroPosTerm_nonneg j)
  exact m056ZeroPos_partial_le_one

private theorem m056ZeroPosTerm_tsum_le_one : ∑' j : ℕ, m056ZeroPosTerm j ≤ 1 :=
  m056ZeroPosTerm_summable.tsum_le_of_sum_range_le m056ZeroPos_partial_le_one

private theorem m056ZeroMode_le_two :
    (∑' m : ℤ, m056ShiftedTerm m 0) ≤ 2 := by
  let f : ℤ → ℝ := fun m => m056ShiftedTerm m 0
  have hs : Summable f := m056ShiftedTerm_summable 0
  have hpnatSummable : Summable (fun d : ℕ+ => f (d : ℤ)) := by
    apply hs.comp_injective (i := fun d : ℕ+ => (d : ℤ))
    exact Int.ofNat_injective.comp PNat.coe_injective
  have heven : Function.Even f := by
    intro m
    simp [f, m056ShiftedTerm, abs_neg]
  have hpair := tsum_int_eq_zero_add_two_mul_tsum_pnat heven hs
  have hpnat : (∑' d : ℕ+, f (d : ℤ)) = ∑' j : ℕ, m056ZeroPosTerm j := by
    calc
      ∑' d : ℕ+, f (d : ℤ) =
          ∑' j : ℕ, f ((j + 1 : ℕ) : ℤ) :=
        tsum_pnat_eq_tsum_succ (f := fun d : ℕ => f (d : ℤ))
      _ = ∑' j : ℕ, m056ZeroPosTerm j := by
        apply tsum_congr
        intro j
        have hj : 0 ≤ (j : ℝ) + 1 := by positivity
        have hjzero : ((j + 1 : ℕ) : ℤ) ≠ 0 := by
          exact_mod_cast (Nat.succ_ne_zero j)
        simp only [f, m056ShiftedTerm, m056ZeroPosTerm, mul_zero, add_zero]
        rw [if_neg hjzero]
        push_cast
        rw [abs_of_nonneg hj]
        congr 1
        ring
  change (∑' m : ℤ, f m) ≤ 2
  calc
    _ = f 0 + 2 * (∑' d : ℕ+, f (d : ℤ)) := by
      simpa only [nsmul_eq_mul, Nat.cast_ofNat] using hpair
    _ = 2 * (∑' j : ℕ, m056ZeroPosTerm j) := by
      rw [hpnat]
      simp [f, m056ShiftedTerm]
    _ ≤ 2 := by linarith [m056ZeroPosTerm_tsum_le_one]

private theorem m056ZeroMode_lt_five_halves :
    (∑' m : ℤ, m056ShiftedTerm m 0) < 5 / 2 := by
  exact lt_of_le_of_lt m056ZeroMode_le_two (by norm_num)

private def m056CoreB (N a : ℕ) : ℝ :=
  1 / (((2 : ℝ) * (N : ℝ) - (a : ℝ)) ^ 2 * ((a : ℝ) + 1) ^ 2)

private def m056OuterC (N a : ℕ) : ℝ :=
  1 / ((a : ℝ) ^ 2 * ((a : ℝ) + 2 * (N : ℝ) + 1) ^ 2)

private def m056OuterD (N a : ℕ) : ℝ :=
  1 / (((a : ℝ) + 2 * (N : ℝ)) ^ 2 * ((a : ℝ) + 1) ^ 2)

private def m056FiniteCore (N : ℕ) : ℝ :=
  if N = 0 then 0 else
    1 / ((N : ℝ) ^ 2 * ((N : ℝ) + 1) ^ 2) +
    1 / (4 * (N : ℝ) ^ 2) +
    (∑ j ∈ Finset.range (N - 1),
      (m056CoreA N (j + 1) + m056CoreB N (j + 1))) +
    (∑ j ∈ Finset.range 16,
      (m056OuterC N (j + 1) + m056OuterD N (j + 1)))

private def m056FiniteUpper (N : ℕ) : ℝ :=
  ((N : ℝ) + 1) ^ 2 * (m056FiniteCore N + 2 / (3 * (16 : ℝ) ^ 3))

private theorem m056FiniteUpper_certificate :
    ∀ N : ℕ, N ∈ Finset.Icc 1 23 → m056FiniteUpper N < 249 / 100 := by
  intro N hN
  rcases Finset.mem_Icc.mp hN with ⟨hlo, hhi⟩
  interval_cases N <;>
    norm_num [m056FiniteUpper, m056FiniteCore, m056CoreA, m056CoreB,
      m056OuterC, m056OuterD, Finset.sum_range_succ]

private def m056FourthTailTerm (j : ℕ) : ℝ :=
  1 / ((j + 17 : ℕ) : ℝ) ^ 4

private def m056FourthTailTelescope (j : ℕ) : ℝ :=
  (1 / ((j + 16 : ℕ) : ℝ) ^ 3 -
    1 / ((j + 17 : ℕ) : ℝ) ^ 3) / 3

private theorem m056FourthTailTerm_nonneg (j : ℕ) :
    0 ≤ m056FourthTailTerm j := by
  unfold m056FourthTailTerm
  positivity

private theorem m056FourthTailTerm_le_telescope (j : ℕ) :
    m056FourthTailTerm j ≤ m056FourthTailTelescope j := by
  have hx : 0 < ((j + 16 : ℕ) : ℝ) := by positivity
  have hy : ((j + 17 : ℕ) : ℝ) = ((j + 16 : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  have hx1 : 0 < ((j + 16 : ℕ) : ℝ) + 1 := by linarith
  unfold m056FourthTailTerm m056FourthTailTelescope
  rw [hy]
  have hpoly : 3 * ((j + 16 : ℕ) : ℝ) ^ 3 ≤
      (3 * ((j + 16 : ℕ) : ℝ) ^ 2 +
        3 * ((j + 16 : ℕ) : ℝ) + 1) * (((j + 16 : ℕ) : ℝ) + 1) := by
    nlinarith [sq_nonneg (((j + 16 : ℕ) : ℝ) - 1)]
  field_simp [ne_of_gt hx, ne_of_gt hx1]
  nlinarith

private theorem m056FourthTailTelescope_partial (n : ℕ) :
    (∑ j ∈ Finset.range n, m056FourthTailTelescope j) =
      (1 / (16 : ℝ) ^ 3 - 1 / ((n + 16 : ℕ) : ℝ) ^ 3) / 3 := by
  induction n with
  | zero => norm_num [m056FourthTailTelescope]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hcast : ((n + 17 : ℕ) : ℝ) = ((n + 16 : ℕ) : ℝ) + 1 := by
        push_cast
        ring
      unfold m056FourthTailTelescope
      rw [hcast]
      push_cast
      ring_nf

private theorem m056FourthTailTerm_partial_le (n : ℕ) :
    (∑ j ∈ Finset.range n, m056FourthTailTerm j) ≤
      1 / (3 * (16 : ℝ) ^ 3) := by
  calc
    (∑ j ∈ Finset.range n, m056FourthTailTerm j) ≤
        ∑ j ∈ Finset.range n, m056FourthTailTelescope j := by
      apply Finset.sum_le_sum
      intro j hj
      exact m056FourthTailTerm_le_telescope j
    _ = (1 / (16 : ℝ) ^ 3 - 1 / ((n + 16 : ℕ) : ℝ) ^ 3) / 3 :=
      m056FourthTailTelescope_partial n
    _ ≤ (1 / (16 : ℝ) ^ 3) / 3 := by
      apply div_le_div_of_nonneg_right
      · have hnonneg : 0 ≤ 1 / ((n + 16 : ℕ) : ℝ) ^ 3 := by positivity
        linarith
      · norm_num
    _ = 1 / (3 * (16 : ℝ) ^ 3) := by
      field_simp
      <;> ring

private theorem m056FourthTailTerm_summable :
    Summable m056FourthTailTerm := by
  apply summable_of_sum_range_le (fun j => m056FourthTailTerm_nonneg j)
  exact m056FourthTailTerm_partial_le

private theorem m056FourthTailTerm_tsum_le :
    (∑' j : ℕ, m056FourthTailTerm j) ≤ 1 / (3 * (16 : ℝ) ^ 3) :=
  Real.tsum_le_of_sum_range_le (fun j => m056FourthTailTerm_nonneg j)
    m056FourthTailTerm_partial_le

private def m056LargeUpper (N : ℕ) : ℝ :=
  125 / 192 + 93 / (16 * (N : ℝ)) + 2 / 3 + 5 / 12 + 6 / 25 +
    ((N : ℝ) + 1) ^ 2 / (4 * (N : ℝ) ^ 2) + 1 / (N : ℝ) ^ 2

private theorem m056LargeUpper_lt_two_half {N : ℕ} (hN : 24 ≤ N) :
    m056LargeUpper N < 5 / 2 := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have h24 : (24 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hrecip : 1 / (N : ℝ) ≤ 1 / 24 :=
    one_div_le_one_div_of_le (by norm_num) h24
  have hratio_eq : ((N : ℝ) + 1) / (N : ℝ) = 1 + 1 / (N : ℝ) := by
    field_simp [ne_of_gt hNr]
  have hratio : ((N : ℝ) + 1) / (N : ℝ) ≤ 25 / 24 := by
    rw [hratio_eq]
    linarith
  have hratio_nonneg : 0 ≤ ((N : ℝ) + 1) / (N : ℝ) := by positivity
  have hratio_sq : (((N : ℝ) + 1) / (N : ℝ)) ^ 2 ≤ (25 / 24 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 25 / 24 - ((N : ℝ) + 1) / (N : ℝ) by linarith)
      (show 0 ≤ 25 / 24 + ((N : ℝ) + 1) / (N : ℝ) by positivity)]
  have hterm_eq : ((N : ℝ) + 1) ^ 2 / (4 * (N : ℝ) ^ 2) =
      ((((N : ℝ) + 1) / (N : ℝ)) ^ 2) / 4 := by
    field_simp [ne_of_gt hNr]
  have hterm : ((N : ℝ) + 1) ^ 2 / (4 * (N : ℝ) ^ 2) ≤ 625 / 2304 := by
    rw [hterm_eq]
    nlinarith [hratio_sq]
  have hrecip_sq : 1 / (N : ℝ) ^ 2 ≤ 1 / 576 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith [h24]
  have hrecip_weighted : 93 / (16 * (N : ℝ)) ≤ 93 / (16 * 24) := by
    have hm := mul_le_mul_of_nonneg_left hrecip (by norm_num : 0 ≤ (93 / 16 : ℝ))
    convert hm using 1 <;> field_simp [ne_of_gt hNr] <;> ring
  unfold m056LargeUpper
  norm_num at hterm hrecip_sq hrecip_weighted ⊢
  linarith

private def m056SourcePair (N : ℤ) (j : ℕ) : ℝ :=
  m056SourceTerm ((j + 1 : ℕ) : ℤ) N +
    m056SourceTerm (-((j + 1 : ℕ) : ℤ)) N

private theorem m056SourcePair_inner_eq_core {N j : ℕ}
    (hN : 2 ≤ N) (hj : j < N - 1) :
    m056SourcePair (N : ℤ) (N - 2 - j) =
      m056CoreA N (j + 1) + m056CoreB N (j + 1) := by
  have hqNat : N - 2 - j + 1 = N - 1 - j := by omega
  have hqposNat : 0 < N - 1 - j := by omega
  have hqleNat : N - 1 - j < N := by omega
  have hqInt : ((N - 2 - j + 1 : ℕ) : ℤ) = ((N - 1 - j : ℕ) : ℤ) := by
    exact_mod_cast hqNat
  have hqne : ((N - 1 - j : ℕ) : ℤ) ≠ (N : ℤ) := by
    exact_mod_cast (show N - 1 - j ≠ N by omega)
  have hnegne : -((N - 1 - j : ℕ) : ℤ) ≠ (N : ℤ) := by
    have hpos : 0 < ((N - 1 - j : ℕ) : ℤ) := by exact_mod_cast hqposNat
    omega
  have hqcast : ((N - 1 - j : ℕ) : ℝ) = (N : ℝ) - (j : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : j ≤ N - 1), Nat.cast_sub (by omega : 1 ≤ N)]
    push_cast
    ring
  have hqbracket : 0 ≤ (N : ℝ) - (j : ℝ) - 1 + (N : ℝ) := by
    have hj' : (j : ℝ) ≤ (N : ℝ) - 2 := by exact_mod_cast (show j ≤ N - 2 by omega)
    linarith
  have hqdiff : 0 ≤ (N : ℝ) - ((N : ℝ) - (j : ℝ) - 1) := by linarith
  have hnegbracket : 0 ≤ -( (N : ℝ) - (j : ℝ) - 1) + (N : ℝ) := by linarith
  have hnegdiff : 0 ≤ (N : ℝ) - (-((N : ℝ) - (j : ℝ) - 1)) := by linarith
  unfold m056SourcePair m056SourceTerm m056CoreA m056CoreB
  rw [hqInt, if_neg hqne, if_neg hnegne]
  push_cast
  rw [hqcast]
  rw [abs_of_nonneg hqbracket, abs_of_nonneg hqdiff,
      abs_of_nonneg hnegbracket, abs_of_nonneg hnegdiff]
  have hdenA :
      (1 + ((N : ℝ) - (j : ℝ) - 1 + (N : ℝ))) ^ 2 *
        ((N : ℝ) - ((N : ℝ) - (j : ℝ) - 1)) ^ 2 =
      ((j : ℝ) + 1) ^ 2 *
        ((2 : ℝ) * (N : ℝ) - ((j : ℝ) + 1) + 1) ^ 2 := by ring
  have hdenB :
      (1 + (-((N : ℝ) - (j : ℝ) - 1) + (N : ℝ))) ^ 2 *
        ((N : ℝ) - (-((N : ℝ) - (j : ℝ) - 1))) ^ 2 =
      ((2 : ℝ) * (N : ℝ) - ((j : ℝ) + 1)) ^ 2 *
        (((j : ℝ) + 1) + 1) ^ 2 := by ring
  apply congrArg₂ (fun x y : ℝ => x + y)
  · exact congrArg (fun d : ℝ => (1 : ℝ) / d) hdenA
  · exact congrArg (fun d : ℝ => (1 : ℝ) / d) hdenB

private theorem m056SourcePair_tail_eq_outer {N j : ℕ} :
    m056SourcePair (N : ℤ) (j + N) =
      m056OuterC N (j + 1) + m056OuterD N (j + 1) := by
  have hqNat : j + N + 1 = N + (j + 1) := by omega
  have hqInt : ((j + N + 1 : ℕ) : ℤ) = (N + (j + 1) : ℕ) := by
    exact_mod_cast hqNat
  have hqne : ((N + (j + 1) : ℕ) : ℤ) ≠ (N : ℤ) := by
    exact_mod_cast (show N + (j + 1) ≠ N by omega)
  have hnegne : -((N + (j + 1) : ℕ) : ℤ) ≠ (N : ℤ) := by
    have hpos : 0 < ((N + (j + 1) : ℕ) : ℤ) := by positivity
    omega
  unfold m056SourcePair m056SourceTerm m056OuterC m056OuterD
  rw [hqInt, if_neg hqne, if_neg hnegne]
  push_cast
  rw [abs_of_nonneg (show 0 ≤ (N : ℝ) + ((j : ℝ) + 1) + (N : ℝ) by positivity),
      abs_of_nonpos (show (N : ℝ) - ((N : ℝ) + ((j : ℝ) + 1)) ≤ 0 by linarith),
      abs_of_nonpos (show -((N : ℝ) + ((j : ℝ) + 1)) + (N : ℝ) ≤ 0 by linarith),
      abs_of_nonneg (show 0 ≤ (N : ℝ) - (-((N : ℝ) + ((j : ℝ) + 1))) by
        have hNreal : 0 ≤ (N : ℝ) := by positivity
        have hjreal : 0 ≤ (j : ℝ) := by positivity
        nlinarith)]
  have hdenC :
      (1 + ((N : ℝ) + ((j : ℝ) + 1) + (N : ℝ))) ^ 2 *
        (-( (N : ℝ) - ((N : ℝ) + ((j : ℝ) + 1)))) ^ 2 =
      ((j : ℝ) + 1) ^ 2 *
        (((j : ℝ) + 1) + (2 : ℝ) * (N : ℝ) + 1) ^ 2 := by ring
  have hdenD :
      (1 + (-( -((N : ℝ) + ((j : ℝ) + 1)) + (N : ℝ)))) ^ 2 *
        ((N : ℝ) - (-((N : ℝ) + ((j : ℝ) + 1)))) ^ 2 =
      (((j : ℝ) + 1) + (2 : ℝ) * (N : ℝ)) ^ 2 *
        (((j : ℝ) + 1) + 1) ^ 2 := by ring
  apply congrArg₂ (fun x y : ℝ => x + y)
  · exact congrArg (fun d : ℝ => (1 : ℝ) / d) hdenC
  · exact congrArg (fun d : ℝ => (1 : ℝ) / d) hdenD

private theorem m056SourcePair_zero_eq_base (N : ℕ) (hN : 1 ≤ N) :
    m056SourceTerm 0 (N : ℤ) =
      1 / ((N : ℝ) ^ 2 * ((N : ℝ) + 1) ^ 2) := by
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  unfold m056SourceTerm
  rw [if_neg (Ne.symm hN0)]
  push_cast
  have hNreal : 0 ≤ (N : ℝ) := by positivity
  have hNpos : 0 < (N : ℝ) := by positivity
  rw [abs_of_nonneg (show 0 ≤ (0 : ℝ) + (N : ℝ) by positivity),
      abs_of_nonneg (show 0 ≤ (N : ℝ) - 0 by positivity)]
  field_simp [ne_of_gt hNpos, ne_of_gt (by linarith : 0 < (N : ℝ) + 1)] <;> ring

private theorem m056SourcePair_special_eq (N : ℕ) (hN : 1 ≤ N) :
    m056SourcePair (N : ℤ) (N - 1) = 1 / (4 * (N : ℝ) ^ 2) := by
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hneg : -(N : ℤ) ≠ (N : ℤ) := by omega
  have hcast : (((N - 1 + 1 : ℕ) : ℤ)) = (N : ℤ) := by
    congr 1
    omega
  unfold m056SourcePair
  rw [hcast]
  simp only [m056SourceTerm, if_pos rfl, if_neg hneg]
  push_cast
  have hcancel : -(N : ℝ) + (N : ℝ) = 0 := by ring
  have htwice : (N : ℝ) - (-(N : ℝ)) = 2 * (N : ℝ) := by ring
  rw [hcancel, abs_zero, htwice, abs_of_nonneg (by positivity : 0 ≤ 2 * (N : ℝ))]
  field_simp <;> ring

private theorem m056SourceTsum_positive_decomposition (N : ℕ)
    (hN : 1 ≤ N) :
    (∑' l : ℤ, m056SourceTerm l (N : ℤ)) =
      1 / ((N : ℝ) ^ 2 * ((N : ℝ) + 1) ^ 2) +
      1 / (4 * (N : ℝ) ^ 2) +
      (∑ j ∈ Finset.range (N - 1),
        (m056CoreA N (j + 1) + m056CoreB N (j + 1))) +
      (∑' j : ℕ,
        (m056OuterC N (j + 1) + m056OuterD N (j + 1))) := by
  let pair : ℤ → ℝ := fun q =>
    m056SourceTerm q (N : ℤ) + m056SourceTerm (-q) (N : ℤ)
  have hsource : Summable (fun l : ℤ => m056SourceTerm l (N : ℤ)) :=
    m056SourceTerm_summable (N : ℤ)
  have hpair : Summable pair := by
    have hneg := hsource.comp_injective (i := fun q : ℤ => -q)
      (by intro a b h; simpa using congrArg (fun z : ℤ => -z) h)
    exact hsource.add hneg
  have hpairNat : Summable (fun j : ℕ => pair ((j + 1 : ℕ) : ℤ)) :=
    hpair.comp_injective (i := fun j : ℕ => ((j + 1 : ℕ) : ℤ))
      (by intro a b h; exact Nat.succ.inj (Int.ofNat.inj h))
  have hsumPair := m056_tsum_eq_zero_add_positive_pairs
    (fun l : ℤ => m056SourceTerm l (N : ℤ)) hsource
  have hsumPair' :
      (∑' l : ℤ, m056SourceTerm l (N : ℤ)) =
        m056SourceTerm 0 (N : ℤ) +
          ∑' j : ℕ, pair ((j + 1 : ℕ) : ℤ) := by
    simpa only [pair] using hsumPair
  have hsplit := hpairNat.sum_add_tsum_nat_add N
  have hsucc : N - 1 + 1 = N := by omega
  have hfinite :
      (∑ j ∈ Finset.range N, pair ((j + 1 : ℕ) : ℤ)) =
        (∑ j ∈ Finset.range (N - 1), pair ((j + 1 : ℕ) : ℤ)) +
          pair ((N - 1 + 1 : ℕ) : ℤ) := by
    calc
      _ = ∑ j ∈ Finset.range (N - 1 + 1), pair ((j + 1 : ℕ) : ℤ) := by rw [hsucc]
      _ = _ := by rw [Finset.sum_range_succ]
  have hinner :
      (∑ j ∈ Finset.range (N - 1),
        pair ((j + 1 : ℕ) : ℤ)) =
      ∑ j ∈ Finset.range (N - 1),
        (m056CoreA N (j + 1) + m056CoreB N (j + 1)) := by
    rw [← Finset.sum_range_reflect (fun j : ℕ =>
      pair ((j + 1 : ℕ) : ℤ)) (N - 1)]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < N - 1 := Finset.mem_range.mp hj
    have hq : (((N - 1 - 1 - j + 1 : ℕ) : ℤ)) =
        ((N - 2 - j + 1 : ℕ) : ℤ) := by
      congr 1
    rw [hq]
    have hN2 : 2 ≤ N := by omega
    exact m056SourcePair_inner_eq_core hN2 hj'
  have htail :
      (∑' j : ℕ, pair ((j + N + 1 : ℕ) : ℤ)) =
        ∑' j : ℕ, (m056OuterC N (j + 1) + m056OuterD N (j + 1)) := by
    apply tsum_congr
    intro j
    have hq : (j + N + 1 : ℕ) = ((j + N) + 1 : ℕ) := by omega
    rw [hq]
    exact m056SourcePair_tail_eq_outer (N := N) (j := j)
  have hbase := m056SourcePair_zero_eq_base N (by omega)
  have hspecial := m056SourcePair_special_eq N (by omega)
  have hspecialPair : pair ((N - 1 + 1 : ℕ) : ℤ) = 1 / (4 * (N : ℝ) ^ 2) := by
    simpa [pair, m056SourcePair, hsucc] using hspecial
  rw [hsumPair', hsplit.symm, hfinite, hinner, htail, hbase, hspecialPair]
  ring

private theorem m056_scaled_reciprocal_square (x b d c : ℝ)
    (hx : 0 ≤ x) (hb : 0 < b) (hd : 0 < d) (hc : 0 ≤ c)
    (hr : x ≤ c * d) :
    x ^ 2 * (1 / (b ^ 2 * d ^ 2)) ≤ c ^ 2 * (1 / b ^ 2) := by
  have hratio : x / d ≤ c := (div_le_iff₀ hd).2 hr
  have hratioNonneg : 0 ≤ x / d := div_nonneg hx (le_of_lt hd)
  have hsquare : (x / d) ^ 2 ≤ c ^ 2 :=
    (sq_le_sq₀ hratioNonneg hc).2 hratio
  calc
    _ = (x / d) ^ 2 * (1 / b ^ 2) := by
      field_simp [ne_of_gt hb, ne_of_gt hd]
    _ ≤ c ^ 2 * (1 / b ^ 2) :=
      mul_le_mul_of_nonneg_right hsquare (by positivity)

private theorem m056CoreB_normalized_pointwise (N a : ℕ)
    (ha : a ∈ Finset.Ico 1 N) :
    ((N : ℝ) + 1) ^ 2 * m056CoreB N a ≤ 1 / ((a : ℝ) + 1) ^ 2 := by
  have hamem := Finset.mem_Ico.mp ha
  have hgap : (a : ℝ) + 1 ≤ N := by
    exact_mod_cast (show a + 1 ≤ N by omega)
  have hb : 0 < (a : ℝ) + 1 := by positivity
  have hd : 0 < 2 * (N : ℝ) - (a : ℝ) := by
    have haReal : 0 ≤ (a : ℝ) := by positivity
    linarith
  have hr : (N : ℝ) + 1 ≤ (1 : ℝ) * (2 * (N : ℝ) - (a : ℝ)) := by
    linarith
  have h := m056_scaled_reciprocal_square ((N : ℝ) + 1)
    ((a : ℝ) + 1) (2 * (N : ℝ) - (a : ℝ)) 1
    (by positivity) hb hd (by norm_num) hr
  simpa only [m056CoreB, one_pow, one_mul, mul_comm] using h

private theorem m056CoreB_large_normalized (N : ℕ) (hN : 24 ≤ N) :
    ((N : ℝ) + 1) ^ 2 * (∑ a ∈ Finset.Ico 1 N, m056CoreB N a) ≤ 2 / 3 := by
  have hsuccSummable : Summable (fun j : ℕ => reciprocalSqTerm (j + 1)) :=
    m056ReciprocalSqTerm_summable.comp_injective
      (i := fun j : ℕ => j + 1) (by intro a b h; exact Nat.add_right_cancel h)
  calc
    _ = ∑ a ∈ Finset.Ico 1 N, ((N : ℝ) + 1) ^ 2 * m056CoreB N a := by
      rw [Finset.mul_sum]
    _ ≤ ∑ a ∈ Finset.Ico 1 N, 1 / ((a : ℝ) + 1) ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      exact m056CoreB_normalized_pointwise N a ha
    _ = ∑ j ∈ Finset.range (N - 1), reciprocalSqTerm (j + 1) := by
      rw [Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [reciprocalSqTerm, Nat.cast_add, Nat.cast_one]
      congr 1
      ring
    _ ≤ ∑' j : ℕ, reciprocalSqTerm (j + 1) := by
      exact Summable.sum_le_tsum (Finset.range (N - 1))
        (by intro j hj; unfold reciprocalSqTerm; positivity) hsuccSummable
    _ ≤ 2 / 3 := le_of_lt m056ReciprocalSqPositive_tsum_lt_two_thirds

private theorem m056OuterC_le_reciprocal (N j : ℕ) :
    m056OuterC N (j + 1) ≤ reciprocalSqTerm j := by
  have hb : 0 < ((j + 1 : ℕ) : ℝ) := by positivity
  have hd : 0 < ((j + 1 : ℕ) : ℝ) + 2 * (N : ℝ) + 1 := by positivity
  have hr : (1 : ℝ) ≤ 1 * (((j + 1 : ℕ) : ℝ) + 2 * (N : ℝ) + 1) := by
    have hN : 0 ≤ (N : ℝ) := by positivity
    linarith
  have h := m056_scaled_reciprocal_square 1 ((j + 1 : ℕ) : ℝ)
    (((j + 1 : ℕ) : ℝ) + 2 * (N : ℝ) + 1) 1
    (by norm_num) hb hd (by norm_num) hr
  simpa only [m056OuterC, reciprocalSqTerm, one_pow, one_mul] using h

private theorem m056OuterC_summable (N : ℕ) :
    Summable (fun j : ℕ => m056OuterC N (j + 1)) := by
  apply Summable.of_nonneg_of_le
    (fun j => by unfold m056OuterC; positivity)
  · intro j
    exact m056OuterC_le_reciprocal N j
  · exact m056ReciprocalSqTerm_summable

private theorem m056OuterC_normalized_pointwise (N j : ℕ) :
    ((N : ℝ) + 1) ^ 2 * m056OuterC N (j + 1) ≤
      (1 / 4 : ℝ) * reciprocalSqTerm j := by
  have hb : 0 < ((j + 1 : ℕ) : ℝ) := by positivity
  have hd : 0 < ((j + 1 : ℕ) : ℝ) + 2 * (N : ℝ) + 1 := by positivity
  have ha : 1 ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_add_left 1 j)
  have hr : (N : ℝ) + 1 ≤
      (1 / 2 : ℝ) * (((j + 1 : ℕ) : ℝ) + 2 * (N : ℝ) + 1) := by
    linarith
  have h := m056_scaled_reciprocal_square ((N : ℝ) + 1)
    ((j + 1 : ℕ) : ℝ) (((j + 1 : ℕ) : ℝ) + 2 * (N : ℝ) + 1)
    (1 / 2) (by positivity) hb hd (by norm_num) hr
  simpa only [m056OuterC, reciprocalSqTerm,
    show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num] using h

private theorem m056OuterC_large_normalized (N : ℕ) (hN : 24 ≤ N) :
    ((N : ℝ) + 1) ^ 2 * (∑' j : ℕ, m056OuterC N (j + 1)) ≤ 5 / 12 := by
  have hs := m056OuterC_summable N
  have hweighted : Summable (fun j : ℕ => ((N : ℝ) + 1) ^ 2 * m056OuterC N (j + 1)) :=
    hs.mul_left (((N : ℝ) + 1) ^ 2)
  have hmajorant : Summable (fun j : ℕ => (1 / 4 : ℝ) * reciprocalSqTerm j) :=
    m056ReciprocalSqTerm_summable.mul_left (1 / 4)
  calc
    _ = ∑' j : ℕ, ((N : ℝ) + 1) ^ 2 * m056OuterC N (j + 1) := by
      rw [tsum_mul_left]
    _ ≤ ∑' j : ℕ, (1 / 4 : ℝ) * reciprocalSqTerm j :=
      Summable.tsum_le_tsum (m056OuterC_normalized_pointwise N) hweighted hmajorant
    _ = (1 / 4 : ℝ) * (∑' j : ℕ, reciprocalSqTerm j) := by
      rw [tsum_mul_left]
    _ ≤ (1 / 4 : ℝ) * (5 / 3) :=
      mul_le_mul_of_nonneg_left (le_of_lt m056ReciprocalSqBase_tsum_lt_five_thirds)
        (by norm_num)
    _ = 5 / 12 := by norm_num

private theorem m056OuterD_le_reciprocal (N j : ℕ) :
    m056OuterD N (j + 1) ≤ reciprocalSqTerm (j + 1) := by
  have ha : 1 ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_add_left 1 j)
  have hb : 0 < ((j + 1 : ℕ) : ℝ) + 1 := by positivity
  have hd : 0 < ((j + 1 : ℕ) : ℝ) + 2 * (N : ℝ) := by positivity
  have hr : (1 : ℝ) ≤ 1 * (((j + 1 : ℕ) : ℝ) + 2 * (N : ℝ)) := by
    have hN : 0 ≤ (N : ℝ) := by positivity
    linarith
  have h := m056_scaled_reciprocal_square 1 (((j + 1 : ℕ) : ℝ) + 1)
    (((j + 1 : ℕ) : ℝ) + 2 * (N : ℝ)) 1
    (by norm_num) hb hd (by norm_num) hr
  simpa only [m056OuterD, reciprocalSqTerm, one_pow, one_mul,
    Nat.cast_add, Nat.cast_one, mul_comm] using h

private theorem m056OuterD_summable (N : ℕ) :
    Summable (fun j : ℕ => m056OuterD N (j + 1)) := by
  have hsuccSummable : Summable (fun j : ℕ => reciprocalSqTerm (j + 1)) :=
    m056ReciprocalSqTerm_summable.comp_injective
      (i := fun j : ℕ => j + 1) (by intro a b h; exact Nat.add_right_cancel h)
  apply Summable.of_nonneg_of_le
    (fun j => by unfold m056OuterD; positivity)
  · intro j
    exact m056OuterD_le_reciprocal N j
  · exact hsuccSummable

private theorem m056OuterD_normalized_pointwise (N j : ℕ) (hN : 24 ≤ N) :
    ((N : ℝ) + 1) ^ 2 * m056OuterD N (j + 1) ≤
      (9 / 25 : ℝ) * reciprocalSqTerm (j + 1) := by
  have ha : 1 ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_add_left 1 j)
  have hNreal : 24 ≤ (N : ℝ) := by exact_mod_cast hN
  have hb : 0 < ((j + 1 : ℕ) : ℝ) + 1 := by positivity
  have hd : 0 < ((j + 1 : ℕ) : ℝ) + 2 * (N : ℝ) := by positivity
  have hr : (N : ℝ) + 1 ≤
      (3 / 5 : ℝ) * (((j + 1 : ℕ) : ℝ) + 2 * (N : ℝ)) := by
    linarith
  have h := m056_scaled_reciprocal_square ((N : ℝ) + 1)
    (((j + 1 : ℕ) : ℝ) + 1) (((j + 1 : ℕ) : ℝ) + 2 * (N : ℝ))
    (3 / 5) (by positivity) hb hd (by norm_num) hr
  simpa only [m056OuterD, reciprocalSqTerm, Nat.cast_add, Nat.cast_one, mul_comm,
    show (3 / 5 : ℝ) ^ 2 = 9 / 25 by norm_num] using h

private theorem m056OuterD_large_normalized (N : ℕ) (hN : 24 ≤ N) :
    ((N : ℝ) + 1) ^ 2 * (∑' j : ℕ, m056OuterD N (j + 1)) ≤ 6 / 25 := by
  have hs := m056OuterD_summable N
  have hweighted : Summable (fun j : ℕ => ((N : ℝ) + 1) ^ 2 * m056OuterD N (j + 1)) :=
    hs.mul_left (((N : ℝ) + 1) ^ 2)
  have hsuccSummable : Summable (fun j : ℕ => reciprocalSqTerm (j + 1)) :=
    m056ReciprocalSqTerm_summable.comp_injective
      (i := fun j : ℕ => j + 1) (by intro a b h; exact Nat.add_right_cancel h)
  have hmajorant : Summable (fun j : ℕ => (9 / 25 : ℝ) * reciprocalSqTerm (j + 1)) :=
    hsuccSummable.mul_left (9 / 25)
  calc
    _ = ∑' j : ℕ, ((N : ℝ) + 1) ^ 2 * m056OuterD N (j + 1) := by
      rw [tsum_mul_left]
    _ ≤ ∑' j : ℕ, (9 / 25 : ℝ) * reciprocalSqTerm (j + 1) :=
      Summable.tsum_le_tsum (fun j => m056OuterD_normalized_pointwise N j hN)
        hweighted hmajorant
    _ = (9 / 25 : ℝ) * (∑' j : ℕ, reciprocalSqTerm (j + 1)) := by
      rw [tsum_mul_left]
    _ ≤ (9 / 25 : ℝ) * (2 / 3) :=
      mul_le_mul_of_nonneg_left (le_of_lt m056ReciprocalSqPositive_tsum_lt_two_thirds)
        (by norm_num)
    _ = 6 / 25 := by norm_num

private theorem m056_reciprocal_product_le_fourth (a b d : ℝ)
    (ha : 0 < a) (hb : a ≤ b) (hd : a ≤ d) :
    1 / (b ^ 2 * d ^ 2) ≤ 1 / a ^ 4 := by
  have hbNonneg : 0 ≤ b := (le_of_lt ha).trans hb
  have hdNonneg : 0 ≤ d := (le_of_lt ha).trans hd
  have hbSquare : a ^ 2 ≤ b ^ 2 := (sq_le_sq₀ (le_of_lt ha) hbNonneg).2 hb
  have hdSquare : a ^ 2 ≤ d ^ 2 := (sq_le_sq₀ (le_of_lt ha) hdNonneg).2 hd
  have hden : a ^ 4 ≤ b ^ 2 * d ^ 2 := by
    calc
      _ = a ^ 2 * a ^ 2 := by ring
      _ ≤ b ^ 2 * d ^ 2 :=
        mul_le_mul hbSquare hdSquare (sq_nonneg a) (sq_nonneg b)
  exact one_div_le_one_div_of_le (pow_pos ha 4) hden

private theorem m056OuterC_le_fourth (N j : ℕ) :
    m056OuterC N (j + 1) ≤ 1 / (((j + 1 : ℕ) : ℝ) ^ 4) := by
  have ha : 0 < ((j + 1 : ℕ) : ℝ) := by positivity
  have hN : 0 ≤ (N : ℝ) := by positivity
  have hd : ((j + 1 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) + 2 * (N : ℝ) + 1 := by
    linarith
  simpa only [m056OuterC] using
    m056_reciprocal_product_le_fourth ((j + 1 : ℕ) : ℝ)
      ((j + 1 : ℕ) : ℝ) (((j + 1 : ℕ) : ℝ) + 2 * (N : ℝ) + 1)
      ha le_rfl hd

private theorem m056OuterD_le_fourth (N j : ℕ) :
    m056OuterD N (j + 1) ≤ 1 / (((j + 1 : ℕ) : ℝ) ^ 4) := by
  have ha : 0 < ((j + 1 : ℕ) : ℝ) := by positivity
  have hN : 0 ≤ (N : ℝ) := by positivity
  have hb : ((j + 1 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) + 2 * (N : ℝ) := by
    linarith
  have hd : ((j + 1 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) + 1 := by linarith
  simpa only [m056OuterD] using
    m056_reciprocal_product_le_fourth ((j + 1 : ℕ) : ℝ)
      (((j + 1 : ℕ) : ℝ) + 2 * (N : ℝ)) (((j + 1 : ℕ) : ℝ) + 1)
      ha hb hd

private theorem m056OuterPair_tail_pointwise (N j : ℕ) :
    m056OuterC N ((j + 16) + 1) + m056OuterD N ((j + 16) + 1) ≤
      2 * m056FourthTailTerm j := by
  have hindex : (j + 16) + 1 = j + 17 := by omega
  simpa only [m056FourthTailTerm, hindex, two_mul] using
    add_le_add (m056OuterC_le_fourth N (j + 16))
      (m056OuterD_le_fourth N (j + 16))

private theorem m056OuterPair_tsum_le_sixteen_prefix (N : ℕ) :
    (∑' j : ℕ, (m056OuterC N (j + 1) + m056OuterD N (j + 1))) ≤
      (∑ j ∈ Finset.range 16, (m056OuterC N (j + 1) + m056OuterD N (j + 1))) +
        2 / (3 * (16 : ℝ) ^ 3) := by
  have hsC := m056OuterC_summable N
  have hsD := m056OuterD_summable N
  have hs : Summable (fun j : ℕ => m056OuterC N (j + 1) + m056OuterD N (j + 1)) :=
    hsC.add hsD
  have htailSummable : Summable (fun j : ℕ =>
      m056OuterC N ((j + 16) + 1) + m056OuterD N ((j + 16) + 1)) :=
    hs.comp_injective (i := fun j : ℕ => j + 16)
      (by intro a b h; exact Nat.add_right_cancel h)
  have hmajorant : Summable (fun j : ℕ => (2 : ℝ) * m056FourthTailTerm j) :=
    m056FourthTailTerm_summable.mul_left 2
  have htail :
      (∑' j : ℕ, (m056OuterC N ((j + 16) + 1) + m056OuterD N ((j + 16) + 1))) ≤
        2 / (3 * (16 : ℝ) ^ 3) := by
    calc
      _ ≤ ∑' j : ℕ, (2 : ℝ) * m056FourthTailTerm j :=
        Summable.tsum_le_tsum (m056OuterPair_tail_pointwise N) htailSummable hmajorant
      _ = 2 * (∑' j : ℕ, m056FourthTailTerm j) := by rw [tsum_mul_left]
      _ ≤ 2 * (1 / (3 * (16 : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_left m056FourthTailTerm_tsum_le (by norm_num)
      _ = 2 / (3 * (16 : ℝ) ^ 3) := by norm_num
  have hsplit := hs.sum_add_tsum_nat_add 16
  rw [hsplit.symm]
  exact add_le_add le_rfl htail

private theorem m056Finite_components_le_upper (N : ℕ) (hN : 0 < N) :
    ((N : ℝ) + 1) ^ 2 *
      (1 / ((N : ℝ) ^ 2 * ((N : ℝ) + 1) ^ 2) +
        1 / (4 * (N : ℝ) ^ 2) +
        (∑ j ∈ Finset.range (N - 1),
          (m056CoreA N (j + 1) + m056CoreB N (j + 1))) +
        (∑' j : ℕ, (m056OuterC N (j + 1) + m056OuterD N (j + 1)))) ≤
      m056FiniteUpper N := by
  have houter := m056OuterPair_tsum_le_sixteen_prefix N
  unfold m056FiniteUpper m056FiniteCore
  rw [if_neg (by omega : N ≠ 0)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg ((N : ℝ) + 1))
  linarith only [houter]

private theorem m056_sum_shift_Ico (f : ℕ → ℝ) (N : ℕ) :
    (∑ a ∈ Finset.Ico 1 N, f a) =
      ∑ j ∈ Finset.range (N - 1), f (j + 1) := by
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  omega

private theorem m056Positive_large_normalized_lt (N : ℕ) (hN : 24 ≤ N) :
    ((N : ℝ) + 1) ^ 2 * (∑' l : ℤ, m056SourceTerm l (N : ℤ)) < 5 / 2 := by
  have hNpos : 0 < N := by omega
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hfactor : 0 < ((N : ℝ) + 1) ^ 2 := by positivity
  have hdecomp := m056SourceTsum_positive_decomposition N (by omega)
  have hsumTail : (∑' j : ℕ,
      (m056OuterC N (j + 1) + m056OuterD N (j + 1))) =
      (∑' j : ℕ, m056OuterC N (j + 1)) +
      (∑' j : ℕ, m056OuterD N (j + 1)) :=
    (m056OuterC_summable N).tsum_add (m056OuterD_summable N)
  have hnormEq : ((N : ℝ) + 1) ^ 2 *
      (∑' l : ℤ, m056SourceTerm l (N : ℤ)) =
      ((N : ℝ) + 1) ^ 2 *
          (1 / ((N : ℝ) ^ 2 * ((N : ℝ) + 1) ^ 2)) +
        ((N : ℝ) + 1) ^ 2 * (1 / (4 * (N : ℝ) ^ 2)) +
        ((N : ℝ) + 1) ^ 2 *
          (∑ j ∈ Finset.range (N - 1),
            (m056CoreA N (j + 1) + m056CoreB N (j + 1))) +
        ((N : ℝ) + 1) ^ 2 * (∑' j : ℕ, m056OuterC N (j + 1)) +
        ((N : ℝ) + 1) ^ 2 * (∑' j : ℕ, m056OuterD N (j + 1)) := by
    rw [hdecomp, hsumTail]
    ring
  have hA : ((N : ℝ) + 1) ^ 2 *
      (∑ j ∈ Finset.range (N - 1), m056CoreA N (j + 1)) ≤
        125 / 192 + 45 / (16 * (N : ℝ)) + 3 / (N : ℝ) := by
    rw [← m056_sum_shift_Ico (fun a => m056CoreA N a) N]
    exact m056CoreA_large_normalized N hN
  have hB : ((N : ℝ) + 1) ^ 2 *
      (∑ j ∈ Finset.range (N - 1), m056CoreB N (j + 1)) ≤ 2 / 3 := by
    rw [← m056_sum_shift_Ico (fun a => m056CoreB N a) N]
    exact m056CoreB_large_normalized N hN
  have hABsum :
      (∑ j ∈ Finset.range (N - 1),
        (m056CoreA N (j + 1) + m056CoreB N (j + 1))) =
        (∑ j ∈ Finset.range (N - 1), m056CoreA N (j + 1)) +
        (∑ j ∈ Finset.range (N - 1), m056CoreB N (j + 1)) := by
    rw [Finset.sum_add_distrib]
  have hAB : ((N : ℝ) + 1) ^ 2 *
      (∑ j ∈ Finset.range (N - 1),
        (m056CoreA N (j + 1) + m056CoreB N (j + 1))) ≤
        (125 / 192 + 45 / (16 * (N : ℝ)) + 3 / (N : ℝ)) + 2 / 3 := by
    rw [hABsum, mul_add]
    exact add_le_add hA hB
  have hC := m056OuterC_large_normalized N hN
  have hD := m056OuterD_large_normalized N hN
  have hbase : ((N : ℝ) + 1) ^ 2 *
      (1 / ((N : ℝ) ^ 2 * ((N : ℝ) + 1) ^ 2)) = 1 / (N : ℝ) ^ 2 := by
    field_simp [ne_of_gt hNr] <;> ring
  have hspecial : ((N : ℝ) + 1) ^ 2 *
      (1 / (4 * (N : ℝ) ^ 2)) =
        ((N : ℝ) + 1) ^ 2 / (4 * (N : ℝ) ^ 2) := by ring
  have hrate : 45 / (16 * (N : ℝ)) + 3 / (N : ℝ) =
      93 / (16 * (N : ℝ)) := by
    field_simp [ne_of_gt hNr]
    <;> ring
  have hlarge : ((N : ℝ) + 1) ^ 2 *
      (∑' l : ℤ, m056SourceTerm l (N : ℤ)) ≤ m056LargeUpper N := by
    rw [hnormEq, hbase, hspecial]
    unfold m056LargeUpper
    nlinarith [hAB, hC, hD, hrate]
  exact lt_of_le_of_lt hlarge (m056LargeUpper_lt_two_half hN)

private theorem m056Positive_small_normalized_lt (N : ℕ)
    (hN : 1 ≤ N) (hNle : N ≤ 23) :
    ((N : ℝ) + 1) ^ 2 * (∑' l : ℤ, m056SourceTerm l (N : ℤ)) < 5 / 2 := by
  have hcomponent := m056Finite_components_le_upper N (by omega)
  have hcertificate := m056FiniteUpper_certificate N
    (Finset.mem_Icc.mpr ⟨hN, hNle⟩)
  have hbound : ((N : ℝ) + 1) ^ 2 *
      (∑' l : ℤ, m056SourceTerm l (N : ℤ)) ≤ m056FiniteUpper N := by
    rw [m056SourceTsum_positive_decomposition N hN]
    exact hcomponent
  exact lt_trans (hbound.trans_lt hcertificate) (by norm_num)

private theorem m056Positive_normalized_le (N : ℕ) (hN : 1 ≤ N) :
    ((N : ℝ) + 1) ^ 2 * (∑' l : ℤ, m056SourceTerm l (N : ℤ)) ≤ 5 / 2 := by
  by_cases hsmall : N ≤ 23
  · exact le_of_lt (m056Positive_small_normalized_lt N hN hsmall)
  · have hlarge : 24 ≤ N := by omega
    exact le_of_lt (m056Positive_large_normalized_lt N hlarge)

theorem second_two_resolvent_kernel_sum (n : ℤ) :
    (∑' l : ℤ,
      if l = n then (0 : ℝ) else
        1 / ((1 + |((l + n : ℤ) : ℝ)|) ^ 2 * |((n - l : ℤ) : ℝ)| ^ 2)) ≤
      (5 / 2 : ℝ) / (1 + |(n : ℝ)|) ^ 2 := by
  have htarget :
      (∑' l : ℤ,
        if l = n then (0 : ℝ) else
          1 / ((1 + |((l + n : ℤ) : ℝ)|) ^ 2 * |((n - l : ℤ) : ℝ)| ^ 2)) =
        ∑' l : ℤ, m056SourceTerm l n := by
    apply tsum_congr
    intro l
    rfl
  rw [htarget]
  by_cases hnzero : n = 0
  · subst n
    rw [m056SourceTsum_eq_shift]
    have hzero := le_of_lt m056ZeroMode_lt_five_halves
    norm_num at hzero ⊢
    exact hzero
  · let N : ℕ := n.natAbs
    have hNpos : 1 ≤ N := by
      have hNne : N ≠ 0 := by
        exact Int.natAbs_ne_zero.mpr hnzero
      omega
    have hNrepr : (N : ℤ) = n ∨ (N : ℤ) = -n := by
      rcases le_total 0 n with hn | hn
      · left
        exact Int.natAbs_of_nonneg hn
      · right
        calc
          (N : ℤ) = ((-n).natAbs : ℤ) := by simp [N]
          _ = -n := Int.natAbs_of_nonneg (by omega)
    have hsource : (∑' l : ℤ, m056SourceTerm l n) =
        (∑' l : ℤ, m056SourceTerm l (N : ℤ)) := by
      rcases hNrepr with hrepr | hrepr
      · rw [← hrepr]
      · rw [m056SourceTsum_reflect n, ← hrepr]
    have hcastAbs : (N : ℝ) = |(n : ℝ)| := by
      have hcastInt : (N : ℤ) = |n| := by
        rw [Int.natCast_natAbs]
      calc
        (N : ℝ) = ((N : ℤ) : ℝ) := by simp
        _ = ((|n| : ℤ) : ℝ) := congrArg Int.cast hcastInt
        _ = |(n : ℝ)| := by rw [Int.cast_abs]
    have hposnorm := m056Positive_normalized_le N hNpos
    have hfactor : 0 < ((N : ℝ) + 1) ^ 2 := by positivity
    have hscaled : ((N : ℝ) + 1) ^ 2 *
        (∑' l : ℤ, m056SourceTerm l n) ≤ 5 / 2 := by
      rw [hsource]
      exact hposnorm
    have hden : 0 < (1 + |(n : ℝ)|) ^ 2 := by positivity
    apply (le_div_iff₀ hden).2
    calc
      (∑' l : ℤ, m056SourceTerm l n) * (1 + |(n : ℝ)|) ^ 2 =
          ((N : ℝ) + 1) ^ 2 *
            (∑' l : ℤ, m056SourceTerm l n) := by rw [hcastAbs]; ring
      _ ≤ 5 / 2 := by simpa [hcastAbs, mul_comm] using hscaled

end NlsGge.Atomic.M.M056
end
