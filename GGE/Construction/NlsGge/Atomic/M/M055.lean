import NlsGge.Atomic.KST.KST005

set_option autoImplicit false
noncomputable section
namespace NlsGge.Atomic.M.M055

open scoped BigOperators

private def bracketKernel (d : ℤ) : ℝ := 1 / (1 + |(d : ℝ)|) ^ 2

private theorem bracketKernel_nonneg (d : ℤ) : 0 ≤ bracketKernel d := by
  unfold bracketKernel
  positivity

private theorem bracketKernel_summable : Summable bracketKernel := by
  have hhalf : Summable (fun d : ℤ => 1 / |(d : ℝ) + (1 / 2 : ℝ)| ^ (2 : ℝ)) := by
    exact (Real.summable_one_div_int_add_rpow (a := (1 / 2 : ℝ)) (s := (2 : ℝ))).2 (by norm_num)
  apply Summable.of_nonneg_of_le (fun d => bracketKernel_nonneg d)
  intro d
  unfold bracketKernel
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

private def bracketPositiveTerm (j : ℕ) : ℝ := 1 / ((j + 2 : ℕ) : ℝ) ^ 2

private theorem bracketPositiveTerm_nonneg (j : ℕ) : 0 ≤ bracketPositiveTerm j := by
  unfold bracketPositiveTerm
  positivity

private theorem bracketPositiveTerm_le_telescope (j : ℕ) (hj : 0 < j) :
    bracketPositiveTerm j ≤
      1 / ((j + 1 : ℕ) : ℝ) - 1 / ((j + 2 : ℕ) : ℝ) := by
  unfold bracketPositiveTerm
  have hj1 : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have hj2 : (0 : ℝ) < ((j + 2 : ℕ) : ℝ) := by positivity
  have hjrel : ((j + 2 : ℕ) : ℝ) = ((j + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [hjrel]
  field_simp
  nlinarith

private theorem bracketPositiveTerm_partial_le (n : ℕ) :
    (∑ j ∈ Finset.range n, bracketPositiveTerm j) ≤
      if n = 0 then 0 else 3 / 4 - 1 / ((n + 1 : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      by_cases hn : n = 0
      · subst n
        norm_num [bracketPositiveTerm]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        calc
          (∑ j ∈ Finset.range n, bracketPositiveTerm j) + bracketPositiveTerm n ≤
              (3 / 4 - 1 / ((n + 1 : ℕ) : ℝ)) +
                (1 / ((n + 1 : ℕ) : ℝ) - 1 / ((n + 2 : ℕ) : ℝ)) := by
            have hih : (∑ j ∈ Finset.range n, bracketPositiveTerm j) ≤
                3 / 4 - 1 / ((n + 1 : ℕ) : ℝ) := by simpa [hn] using ih
            exact add_le_add hih (bracketPositiveTerm_le_telescope n hnpos)
          _ = 3 / 4 - 1 / (((n + 1) + 1 : ℕ) : ℝ) := by
            push_cast
            ring

private theorem bracketPositiveTerm_summable : Summable bracketPositiveTerm := by
  apply summable_of_sum_range_le (c := 3 / 4) (fun j => bracketPositiveTerm_nonneg j)
  intro n
  have h := bracketPositiveTerm_partial_le n
  by_cases hn : n = 0
  · simpa [hn] using (show 0 ≤ (3 / 4 : ℝ) by norm_num)
  · have hp : 0 ≤ 1 / ((n + 1 : ℕ) : ℝ) := by positivity
    have hle : 3 / 4 - 1 / ((n + 1 : ℕ) : ℝ) ≤ 3 / 4 := by linarith
    have h' : (∑ j ∈ Finset.range n, bracketPositiveTerm j) ≤
        3 / 4 - 1 / ((n + 1 : ℕ) : ℝ) := by simpa [hn] using h
    exact h'.trans hle

private theorem bracketPositiveTerm_tsum_le :
    ∑' j : ℕ, bracketPositiveTerm j ≤ 3 / 4 := by
  apply bracketPositiveTerm_summable.tsum_le_of_sum_range_le
  intro n
  have h := bracketPositiveTerm_partial_le n
  by_cases hn : n = 0
  · simpa [hn] using (show 0 ≤ (3 / 4 : ℝ) by norm_num)
  · have hp : 0 ≤ 1 / ((n + 1 : ℕ) : ℝ) := by positivity
    have hle : 3 / 4 - 1 / ((n + 1 : ℕ) : ℝ) ≤ 3 / 4 := by linarith
    have h' : (∑ j ∈ Finset.range n, bracketPositiveTerm j) ≤
        3 / 4 - 1 / ((n + 1 : ℕ) : ℝ) := by simpa [hn] using h
    exact h'.trans hle

private theorem bracketKernel_tsum_le : ∑' d : ℤ, bracketKernel d ≤ 5 / 2 := by
  have heven : Function.Even bracketKernel := by
    intro d
    simp [bracketKernel, Int.cast_neg, abs_neg]
  have hpair := tsum_int_eq_zero_add_two_mul_tsum_pnat heven bracketKernel_summable
  have hpnat : (∑' d : ℕ+, bracketKernel (d : ℤ)) = ∑' j : ℕ, bracketPositiveTerm j := by
    calc
      ∑' d : ℕ+, bracketKernel (d : ℤ) =
          ∑' j : ℕ, bracketKernel ((j + 1 : ℕ) : ℤ) :=
        tsum_pnat_eq_tsum_succ (f := fun d : ℕ => bracketKernel (d : ℤ))
      _ = ∑' j : ℕ, bracketPositiveTerm j := by
        apply tsum_congr
        intro j
        have hj : 0 ≤ (j : ℝ) + 1 := by positivity
        simp [bracketKernel, bracketPositiveTerm, Int.cast_natCast]
        rw [abs_of_nonneg hj]
        ring_nf
  rw [hpair, hpnat]
  simp only [bracketKernel]
  have hpos := bracketPositiveTerm_tsum_le
  norm_num at hpos ⊢
  linarith

private def kernelTerm (m r : ℤ) : ℝ :=
  if m = 0 then 0 else
    (1 + |(m : ℝ)|) ^ 2 /
      ((1 + |((m + r : ℤ) : ℝ)|) ^ 2 * |(m : ℝ)| ^ 2)

private theorem kernelTerm_nonneg (m r : ℤ) : 0 ≤ kernelTerm m r := by
  unfold kernelTerm
  split_ifs <;> positivity

private theorem kernelTerm_le_four_bracket (m r : ℤ) :
    kernelTerm m r ≤ 4 * bracketKernel (m + r) := by
  by_cases hm : m = 0
  · simp [kernelTerm, hm, bracketKernel]
    positivity
  · have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hsmall : 1 ≤ |(m : ℝ)| := by
      have hpos : 0 < |(m : ℝ)| := abs_pos.mpr hmreal
      have hcase : (m : ℝ) ≤ -1 ∨ 1 ≤ (m : ℝ) := by
        exact_mod_cast (show m ≤ -1 ∨ 1 ≤ m by omega)
      rcases hcase with hneg | hpos'
      · rw [abs_of_nonpos (by linarith : (m : ℝ) ≤ 0)]
        linarith
      · rw [abs_of_nonneg (by linarith : 0 ≤ (m : ℝ))]
        linarith
    have hratio : (1 + |(m : ℝ)|) ^ 2 ≤ 4 * |(m : ℝ)| ^ 2 := by
      nlinarith [hsmall]
    unfold kernelTerm
    rw [if_neg hm]
    unfold bracketKernel
    have hbracket : 0 < (1 + |((m + r : ℤ) : ℝ)|) ^ 2 := by positivity
    have hnonzero : |(m : ℝ)| ^ 2 ≠ 0 := pow_ne_zero 2 (abs_ne_zero.mpr hmreal)
    have := mul_le_mul_of_nonneg_right hratio
      (by positivity : 0 ≤ 1 / ((1 + |((m + r : ℤ) : ℝ)|) ^ 2))
    field_simp at this ⊢
    nlinarith [hbracket, hnonzero]

private theorem kernelTerm_summable (r : ℤ) : Summable (fun m : ℤ => kernelTerm m r) := by
  have hshift : Summable (fun m : ℤ => bracketKernel (m + r)) := by
    exact bracketKernel_summable.comp_injective (i := fun m : ℤ => m + r)
      (by intro a b h; exact add_right_cancel h)
  apply Summable.of_nonneg_of_le (fun m => kernelTerm_nonneg m r)
  intro m
  exact kernelTerm_le_four_bracket m r
  exact hshift.mul_left 4

private def sourceTerm (k n l : ℤ) : ℝ :=
  if k = n then 0 else
    (1 + |((k - n : ℤ) : ℝ)|) ^ 2 /
      ((1 + |((k + l : ℤ) : ℝ)|) ^ 2 * |((n - k : ℤ) : ℝ)| ^ 2)

private theorem sourceTerm_eq_kernel (k n l : ℤ) :
    sourceTerm k n l = kernelTerm (k - n) (n + l) := by
  by_cases hk : k = n
  · simp [sourceTerm, kernelTerm, hk]
  · simp only [sourceTerm, kernelTerm, if_neg hk]
    have hsub : k - n ≠ 0 := sub_ne_zero.mpr hk
    simp only [if_neg hsub]
    simp only [Int.cast_sub, Int.cast_add]
    have hsum : (k : ℝ) - n + (n + l) = k + l := by push_cast; ring
    have hneg : (n : ℝ) - k = -((k : ℝ) - n) := by ring
    rw [← hsum, hneg, abs_neg]

private theorem sourceTerm_summable (n l : ℤ) : Summable (fun k : ℤ => sourceTerm k n l) := by
  have h : Summable (fun k : ℤ => kernelTerm (k - n) (n + l)) :=
    (kernelTerm_summable (n + l)).comp_injective (i := fun k : ℤ => k - n)
      (by intro a b h; have := congrArg (fun z : ℤ => z + n) h; simpa using this)
  rcases h with ⟨s, hs⟩
  refine ⟨s, hs.congr_fun ?_⟩
  intro k
  exact sourceTerm_eq_kernel k n l

private theorem sourceTsum_eq_kernelTsum (n l : ℤ) :
    (∑' k : ℤ, sourceTerm k n l) = ∑' m : ℤ, kernelTerm m (n + l) := by
  calc
    ∑' k : ℤ, sourceTerm k n l = ∑' k : ℤ, kernelTerm (k - n) (n + l) := by
      apply tsum_congr
      intro k
      exact sourceTerm_eq_kernel k n l
    _ = ∑' m : ℤ, kernelTerm m (n + l) := by
      have h := (Equiv.addRight n).tsum_eq
        (fun k : ℤ => kernelTerm (k - n) (n + l))
      simpa [sub_add_cancel] using h.symm

private theorem kernelTerm_reflect (m r : ℤ) :
    kernelTerm (-m) r = kernelTerm m (-r) := by
  by_cases hm : m = 0
  · simp [kernelTerm, hm]
  · have hzero : -m ≠ 0 := by omega
    simp only [kernelTerm, if_neg hm, if_neg hzero]
    simp only [Int.cast_neg]
    push_cast
    have hnum : |(-m : ℝ)| = |(m : ℝ)| := abs_neg _
    have hden : |(-m : ℝ) + r| = |(m : ℝ) + -r| := by
      rw [show (-(m : ℝ) + r) = -((m : ℝ) + -(r : ℝ)) by ring, abs_neg]
    rw [hnum, hden]

private theorem kernelTsum_reflect (r : ℤ) :
    (∑' m : ℤ, kernelTerm m r) = ∑' m : ℤ, kernelTerm m (-r) := by
  calc
    ∑' m : ℤ, kernelTerm m r = ∑' m : ℤ, kernelTerm (-m) r := by
      simpa using (Equiv.neg ℤ).tsum_eq (fun m : ℤ => kernelTerm (-m) r)
    _ = ∑' m : ℤ, kernelTerm m (-r) := by
      apply tsum_congr
      intro m
      exact kernelTerm_reflect m r

private def smallTailKernel (m : ℤ) : ℝ :=
  if (32 : ℝ) < |(m : ℝ)| then 1 / |(m : ℝ)| ^ 2 else 0

private theorem smallTailKernel_nonneg (m : ℤ) : 0 ≤ smallTailKernel m := by
  unfold smallTailKernel
  split_ifs <;> positivity

private theorem smallTailKernel_le_four_bracket (m : ℤ) :
    smallTailKernel m ≤ 4 * bracketKernel m := by
  by_cases hm : (32 : ℝ) < |(m : ℝ)|
  · have hmpos : 1 ≤ |(m : ℝ)| := by linarith
    have hden : 0 < |(m : ℝ)| := by positivity
    have hsum : 1 + |(m : ℝ)| ≤ 2 * |(m : ℝ)| := by nlinarith [hmpos]
    unfold smallTailKernel bracketKernel
    rw [if_pos hm]
    have hsq : (1 + |(m : ℝ)|) ^ 2 ≤ 4 * |(m : ℝ)| ^ 2 := by nlinarith [hsum]
    have hpow : |(m : ℝ)| ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hden)
    have hden' : 0 < (1 + |(m : ℝ)|) ^ 2 := by positivity
    rw [div_eq_mul_one_div, div_eq_mul_one_div]
    field_simp
    nlinarith [hsq, hpow]
  · simp [smallTailKernel, bracketKernel, hm]
    positivity

private theorem smallTailKernel_summable : Summable smallTailKernel := by
  apply Summable.of_nonneg_of_le smallTailKernel_nonneg smallTailKernel_le_four_bracket
  exact bracketKernel_summable.mul_left 4

private theorem smallTailKernel_tsum_le : ∑' m : ℤ, smallTailKernel m ≤ 5 / 64 := by
  let f : ℤ → ℝ := fun k =>
    if (64 : ℝ) / 2 < ((k - 64).natAbs : ℝ) then
      1 / ((k - 64).natAbs : ℝ) ^ 2 else 0
  have hshift : (∑' m : ℤ, smallTailKernel m) = ∑' k : ℤ, f k := by
    have h := (Equiv.addRight (64 : ℤ)).tsum_eq f
    dsimp [f] at h
    rw [show (64 : ℝ) / 2 = 32 by norm_num] at h
    dsimp [f, smallTailKernel]
    rw [show (64 : ℝ) / 2 = 32 by norm_num]
    simpa [Int.natCast_natAbs, Int.cast_abs, sub_add_cancel] using h
  rw [hshift]
  dsimp [f]
  exact lattice_reciprocal_sq_tail_contract (n := 64) (by norm_num)

private theorem kernelTerm_small_core_le (r : ℤ) (hrlo : 1 ≤ r) (hrhi : r ≤ 8) :
    (∑ m ∈ Finset.Icc (-32 : ℤ) 32, kernelTerm m r) ≤ 6 := by
  have hr : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 := by omega
  let e : ℕ ↪ ℤ := ⟨fun j => (j : ℤ) - 32, by
    intro a b h
    change (a : ℤ) - 32 = (b : ℤ) - 32 at h
    have hab : (a : ℤ) = (b : ℤ) := by
      have h' := congrArg (fun x : ℤ => x + 32) h
      simpa only [sub_add_cancel] using h'
    exact_mod_cast hab⟩
  have hIcc : Finset.Icc (-32 : ℤ) 32 = (Finset.range 65).map e := by
    ext z
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hzlo, hzhi⟩
      refine ⟨(z + 32).toNat, ?_, ?_⟩
      · have hcast : ((z + 32).toNat : ℤ) = z + 32 :=
          Int.toNat_of_nonneg (by omega)
        have hj : ((z + 32).toNat : ℤ) < 65 := by omega
        exact_mod_cast hj
      · have hcast : ((z + 32).toNat : ℤ) = z + 32 :=
          Int.toNat_of_nonneg (by omega)
        change ((z + 32).toNat : ℤ) - 32 = z
        omega
    · rintro ⟨j, hj, hz⟩
      change (j : ℤ) - 32 = z at hz
      constructor <;> omega
  rw [hIcc]
  rw [Finset.sum_map]
  · change (∑ x ∈ Finset.range 65, kernelTerm ((x : ℤ) - 32) r) ≤ 6
    rcases hr with hr | hr | hr | hr | hr | hr | hr | hr <;> subst r <;>
      norm_num [Finset.sum_range_succ, kernelTerm]

private def smallCoreTerm (r m : ℤ) : ℝ :=
  if m ∈ Finset.Icc (-32 : ℤ) 32 then kernelTerm m r else 0

private theorem smallCoreTerm_summable (r : ℤ) : Summable (smallCoreTerm r) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc (-32 : ℤ) 32)
  intro m hm
  simp [smallCoreTerm, Finset.mem_Icc, hm]

private theorem smallCoreTerm_tsum (r : ℤ) :
    (∑' m : ℤ, smallCoreTerm r m) = ∑ m ∈ Finset.Icc (-32 : ℤ) 32, kernelTerm m r := by
  rw [tsum_eq_sum (s := Finset.Icc (-32 : ℤ) 32)
    (fun m hm => by simp [smallCoreTerm, Finset.mem_Icc, hm])]
  apply Finset.sum_congr rfl
  intro m hm
  simp [smallCoreTerm, hm]

private def nearTerm (r m : ℤ) : ℝ :=
  if |((m + r : ℤ) : ℝ)| ≤ (r : ℝ) / 2 then kernelTerm m r else 0

private def farTerm (r m : ℤ) : ℝ :=
  if (r : ℝ) / 2 < |((m + r : ℤ) : ℝ)| then kernelTerm m r else 0

private def farTailTerm (r m : ℤ) : ℝ :=
  if (r : ℝ) / 2 < |((m + r : ℤ) : ℝ)| then
    1 / |((m + r : ℤ) : ℝ)| ^ 2 else 0

private theorem nearFar_eq (r m : ℤ) :
    kernelTerm m r = nearTerm r m + farTerm r m := by
  have hcast : ((m + r : ℤ) : ℝ) = (m : ℝ) + (r : ℝ) := by push_cast; ring
  by_cases h : |((m + r : ℤ) : ℝ)| ≤ (r : ℝ) / 2
  · have hreal : |(m : ℝ) + (r : ℝ)| ≤ (r : ℝ) / 2 := by simpa [hcast] using h
    have hnreal : ¬ (r : ℝ) / 2 < |(m : ℝ) + (r : ℝ)| := not_lt.mpr hreal
    simp [nearTerm, farTerm, hcast, hreal, hnreal]
  · have hreal : ¬ |(m : ℝ) + (r : ℝ)| ≤ (r : ℝ) / 2 := by
      simpa [hcast] using h
    have hnreal : (r : ℝ) / 2 < |(m : ℝ) + (r : ℝ)| := not_le.mp hreal
    simp [nearTerm, farTerm, hcast, hreal, hnreal]

private theorem nearTerm_nonneg (r m : ℤ) : 0 ≤ nearTerm r m := by
  unfold nearTerm
  split_ifs
  · exact kernelTerm_nonneg m r
  · positivity

private theorem farTerm_nonneg (r m : ℤ) : 0 ≤ farTerm r m := by
  unfold farTerm
  split_ifs
  · exact kernelTerm_nonneg m r
  · positivity

private theorem nearTerm_le_kernelTerm (r m : ℤ) : nearTerm r m ≤ kernelTerm m r := by
  unfold nearTerm
  split_ifs
  · exact le_rfl
  · exact kernelTerm_nonneg m r

private theorem farTerm_le_kernelTerm (r m : ℤ) : farTerm r m ≤ kernelTerm m r := by
  unfold farTerm
  split_ifs
  · exact le_rfl
  · exact kernelTerm_nonneg m r

private theorem nearTerm_summable (r : ℤ) : Summable (nearTerm r) := by
  apply Summable.of_nonneg_of_le (nearTerm_nonneg r) (nearTerm_le_kernelTerm r)
  exact kernelTerm_summable r

private theorem farTerm_summable (r : ℤ) : Summable (farTerm r) := by
  apply Summable.of_nonneg_of_le (farTerm_nonneg r) (farTerm_le_kernelTerm r)
  exact kernelTerm_summable r

private theorem kernelTsum_eq_near_add_far (r : ℤ) :
    (∑' m : ℤ, kernelTerm m r) =
      (∑' m : ℤ, nearTerm r m) + ∑' m : ℤ, farTerm r m := by
  calc
    (∑' m : ℤ, kernelTerm m r) = ∑' m : ℤ, (nearTerm r m + farTerm r m) := by
      apply tsum_congr
      intro m
      exact nearFar_eq r m
    _ = (∑' m : ℤ, nearTerm r m) + ∑' m : ℤ, farTerm r m :=
      (nearTerm_summable r).tsum_add (farTerm_summable r)

private theorem nearTerm_le_majorant (r m : ℤ) (hr : 9 ≤ r) :
    nearTerm r m ≤ (1 + 2 / (r : ℝ)) ^ 2 * bracketKernel (m + r) := by
  by_cases hm : m = 0
  · simp [nearTerm, kernelTerm, hm]
    exact mul_nonneg (sq_nonneg _) (bracketKernel_nonneg r)
  · have hu : ((m + r : ℤ) : ℝ) = (m : ℝ) + (r : ℝ) := by push_cast; ring
    by_cases hn : |((m + r : ℤ) : ℝ)| ≤ (r : ℝ) / 2
    · have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
      have hr0 : 0 ≤ (r : ℝ) := hrpos.le
      have hmpos : 0 < |(m : ℝ)| := abs_pos.mpr (by exact_mod_cast hm)
      have hshift : ((m + r : ℤ) : ℝ) + -(m : ℝ) = (r : ℝ) := by rw [hu]; ring
      have htriangle : |(r : ℝ)| ≤ |((m + r : ℤ) : ℝ)| + |(m : ℝ)| := by
        calc
          |(r : ℝ)| = |((m + r : ℤ) : ℝ) + -(m : ℝ)| := by rw [← hshift]
          _ ≤ |((m + r : ℤ) : ℝ)| + |-(m : ℝ)| := abs_add_le _ _
          _ = |((m + r : ℤ) : ℝ)| + |(m : ℝ)| := by rw [abs_neg]
      have htri : (r : ℝ) ≤ |((m + r : ℤ) : ℝ)| + |(m : ℝ)| := by
        simpa [abs_of_nonneg hr0] using htriangle
      have hrby2 : (r : ℝ) / 2 ≤ |(m : ℝ)| := by nlinarith
      have hinv : 1 / |(m : ℝ)| ≤ 2 / (r : ℝ) := by
        rw [div_le_div_iff₀ hmpos hrpos]
        nlinarith
      have hratioEq : (1 + |(m : ℝ)|) / |(m : ℝ)| =
          1 + 1 / |(m : ℝ)| := by field_simp [ne_of_gt hmpos]; ring
      have hratio : (1 + |(m : ℝ)|) / |(m : ℝ)| ≤ 1 + 2 / (r : ℝ) := by
        rw [hratioEq]
        linarith
      have hsq : ((1 + |(m : ℝ)|) / |(m : ℝ)|) ^ 2 ≤
          (1 + 2 / (r : ℝ)) ^ 2 :=
        (sq_le_sq₀ (by positivity) (by positivity)).2 hratio
      have hfactor : kernelTerm m r =
          ((1 + |(m : ℝ)|) / |(m : ℝ)|) ^ 2 * bracketKernel (m + r) := by
        unfold kernelTerm
        rw [if_neg hm]
        unfold bracketKernel
        field_simp [ne_of_gt hmpos]
        <;> ring
      have hnreal : |(m : ℝ) + (r : ℝ)| ≤ (r : ℝ) / 2 := by simpa [hu] using hn
      simp only [nearTerm, if_pos hnreal, hu]
      rw [hfactor]
      exact mul_le_mul_of_nonneg_right hsq (bracketKernel_nonneg (m + r))
    · have hnreal : ¬ |(m : ℝ) + (r : ℝ)| ≤ (r : ℝ) / 2 := by simpa [hu] using hn
      simp [nearTerm, hu, hnreal]
      exact mul_nonneg (sq_nonneg _) (bracketKernel_nonneg (m + r))

private theorem bracketKernel_shift_summable (r : ℤ) :
    Summable (fun m : ℤ => bracketKernel (m + r)) :=
  bracketKernel_summable.comp_injective (i := fun m : ℤ => m + r)
    (by intro a b h; exact add_right_cancel h)

private theorem nearTerm_tsum_le (r : ℤ) (hr : 9 ≤ r) :
    (∑' m : ℤ, nearTerm r m) ≤ (1 + 2 / (r : ℝ)) ^ 2 * (5 / 2) := by
  let C : ℝ := (1 + 2 / (r : ℝ)) ^ 2
  have hC : 0 ≤ C := by positivity
  have hmajor : Summable (fun m : ℤ => C * bracketKernel (m + r)) :=
    (bracketKernel_shift_summable r).mul_left C
  have hle := (nearTerm_summable r).tsum_le_tsum
    (fun m => by simpa [C] using nearTerm_le_majorant r m hr) hmajor
  rw [tsum_mul_left] at hle
  have htranslate : (∑' m : ℤ, bracketKernel (m + r)) =
      ∑' u : ℤ, bracketKernel u :=
    (Equiv.addRight r).tsum_eq (fun u : ℤ => bracketKernel u)
  rw [htranslate] at hle
  exact hle.trans (mul_le_mul_of_nonneg_left bracketKernel_tsum_le hC)

private def smallTailTerm (r m : ℤ) : ℝ :=
  if m ∈ Finset.Icc (-32 : ℤ) 32 then 0 else kernelTerm m r

private theorem smallSplit_eq (r m : ℤ) :
    kernelTerm m r = smallCoreTerm r m + smallTailTerm r m := by
  by_cases hm : m ∈ Finset.Icc (-32 : ℤ) 32
  · simp [smallCoreTerm, smallTailTerm, hm]
  · simp [smallCoreTerm, smallTailTerm, hm]

private theorem smallTailTerm_summable (r : ℤ) : Summable (smallTailTerm r) := by
  apply Summable.of_nonneg_of_le
  · intro m
    unfold smallTailTerm
    split_ifs
    · positivity
    · exact kernelTerm_nonneg m r
  · intro m
    unfold smallTailTerm
    split_ifs
    · exact kernelTerm_nonneg m r
    · exact le_of_eq rfl
  · exact kernelTerm_summable r

private theorem smallTailTerm_le_kernelTail (r : ℤ)
    (hrlo : 1 ≤ r) (hrhi : r ≤ 8) (m : ℤ) :
    smallTailTerm r m ≤ (17 / 13 : ℝ) ^ 2 * smallTailKernel m := by
  by_cases hm : m ∈ Finset.Icc (-32 : ℤ) 32
  · simp [smallTailTerm, hm]
    exact mul_nonneg (sq_nonneg (17 / 13 : ℝ)) (smallTailKernel_nonneg m)
  · have hmout : m < -32 ∨ 32 < m := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hm
      exact hm
    have hmabsInt : (33 : ℤ) ≤ |m| := by
      rcases hmout with hmleft | hmright
      · rw [abs_of_neg (by omega : m < 0)]
        omega
      · rw [abs_of_nonneg (by omega : 0 ≤ m)]
        omega
    have hmabs : (33 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast hmabsInt
    have hlarge : 32 < |(m : ℝ)| := by linarith
    have hmne : m ≠ 0 := by
      intro hmzero
      subst m
      simp at hmabsInt
    have hr0 : 0 ≤ (r : ℝ) := by exact_mod_cast (show 0 ≤ r by omega)
    have hr8 : (r : ℝ) ≤ 8 := by exact_mod_cast hrhi
    have hden : |((m + r : ℤ) : ℝ)| ≥ |(m : ℝ)| - 8 := by
      have htriangle := abs_add_le ((m + r : ℤ) : ℝ) (-(r : ℝ))
      have heq : ((m + r : ℤ) : ℝ) + -(r : ℝ) = (m : ℝ) := by push_cast; ring
      rw [heq] at htriangle
      have hrabs : |(r : ℝ)| ≤ 8 := by rw [abs_of_nonneg hr0]; exact hr8
      rw [abs_neg] at htriangle
      nlinarith [abs_nonneg (r : ℝ), abs_nonneg (m : ℝ)]
    have hfactor :
        (1 + |(m : ℝ)|) / |(m : ℝ)| *
          (|(m : ℝ)| / (1 + |((m + r : ℤ) : ℝ)|)) ≤ 17 / 13 := by
      have hmpos : 0 < |(m : ℝ)| := by positivity
      have hupos : 0 < 1 + |((m + r : ℤ) : ℝ)| := by positivity
      have hlower : 26 ≤ 1 + |((m + r : ℤ) : ℝ)| := by
        have : 26 ≤ |(m : ℝ)| - 7 := by linarith [hmabs]
        linarith [hden]
      have hnum : 1 + |(m : ℝ)| ≤ 17 / 13 * (1 + |((m + r : ℤ) : ℝ)|) := by
        nlinarith [hmabs, hlower, hden]
      field_simp [ne_of_gt hmpos, ne_of_gt hupos]
      nlinarith [hnum]
    have hkernel : kernelTerm m r =
        ((1 + |(m : ℝ)|) / |(m : ℝ)| *
          (|(m : ℝ)| / (1 + |((m + r : ℤ) : ℝ)|))) ^ 2 *
          (1 / |(m : ℝ)| ^ 2) := by
      simp [kernelTerm, hmne]
      field_simp
    have hsq := (sq_le_sq₀ (by positivity) (by norm_num : (0 : ℝ) ≤ 17 / 13)).2 hfactor
    rw [smallTailTerm, if_neg hm, smallTailKernel, if_pos hlarge, hkernel]
    exact mul_le_mul_of_nonneg_right hsq (by positivity)

private theorem smallTailTerm_tsum_le (r : ℤ)
    (hrlo : 1 ≤ r) (hrhi : r ≤ 8) :
    (∑' m : ℤ, smallTailTerm r m) ≤ (17 / 13 : ℝ) ^ 2 * (5 / 64) := by
  have hmajor : Summable (fun m : ℤ =>
      (17 / 13 : ℝ) ^ 2 * smallTailKernel m) :=
    smallTailKernel_summable.mul_left ((17 / 13 : ℝ) ^ 2)
  have hle := (smallTailTerm_summable r).tsum_le_tsum
    (fun m => smallTailTerm_le_kernelTail r hrlo hrhi m) hmajor
  rw [tsum_mul_left] at hle
  exact hle.trans (mul_le_mul_of_nonneg_left smallTailKernel_tsum_le (by positivity))

private theorem smallKernelTsum_le_32_5 (r : ℤ)
    (hrlo : 1 ≤ r) (hrhi : r ≤ 8) :
    (∑' m : ℤ, kernelTerm m r) ≤ 32 / 5 := by
  have hsplit : (∑' m : ℤ, kernelTerm m r) =
      (∑' m : ℤ, smallCoreTerm r m) + ∑' m : ℤ, smallTailTerm r m := by
    calc
      (∑' m : ℤ, kernelTerm m r) =
          ∑' m : ℤ, (smallCoreTerm r m + smallTailTerm r m) := by
        apply tsum_congr
        intro m
        exact smallSplit_eq r m
      _ = (∑' m : ℤ, smallCoreTerm r m) + ∑' m : ℤ, smallTailTerm r m :=
        (smallCoreTerm_summable r).tsum_add (smallTailTerm_summable r)
  have hcore : (∑' m : ℤ, smallCoreTerm r m) ≤ 6 := by
    rw [smallCoreTerm_tsum]
    exact kernelTerm_small_core_le r hrlo hrhi
  have htail := smallTailTerm_tsum_le r hrlo hrhi
  calc
    (∑' m : ℤ, kernelTerm m r) =
        (∑' m : ℤ, smallCoreTerm r m) + ∑' m : ℤ, smallTailTerm r m := hsplit
    _ ≤ 6 + (17 / 13 : ℝ) ^ 2 * (5 / 64) := add_le_add hcore htail
    _ ≤ 32 / 5 := by norm_num

private theorem farBracket_le_inverseSq (r m : ℤ) (hr : 9 ≤ r)
    (hfar : (r : ℝ) / 2 < |((m + r : ℤ) : ℝ)|) :
    bracketKernel (m + r) ≤ 1 / |((m + r : ℤ) : ℝ)| ^ 2 := by
  have hu : (1 : ℝ) ≤ |((m + r : ℤ) : ℝ)| := by
    have hrR : (9 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    nlinarith [abs_nonneg ((m + r : ℤ) : ℝ)]
  have huPos : (0 : ℝ) < |((m + r : ℤ) : ℝ)| := by positivity
  have hdenPos : (0 : ℝ) < (1 + |((m + r : ℤ) : ℝ)|) ^ 2 := by positivity
  have hsum : |((m + r : ℤ) : ℝ)| ≤ 1 + |((m + r : ℤ) : ℝ)| := by linarith
  unfold bracketKernel
  rw [div_le_div_iff₀ hdenPos (pow_pos huPos 2)]
  nlinarith [hsum]

private theorem inverseSq_le_four_bracket (u : ℤ)
    (hu : (1 : ℝ) ≤ |(u : ℝ)|) :
    1 / |(u : ℝ)| ^ 2 ≤ 4 * bracketKernel u := by
  have huPos : (0 : ℝ) < |(u : ℝ)| := by positivity
  have hdenPos : (0 : ℝ) < (1 + |(u : ℝ)|) ^ 2 := by positivity
  have hsum : 1 + |(u : ℝ)| ≤ 2 * |(u : ℝ)| := by linarith
  have hsq : (1 + |(u : ℝ)|) ^ 2 ≤ 4 * |(u : ℝ)| ^ 2 := by nlinarith [hsum]
  unfold bracketKernel
  field_simp [ne_of_gt huPos, ne_of_gt hdenPos]
  nlinarith [hsq]

private theorem farTailTerm_nonneg (r m : ℤ) : 0 ≤ farTailTerm r m := by
  unfold farTailTerm
  split_ifs <;> positivity

private theorem farTailTerm_le_four_bracket (r m : ℤ) (hr : 9 ≤ r) :
    farTailTerm r m ≤ 4 * bracketKernel (m + r) := by
  by_cases hfar : (r : ℝ) / 2 < |((m + r : ℤ) : ℝ)|
  · have hu : (1 : ℝ) ≤ |((m + r : ℤ) : ℝ)| := by
      have hrR : (9 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      nlinarith [abs_nonneg ((m + r : ℤ) : ℝ)]
    unfold farTailTerm
    rw [if_pos hfar]
    exact inverseSq_le_four_bracket (m + r) (by simpa using hu)
  · unfold farTailTerm
    split_ifs with h
    · exact (hfar h).elim
    · exact mul_nonneg (by norm_num) (bracketKernel_nonneg (m + r))

private theorem farTailTerm_summable (r : ℤ) (hr : 9 ≤ r) :
    Summable (farTailTerm r) := by
  apply Summable.of_nonneg_of_le (farTailTerm_nonneg r)
  intro m
  exact farTailTerm_le_four_bracket r m hr
  exact (bracketKernel_shift_summable r).mul_left 4

private theorem farTerm_le_four_farTail (r m : ℤ) (hr : 9 ≤ r) :
    farTerm r m ≤ 4 * farTailTerm r m := by
  by_cases hfar : (r : ℝ) / 2 < |((m + r : ℤ) : ℝ)|
  · have hbr := farBracket_le_inverseSq r m hr hfar
    calc
      farTerm r m = kernelTerm m r := by
        unfold farTerm
        rw [if_pos hfar]
      _ ≤ 4 * bracketKernel (m + r) := kernelTerm_le_four_bracket m r
      _ ≤ 4 * (1 / |((m + r : ℤ) : ℝ)| ^ 2) := by nlinarith [hbr]
      _ = 4 * farTailTerm r m := by
        unfold farTailTerm
        rw [if_pos hfar]
  · unfold farTerm farTailTerm
    rw [if_neg hfar, if_neg hfar]
    simp

private theorem farTailTerm_tsum_le (r : ℤ) (hr : 9 ≤ r) :
    (∑' m : ℤ, farTailTerm r m) ≤ 5 / (r : ℝ) := by
  have hr0 : 0 ≤ r := by omega
  have hrabs : (r.natAbs : ℤ) = r := by
    rw [Int.natCast_natAbs, abs_of_nonneg hr0]
  have hrnatInt : (5 : ℤ) ≤ (r.natAbs : ℤ) := by rw [hrabs]; omega
  have hrnat : 5 ≤ r.natAbs := by exact_mod_cast hrnatInt
  have hn : 5 ≤ (-r).natAbs := by simpa [Int.natAbs_neg] using hrnat
  have hprovider := lattice_reciprocal_sq_tail_contract (n := -r) hn
  have hrReal : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr0
  simpa [farTailTerm, Int.natCast_natAbs, Int.cast_abs, Int.natAbs_neg,
    sub_neg, abs_of_nonneg hrReal] using hprovider

private theorem farTerm_tsum_le (r : ℤ) (hr : 9 ≤ r) :
    (∑' m : ℤ, farTerm r m) ≤ 20 / (r : ℝ) := by
  have hmajor : Summable (fun m : ℤ => 4 * farTailTerm r m) :=
    (farTailTerm_summable r hr).mul_left 4
  have hle := (farTerm_summable r).tsum_le_tsum
    (fun m => farTerm_le_four_farTail r m hr) hmajor
  rw [tsum_mul_left] at hle
  calc
    (∑' m : ℤ, farTerm r m) ≤ 4 * ∑' m : ℤ, farTailTerm r m := hle
    _ ≤ 20 / (r : ℝ) := by
      have htail := farTailTerm_tsum_le r hr
      rw [show (20 : ℝ) / r = 4 * (5 / r) by ring]
      exact mul_le_mul_of_nonneg_left htail (by norm_num)

private theorem largeKernelTsum_le_32_5 (r : ℤ) (hr : 9 ≤ r) :
    (∑' m : ℤ, kernelTerm m r) ≤ 32 / 5 := by
  rw [kernelTsum_eq_near_add_far]
  have hrR : (9 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < r := by positivity
  have hfrac : 2 / (r : ℝ) ≤ 2 / 9 := by
    rw [div_le_div_iff₀ hrpos (by norm_num : (0 : ℝ) < 9)]
    nlinarith [hrR]
  have hnearCoeff : 1 + 2 / (r : ℝ) ≤ 11 / 9 := by linarith
  have hnearSq : (1 + 2 / (r : ℝ)) ^ 2 ≤ (11 / 9 : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by norm_num)).2 hnearCoeff
  have hnear := nearTerm_tsum_le r hr
  have hfar := farTerm_tsum_le r hr
  have hfarConst : 20 / (r : ℝ) ≤ 20 / 9 := by
    rw [div_le_div_iff₀ hrpos (by norm_num : (0 : ℝ) < 9)]
    nlinarith
  calc
    (∑' m : ℤ, nearTerm r m) + ∑' m : ℤ, farTerm r m
        ≤ (11 / 9 : ℝ) ^ 2 * (5 / 2) + 20 / 9 :=
          add_le_add (hnear.trans (mul_le_mul_of_nonneg_right hnearSq (by norm_num)))
            (hfar.trans hfarConst)
    _ = 965 / 162 := by norm_num
    _ ≤ 32 / 5 := by norm_num

private theorem kernelTerm_zero_eq_kst (m : ℤ) :
    kernelTerm m 0 = if m ≠ 0 then 1 / ((m - 0).natAbs : ℝ) ^ 2 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [kernelTerm]
  · have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    simp [kernelTerm, hm, Int.natCast_natAbs, Int.cast_abs]
    field_simp [hmreal]

private theorem kernelTsum_zero_le_four :
    (∑' m : ℤ, kernelTerm m 0) ≤ 4 := by
  have heq : (∑' m : ℤ, kernelTerm m 0) =
      ∑' k : ℤ, (if k ≠ 0 then 1 / ((k - 0).natAbs : ℝ) ^ 2 else 0) := by
    apply tsum_congr
    intro m
    exact kernelTerm_zero_eq_kst m
  rw [heq]
  exact lattice_reciprocal_sq_bound_contract (n := 0)

private theorem positiveKernelTsum_le_32_5 (r : ℤ) (hr : 1 ≤ r) :
    (∑' m : ℤ, kernelTerm m r) ≤ 32 / 5 := by
  by_cases hrsmall : r ≤ 8
  · exact smallKernelTsum_le_32_5 r hr hrsmall
  · have hrlarge : 9 ≤ r := by omega
    exact largeKernelTsum_le_32_5 r hrlarge

private theorem kernelTsum_le_32_5 (r : ℤ) :
    (∑' m : ℤ, kernelTerm m r) ≤ 32 / 5 := by
  by_cases hrzero : r = 0
  · subst r
    calc
      (∑' m : ℤ, kernelTerm m 0) ≤ 4 := kernelTsum_zero_le_four
      _ ≤ 32 / 5 := by norm_num
  · by_cases hrpos : 0 < r
    · exact positiveKernelTsum_le_32_5 r (by omega)
    · have hrpos' : 1 ≤ -r := by omega
      rw [kernelTsum_reflect r]
      exact positiveKernelTsum_le_32_5 (-r) hrpos'

theorem first_two_resolvent_kernel_sum (n l : ℤ) :
    ∑' k : ℤ,
      (if k = n then 0 else
        (1 + |((k - n : ℤ) : ℝ)|) ^ 2 /
          ((1 + |((k + l : ℤ) : ℝ)|) ^ 2 * |((n - k : ℤ) : ℝ)| ^ 2)) ≤
      (32 / 5 : ℝ) := by
  change (∑' k : ℤ, sourceTerm k n l) ≤ (32 / 5 : ℝ)
  rw [sourceTsum_eq_kernelTsum]
  exact kernelTsum_le_32_5 (n + l)

end NlsGge.Atomic.M.M055
end
