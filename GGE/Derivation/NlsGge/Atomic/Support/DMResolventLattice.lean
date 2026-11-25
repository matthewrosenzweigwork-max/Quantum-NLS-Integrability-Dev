import Mathlib
import NlsGge.Atomic.KST.KST005

set_option autoImplicit false
noncomputable section
open Filter MeasureTheory
open scoped BigOperators

namespace NlsGge.Atomic.DMResolventLattice

/-- The signed source parameter `n + x + it` used in the free resolvent strip. -/
def dmLambda (n : ℤ) (x t : ℝ) : ℂ :=
  (n : ℂ) + (x : ℂ) + Complex.I * (t : ℂ)

/-- The real-coordinate full-integer resolvent weight. At a pole, real division is totalized. -/
def dmRealLatticeTerm (x t : ℝ) (d : ℤ) : ℝ :=
  1 / ((x - (d : ℝ)) ^ 2 + t ^ 2)

private lemma dmRealLatticeTerm_nonneg (x t : ℝ) (d : ℤ) :
    0 ≤ dmRealLatticeTerm x t d := by
  unfold dmRealLatticeTerm
  positivity

/-- The full-integer real row, used only as an algebraic majorant. -/
def dmFullLatticeSum (x t : ℝ) : ℝ :=
  ∑' d : ℤ, dmRealLatticeTerm x t d

/-- The finite branch of the paper's tail profile includes `t = 0`. -/
def dmTailProfile (t : ℝ) : ℝ := if 1 ≤ |t| then |t|⁻¹ else 1

/-- The three full-integer nearby denominators in the source estimate. -/
def dmNearbySum (x t : ℝ) : ℝ :=
  ∑ τ ∈ Finset.Icc (-1 : ℤ) 1, 1 / ((x - (τ : ℝ)) ^ 2 + t ^ 2)

/-- The complex norm is the source's real-coordinate denominator. -/
theorem dmLambda_sub_frequency_norm_sq (n k : ℤ) (x t : ℝ) :
    ‖dmLambda n x t - (k : ℂ)‖ ^ 2 =
      (x - ((k - n : ℤ) : ℝ)) ^ 2 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [dmLambda, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

private lemma dm_nat_shift_square_summable :
    Summable (fun m : ℕ => (16 : ℝ) / ((m : ℝ) + 1) ^ 2) := by
  have h := (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
  have hs := h.comp_injective Nat.succ_injective
  convert hs.mul_left (16 : ℝ) using 1 <;> simp [div_eq_mul_inv]

/-- The real full-integer row is summable for every real `x,t`; totalized pole terms
are finite algebraic terms, and both rays have square-summable tails. -/
theorem dm_full_lattice_summable (x t : ℝ) :
    Summable (dmRealLatticeTerm x t) := by
  have hg := dm_nat_shift_square_summable
  have hev : ∀ᶠ m : ℕ in Filter.atTop, 2 * |x| + 2 < (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (Filter.eventually_gt_atTop (2 * |x| + 2))
  have hpos : Summable (fun m : ℕ => dmRealLatticeTerm x t (m : ℤ)) := by
    apply Summable.of_norm_bounded_eventually_nat hg
    filter_upwards [hev] with m hm
    have hmpos : 0 < (m : ℝ) := by linarith [abs_nonneg x]
    have hm1 : 1 ≤ (m : ℝ) := by linarith [abs_nonneg x]
    have hmx : 2 * |x| ≤ (m : ℝ) := by linarith
    have hdist : (m : ℝ) / 2 ≤ |x - (m : ℝ)| := by
      have hxle : x ≤ |x| := le_abs_self x
      have hsign : x - (m : ℝ) ≤ 0 := by nlinarith
      rw [abs_of_nonpos hsign]
      nlinarith
    have hsq : ((m : ℝ) / 2) ^ 2 ≤ |x - (m : ℝ)| ^ 2 := by
      nlinarith [sq_nonneg (|x - (m : ℝ)| - (m : ℝ) / 2)]
    have hsq' : ((m : ℝ) / 2) ^ 2 ≤ (x - (m : ℝ)) ^ 2 := by
      simpa only [sq_abs] using hsq
    have hden : ((m : ℝ) / 2) ^ 2 ≤ (x - (m : ℝ)) ^ 2 + t ^ 2 := by
      nlinarith [hsq', sq_nonneg t]
    have hrecip :
        1 / ((x - (m : ℝ)) ^ 2 + t ^ 2) ≤ 1 / ((m : ℝ) / 2) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) hden
    have hcompare : 1 / ((m : ℝ) / 2) ^ 2 ≤ (16 : ℝ) / ((m : ℝ) + 1) ^ 2 := by
      have hm0 : 0 < (m : ℝ) := hmpos
      have hden0 : 0 < ((m : ℝ) / 2) ^ 2 := by positivity
      have hden1 : 0 < ((m : ℝ) + 1) ^ 2 := by positivity
      rw [div_le_div_iff₀ hden0 hden1]
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (dmRealLatticeTerm_nonneg x t (m : ℤ))]
    exact hrecip.trans hcompare
  have hneg : Summable (fun m : ℕ => dmRealLatticeTerm x t (-((m : ℤ) + 1))) := by
    apply Summable.of_norm_bounded_eventually_nat hg
    filter_upwards [hev] with m hm
    let s : ℝ := (m : ℝ) + 1
    have hsx : 2 * |x| ≤ s := by dsimp [s]; linarith
    have hs0 : 0 < s := by dsimp [s]; positivity
    have hdist : s / 2 ≤ |x + s| := by
      have hsign : 0 ≤ s - |x| := by linarith
      have hxlo : -|x| ≤ x := neg_abs_le x
      rw [abs_of_nonneg (by nlinarith [hxlo] : 0 ≤ x + s)]
      nlinarith [hxlo]
    have hsq : (s / 2) ^ 2 ≤ |x + s| ^ 2 := by
      nlinarith [sq_nonneg (|x + s| - s / 2)]
    have hsq' : (s / 2) ^ 2 ≤ (x + s) ^ 2 := by
      simpa only [sq_abs] using hsq
    have hden : (s / 2) ^ 2 ≤ (x + s) ^ 2 + t ^ 2 := by
      nlinarith [hsq', sq_nonneg t]
    have hrecip : 1 / ((x + s) ^ 2 + t ^ 2) ≤ 1 / (s / 2) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) hden
    have hcompare : 1 / (s / 2) ^ 2 ≤ (16 : ℝ) / s ^ 2 := by
      have hspos : 0 < s := hs0
      have hsden0 : 0 < (s / 2) ^ 2 := by positivity
      have hsden1 : 0 < s ^ 2 := by positivity
      rw [div_le_div_iff₀ hsden0 hsden1]
      nlinarith
    have hcast : ((-((m : ℤ) + 1) : ℤ) : ℝ) = -s := by
      dsimp [s]
      push_cast
      ring
    rw [Real.norm_eq_abs,
      abs_of_nonneg (dmRealLatticeTerm_nonneg x t (-((m : ℤ) + 1)))]
    simp only [dmRealLatticeTerm]
    rw [hcast, sub_neg_eq_add]
    change 1 / ((x + s) ^ 2 + t ^ 2) ≤ 16 / s ^ 2
    exact hrecip.trans (by simpa [s] using hcompare)
  exact Summable.of_nat_of_neg_add_one hpos hneg

private def dmHalflineTerm (t y : ℝ) : ℝ := 1 / (y ^ 2 + t ^ 2)

private lemma dm_reciprocalSqTerm_nonneg (m : ℕ) : 0 ≤ reciprocalSqTerm m := by
  unfold reciprocalSqTerm
  positivity

private lemma dm_halfline_nonneg (t y : ℝ) : 0 ≤ dmHalflineTerm t y := by
  unfold dmHalflineTerm
  positivity

private lemma dm_reciprocalSqTerm_summable : Summable reciprocalSqTerm := by
  have h := (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
  have hs := h.comp_injective Nat.succ_injective
  convert hs using 1 <;> ext m <;> simp [reciprocalSqTerm, Nat.cast_add]

private lemma dm_reciprocalSqTail_tsum_le_one :
    (∑' m : ℕ, reciprocalSqTerm (m + 1)) ≤ 1 := by
  have hlat : reciprocalSqLattice 0 ≤ 4 := by
    rw [← reciprocalSqInteger_eq_lattice 0]
    exact lattice_reciprocal_sq_bound 0
  have h := hlat
  simp [reciprocalSqLattice] at h
  have hnonneg : 0 ≤ ∑' m : ℕ, reciprocalSqTerm (m + 1) :=
    tsum_nonneg (fun m => dm_reciprocalSqTerm_nonneg (m + 1))
  nlinarith

private lemma dm_reciprocalSq_tsum_le_two :
    (∑' m : ℕ, reciprocalSqTerm m) ≤ 2 := by
  have hs := dm_reciprocalSqTerm_summable
  have hsplit := hs.sum_add_tsum_nat_add 1
  have hzero : reciprocalSqTerm 0 = 1 := by norm_num [reciprocalSqTerm]
  have hsum :
      (∑' m : ℕ, reciprocalSqTerm m) =
        reciprocalSqTerm 0 + ∑' m : ℕ, reciprocalSqTerm (m + 1) := by
    rw [← hsplit]
    simp [hzero]
  rw [hsum, hzero]
  have htail := dm_reciprocalSqTail_tsum_le_one
  linarith

private lemma dm_halfline_antitone (t : ℝ) (ht : 0 < |t|) :
    AntitoneOn (dmHalflineTerm t) (Set.Ici 0) := by
  intro y hy z hz hyz
  have ht0 : t ≠ 0 := abs_pos.mp ht
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht0
  have hy0 : 0 ≤ y := hy
  have hz0 : 0 ≤ z := hz
  unfold dmHalflineTerm
  apply one_div_le_one_div_of_le
  · nlinarith [sq_nonneg y, ht2]
  · have hprod : 0 ≤ (z - y) * (z + y) :=
      mul_nonneg (sub_nonneg.mpr hyz) (by positivity)
    nlinarith [hprod]

private lemma dm_halfline_integrable (t : ℝ) (ht : 0 < |t|) :
    Integrable (dmHalflineTerm t) := by
  let s : ℝ := |t|
  have hs : 0 < s := ht
  have hbase := integrable_inv_one_add_mul_sq (inv_ne_zero hs.ne')
  have heq : dmHalflineTerm t =
      fun y : ℝ => s⁻¹ ^ 2 * (1 + (s⁻¹ * y) ^ 2)⁻¹ := by
    funext y
    dsimp [dmHalflineTerm, s]
    rw [← sq_abs t]
    field_simp
    ring
  rw [heq]
  exact hbase.const_mul (s⁻¹ ^ 2)

private lemma dm_halfline_integral (t : ℝ) (ht : 0 < |t|) :
    (∫ y in Set.Ioi 0, dmHalflineTerm t y) = Real.pi / (2 * |t|) := by
  let s : ℝ := |t|
  have hs : 0 < s := ht
  have hbase :
      (∫ y in Set.Ioi 0, (1 + y ^ 2)⁻¹) = Real.pi / 2 := by
    simpa using (Real.integral_Ioi_inv_one_add_sq (i := 0))
  have hscale := MeasureTheory.integral_comp_mul_left_Ioi
    (fun y : ℝ => (1 + y ^ 2)⁻¹) 0 (b := s⁻¹) (by positivity)
  have hscaled :
      (∫ y in Set.Ioi 0, (1 + (s⁻¹ * y) ^ 2)⁻¹) = s * (Real.pi / 2) := by
    simpa [hbase, inv_inv, smul_eq_mul] using hscale
  have heq : dmHalflineTerm t =
      fun y : ℝ => s⁻¹ ^ 2 * (1 + (s⁻¹ * y) ^ 2)⁻¹ := by
    funext y
    dsimp [dmHalflineTerm]
    rw [show t ^ 2 = s ^ 2 by simp [s]]
    field_simp
    ring
  calc
    _ = s⁻¹ ^ 2 * (s * (Real.pi / 2)) := by
      rw [heq, MeasureTheory.integral_const_mul, hscaled]
    _ = Real.pi / (2 * |t|) := by
      dsimp [s]
      field_simp [ne_of_gt ht]

private lemma dm_halfline_tsum_le_small (t : ℝ) :
    (∑' m : ℕ, dmHalflineTerm t ((m : ℝ) + 1)) ≤ 2 := by
  have hmajor (m : ℕ) : dmHalflineTerm t ((m : ℝ) + 1) ≤ reciprocalSqTerm m := by
    have hpos : 0 < ((m : ℝ) + 1) ^ 2 := by positivity
    have hden : ((m : ℝ) + 1) ^ 2 ≤ ((m : ℝ) + 1) ^ 2 + t ^ 2 := by
      nlinarith [sq_nonneg t]
    simpa [dmHalflineTerm, reciprocalSqTerm, Nat.cast_add] using
      (one_div_le_one_div_of_le hpos hden)
  have hsum : Summable (fun m : ℕ => dmHalflineTerm t ((m : ℝ) + 1)) := by
    apply Summable.of_nonneg_of_le (fun m => dm_halfline_nonneg t _) hmajor
    exact dm_reciprocalSqTerm_summable
  have hcmp := Summable.tsum_le_tsum hmajor hsum dm_reciprocalSqTerm_summable
  exact hcmp.trans dm_reciprocalSq_tsum_le_two

private lemma dm_halfline_tsum_le_large (t : ℝ) (ht : 1 ≤ |t|) :
    (∑' m : ℕ, dmHalflineTerm t ((m : ℝ) + 1)) ≤ 2 / |t| := by
  have hpos : 0 < |t| := by linarith
  have hint : IntegrableOn (dmHalflineTerm t) (Set.Ioi 0) :=
    (dm_halfline_integrable t hpos).integrableOn
  have hnonneg : ∀ y ∈ Set.Ioi 0, 0 ≤ dmHalflineTerm t y := by
    intro y hy
    exact dm_halfline_nonneg t y
  have hsum0 := (dm_halfline_antitone t hpos).summable_of_integrableOn_Ioi_zero hint hnonneg
  have hsum1 : Summable (fun m : ℕ => dmHalflineTerm t ((m : ℝ) + 1)) := by
    have h := hsum0.comp_injective Nat.succ_injective
    have hfun :
        (fun m : ℕ => dmHalflineTerm t ((m : ℝ) + 1)) =
          (fun m : ℕ => dmHalflineTerm t ((m.succ : ℕ) : ℝ)) := by
      funext m
      simp [Nat.cast_succ]
    exact hfun ▸ h
  have hInt := (dm_halfline_antitone t hpos).tsum_add_one_le_integral hint hnonneg
  have hIntegralBound :
      (∫ y in Set.Ioi 0, dmHalflineTerm t y) ≤ 2 / |t| := by
    rw [dm_halfline_integral t hpos]
    have hpi : Real.pi / 2 < 2 := by linarith [Real.pi_lt_four]
    calc
      Real.pi / (2 * |t|) = (Real.pi / 2) / |t| := by ring
      _ ≤ 2 / |t| := div_le_div_of_nonneg_right hpi.le (abs_nonneg t)
  calc
    _ ≤ ∫ y in Set.Ioi 0, dmHalflineTerm t y := by simpa using hInt
    _ ≤ 2 / |t| := hIntegralBound

private lemma dm_halfline_tsum_le_profile (t : ℝ) :
    (∑' m : ℕ, dmHalflineTerm t ((m : ℝ) + 1)) ≤ 3 * dmTailProfile t := by
  by_cases ht : 1 ≤ |t|
  · rw [dmTailProfile, if_pos ht]
    have h := dm_halfline_tsum_le_large t ht
    have heq : 2 / |t| = 2 * |t|⁻¹ := by rw [div_eq_mul_inv]
    rw [heq] at h
    have hs : 0 ≤ |t|⁻¹ := inv_nonneg.mpr (abs_nonneg t)
    nlinarith
  · rw [dmTailProfile, if_neg ht]
    have h := dm_halfline_tsum_le_small t
    linarith

private lemma dm_positive_tail_le (x t : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) :
    (∑' m : ℕ, dmRealLatticeTerm x t ((m : ℤ) + 2)) ≤ 3 * dmTailProfile t := by
  have hrow := dm_full_lattice_summable x t
  have hpos := hrow.comp_injective (i := fun m : ℕ => (m : ℤ)) Nat.cast_injective
  have htail : Summable (fun m : ℕ => dmRealLatticeTerm x t ((m : ℤ) + 2)) :=
    hpos.comp_injective (i := fun m : ℕ => m + 2) (by intro a b hab; exact Nat.add_right_cancel hab)
  have hmajor : Summable (fun m : ℕ => dmHalflineTerm t ((m : ℝ) + 1)) := by
    have hs := dm_reciprocalSqTerm_summable
    have hle (m : ℕ) : dmHalflineTerm t ((m : ℝ) + 1) ≤ reciprocalSqTerm m := by
      have hpos : 0 < ((m : ℝ) + 1) ^ 2 := by positivity
      have hden : ((m : ℝ) + 1) ^ 2 ≤ ((m : ℝ) + 1) ^ 2 + t ^ 2 := by
        nlinarith [sq_nonneg t]
      simpa [dmHalflineTerm, reciprocalSqTerm, Nat.cast_add] using
        (one_div_le_one_div_of_le hpos hden)
    exact Summable.of_nonneg_of_le (fun m => dm_halfline_nonneg t _) hle hs
  have hpoint (m : ℕ) :
      dmRealLatticeTerm x t ((m : ℤ) + 2) ≤ dmHalflineTerm t ((m : ℝ) + 1) := by
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have hdist : (m : ℝ) + 1 ≤ |x - ((m : ℤ) + 2 : ℤ)| := by
      have hsign : x - ((m : ℤ) + 2 : ℤ) ≤ 0 := by
        push_cast
        nlinarith [hx.2, hm]
      rw [abs_of_nonpos hsign]
      push_cast
      nlinarith [hx.2, hm]
    have hsq := (sq_le_sq₀ (by positivity : 0 ≤ (m : ℝ) + 1)
      (abs_nonneg (x - ((m : ℤ) + 2 : ℤ)))).2 hdist
    have hden : ((m : ℝ) + 1) ^ 2 + t ^ 2 ≤
        (x - ((m : ℤ) + 2 : ℤ)) ^ 2 + t ^ 2 := by
      rw [sq_abs] at hsq
      push_cast at hsq ⊢
      nlinarith [hsq]
    have hpos : 0 < ((m : ℝ) + 1) ^ 2 + t ^ 2 := by positivity
    simpa [dmRealLatticeTerm, dmHalflineTerm, Nat.cast_add, Int.cast_add] using
      (one_div_le_one_div_of_le hpos hden)
  have hcmp := Summable.tsum_le_tsum hpoint htail hmajor
  exact hcmp.trans (dm_halfline_tsum_le_profile t)

private lemma dm_negative_tail_le (x t : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) :
    (∑' m : ℕ, dmRealLatticeTerm x t (-((m : ℤ) + 2))) ≤ 3 * dmTailProfile t := by
  have hrow := dm_full_lattice_summable x t
  have hneg := hrow.comp_injective (i := fun m : ℕ => -((m : ℤ) + 1)) (by
    intro a b hab
    change Int.negSucc a = Int.negSucc b at hab
    exact Int.negSucc.inj hab)
  have htail : Summable (fun m : ℕ => dmRealLatticeTerm x t (-((m : ℤ) + 2))) :=
    hneg.comp_injective (i := fun m : ℕ => m + 1) (by intro a b hab; exact Nat.add_right_cancel hab)
  have hmajor : Summable (fun m : ℕ => dmHalflineTerm t ((m : ℝ) + 1)) := by
    have hs := dm_reciprocalSqTerm_summable
    have hle (m : ℕ) : dmHalflineTerm t ((m : ℝ) + 1) ≤ reciprocalSqTerm m := by
      have hpos : 0 < ((m : ℝ) + 1) ^ 2 := by positivity
      have hden : ((m : ℝ) + 1) ^ 2 ≤ ((m : ℝ) + 1) ^ 2 + t ^ 2 := by
        nlinarith [sq_nonneg t]
      simpa [dmHalflineTerm, reciprocalSqTerm, Nat.cast_add] using
        (one_div_le_one_div_of_le hpos hden)
    exact Summable.of_nonneg_of_le (fun m => dm_halfline_nonneg t _) hle hs
  have hpoint (m : ℕ) :
      dmRealLatticeTerm x t (-((m : ℤ) + 2)) ≤ dmHalflineTerm t ((m : ℝ) + 1) := by
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have hdist : (m : ℝ) + 1 ≤ |x + ((m : ℤ) + 2 : ℤ)| := by
      have hsign : 0 ≤ x + ((m : ℤ) + 2 : ℤ) := by
        push_cast
        nlinarith [hx.1, hm]
      rw [abs_of_nonneg hsign]
      push_cast
      nlinarith [hx.1, hm]
    have hsq := (sq_le_sq₀ (by positivity : 0 ≤ (m : ℝ) + 1)
      (abs_nonneg (x + ((m : ℤ) + 2 : ℤ)))).2 hdist
    have hden : ((m : ℝ) + 1) ^ 2 + t ^ 2 ≤
        (x + ((m : ℤ) + 2 : ℤ)) ^ 2 + t ^ 2 := by
      rw [sq_abs] at hsq
      push_cast at hsq ⊢
      nlinarith [hsq]
    have hpos : 0 < ((m : ℝ) + 1) ^ 2 + t ^ 2 := by positivity
    rw [dmRealLatticeTerm, dmHalflineTerm]
    apply one_div_le_one_div_of_le hpos
    convert hden using 1 <;> push_cast <;> ring
  have hcmp := Summable.tsum_le_tsum hpoint htail hmajor
  exact hcmp.trans (dm_halfline_tsum_le_profile t)

private lemma dm_nearbySum_eq (x t : ℝ) :
    dmNearbySum x t = dmRealLatticeTerm x t (-1) +
      dmRealLatticeTerm x t 0 + dmRealLatticeTerm x t 1 := by
  have hIcc : Finset.Icc (-1 : ℤ) 1 = {-1, 0, 1} := by
    ext z
    simp
    omega
  simp [dmNearbySum, dmRealLatticeTerm, hIcc, add_assoc, add_comm, add_left_comm]

/-- Full-integer scalar lattice estimate on the source strip. This is only an
algebraic majorant; actual parity resolvents retain their own pole exclusion. -/
theorem dm_full_lattice_sum_le (x t : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) :
    dmFullLatticeSum x t ≤ dmNearbySum x t + 6 * dmTailProfile t := by
  have hrow := dm_full_lattice_summable x t
  have hpos := hrow.comp_injective (i := fun m : ℕ => (m : ℤ)) Nat.cast_injective
  have hneg := hrow.comp_injective (i := fun m : ℕ => -((m : ℤ) + 1)) (by
    intro a b hab
    change Int.negSucc a = Int.negSucc b at hab
    exact Int.negSucc.inj hab)
  have hposSplit := hpos.sum_add_tsum_nat_add 2
  have hnegSplit := hneg.sum_add_tsum_nat_add 1
  have hposSplit' :
      (∑' i : ℕ, dmRealLatticeTerm x t (i : ℤ)) =
        (∑ i ∈ Finset.range 2, dmRealLatticeTerm x t (i : ℤ)) +
          ∑' i : ℕ, dmRealLatticeTerm x t ((i : ℤ) + 2) := by
    simpa [Function.comp_def] using hposSplit.symm
  have hnegSplit' :
      (∑' i : ℕ, dmRealLatticeTerm x t (-((i : ℤ) + 1))) =
        (∑ i ∈ Finset.range 1, dmRealLatticeTerm x t (-((i : ℤ) + 1))) +
          ∑' i : ℕ, dmRealLatticeTerm x t (-1 + (-1 + -(i : ℤ))) := by
    simpa [Function.comp_def] using hnegSplit.symm
  have hplus := dm_positive_tail_le x t hx
  have hminus := dm_negative_tail_le x t hx
  have hminus' :
      (∑' i : ℕ, dmRealLatticeTerm x t (-1 + (-1 + -(i : ℤ)))) ≤
        3 * dmTailProfile t := by
    have harg (i : ℕ) : -1 + (-1 + -(i : ℤ)) = -((i : ℤ) + 2) := by ring
    simpa [harg] using hminus
  have hdecomp :
      dmFullLatticeSum x t = dmNearbySum x t +
        (∑' i : ℕ, dmRealLatticeTerm x t ((i : ℤ) + 2)) +
          ∑' i : ℕ, dmRealLatticeTerm x t (-1 + (-1 + -(i : ℤ))) := by
    rw [dmFullLatticeSum, tsum_of_nat_of_neg_add_one hpos hneg,
      hposSplit', hnegSplit', dm_nearbySum_eq]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_range_one,
      Nat.cast_zero, Nat.cast_one, Nat.cast_add, Int.cast_ofNat, Int.cast_neg,
      Int.cast_natCast]
    ring
  rw [hdecomp]
  have htails := add_le_add hplus hminus'
  calc
    _ = dmNearbySum x t +
        ((∑' i : ℕ, dmRealLatticeTerm x t ((i : ℤ) + 2)) +
          ∑' i : ℕ, dmRealLatticeTerm x t (-1 + (-1 + -(i : ℤ)))) := by ring
    _ ≤ dmNearbySum x t + 6 * dmTailProfile t := by nlinarith [htails]

end NlsGge.Atomic.DMResolventLattice
