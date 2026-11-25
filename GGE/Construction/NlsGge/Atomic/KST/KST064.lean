import NlsGge.Atomic.KST.KST043

set_option autoImplicit false
noncomputable section

namespace NlsGge.Atomic.KST064

open Filter
open scoped Topology

/-- The polynomial KST weight of order s. -/
def polynomialWeight (s : ℝ) (k : ℤ) : ℝ :=
  (1 + (k.natAbs : ℝ)) ^ s

/-- The physical Sobolev multiplier with period-one Fourier normalization. -/
def sobolevWeight (s : ℝ) (n : ℤ) : ℝ :=
  (1 + (2 * Real.pi * (n : ℝ)) ^ 2) ^ (s / 2)

private theorem polynomialWeight_at_zero (s : ℝ) : polynomialWeight s 0 = 1 := by
  simp [polynomialWeight]

private theorem polynomialWeight_even (s : ℝ) (k : ℤ) :
    polynomialWeight s (-k) = polynomialWeight s k := by
  simp [polynomialWeight]

private theorem polynomialWeight_monotone_nat (s : ℝ) (hs : 0 ≤ s) :
    Monotone (fun n : ℕ => polynomialWeight s (n : ℤ)) := by
  intro a b hab
  unfold polynomialWeight
  simp only [Int.natAbs_natCast]
  apply Real.rpow_le_rpow
  · positivity
  · nlinarith [show (a : ℝ) ≤ b by exact_mod_cast hab]
  · exact hs

private theorem one_add_natAbs_add_le (k l : ℤ) :
    (1 + ((k + l).natAbs : ℝ)) ≤
      (1 + (k.natAbs : ℝ)) * (1 + (l.natAbs : ℝ)) := by
  have htri := Int.natAbs_add_le k l
  have htri' : ((k + l).natAbs : ℝ) ≤ (k.natAbs : ℝ) + (l.natAbs : ℝ) := by
    exact_mod_cast htri
  nlinarith [htri']

private theorem polynomialWeight_submultiplicative (s : ℝ) (hs : 0 ≤ s) :
    NlsGge.Atomic.DM046.SubmultiplicativeWeight (polynomialWeight s) := by
  intro k l
  unfold polynomialWeight
  have hbase := one_add_natAbs_add_le k l
  have hp := Real.rpow_le_rpow (by positivity) hbase hs
  rw [Real.mul_rpow (by positivity) (by positivity)] at hp
  exact hp

private theorem polynomial_log_ratio_formula (s : ℝ) (n : ℕ+) :
    NlsGge.Atomic.KST043.KSTLogRatio (polynomialWeight s) n =
      s * (Real.log (1 + (n : ℝ)) / (n : ℝ)) := by
  unfold NlsGge.Atomic.KST043.KSTLogRatio polynomialWeight
  have hn : 0 < (1 + (n : ℝ)) := by positivity
  have hnat : ((n : ℤ).natAbs : ℝ) = (n : ℝ) := by
    simp
  rw [hnat]
  rw [Real.log_rpow hn]
  ring

private theorem cast_pos_tendsto_atTop :
    Tendsto (fun n : ℕ+ => (n : ℝ)) atTop atTop := by
  exact tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop

private theorem cast_add_one_tendsto_atTop :
    Tendsto (fun n : ℕ+ => (1 : ℝ) + (n : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ+ => (n : ℝ))
  · intro n
    linarith
  · exact cast_pos_tendsto_atTop

private theorem inv_cast_tendsto_zero :
    Tendsto (fun n : ℕ+ => (n : ℝ)⁻¹) atTop (𝓝 0) := by
  convert tendsto_inv_atTop_zero.comp cast_pos_tendsto_atTop using 1 <;> rfl

private theorem log_one_add_div_nat_tendsto_zero :
    Tendsto (fun n : ℕ+ => Real.log (1 + (n : ℝ)) / (n : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hfirst := hlog.comp cast_add_one_tendsto_atTop
  have hfactor : Tendsto (fun n : ℕ+ => (1 + (n : ℝ)) / (n : ℝ)) atTop (𝓝 1) := by
    have hsum : Tendsto (fun n : ℕ+ => (1 : ℝ) + (n : ℝ)⁻¹) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add inv_cast_tendsto_zero
    convert hsum using 1 <;> ext n <;> field_simp <;> ring
  have hmul := hfirst.mul hfactor
  have hEq : (fun n : ℕ+ => Real.log (1 + (n : ℝ)) / (n : ℝ)) =
      fun n : ℕ+ => (Real.log (1 + (n : ℝ)) / (1 + (n : ℝ))) *
        ((1 + (n : ℝ)) / (n : ℝ)) := by
    funext n
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast n.property.ne'
    have hn1 : 1 + (n : ℝ) ≠ 0 := by positivity
    field_simp <;> ring
  rw [hEq]
  simpa using hmul

private theorem log_one_add_div_nat_antitone_two :
    AntitoneOn (fun n : ℕ+ => Real.log (1 + (n : ℝ)) / (n : ℝ))
      {n | 2 ≤ (n : ℕ)} := by
  intro m hm n hn hmn
  change 2 ≤ m.val at hm
  change 2 ≤ n.val at hn
  have hmexp : Real.exp 1 ≤ 1 + (m : ℝ) := by
    have hthree : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hm3 : (3 : ℝ) ≤ 1 + (m : ℝ) := by
      have hmnat : 3 ≤ 1 + (m : ℕ) := by omega
      exact_mod_cast hmnat
    linarith
  have hnexp : Real.exp 1 ≤ 1 + (n : ℝ) := by
    have hthree : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hn3 : (3 : ℝ) ≤ 1 + (n : ℝ) := by
      have hnnat : 3 ≤ 1 + (n : ℕ) := by omega
      exact_mod_cast hnnat
    linarith
  have hmval : 2 ≤ m.val := by
    change 2 ≤ m.val at hm
    exact hm
  have hnval : 2 ≤ n.val := by
    change 2 ≤ n.val at hn
    exact hn
  have hfirst : Real.log (1 + (n : ℝ)) / (1 + (n : ℝ)) ≤
      Real.log (1 + (m : ℝ)) / (1 + (m : ℝ)) := by
    apply Real.log_div_self_antitoneOn hmexp hnexp
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    linarith
  have hsecond : (1 + (n : ℝ)) / (n : ℝ) ≤ (1 + (m : ℝ)) / (m : ℝ) := by
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast m.property
    have hrecip : (n : ℝ)⁻¹ ≤ (m : ℝ)⁻¹ := by
      have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      simpa [one_div] using one_div_le_one_div_of_le hmpos hmn'
    have hrewriteN : (1 + (n : ℝ)) / (n : ℝ) = 1 + (n : ℝ)⁻¹ := by field_simp <;> ring
    have hrewriteM : (1 + (m : ℝ)) / (m : ℝ) = 1 + (m : ℝ)⁻¹ := by field_simp <;> ring
    rw [hrewriteN, hrewriteM]
    linarith
  have hfirst_nonneg : 0 ≤ Real.log (1 + (n : ℝ)) / (1 + (n : ℝ)) := by
    apply div_nonneg
    · apply Real.log_nonneg
      linarith
    · positivity
  have hsecond_nonneg : 0 ≤ (1 + (m : ℝ)) / (m : ℝ) := by positivity
  have hprod := mul_le_mul hfirst hsecond
    (show 0 ≤ (1 + (n : ℝ)) / (n : ℝ) by positivity)
    (show 0 ≤ Real.log (1 + (m : ℝ)) / (1 + (m : ℝ)) by
      apply div_nonneg
      · apply Real.log_nonneg; linarith
      · positivity)
  have hleft : (Real.log (1 + (n : ℝ)) / (1 + (n : ℝ))) *
      ((1 + (n : ℝ)) / (n : ℝ)) = Real.log (1 + (n : ℝ)) / (n : ℝ) := by
    have hnpos : (n : ℝ) ≠ 0 := by exact_mod_cast n.property.ne'
    field_simp <;> ring
  have hright : (Real.log (1 + (m : ℝ)) / (1 + (m : ℝ))) *
      ((1 + (m : ℝ)) / (m : ℝ)) = Real.log (1 + (m : ℝ)) / (m : ℝ) := by
    have hmpos : (m : ℝ) ≠ 0 := by exact_mod_cast m.property.ne'
    field_simp <;> ring
  rw [hleft, hright] at hprod
  exact hprod

private theorem polynomial_log_ratio_tendsto (s : ℝ) :
    Tendsto (NlsGge.Atomic.KST043.KSTLogRatio (polynomialWeight s)) atTop (𝓝 0) := by
  rw [show NlsGge.Atomic.KST043.KSTLogRatio (polynomialWeight s) =
      fun n : ℕ+ => s * (Real.log (1 + (n : ℝ)) / (n : ℝ)) from by
        funext n
        exact polynomial_log_ratio_formula s n]
  simpa using (tendsto_const_nhds.mul log_one_add_div_nat_tendsto_zero)

private theorem polynomial_log_ratio_antitone (s : ℝ) (hs : 0 ≤ s) :
    AntitoneOn (NlsGge.Atomic.KST043.KSTLogRatio (polynomialWeight s))
      {n : ℕ+ | 2 ≤ (n : ℕ)} := by
  intro m hm n hn hmn
  rw [polynomial_log_ratio_formula, polynomial_log_ratio_formula]
  exact mul_le_mul_of_nonneg_left
    (log_one_add_div_nat_antitone_two hm hn hmn) hs

/-- The polynomial weight is KST-subexponential and its doubled Fourier
profile is pointwise equivalent, with explicit constants, to the physical
period-one Sobolev multiplier. This is a pointwise comparison only. -/
theorem kst_sobolev_weight_equivalence (s : ℝ) (hs : 0 ≤ s) :
    NlsGge.Atomic.KST043.KSTSubexponentialWeight (polynomialWeight s) ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℤ,
        c * sobolevWeight s n ≤ polynomialWeight s (2 * n) ∧
        polynomialWeight s (2 * n) ≤ C * sobolevWeight s n := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_, polynomial_log_ratio_tendsto s, ?_⟩
    · simpa [polynomialWeight]
    · exact polynomialWeight_even s
    · exact polynomialWeight_monotone_nat s hs
    · exact polynomialWeight_submultiplicative s hs
    · refine ⟨2, Or.inr ?_⟩
      intro m n hm hmn
      have hm' : 2 ≤ (m : ℕ) := hm
      have hn' : 2 ≤ (n : ℕ) := le_trans hm hmn
      exact polynomial_log_ratio_antitone s hs (by simpa using hm')
        (by simpa using hn') hmn
  · refine ⟨Real.pi ^ (-s), (Real.sqrt 2) ^ s, ?_, ?_, ?_⟩
    · positivity
    · positivity
    · intro n
      let t : ℝ := (n.natAbs : ℝ)
      let x : ℝ := 2 * Real.pi * t
      have ht : 0 ≤ t := by positivity
      have hx_nonneg : 0 ≤ x := by dsimp [x]; positivity
      have hbase_left : 1 + 2 * t ≤ Real.sqrt 2 * Real.sqrt (1 + x ^ 2) := by
        have htwo : 1 + 2 * t ≤ 1 + x := by
          dsimp [x]
          nlinarith [Real.pi_gt_three, ht]
        have hroot : 1 + x ≤ Real.sqrt 2 * Real.sqrt (1 + x ^ 2) := by
          have hsquare : (1 + x) ^ 2 ≤ 2 * (1 + x ^ 2) := by
            nlinarith [sq_nonneg (x - 1)]
          have hsq : (Real.sqrt 2 * Real.sqrt (1 + x ^ 2)) ^ 2 =
              2 * (1 + x ^ 2) := by
            rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
              Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)]
          have hroot0 : 0 ≤ Real.sqrt 2 * Real.sqrt (1 + x ^ 2) := by positivity
          nlinarith
        exact htwo.trans hroot
      have hbase_right : Real.sqrt (1 + x ^ 2) ≤ Real.pi * (1 + 2 * t) := by
        have hroot_le : Real.sqrt (1 + x ^ 2) ≤ 1 + x := by
          apply Real.sqrt_le_iff.mpr
          refine ⟨?_, ?_⟩
          · positivity
          · nlinarith [hx_nonneg]
        have hxupper : x ≤ Real.pi * (2 * t) := by
          dsimp [x]
          exact le_of_eq (by ring)
        have hpiA : 1 + x ≤ Real.pi * (1 + 2 * t) := by
          have hpi1 : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
          calc
            1 + x ≤ 1 + Real.pi * (2 * t) := by linarith
            _ ≤ Real.pi * (1 + 2 * t) := by nlinarith [hpi1, ht]
        exact hroot_le.trans hpiA
      have hp_left := Real.rpow_le_rpow (by positivity) hbase_right hs
      have hp_right := Real.rpow_le_rpow (by positivity) hbase_left hs
      have hpower_sqrt : (Real.sqrt (1 + x ^ 2)) ^ s =
          (1 + x ^ 2) ^ (s / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
        ring_nf
      have hpower_pi : (Real.pi * (1 + 2 * t)) ^ s =
          Real.pi ^ s * (1 + 2 * t) ^ s := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
      have hpoly : polynomialWeight s (2 * n) = (1 + 2 * t) ^ s := by
        unfold polynomialWeight
        have habs : ((2 * n).natAbs : ℝ) = 2 * t := by
          have hnabs : (2 * n).natAbs = 2 * n.natAbs := by
            simp [Int.natAbs_mul]
          dsimp [t]
          exact_mod_cast hnabs
        rw [habs]
      have hsob : sobolevWeight s n = (1 + x ^ 2) ^ (s / 2) := by
        have habs : (n : ℝ)^2 = (n.natAbs : ℝ)^2 := by
          have hreal : (n.natAbs : ℝ) = |(n : ℝ)| := by
            rw [Nat.cast_natAbs, Int.cast_abs]
          rw [hreal, sq_abs]
        have harg : (2 * Real.pi * (n : ℝ)) ^ 2 = x ^ 2 := by
          dsimp [x, t]
          calc
            (2 * Real.pi * (n : ℝ)) ^ 2 =
                (2 * Real.pi) ^ 2 * (n : ℝ) ^ 2 := by ring
            _ = (2 * Real.pi) ^ 2 * (n.natAbs : ℝ) ^ 2 := by rw [habs]
            _ = (2 * Real.pi * (n.natAbs : ℝ)) ^ 2 := by ring
        simp [sobolevWeight, x, harg]
      constructor
      · rw [hpoly, hsob] 
        have hpi_s : 0 < Real.pi ^ s := by positivity
        have hpi_inv : Real.pi ^ (-s) * Real.pi ^ s = 1 := by
          rw [← Real.rpow_add (by positivity)]
          simp
        have hbase := hp_left
        rw [hpower_pi] at hbase
        have hconst_nonneg : 0 ≤ Real.pi ^ (-s) := by positivity
        have hmul := mul_le_mul_of_nonneg_left hbase hconst_nonneg
        calc
          Real.pi ^ (-s) * (1 + x ^ 2) ^ (s / 2) =
              Real.pi ^ (-s) * (Real.sqrt (1 + x ^ 2)) ^ s := by rw [← hpower_sqrt]
          _ ≤ Real.pi ^ (-s) * (Real.pi ^ s * (1 + 2 * t) ^ s) := hmul
          _ = (1 + 2 * t) ^ s := by rw [← mul_assoc, hpi_inv, one_mul]
      · rw [hpoly, hsob, ← hpower_sqrt]
        have hsqrt_two : (Real.sqrt 2) ^ s * (Real.sqrt (1 + x ^ 2)) ^ s =
            (Real.sqrt 2 * Real.sqrt (1 + x ^ 2)) ^ s := by
          rw [← Real.mul_rpow (by positivity) (by positivity)]
        rw [hsqrt_two]
        exact hp_right

end NlsGge.Atomic.KST064
