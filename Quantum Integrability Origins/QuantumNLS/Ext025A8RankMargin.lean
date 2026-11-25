import QuantumNLS.Ext025A2ODE

/-! The source exponential rank sum supplies both Hartree majorants on
a strictly larger ball; these majorants are proved from that single sum. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.Ext025A8

theorem exponential_rank_margin {a : ℝ} (ha : 0 < a) {b : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n)
    (hs : Summable (fun n => (n + 1 : ℕ) * b n * Real.exp (a * n))) :
    ∃ S > (1 : ℝ),
      Summable (fun n => (n + 1 : ℕ) * b n * S ^ (2 * n + 1)) ∧
      Summable (fun n => (n + 1 : ℕ) * (2 * n + 1 : ℕ) * b n * S ^ (2 * n)) := by
  let S := Real.exp (a / 4)
  have hS : 1 < S := Real.one_lt_exp_iff.mpr (by linarith)
  have hpow (n : ℕ) : S ^ (2 * n) = Real.exp (a * n / 2) := by
    dsimp only [S]
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hS0 : 0 ≤ S := (zero_lt_one.trans hS).le
  refine ⟨S, hS, ?_, ?_⟩
  · apply Summable.of_nonneg_of_le (fun n => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (hb n)) (pow_nonneg hS0 _)) _ (hs.mul_right S)
    intro n
    rw [pow_succ, hpow]
    have he : Real.exp (a * n / 2) ≤ Real.exp (a * n) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    dsimp only [S]
    calc
      _ = ((n + 1 : ℕ) * b n * Real.exp (a * n / 2)) * Real.exp (a / 4) := by ring
      _ ≤ ((n + 1 : ℕ) * b n * Real.exp (a * n)) * Real.exp (a / 4) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left he (mul_nonneg (Nat.cast_nonneg _) (hb n)))
          (Real.exp_pos _).le
      _ = _ := by ring
  · let C : ℝ := 1 + 4 / a
    have hC : 0 ≤ C := by dsimp [C]; positivity
    apply Summable.of_nonneg_of_le (fun n => mul_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hb n))
      (pow_nonneg hS0 _)) _ (hs.mul_left C)
    intro n
    rw [hpow]
    have he : 1 ≤ Real.exp (a * n / 2) := Real.one_le_exp (by positivity)
    have hn := Real.add_one_le_exp (a * n / 2)
    have hratio : (2 * n + 1 : ℕ) ≤ C * Real.exp (a * n / 2) := by
      have hnorm : (2 * (n : ℝ)) ≤ 4 * Real.exp (a * n / 2) / a :=
        (le_div_iff₀ ha).mpr (by nlinarith)
      dsimp only [C]
      push_cast
      rw [add_mul, one_mul, div_mul_eq_mul_div]
      nlinarith
    calc
      _ = ((n + 1 : ℕ) * b n) * ((2 * n + 1 : ℕ) * Real.exp (a * n / 2)) := by ring
      _ ≤ ((n + 1 : ℕ) * b n) * ((C * Real.exp (a * n / 2)) * Real.exp (a * n / 2)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hratio (Real.exp_pos _).le)
          (mul_nonneg (Nat.cast_nonneg _) (hb n))
      _ = C * ((n + 1 : ℕ) * b n * Real.exp (a * n)) := by
        rw [mul_assoc C, ← Real.exp_add, show a * (n : ℝ) / 2 + a * n / 2 = a * n by ring]
        ring
end QuantumNLS.Ext025A8

#print axioms QuantumNLS.Ext025A8.exponential_rank_margin
