import Mathlib

namespace NlsGge.Atomic.F004


                                                                                  
                                                                            
                                                                                                       

theorem F004_bound :
  ∀ m : ℕ, ∀ β : ℕ → ℝ, (∀ j, j ≤ m → 0 < β j) →
    ∀ r : ℝ, 1 ≤ |r| →
      |deriv (fun x : ℝ => ∑ j ∈ Finset.range (m + 1), β j * x ^ (2 * j)) r| /
        (∑ j ∈ Finset.range (m + 1), β j * r ^ (2 * j)) ≤ 2 * (m : ℝ) / |r| := by
  intro m β hβ r hr
  have hr0 : 0 < |r| := lt_of_lt_of_le one_pos hr
  have hrne : r ≠ 0 := abs_pos.mp hr0
  have hd : HasDerivAt (fun x : ℝ => ∑ j ∈ Finset.range (m + 1), β j * x ^ (2 * j))
      (∑ j ∈ Finset.range (m + 1), β j * ((2 * j : ℕ) : ℝ) * r ^ (2 * j - 1)) r := by
    apply HasDerivAt.fun_sum
    intro j _
    have h := (hasDerivAt_pow (2 * j) r).const_mul (β j)
    convert h using 1
    ring
  rw [hd.deriv]
  have hWpos : 0 < ∑ j ∈ Finset.range (m + 1), β j * r ^ (2 * j) := by
    apply Finset.sum_pos
    · intro j hj
      have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hpow : 0 < r ^ (2 * j) := by
        rw [pow_mul]
        positivity
      exact mul_pos (hβ j hjm) hpow
    · exact ⟨0, by simp⟩
  have hWabs : (∑ j ∈ Finset.range (m + 1), β j * r ^ (2 * j)) =
      ∑ j ∈ Finset.range (m + 1), β j * |r| ^ (2 * j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_mul, pow_mul, sq_abs]
  have key : ∀ j ∈ Finset.range (m + 1),
      |β j * ((2 * j : ℕ) : ℝ) * r ^ (2 * j - 1)| ≤ (2 * (m : ℝ) / |r|) * (β j * |r| ^ (2 * j)) := by
    intro j hj
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hβj := hβ j hjm
    have hjm' : ((2 * j : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by
      have : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hjm
      push_cast
      linarith
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      simp
      exact mul_nonneg (div_nonneg (by positivity) hr0.le) hβj.le
    · have hpow : |r| ^ (2 * j) = |r| ^ (2 * j - 1) * |r| := by
        rw [← pow_succ]
        congr 1
        omega
      have habsr : |β j * ((2 * j : ℕ) : ℝ) * r ^ (2 * j - 1)| =
          β j * ((2 * j : ℕ) : ℝ) * |r| ^ (2 * j - 1) := by
        rw [abs_mul, abs_mul, abs_pow, abs_of_pos hβj, abs_of_nonneg (by positivity)]
      rw [habsr, hpow]
      have hsimp : (2 * (m : ℝ) / |r|) * (β j * (|r| ^ (2 * j - 1) * |r|)) =
          (2 * (m : ℝ)) * (β j * |r| ^ (2 * j - 1)) := by
        field_simp
      rw [hsimp]
      have hnn : 0 ≤ β j * |r| ^ (2 * j - 1) := by positivity
      nlinarith [mul_nonneg hnn (sub_nonneg.mpr hjm')]
  rw [div_le_iff₀ hWpos, hWabs]
  calc |∑ j ∈ Finset.range (m + 1), β j * ((2 * j : ℕ) : ℝ) * r ^ (2 * j - 1)|
      ≤ ∑ j ∈ Finset.range (m + 1), |β j * ((2 * j : ℕ) : ℝ) * r ^ (2 * j - 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (m + 1), (2 * (m : ℝ) / |r|) * (β j * |r| ^ (2 * j)) :=
        Finset.sum_le_sum key
    _ = (2 * (m : ℝ) / |r|) * ∑ j ∈ Finset.range (m + 1), β j * |r| ^ (2 * j) := by
        rw [Finset.mul_sum]


end NlsGge.Atomic.F004
