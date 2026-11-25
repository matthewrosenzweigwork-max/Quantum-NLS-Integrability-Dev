import Mathlib

/-! # S5: integer level-index steps from monotonicity, surjectivity and signs -/
set_option autoImplicit false
namespace NlsGge.GK38
noncomputable section

theorem realType_monotone_surj_succ_le38 (J : ℤ → ℤ) (hmono : Monotone J)
    (hsurj : Function.Surjective J) (k : ℤ) : J (k + 1) ≤ J k + 1 := by
  by_contra h
  obtain ⟨l, hl⟩ := hsurj (J k + 1)
  by_cases hle : l ≤ k
  · have hm := hmono hle
    omega
  · have hm := hmono (show k + 1 ≤ l by omega)
    omega

theorem realType_cos_int_succ38 (j : ℤ) :
    Real.cos (((j + 1 : ℤ) : ℝ) * Real.pi) = -Real.cos ((j : ℝ) * Real.pi) := by
  push_cast
  rw [add_mul, one_mul, Real.cos_add_pi]

theorem realType_cos_int_ne_zero38 (j : ℤ) : Real.cos ((j : ℝ) * Real.pi) ≠ 0 := by
  have h := Real.abs_cos_int_mul_pi j
  intro hz
  rw [hz, abs_zero] at h
  norm_num at h

theorem realType_pair_index_steps38 (J : ℤ → ℤ) (hmono : Monotone J)
    (hsurj : Function.Surjective J)
    (hsign : ∀ n : ℤ, Real.cos ((J (2 * n) : ℝ) * Real.pi) = Real.cos ((n : ℝ) * Real.pi) ∧
      Real.cos ((J (2 * n + 1) : ℝ) * Real.pi) = Real.cos ((n : ℝ) * Real.pi)) :
    ∀ n : ℤ, J (2 * n + 1) = J (2 * n) ∧ J (2 * (n + 1)) = J (2 * n) + 1 := by
  intro n
  have he : J (2 * n + 1) = J (2 * n) := by
    by_contra hne
    have hm := hmono (show 2 * n ≤ 2 * n + 1 by omega)
    have hs := realType_monotone_surj_succ_le38 J hmono hsurj (2 * n)
    have hj : J (2 * n + 1) = J (2 * n) + 1 := by omega
    have hc := (hsign n).2
    rw [hj, realType_cos_int_succ38, (hsign n).1] at hc
    exact realType_cos_int_ne_zero38 n (by linarith)
  refine ⟨he, ?_⟩
  have hm := hmono (show 2 * n + 1 ≤ 2 * (n + 1) by omega)
  have hs := realType_monotone_surj_succ_le38 J hmono hsurj (2 * n + 1)
  rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, he] at hs
  rw [he] at hm
  have hne : J (2 * (n + 1)) ≠ J (2 * n) := by
    intro hj
    have hc := (hsign (n + 1)).1
    rw [hj, (hsign n).1, realType_cos_int_succ38] at hc
    exact realType_cos_int_ne_zero38 n (by linarith)
  omega

theorem realType_pair_index_translation38 (J : ℤ → ℤ)
    (hstep : ∀ n : ℤ, J (2 * n + 1) = J (2 * n) ∧ J (2 * (n + 1)) = J (2 * n) + 1) :
    ∃ c : ℤ, ∀ n : ℤ, J (2 * n) = n + c ∧ J (2 * n + 1) = n + c := by
  have hd : ∀ n : ℤ, J (2 * n) = n + J 0 := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ i hi =>
      have h := (hstep (i : ℤ)).2
      omega
    | pred i hi =>
      have h := (hstep (-(i : ℤ) - 1)).2
      rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring] at h
      omega
  exact ⟨J 0, fun n => ⟨hd n, (hstep n).1.trans (hd n)⟩⟩

end
end NlsGge.GK38
