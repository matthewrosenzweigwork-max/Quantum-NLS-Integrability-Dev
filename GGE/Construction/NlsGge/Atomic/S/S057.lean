import Mathlib

namespace NlsGge.Atomic.S057


                                                                                                                                          
set_option autoImplicit false

theorem S057_thresh (C c ε : ℝ) (hC : 0 < C) (hc : 0 < c) (he : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      C * ((k : ℝ) + 2) ^ 9 - ε * c * Real.exp (c * (k : ℝ) ^ (1 / 4 : ℝ)) ≤ -(k : ℝ) := by
  set A : ℝ := C * 3 ^ 9 + 1 with hA
  have hApos : 0 < A := by positivity
  set X0 : ℝ := max 1 (A * (Nat.factorial 37 : ℝ) / (ε * c ^ 38)) with hX0
  refine ⟨⌈X0 ^ 4⌉₊, fun k hk => ?_⟩
  have hk' : X0 ^ 4 ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set x : ℝ := (k : ℝ) ^ (1 / 4 : ℝ) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg hk0 _
  have hx4 : x ^ 4 = (k : ℝ) := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hk0]; norm_num
  have hX1 : 1 ≤ X0 := le_max_left _ _
  have hxX : X0 ≤ x := by
    by_contra h
    push_neg at h
    have : x ^ 4 < X0 ^ 4 := pow_lt_pow_left₀ h hx0 (by norm_num)
    linarith
  have hx1 : 1 ≤ x := hX1.trans hxX
  have hk1 : (1 : ℝ) ≤ k := by rw [← hx4]; exact one_le_pow₀ hx1
  have h1 : ((k : ℝ) + 2) ^ 9 ≤ 3 ^ 9 * x ^ 36 := by
    have h3 : (k : ℝ) + 2 ≤ 3 * x ^ 4 := by rw [hx4]; linarith
    calc ((k : ℝ) + 2) ^ 9 ≤ (3 * x ^ 4) ^ 9 := pow_le_pow_left₀ (by positivity) h3 9
      _ = 3 ^ 9 * x ^ 36 := by rw [mul_pow, ← pow_mul]
  have h2 : (k : ℝ) ≤ x ^ 36 := by
    rw [← hx4]; exact pow_le_pow_right₀ hx1 (by norm_num)
  have h3 : C * ((k : ℝ) + 2) ^ 9 + k ≤ A * x ^ 36 := by
    have := mul_le_mul_of_nonneg_left h1 hC.le
    rw [hA]
    nlinarith
  have hxbig : A * (Nat.factorial 37 : ℝ) ≤ x * (ε * c ^ 38) := by
    have := (div_le_iff₀ (by positivity : 0 < ε * c ^ 38)).mp ((le_max_right _ _).trans hxX)
    exact this
  have hexp : (c * x) ^ 37 / (Nat.factorial 37 : ℝ) ≤ Real.exp (c * x) :=
    Real.pow_div_factorial_le_exp (c * x) (by positivity) 37
  have h4 : A * x ^ 36 ≤ ε * c * Real.exp (c * x) := by
    have hfac : (0 : ℝ) < (Nat.factorial 37 : ℝ) := by positivity
    have h5 : A * x ^ 36 ≤ ε * c * ((c * x) ^ 37 / (Nat.factorial 37 : ℝ)) := by
      rw [mul_div_assoc', le_div_iff₀ hfac]
      have h6 := mul_le_mul_of_nonneg_right hxbig (pow_nonneg hx0 36)
      have e : ε * c * (c * x) ^ 37 = x * (ε * c ^ 38) * x ^ 36 := by ring
      rw [e]
      nlinarith [h6]
    calc A * x ^ 36 ≤ ε * c * ((c * x) ^ 37 / (Nat.factorial 37 : ℝ)) := h5
      _ ≤ ε * c * Real.exp (c * x) := mul_le_mul_of_nonneg_left hexp (by positivity)
  linarith

theorem S057_main : ((∀ C c ε : ℝ, 0 < C → 0 < c → 0 < ε →
    Summable (fun k : ℕ => Real.exp (C * ((k : ℝ) + 2) ^ 9 - ε * c * Real.exp (c * (k : ℝ) ^ (1 / 4 : ℝ)))) ∧
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → C * ((k : ℝ) + 2) ^ 9 - ε * c * Real.exp (c * (k : ℝ) ^ (1 / 4 : ℝ)) ≤ -(k : ℝ)) : Prop) := by
  intro C c ε hC hc he
  obtain ⟨K, hK⟩ := S057_thresh C c ε hC hc he
  refine ⟨?_, K, hK⟩
  have hle : ∀ k : ℕ, K ≤ k →
      Real.exp (C * ((k : ℝ) + 2) ^ 9 - ε * c * Real.exp (c * (k : ℝ) ^ (1 / 4 : ℝ))) ≤
        Real.exp (-(k : ℝ)) := fun k hk => Real.exp_le_exp.mpr (hK k hk)
  refine (summable_nat_add_iff K).mp ?_
  refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le)
    (fun k => hle (k + K) (by omega)) ?_
  have e : (fun k : ℕ => Real.exp (-(((k + K : ℕ)) : ℝ))) =
      fun k : ℕ => Real.exp (-(K : ℝ)) * (Real.exp (-1)) ^ k := by
    funext k
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [e]
  exact (summable_geometric_of_lt_one (Real.exp_pos _).le ((Real.exp_lt_exp.mpr (by norm_num : (-1 : ℝ) < 0)).trans_eq Real.exp_zero)).mul_left _


end NlsGge.Atomic.S057
