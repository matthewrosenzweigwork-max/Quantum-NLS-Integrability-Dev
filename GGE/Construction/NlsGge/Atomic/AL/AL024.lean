import Mathlib

namespace NlsGge.Atomic.AL024


                                                                                                                                            
set_option autoImplicit false

theorem AL024_reflect (f : ℕ → ℝ) (j : ℕ) :
    ∑ i ∈ Finset.range (2 * j + 1), f i =
      f j + ∑ k ∈ Finset.Icc 1 j, (f (j - k) + f (j + k)) := by
  have h2 : 2 * j + 1 = j + (j + 1) := by ring
  rw [h2, Finset.sum_range_add, Finset.sum_range_succ' (fun x => f (j + x)), Finset.sum_add_distrib]
  have hI : ∀ F : ℕ → ℝ, ∑ k ∈ Finset.Icc 1 j, F k = ∑ x ∈ Finset.range j, F (1 + x) := by
    intro F
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp [add_comm]
  rw [hI (fun k => f (j - k)), hI (fun k => f (j + k))]
  have hr : ∑ x ∈ Finset.range j, f x = ∑ x ∈ Finset.range j, f (j - (1 + x)) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    congr 1
    have := Finset.mem_range.mp hx
    omega
  have hs : ∑ x ∈ Finset.range j, f (j + (x + 1)) = ∑ x ∈ Finset.range j, f (j + (1 + x)) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    congr 1
    omega
  rw [hr]
  simp only [add_zero]
  rw [hs]
  ring

theorem AL024_complex (j : ℕ) (θ : ℝ) :
    (((2 - 2 * Real.cos (2 * θ)) ^ j : ℝ) : ℂ) =
      ∑ i ∈ Finset.range (2 * j + 1),
        (((-1 : ℝ) ^ (j + i) * (Nat.choose (2 * j) i : ℝ) : ℝ) : ℂ) *
          (Complex.exp (2 * θ * Complex.I)) ^ ((i : ℤ) - j) := by
  set q : ℂ := Complex.exp (2 * θ * Complex.I) with hq
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _
  have hcos : ((Real.cos (2 * θ) : ℝ) : ℂ) = (q + q⁻¹) / 2 := by
    rw [Complex.ofReal_cos, Complex.cos]
    have e1 : Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) = q := by
      rw [hq]; push_cast; ring_nf
    have e2 : Complex.exp (-((2 * θ : ℝ) : ℂ) * Complex.I) = q⁻¹ := by
      rw [hq, ← Complex.exp_neg]; congr 1; push_cast; ring
    rw [e1, e2]
  have hA : (((2 - 2 * Real.cos (2 * θ)) : ℝ) : ℂ) = -q⁻¹ * (q - 1) ^ 2 := by
    push_cast at hcos ⊢
    rw [hcos]
    field_simp
    ring
  rw [Complex.ofReal_pow, hA, mul_pow, neg_pow, ← pow_mul, show (q - 1) = q + (-1) by ring,
    add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i ≤ 2 * j := by have := Finset.mem_range.mp hi; omega
  have hpar : ((-1 : ℂ)) ^ (2 * j - i) = (-1) ^ i := by
    rw [neg_one_pow_eq_pow_mod_two (n := 2 * j - i), neg_one_pow_eq_pow_mod_two (n := i)]
    congr 1
    omega
  have hz : q ^ ((i : ℤ) - j) = q ^ i * (q⁻¹) ^ j := by
    rw [zpow_sub₀ hq0, zpow_natCast, zpow_natCast, inv_pow, div_eq_mul_inv]
  rw [hz, hpar]
  push_cast
  rw [pow_add]
  ring

theorem AL024_real (j : ℕ) (θ : ℝ) :
    (2 - 2 * Real.cos (2 * θ)) ^ j =
      ∑ i ∈ Finset.range (2 * j + 1),
        (-1 : ℝ) ^ (j + i) * (Nat.choose (2 * j) i : ℝ) * Real.cos (2 * (((i : ℝ) - j)) * θ) := by
  have h := congrArg Complex.re (AL024_complex j θ)
  rw [Complex.ofReal_re, Complex.re_sum] at h
  rw [h]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.re_ofReal_mul]
  congr 1
  have : (Complex.exp (2 * θ * Complex.I)) ^ ((i : ℤ) - j) =
      Complex.exp (((2 * (((i : ℝ) - j)) * θ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  rw [this, Complex.exp_ofReal_mul_I_re]

theorem AL024_negpow (j k : ℕ) (hk : k ≤ j) :
    (-1 : ℝ) ^ (j + (j - k)) = (-1) ^ k ∧ (-1 : ℝ) ^ (j + (j + k)) = (-1) ^ k := by
  constructor
  · rw [neg_one_pow_eq_pow_mod_two (n := j + (j - k)), neg_one_pow_eq_pow_mod_two (n := k)]
    congr 1
    omega
  · rw [neg_one_pow_eq_pow_mod_two (n := j + (j + k)), neg_one_pow_eq_pow_mod_two (n := k)]
    congr 1
    omega

theorem AL024_main : ((∀ (j : ℕ) (θ : ℝ), (2 - 2 * Real.cos (2 * θ)) ^ j =
    (Nat.choose (2 * j) j : ℝ) +
      2 * ∑ k ∈ Finset.Icc 1 j, (-1 : ℝ) ^ k * (Nat.choose (2 * j) (j - k) : ℝ) * Real.cos (2 * k * θ)) : Prop) := by
  intro j θ
  rw [AL024_real, AL024_reflect]
  have hc0 : (-1 : ℝ) ^ (j + j) = 1 := by
    rw [← two_mul, pow_mul]; simp
  have hmid : (-1 : ℝ) ^ (j + j) * (Nat.choose (2 * j) j : ℝ) * Real.cos (2 * (((j : ℝ) - j)) * θ) =
      (Nat.choose (2 * j) j : ℝ) := by
    rw [hc0]; simp
  rw [hmid]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ j := (Finset.mem_Icc.mp hk).2
  obtain ⟨p1, p2⟩ := AL024_negpow j k hk'
  have hch : Nat.choose (2 * j) (j + k) = Nat.choose (2 * j) (j - k) :=
    Nat.choose_symm_of_eq_add (by omega)
  have hc1 : (((j - k : ℕ) : ℝ) - j) = -(k : ℝ) := by
    rw [Nat.cast_sub hk']; ring
  have hc2 : (((j + k : ℕ) : ℝ) - j) = (k : ℝ) := by
    push_cast; ring
  rw [p1, p2, hch, hc1, hc2]
  have hcos : Real.cos (2 * (-(k : ℝ)) * θ) = Real.cos (2 * (k : ℝ) * θ) := by
    rw [show 2 * (-(k : ℝ)) * θ = -(2 * (k : ℝ) * θ) by ring, Real.cos_neg]
  rw [hcos]
  ring


end NlsGge.Atomic.AL024
