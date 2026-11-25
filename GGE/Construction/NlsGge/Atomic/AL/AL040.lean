import Mathlib

namespace NlsGge.Atomic.AL040

                                                                                                                                                              
-- Route: reindex Icc(-N,N) by range(2N+1); orthogonality sum_k exp(2 pi i k m h) = 0 for 0 < |m| < L
-- (geometric sum, q^L = 1, q != 1) and = L for m = 0; surjectivity via injectivity mod L (|difference| <= 2N);
-- inversion by swapping sums and orthogonality.

theorem AL040_Icc_eq (N : ℕ) :
    Finset.Icc (-(N : ℤ)) (N : ℤ) = (Finset.range (2 * N + 1)).image (fun i : ℕ => (i : ℤ) - N) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
  constructor
  · intro h
    exact ⟨(x + N).toNat, by omega, by omega⟩
  · rintro ⟨i, hi, rfl⟩
    omega

theorem AL040_sum_Icc {M : Type*} [AddCommMonoid M] (N : ℕ) (F : ℤ → M) :
    ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), F k = ∑ i ∈ Finset.range (2 * N + 1), F ((i : ℤ) - N) := by
  rw [AL040_Icc_eq, Finset.sum_image]
  intro a _ b _ h
  simp only at h
  omega

theorem AL040_ortho (N : ℕ) (m : ℤ)
    (hmL : -((2 * N + 1 : ℕ) : ℤ) < m ∧ m < ((2 * N + 1 : ℕ) : ℤ)) (hm0 : m ≠ 0) :
    ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (m : ℂ) *
        ((1 / ((2 * N + 1 : ℕ) : ℝ) : ℝ) : ℂ)) = 0 := by
  set h : ℂ := ((1 / ((2 * N + 1 : ℕ) : ℝ) : ℝ) : ℂ) with hh
  have hLh : ((2 * N + 1 : ℕ) : ℂ) * h = 1 := by
    rw [hh]
    have hne : (2 * (N : ℂ) + 1) ≠ 0 := by exact_mod_cast (by omega : (2 * N + 1 : ℕ) ≠ 0)
    push_cast
    exact mul_one_div_cancel hne
  set q : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * h) with hq
  have hterm : ∀ k : ℤ,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (m : ℂ) * h) = q ^ k := by
    intro k
    rw [hq, ← Complex.exp_int_mul]
    congr 1
    ring
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _
  have hLq : q ^ (2 * N + 1) = 1 := by
    rw [hq, ← Complex.exp_nat_mul]
    have e1 : ((2 * N + 1 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * h) =
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      linear_combination (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) * hLh
    rw [e1]
    exact Complex.exp_int_mul_two_pi_mul_I m
  have hq1 : q ≠ 1 := by
    intro h1
    rw [hq, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hmn : (m : ℂ) * h = n := by
      apply mul_left_cancel₀ hpi
      linear_combination hn
    have hmL' : m = n * ((2 * N + 1 : ℕ) : ℤ) := by
      have : (m : ℂ) = (n : ℂ) * ((2 * N + 1 : ℕ) : ℂ) := by
        linear_combination (-(m : ℂ)) * hLh + ((2 * N + 1 : ℕ) : ℂ) * hmn
      exact_mod_cast this
    obtain ⟨hlo, hhi⟩ := hmL
    have hL1 : (1 : ℤ) ≤ ((2 * N + 1 : ℕ) : ℤ) := by omega
    have hn0 : n = 0 := by
      rcases lt_trichotomy n 0 with h' | h' | h'
      · nlinarith
      · exact h'
      · nlinarith
    exact hm0 (by rw [hmL', hn0]; ring)
  rw [AL040_sum_Icc N]
  have hsplit : ∀ i : ℕ, q ^ ((i : ℤ) - (N : ℤ)) = q ^ (-(N : ℤ)) * q ^ i := by
    intro i
    rw [show ((i : ℤ) - (N : ℤ)) = (i : ℤ) + (-(N : ℤ)) by ring, zpow_add₀ hq0, zpow_natCast]
    ring
  simp only [hterm, hsplit]
  rw [← Finset.mul_sum, geom_sum_eq hq1, hLq, sub_self, zero_div, mul_zero]

theorem AL040_card (N : ℕ) : (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
  rw [Int.card_Icc]
  omega

theorem AL040_surj (N : ℕ) :
    Finset.image (fun k : ℤ => (k : ZMod (2 * N + 1))) (Finset.Icc (-(N : ℤ)) (N : ℤ)) = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [Finset.card_image_of_injOn, AL040_card, ZMod.card]
  intro a ha b hb hab
  simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
  simp only at hab
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub a b (2 * N + 1)).mp hab
  have habs : |b - a| < ((2 * N + 1 : ℕ) : ℤ) := by
    rw [abs_lt]
    push_cast
    constructor <;> omega
  have h0 := Int.eq_zero_of_abs_lt_dvd hd habs
  omega

theorem AL040 :
  ∀ N : ℕ, ∀ v : ℕ → ℂ,
    (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 ∧
    Finset.image (fun k : ℤ => (k : ZMod (2 * N + 1))) (Finset.Icc (-(N : ℤ)) (N : ℤ)) = Finset.univ ∧
    ∀ j ∈ Finset.range (2 * N + 1),
      v j = ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ((1 / ((2 * N + 1 : ℕ) : ℝ) : ℂ) * ∑ j' ∈ Finset.range (2 * N + 1),
            v j' * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (k : ℂ) * (j' : ℂ) *
              ((1 / ((2 * N + 1 : ℕ) : ℝ) : ℝ) : ℂ))) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (j : ℂ) *
              ((1 / ((2 * N + 1 : ℕ) : ℝ) : ℝ) : ℂ)) := by
  intro N v
  refine ⟨AL040_card N, AL040_surj N, ?_⟩
  intro j hj
  have hjL : j < 2 * N + 1 := Finset.mem_range.mp hj
  set h : ℂ := ((1 / ((2 * N + 1 : ℕ) : ℝ) : ℝ) : ℂ) with hh
  have hc : ((1 / ((2 * N + 1 : ℕ) : ℝ) : ℂ)) = h := by
    rw [hh]
    simp
  have hLh : ((2 * N + 1 : ℕ) : ℂ) * h = 1 := by
    rw [hh]
    have hne : (2 * (N : ℂ) + 1) ≠ 0 := by exact_mod_cast (by omega : (2 * N + 1 : ℕ) ≠ 0)
    push_cast
    exact mul_one_div_cancel hne
  rw [hc]
  have key : ∀ k : ℤ,
      (h * ∑ j' ∈ Finset.range (2 * N + 1),
          v j' * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (k : ℂ) * (j' : ℂ) * h)) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (j : ℂ) * h) =
      ∑ j' ∈ Finset.range (2 * N + 1),
        v j' * (h * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) *
          (((j : ℤ) - (j' : ℤ) : ℤ) : ℂ) * h)) := by
    intro k
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j' _
    have hexp : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (k : ℂ) * (j' : ℂ) * h) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (j : ℂ) * h) =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) *
          (((j : ℤ) - (j' : ℤ) : ℤ) : ℂ) * h) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [← hexp]
    ring
  rw [Finset.sum_congr rfl (fun k _ => key k), Finset.sum_comm]
  have hsum : ∀ j' ∈ Finset.range (2 * N + 1),
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) *
          (((j : ℤ) - (j' : ℤ) : ℤ) : ℂ) * h) =
        if j = j' then ((2 * N + 1 : ℕ) : ℂ) else 0 := by
    intro j' hj'
    have hj'L : j' < 2 * N + 1 := Finset.mem_range.mp hj'
    by_cases hjj : j = j'
    · subst hjj
      rw [if_pos rfl]
      simp only [sub_self, Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, Finset.sum_const,
        nsmul_eq_mul, mul_one]
      rw [Int.card_Icc]
      congr 1
      omega
    · rw [if_neg hjj]
      exact AL040_ortho N ((j : ℤ) - (j' : ℤ)) ⟨by omega, by omega⟩ (by omega)
  have hortho : ∀ j' ∈ Finset.range (2 * N + 1),
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        v j' * (h * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) *
          (((j : ℤ) - (j' : ℤ) : ℤ) : ℂ) * h)) =
        v j' * (h * (if j = j' then ((2 * N + 1 : ℕ) : ℂ) else 0)) := by
    intro j' hj'
    rw [← Finset.mul_sum, ← Finset.mul_sum, hsum j' hj']
  rw [Finset.sum_congr rfl hortho]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl, mul_comm h, hLh, mul_one]
  · intro b _ hb
    rw [if_neg (fun h' => hb h'.symm), mul_zero, mul_zero]
  · intro hj'
    exact absurd hj hj'

end NlsGge.Atomic.AL040
