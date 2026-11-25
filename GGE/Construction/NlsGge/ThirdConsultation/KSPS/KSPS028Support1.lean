import Mathlib

                                                                                                                    
                                                                                                                   
                                                                                                                      
                                                                                                               
                                                                                           
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS028P
noncomputable section

/-! ### Pure lemmas -/

/-- Copy of the landed KSPS026W.rad_identity (pure ring identity), to avoid importing KSPS026Support5. -/
theorem rad_identity' (e a1 a2 E00 E01 E10 E11 α β : ℂ) :
    (1 + (1 - (e + E00)) * (1 - (-e + E11)) - α * β -
        (α - (-Complex.I * a2 + E10)) * (β - (Complex.I * a1 + E01))) ^ 2 -
      4 * (-1 + α * β + (e + E00) - β * (-Complex.I * a2 + E10)) *
        (-1 + α * β + (-e + E11) - α * (Complex.I * a1 + E01)) + 4 * a1 * a2 =
    4 * (e * (α * (Complex.I * a1 + E01) - β * (-Complex.I * a2 + E10))) +
      (E00 - E11 - β * (-Complex.I * a2 + E10) + α * (Complex.I * a1 + E01)) *
        (E00 - E11 - β * (-Complex.I * a2 + E10) + α * (Complex.I * a1 + E01)) +
      4 * (E00 * E11 - Complex.I * (a1 * E10) + Complex.I * (a2 * E01) - E01 * E10) -
      4 * ((α * β) * ((e + E00) * (-e + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10))) -
      2 * (((e + E00) - β * (-Complex.I * a2 + E10) + ((-e + E11) - α * (Complex.I * a1 + E01))) *
        ((e + E00) * (-e + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10))) +
      ((e + E00) * (-e + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10)) *
        ((e + E00) * (-e + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10)) := by
  linear_combination (4 * a1 * a2) * Complex.I_sq

theorem e_bound (N : ℕ) (IL z : ℂ) (w : ℝ) (hw : 0 < w) (hwX : w ≤ 2 * ‖z‖) :
    w ^ (N + 1) * ‖IL / (2 * Complex.I * z) ^ (N + 1)‖ ≤ ‖IL‖ := by
  have hX : 0 < 2 * ‖z‖ := lt_of_lt_of_le hw hwX
  have e1 : w ^ (N + 1) * ‖IL / (2 * Complex.I * z) ^ (N + 1)‖ = (w / (2 * ‖z‖)) ^ (N + 1) * ‖IL‖ := by
    rw [norm_div, norm_pow, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one, div_pow]
    field_simp
  rw [e1]
  have hr0 : 0 ≤ w / (2 * ‖z‖) := div_nonneg hw.le hX.le
  have hr1 : w / (2 * ‖z‖) ≤ 1 := by rw [div_le_one hX]; exact hwX
  have := mul_le_mul_of_nonneg_right (pow_le_one₀ hr0 hr1 : (w / (2 * ‖z‖)) ^ (N + 1) ≤ 1) (norm_nonneg IL)
  linarith

/-- Real arithmetic of the six weighted radicand terms. -/
theorem rs_real (w W0 W1 t CI S Eu R nT nX nAC nP nEE nab ne : ℝ)
    (hw : 1 ≤ w) (hW1 : W1 = W0 * w) (hW1sq : W1 ≤ W0 * W0) (hW0 : 0 ≤ W0) (hS : 0 ≤ S)
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 4) (hR0 : 0 ≤ R) (hEu0 : 0 ≤ Eu)
    (hRw : W0 * R ≤ t) (hEw : W1 * Eu ≤ t) (he : W1 * ne ≤ CI) (hne : 0 ≤ ne)
    (hnT : nT ≤ S / w * R) (hnX : nX ≤ Eu + S / w * R) (hnAC : nAC ≤ Eu + S / w * R)
    (hnP : nP ≤ 2 * R ^ 2) (hnEE : nEE ≤ 2 * Eu ^ 2) (hnab : nab ≤ (S / w) ^ 2)
    (h0T : 0 ≤ nT) (h0X : 0 ≤ nX) (h0AC : 0 ≤ nAC) (h0P : 0 ≤ nP) (h0ab : 0 ≤ nab) :
    W1 ^ 2 * (4 * (ne * nT) + nX * nX + 4 * nEE + 4 * (nab * nP) + 2 * (nAC * nP) + nP * nP) ≤
      (4 * CI * S + (1 + S) ^ 2 + 8 * S ^ 2 + 4 * (1 + S) + 12) * t := by
  have hw0 : 0 < w := by linarith
  have hW1p : 0 ≤ W1 := by rw [hW1]; exact mul_nonneg hW0 hw0.le
  have wSR : W1 * (S / w * R) = S * (W0 * R) := by rw [hW1]; field_simp
  have hSR : S * (W0 * R) ≤ S * t := mul_le_mul_of_nonneg_left hRw hS
  have wT : W1 * nT ≤ S * t := by
    have := mul_le_mul_of_nonneg_left hnT hW1p
    linarith
  have wX : W1 * nX ≤ (1 + S) * t := by
    have h1 := mul_le_mul_of_nonneg_left hnX hW1p
    rw [mul_add, wSR] at h1
    linarith
  have wAC : W1 * nAC ≤ (1 + S) * t := by
    have h1 := mul_le_mul_of_nonneg_left hnAC hW1p
    rw [mul_add, wSR] at h1
    linarith
  have hW0R : 0 ≤ W0 * R := mul_nonneg hW0 hR0
  have wRR : W0 * W0 * R ^ 2 ≤ t ^ 2 := by
    have h3 : (W0 * R) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hW0R hRw 2
    have h2 : W0 * W0 * R ^ 2 = (W0 * R) ^ 2 := by ring
    linarith
  have wP : W1 * nP ≤ 2 * t ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hnP hW1p
    have h2 : W1 * R ^ 2 ≤ W0 * W0 * R ^ 2 := mul_le_mul_of_nonneg_right hW1sq (sq_nonneg _)
    linarith
  have wP0 : 0 ≤ W1 * nP := mul_nonneg hW1p h0P
  have t1 : W1 ^ 2 * (4 * (ne * nT)) ≤ 4 * CI * S * t := by
    have e1 : W1 ^ 2 * (4 * (ne * nT)) = 4 * ((W1 * ne) * (W1 * nT)) := by ring
    rw [e1]
    have h3 := mul_le_mul he wT (mul_nonneg hW1p h0T) (le_trans (mul_nonneg hW1p hne) he)
    have e2 : CI * (S * t) = CI * S * t := by ring
    linarith
  have t2 : W1 ^ 2 * (nX * nX) ≤ (1 + S) ^ 2 * t ^ 2 := by
    have e1 : W1 ^ 2 * (nX * nX) = (W1 * nX) ^ 2 := by ring
    rw [e1]
    have h := pow_le_pow_left₀ (mul_nonneg hW1p h0X) wX 2
    have e2 : ((1 + S) * t) ^ 2 = (1 + S) ^ 2 * t ^ 2 := by ring
    rw [e2] at h
    exact h
  have t3 : W1 ^ 2 * (4 * nEE) ≤ 8 * t ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hnEE (sq_nonneg W1)
    have h2 : W1 ^ 2 * Eu ^ 2 ≤ t ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (mul_nonneg hW1p hEu0) hEw 2
    have e1 : W1 ^ 2 * (4 * nEE) = 4 * (W1 ^ 2 * nEE) := by ring
    have e2 : W1 ^ 2 * (2 * Eu ^ 2) = 2 * (W1 ^ 2 * Eu ^ 2) := by ring
    linarith
  have t4 : W1 ^ 2 * (4 * (nab * nP)) ≤ 8 * S ^ 2 * t ^ 2 := by
    have h1 : W1 ^ 2 * (S / w) ^ 2 = S ^ 2 * W0 ^ 2 := by rw [hW1]; field_simp
    have h2 : W0 ^ 2 * nP ≤ 2 * t ^ 2 := by
      have := mul_le_mul_of_nonneg_left hnP (sq_nonneg W0)
      have h3 : W0 ^ 2 * (2 * R ^ 2) = 2 * (W0 * W0 * R ^ 2) := by ring
      linarith
    have h5 : nab * nP ≤ (S / w) ^ 2 * nP := mul_le_mul_of_nonneg_right hnab h0P
    have h6 : W1 ^ 2 * (4 * (nab * nP)) ≤ W1 ^ 2 * (4 * ((S / w) ^ 2 * nP)) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    have h7 : W1 ^ 2 * (4 * ((S / w) ^ 2 * nP)) = 4 * S ^ 2 * (W0 ^ 2 * nP) := by
      calc W1 ^ 2 * (4 * ((S / w) ^ 2 * nP)) = 4 * (W1 ^ 2 * (S / w) ^ 2) * nP := by ring
        _ = 4 * (S ^ 2 * W0 ^ 2) * nP := by rw [h1]
        _ = 4 * S ^ 2 * (W0 ^ 2 * nP) := by ring
    have h8 : 4 * S ^ 2 * (W0 ^ 2 * nP) ≤ 4 * S ^ 2 * (2 * t ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  have t5 : W1 ^ 2 * (2 * (nAC * nP)) ≤ 4 * (1 + S) * t ^ 3 := by
    have e1 : W1 ^ 2 * (2 * (nAC * nP)) = 2 * ((W1 * nAC) * (W1 * nP)) := by ring
    rw [e1]
    have h1 := mul_le_mul wAC wP wP0 (by positivity)
    have e2 : (1 + S) * t * (2 * t ^ 2) = 2 * (1 + S) * t ^ 3 := by ring
    linarith
  have t6 : W1 ^ 2 * (nP * nP) ≤ 4 * t ^ 4 := by
    have e1 : W1 ^ 2 * (nP * nP) = (W1 * nP) ^ 2 := by ring
    rw [e1]
    have h1 := pow_le_pow_left₀ wP0 wP 2
    have e2 : (2 * t ^ 2) ^ 2 = 4 * t ^ 4 := by ring
    linarith
  have tt2 : t ^ 2 ≤ t := by
    have h1 := mul_le_mul_of_nonneg_left (ht.trans (by norm_num : (1 / 4 : ℝ) ≤ 1)) ht0
    rw [sq]; linarith only [h1]
  have tt3 : t ^ 3 ≤ t := by
    have e1 : t ^ 3 = t ^ 2 * t := by ring
    have h1 := mul_le_mul_of_nonneg_right tt2 ht0
    have e2 : t * t = t ^ 2 := by ring
    rw [e1]; linarith only [h1, e2, tt2]
  have tt4 : t ^ 4 ≤ t := by
    have e1 : t ^ 4 = t ^ 2 * t ^ 2 := by ring
    have h1 := mul_le_mul_of_nonneg_right tt2 (sq_nonneg t)
    have e2 : t * t ^ 2 = t ^ 3 := by ring
    rw [e1]; linarith only [h1, e2, tt3]
  have k2 : (1 + S) ^ 2 * t ^ 2 ≤ (1 + S) ^ 2 * t := mul_le_mul_of_nonneg_left tt2 (sq_nonneg _)
  have k4 : 8 * S ^ 2 * t ^ 2 ≤ 8 * S ^ 2 * t := mul_le_mul_of_nonneg_left tt2 (by positivity)
  have k5 : 4 * (1 + S) * t ^ 3 ≤ 4 * (1 + S) * t := mul_le_mul_of_nonneg_left tt3 (by positivity)
  have e3 : W1 ^ 2 * (4 * (ne * nT) + nX * nX + 4 * nEE + 4 * (nab * nP) + 2 * (nAC * nP) + nP * nP) =
      W1 ^ 2 * (4 * (ne * nT)) + W1 ^ 2 * (nX * nX) + W1 ^ 2 * (4 * nEE) + W1 ^ 2 * (4 * (nab * nP)) +
        W1 ^ 2 * (2 * (nAC * nP)) + W1 ^ 2 * (nP * nP) := by ring
  rw [e3]
  have e4 : (4 * CI * S + (1 + S) ^ 2 + 8 * S ^ 2 + 4 * (1 + S) + 12) * t =
      4 * CI * S * t + (1 + S) ^ 2 * t + 8 * S ^ 2 * t + 4 * (1 + S) * t + 12 * t := by ring
  rw [e4]
  have a3 : W1 ^ 2 * (4 * nEE) ≤ 8 * t := by
    have := mul_le_mul_of_nonneg_left tt2 (by norm_num : (0 : ℝ) ≤ 8)
    exact t3.trans (by linarith only [this])
  have a6 : W1 ^ 2 * (nP * nP) ≤ 4 * t := by
    have := mul_le_mul_of_nonneg_left tt4 (by norm_num : (0 : ℝ) ≤ 4)
    exact t6.trans (by linarith only [this])
  linarith only [t1, t2.trans k2, a3, t4.trans k4, t5.trans k5, a6]

/-- The six unweighted norm bounds. -/
theorem rs_norms (w : ℝ) (hw : 1 ≤ w) (e a1 a2 E00 E01 E10 E11 α β : ℂ) (R S Eu : ℝ) (hS : 0 ≤ S)
    (hR : ‖e + E00‖ + ‖Complex.I * a1 + E01‖ + ‖-Complex.I * a2 + E10‖ + ‖-e + E11‖ ≤ R)
    (hEu : ‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖ ≤ Eu) (hα : ‖α‖ ≤ S / w) (hβ : ‖β‖ ≤ S / w) :
    ‖α * (Complex.I * a1 + E01) - β * (-Complex.I * a2 + E10)‖ ≤ S / w * R ∧
    ‖E00 - E11 - β * (-Complex.I * a2 + E10) + α * (Complex.I * a1 + E01)‖ ≤ Eu + S / w * R ∧
    ‖(e + E00) - β * (-Complex.I * a2 + E10) + ((-e + E11) - α * (Complex.I * a1 + E01))‖ ≤ Eu + S / w * R ∧
    ‖(e + E00) * (-e + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10)‖ ≤ 2 * R ^ 2 ∧
    ‖E00 * E11 - E01 * E10‖ ≤ 2 * Eu ^ 2 ∧
    ‖α‖ * ‖β‖ ≤ (S / w) ^ 2 := by
  have hw0 : 0 < w := by linarith
  set r00 : ℂ := e + E00
  set r01 : ℂ := Complex.I * a1 + E01
  set r10 : ℂ := -Complex.I * a2 + E10
  set r11 : ℂ := -e + E11
  have nE00 := norm_nonneg E00
  have nE01 := norm_nonneg E01
  have nE10 := norm_nonneg E10
  have nE11 := norm_nonneg E11
  have n00 := norm_nonneg r00
  have n01 := norm_nonneg r01
  have n10 := norm_nonneg r10
  have n11 := norm_nonneg r11
  have hR0 : 0 ≤ R := by linarith
  have hEu0 : 0 ≤ Eu := by linarith
  have hSw : 0 ≤ S / w := div_nonneg hS hw0.le
  have h2 : ‖α * r01‖ ≤ S / w * ‖r01‖ := by rw [norm_mul]; exact mul_le_mul_of_nonneg_right hα n01
  have h3 : ‖β * r10‖ ≤ S / w * ‖r10‖ := by rw [norm_mul]; exact mul_le_mul_of_nonneg_right hβ n10
  have h4 : S / w * ‖r01‖ + S / w * ‖r10‖ ≤ S / w * R := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith) hSw
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := norm_sub_le (α * r01) (β * r10)
    linarith
  · have h1 := norm_add_le (E00 - E11 - β * r10) (α * r01)
    have h5 := norm_sub_le (E00 - E11) (β * r10)
    have h6 := norm_sub_le E00 E11
    linarith
  · have e1 : r00 - β * r10 + (r11 - α * r01) = E00 + E11 - β * r10 - α * r01 := by ring
    rw [e1]
    have h1 := norm_sub_le (E00 + E11 - β * r10) (α * r01)
    have h5 := norm_sub_le (E00 + E11) (β * r10)
    have h6 := norm_add_le E00 E11
    linarith
  · have h1 := norm_sub_le (r00 * r11) (r01 * r10)
    rw [norm_mul, norm_mul] at h1
    have h5 : ‖r00‖ * ‖r11‖ ≤ R * R := mul_le_mul (by linarith) (by linarith) n11 hR0
    have h6 : ‖r01‖ * ‖r10‖ ≤ R * R := mul_le_mul (by linarith) (by linarith) n10 hR0
    have e1 : 2 * R ^ 2 = R * R + R * R := by ring
    linarith
  · have h1 := norm_sub_le (E00 * E11) (E01 * E10)
    rw [norm_mul, norm_mul] at h1
    have h5 : ‖E00‖ * ‖E11‖ ≤ Eu * Eu := mul_le_mul (by linarith) (by linarith) nE11 hEu0
    have h6 : ‖E01‖ * ‖E10‖ ≤ Eu * Eu := mul_le_mul (by linarith) (by linarith) nE10 hEu0
    have e1 : 2 * Eu ^ 2 = Eu * Eu + Eu * Eu := by ring
    linarith
  · rw [sq]; exact mul_le_mul hα hβ (norm_nonneg _) hSw

/-- The radicand minus its two cross terms, at weight 2N+2 (no e^2 term survives). -/
theorem rad_split (N : ℕ) (hN : 1 ≤ N) (w : ℝ) (hw : 1 ≤ w) (e a1 a2 E00 E01 E10 E11 α β : ℂ)
    (R S t CI Eu : ℝ) (hS : 0 ≤ S) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 4)
    (hR : ‖e + E00‖ + ‖Complex.I * a1 + E01‖ + ‖-Complex.I * a2 + E10‖ + ‖-e + E11‖ ≤ R)
    (hRw : w ^ N * R ≤ t)
    (hEu : ‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖ ≤ Eu) (hEw : w ^ (N + 1) * Eu ≤ t)
    (he : w ^ (N + 1) * ‖e‖ ≤ CI) (hα : ‖α‖ ≤ S / w) (hβ : ‖β‖ ≤ S / w) :
    (w ^ (N + 1)) ^ 2 *
      ‖(4 * (e * (α * (Complex.I * a1 + E01) - β * (-Complex.I * a2 + E10))) +
        (E00 - E11 - β * (-Complex.I * a2 + E10) + α * (Complex.I * a1 + E01)) *
          (E00 - E11 - β * (-Complex.I * a2 + E10) + α * (Complex.I * a1 + E01)) +
        4 * (E00 * E11 - Complex.I * (a1 * E10) + Complex.I * (a2 * E01) - E01 * E10) -
        4 * ((α * β) * ((e + E00) * (-e + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10))) -
        2 * (((e + E00) - β * (-Complex.I * a2 + E10) + ((-e + E11) - α * (Complex.I * a1 + E01))) *
          ((e + E00) * (-e + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10))) +
        ((e + E00) * (-e + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10)) *
          ((e + E00) * (-e + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10))) -
        4 * (-Complex.I * (a1 * E10) + Complex.I * (a2 * E01))‖ ≤
      (4 * CI * S + (1 + S) ^ 2 + 8 * S ^ 2 + 4 * (1 + S) + 12) * t := by
  obtain ⟨nT, nX, nAC, nP, nEE, nab⟩ := rs_norms w hw e a1 a2 E00 E01 E10 E11 α β R S Eu hS hR hEu hα hβ
  generalize hT : α * (Complex.I * a1 + E01) - β * (-Complex.I * a2 + E10) = T at nT
  generalize hX : E00 - E11 - β * (-Complex.I * a2 + E10) + α * (Complex.I * a1 + E01) = X at nX
  generalize hAC : (e + E00) - β * (-Complex.I * a2 + E10) + ((-e + E11) - α * (Complex.I * a1 + E01)) = AC at nAC
  generalize hP : (e + E00) * (-e + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10) = P at nP
  have eq : (4 * (e * T) + X * X +
        4 * (E00 * E11 - Complex.I * (a1 * E10) + Complex.I * (a2 * E01) - E01 * E10) -
        4 * ((α * β) * P) - 2 * (AC * P) + P * P) -
        4 * (-Complex.I * (a1 * E10) + Complex.I * (a2 * E01)) =
      4 * (e * T) + X * X + 4 * (E00 * E11 - E01 * E10) - 4 * ((α * β) * P) - 2 * (AC * P) + P * P := by ring
  rw [eq]
  have hsum : ‖4 * (e * T) + X * X + 4 * (E00 * E11 - E01 * E10) - 4 * ((α * β) * P) - 2 * (AC * P) + P * P‖ ≤
      4 * (‖e‖ * ‖T‖) + ‖X‖ * ‖X‖ + 4 * ‖E00 * E11 - E01 * E10‖ + 4 * (‖α‖ * ‖β‖ * ‖P‖) +
        2 * (‖AC‖ * ‖P‖) + ‖P‖ * ‖P‖ := by
    have s1 := norm_add_le (4 * (e * T) + X * X + 4 * (E00 * E11 - E01 * E10) - 4 * ((α * β) * P) -
      2 * (AC * P)) (P * P)
    have s2 := norm_sub_le (4 * (e * T) + X * X + 4 * (E00 * E11 - E01 * E10) - 4 * ((α * β) * P))
      (2 * (AC * P))
    have s3 := norm_sub_le (4 * (e * T) + X * X + 4 * (E00 * E11 - E01 * E10)) (4 * ((α * β) * P))
    have s4 := norm_add_le (4 * (e * T) + X * X) (4 * (E00 * E11 - E01 * E10))
    have s5 := norm_add_le (4 * (e * T)) (X * X)
    simp only [norm_mul, Complex.norm_ofNat] at s1 s2 s3 s4 s5
    linarith
  have hw0 : 0 < w := by linarith
  have hW1sq : w ^ (N + 1) ≤ w ^ N * w ^ N := by
    rw [← pow_add]; exact pow_le_pow_right₀ hw (by omega)
  have hR0 : 0 ≤ R := le_trans (by positivity) hR
  have hEu0 : 0 ≤ Eu := le_trans (by positivity) hEu
  have key := rs_real w (w ^ N) (w ^ (N + 1)) t CI S Eu R ‖T‖ ‖X‖ ‖AC‖ ‖P‖ ‖E00 * E11 - E01 * E10‖
    (‖α‖ * ‖β‖) ‖e‖ hw (pow_succ w N) hW1sq (pow_nonneg hw0.le N) hS ht0 ht hR0 hEu0 hRw hEw he
    (norm_nonneg _) nT nX nAC nP nEE nab (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact (mul_le_mul_of_nonneg_left hsum (sq_nonneg _)).trans key

theorem d_bound (x s Hg K : ℝ) (hx : 0 ≤ x) (hs : 0 ≤ s) (hK : 0 ≤ K) (hHg : 0 ≤ Hg)
    (h : |x ^ 2 - s ^ 2| ≤ Hg + (x + s) * K) : |x - s| ≤ 2 * K + Real.sqrt (2 * Hg) := by
  have hd0 := abs_nonneg (x - s)
  have hdxs : |x - s| ≤ x + s := by
    rw [abs_le]; constructor <;> linarith
  have hprod : |x ^ 2 - s ^ 2| = |x - s| * (x + s) := by
    rw [show x ^ 2 - s ^ 2 = (x - s) * (x + s) by ring, abs_mul, abs_of_nonneg (by linarith : 0 ≤ x + s)]
  rw [hprod] at h
  have hq := Real.sqrt_nonneg (2 * Hg)
  by_cases hc : |x - s| ≤ 2 * K
  · linarith
  · push_neg at hc
    have h1 : (x + s) * K ≤ (x + s) * (|x - s| / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h2 : |x - s| * (x + s) / 2 ≤ Hg := by nlinarith
    have h3 : |x - s| ^ 2 ≤ 2 * Hg := by nlinarith [mul_le_mul_of_nonneg_left hdxs hd0]
    have h4 : |x - s| ≤ Real.sqrt (2 * Hg) := Real.le_sqrt_of_sq_le h3
    linarith

theorem four_of_sq (f : ℤ → ℝ) (hf : Summable (fun n => f n ^ 2)) : Summable (fun n => f n ^ 4) := by
  have h : ∀ᶠ n : ℤ in Filter.cofinite, f n ^ 2 ≤ 1 :=
    hf.tendsto_cofinite_zero.eventually (ge_mem_nhds one_pos)
  refine Summable.of_norm_bounded_eventually hf ?_
  filter_upwards [h] with n hn
  have h0 : 0 ≤ f n ^ 2 := sq_nonneg _
  have h1 : f n ^ 2 ≤ 1 := hn
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have e : f n ^ 4 = f n ^ 2 * f n ^ 2 := by ring
  rw [e]
  nlinarith

theorem pow4_sum_le (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a + b + c) ^ 4 ≤ 27 * (a ^ 4 + b ^ 4 + c ^ 4) := by
  have h1 : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
  have h2 : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≤ 3 * (a ^ 4 + b ^ 4 + c ^ 4) := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (a ^ 2 - c ^ 2)]
  have h3 : ((a + b + c) ^ 2) ^ 2 ≤ (3 * (a ^ 2 + b ^ 2 + c ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) h1 2
  nlinarith

end
end NlsGge.ThirdConsultation.KSPS028P
