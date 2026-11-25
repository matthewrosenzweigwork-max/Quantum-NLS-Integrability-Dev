import Mathlib
import NlsGge.Hierarchy.ALNegativeQuartic38
import NlsGge.Hierarchy.ALGaussianNormalizer38
import NlsGge.Sobolev.SourceWeighted

                                                                                                                                      
                                                                                  
                                                                                                                                        
                                                                                                                                            
                                                                                                                 
set_option autoImplicit false

open scoped BigOperators Matrix ENNReal
open Set Filter Topology MeasureTheory
open NlsGge.AblowitzLadik
open NlsGge.Weights NlsGge.Pilot

namespace NlsGge.ThirdConsultation.AL
noncomputable section

namespace AL107Aux

theorem sqrt_sub_one_bound {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : |Real.sqrt (1 - u) - 1| ≤ u := by
  have h := sqrt_one_sub_bound38 h0 h1
  rw [abs_le] at h ⊢
  constructor <;> nlinarith [h.1, h.2, sq_nonneg u, mul_nonneg h0 (sub_nonneg.2 h1)]


theorem geom_d {omega h q d : ℝ} (hh : 0 < h) (hu1 : h * |q| ≤ 1 / 2)
    (hd : d = omega * Real.sqrt (1 - h ^ 2 * q ^ 2) - omega) :
    |d| ≤ (|omega| * h ^ 2) * q ^ 2 ∧
      |d + h ^ 2 * omega * q ^ 2 / 2| ≤ |omega| * h ^ 4 * q ^ 4 / 2 := by
  have hu0 : 0 ≤ h ^ 2 * q ^ 2 := by positivity
  have hu1' : h ^ 2 * q ^ 2 ≤ 1 := by
    have h2 : h ^ 2 * q ^ 2 = (h * |q|) ^ 2 := by rw [mul_pow, sq_abs]
    rw [h2]; nlinarith [mul_nonneg hh.le (abs_nonneg q)]
  constructor
  · have e : d = omega * (Real.sqrt (1 - h ^ 2 * q ^ 2) - 1) := by rw [hd]; ring
    rw [e, abs_mul]
    calc |omega| * |Real.sqrt (1 - h ^ 2 * q ^ 2) - 1| ≤ |omega| * (h ^ 2 * q ^ 2) :=
          mul_le_mul_of_nonneg_left (sqrt_sub_one_bound hu0 hu1') (abs_nonneg _)
      _ = (|omega| * h ^ 2) * q ^ 2 := by ring
  · have e : d + h ^ 2 * omega * q ^ 2 / 2 =
        omega * (Real.sqrt (1 - h ^ 2 * q ^ 2) - (1 - h ^ 2 * q ^ 2 / 2)) := by rw [hd]; ring
    rw [e, abs_mul]
    calc |omega| * |Real.sqrt (1 - h ^ 2 * q ^ 2) - (1 - h ^ 2 * q ^ 2 / 2)|
        ≤ |omega| * ((h ^ 2 * q ^ 2) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left (sqrt_one_sub_bound38 hu0 hu1') (abs_nonneg _)
      _ = |omega| * h ^ 4 * q ^ 4 / 2 := by ring

theorem geom_s {A d c0 q delta : ℝ} (hA0 : 0 ≤ A) (hd1 : |d| ≤ A * q ^ 2)
    (hq : |q| ≤ delta) (hδ2 : delta ≤ 1 / 4) (hδ3 : delta ≤ 1 / (2 * (A + 1)))
    (hc0 : |c0| ≤ 1) :
    q ^ 2 ≤ |q| ∧ |d + 2 * c0 * q| ≤ 1 ∧ |d - 2 * c0 * q| ≤ 1 ∧
      |d + 2 * c0 * q| ≤ (A + 2) * |q| ∧ |d - 2 * c0 * q| ≤ (A + 2) * |q| := by
  have hqle1 : |q| ≤ 1 / 4 := hq.trans hδ2
  have hq2 : q ^ 2 ≤ |q| := by
    have : q ^ 2 = |q| * |q| := by rw [← sq_abs]; ring
    rw [this]; nlinarith [abs_nonneg q]
  have hAδ : A * q ^ 2 ≤ 1 / 2 := by
    have h1 : q ^ 2 ≤ delta := hq2.trans hq
    have h2 : A * q ^ 2 ≤ A * delta := mul_le_mul_of_nonneg_left h1 hA0
    have h3 : A * delta ≤ A * (1 / (2 * (A + 1))) := mul_le_mul_of_nonneg_left hδ3 hA0
    have h4 : A * (1 / (2 * (A + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hc2q : |2 * c0 * q| ≤ 2 * |q| := by
    rw [abs_mul, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    nlinarith [abs_nonneg c0, abs_nonneg q, mul_nonneg (abs_nonneg c0) (abs_nonneg q)]
  have hdq : |d| ≤ A * |q| := hd1.trans (mul_le_mul_of_nonneg_left hq2 hA0)
  have hp : |d + 2 * c0 * q| ≤ |d| + |2 * c0 * q| := abs_add_le _ _
  have hm : |d - 2 * c0 * q| ≤ |d| + |2 * c0 * q| := by
    simpa [sub_eq_add_neg] using abs_add_le d (-(2 * c0 * q))
  refine ⟨hq2, ?_, ?_, ?_, ?_⟩ <;> nlinarith [abs_nonneg q]

theorem pow4_bound {A x q : ℝ} (hx : |x| ≤ (A + 2) * |q|) : x ^ 4 ≤ (A + 2) ^ 4 * q ^ 4 := by
  have h1 : |x| ^ 4 ≤ ((A + 2) * |q|) ^ 4 := pow_le_pow_left₀ (abs_nonneg x) hx 4
  have h2 : |x| ^ 4 = x ^ 4 := by
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  have h3 : ((A + 2) * |q|) ^ 4 = (A + 2) ^ 4 * q ^ 4 := by
    rw [mul_pow, show (4:ℕ) = 2 * 2 from rfl, pow_mul |q|, sq_abs, ← pow_mul]
  linarith

theorem abs_add4 (a b c e : ℝ) : |a + b + c + e| ≤ |a| + |b| + |c| + |e| := by
  have h1 := abs_add_le (a + b + c) e
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  linarith

theorem err_bound {W0 Wp Wm omega h c0 q d A W1 W2 W3 M : ℝ} (hA : A = |omega| * h ^ 2)
    (hM0 : 0 ≤ M) (hA0 : 0 ≤ A) (hq2 : q ^ 2 ≤ 1)
    (hd1 : |d| ≤ A * q ^ 2) (hd2 : |d + h ^ 2 * omega * q ^ 2 / 2| ≤ |omega| * h ^ 4 * q ^ 4 / 2)
    (hc0 : |c0| ≤ 1)
    (hRp : |Wp - (W0 + W1 * (d + 2 * c0 * q) + W2 * (d + 2 * c0 * q) ^ 2 / 2 +
      W3 * (d + 2 * c0 * q) ^ 3 / 6)| ≤ M * ((A + 2) ^ 4 * q ^ 4))
    (hRm : |Wm - (W0 + W1 * (d - 2 * c0 * q) + W2 * (d - 2 * c0 * q) ^ 2 / 2 +
      W3 * (d - 2 * c0 * q) ^ 3 / 6)| ≤ M * ((A + 2) ^ 4 * q ^ 4)) :
    |(Wp + Wm) / 2 - (W0 + (-h ^ 2 * omega * W1 / 2 + 2 * c0 ^ 2 * W2) * q ^ 2)| ≤
      (|W1| * (|omega| * h ^ 4 / 2) + |W2| / 2 * (A ^ 2) +
        |W3| / 6 * (|omega| ^ 3 * h ^ 6 + 12 * A) + M * (A + 2) ^ 4) * q ^ 4 := by
  have hq4' : (0:ℝ) ≤ q ^ 4 := by positivity
  have hq6 : q ^ 6 ≤ q ^ 4 := by
    have : q ^ 6 = q ^ 4 * q ^ 2 := by ring
    rw [this]; nlinarith
  have hdd2 : d ^ 2 ≤ A ^ 2 * q ^ 4 := by
    have h1 : |d| ^ 2 ≤ (A * q ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg d) hd1 2
    rw [sq_abs] at h1; nlinarith
  have hd3 : |d| ^ 3 ≤ A ^ 3 * q ^ 4 := by
    have h1 : |d| ^ 3 ≤ (A * q ^ 2) ^ 3 := pow_le_pow_left₀ (abs_nonneg d) hd1 3
    have h2 : (A * q ^ 2) ^ 3 = A ^ 3 * q ^ 6 := by ring
    have h3 : A ^ 3 * q ^ 6 ≤ A ^ 3 * q ^ 4 :=
      mul_le_mul_of_nonneg_left hq6 (by positivity)
    linarith
  have hc0sq : c0 ^ 2 ≤ 1 := by
    have : |c0| ^ 2 ≤ 1 := by nlinarith [abs_nonneg c0]
    rwa [sq_abs] at this
  have hE : (Wp + Wm) / 2 - (W0 + (-h ^ 2 * omega * W1 / 2 + 2 * c0 ^ 2 * W2) * q ^ 2) =
      W1 * (d + h ^ 2 * omega * q ^ 2 / 2) + W2 * d ^ 2 / 2 +
        W3 * (d ^ 3 + 12 * c0 ^ 2 * q ^ 2 * d) / 6 +
      ((Wp - (W0 + W1 * (d + 2 * c0 * q) + W2 * (d + 2 * c0 * q) ^ 2 / 2 +
        W3 * (d + 2 * c0 * q) ^ 3 / 6)) +
      (Wm - (W0 + W1 * (d - 2 * c0 * q) + W2 * (d - 2 * c0 * q) ^ 2 / 2 +
        W3 * (d - 2 * c0 * q) ^ 3 / 6))) / 2 := by ring
  rw [hE]
  have b1 : |W1 * (d + h ^ 2 * omega * q ^ 2 / 2)| ≤ |W1| * (|omega| * h ^ 4 / 2) * q ^ 4 := by
    rw [abs_mul]
    calc |W1| * |d + h ^ 2 * omega * q ^ 2 / 2| ≤ |W1| * (|omega| * h ^ 4 * q ^ 4 / 2) :=
          mul_le_mul_of_nonneg_left hd2 (abs_nonneg _)
      _ = _ := by ring
  have b2 : |W2 * d ^ 2 / 2| ≤ |W2| / 2 * A ^ 2 * q ^ 4 := by
    rw [abs_div, abs_mul, show |(2:ℝ)| = 2 by norm_num, abs_of_nonneg (sq_nonneg d)]
    calc |W2| * d ^ 2 / 2 ≤ |W2| * (A ^ 2 * q ^ 4) / 2 := by gcongr
      _ = _ := by ring
  have b3 : |W3 * (d ^ 3 + 12 * c0 ^ 2 * q ^ 2 * d) / 6| ≤
      |W3| / 6 * (A ^ 3 + 12 * A) * q ^ 4 := by
    rw [abs_div, abs_mul, show |(6:ℝ)| = 6 by norm_num]
    have h1 : |d ^ 3 + 12 * c0 ^ 2 * q ^ 2 * d| ≤ (A ^ 3 + 12 * A) * q ^ 4 := by
      calc |d ^ 3 + 12 * c0 ^ 2 * q ^ 2 * d| ≤ |d ^ 3| + |12 * c0 ^ 2 * q ^ 2 * d| :=
            abs_add_le _ _
        _ ≤ A ^ 3 * q ^ 4 + 12 * A * q ^ 4 := by
            refine add_le_add ?_ ?_
            · rw [abs_pow]; exact hd3
            · rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow]
              rw [show |(12:ℝ)| = 12 by norm_num, sq_abs, sq_abs]
              calc 12 * c0 ^ 2 * q ^ 2 * |d| ≤ 12 * 1 * q ^ 2 * (A * q ^ 2) := by
                    have : 0 ≤ q ^ 2 := sq_nonneg q
                    gcongr
                _ = 12 * A * q ^ 4 := by ring
        _ = (A ^ 3 + 12 * A) * q ^ 4 := by ring
    calc |W3| * |d ^ 3 + 12 * c0 ^ 2 * q ^ 2 * d| / 6 ≤ |W3| * ((A ^ 3 + 12 * A) * q ^ 4) / 6 := by
          gcongr
      _ = _ := by ring
  have b4 : |((Wp - (W0 + W1 * (d + 2 * c0 * q) + W2 * (d + 2 * c0 * q) ^ 2 / 2 +
        W3 * (d + 2 * c0 * q) ^ 3 / 6)) +
      (Wm - (W0 + W1 * (d - 2 * c0 * q) + W2 * (d - 2 * c0 * q) ^ 2 / 2 +
        W3 * (d - 2 * c0 * q) ^ 3 / 6))) / 2| ≤ M * ((A + 2) ^ 4 * q ^ 4) := by
    rw [abs_div, show |(2:ℝ)| = 2 by norm_num]
    have := abs_add_le (Wp - (W0 + W1 * (d + 2 * c0 * q) + W2 * (d + 2 * c0 * q) ^ 2 / 2 +
        W3 * (d + 2 * c0 * q) ^ 3 / 6)) (Wm - (W0 + W1 * (d - 2 * c0 * q) +
        W2 * (d - 2 * c0 * q) ^ 2 / 2 + W3 * (d - 2 * c0 * q) ^ 3 / 6))
    linarith
  have hA3 : |omega| ^ 3 * h ^ 6 = A ^ 3 := by rw [hA]; ring
  have hCq : (|W1| * (|omega| * h ^ 4 / 2) + |W2| / 2 * (A ^ 2) +
        |W3| / 6 * (|omega| ^ 3 * h ^ 6 + 12 * A) + M * (A + 2) ^ 4) * q ^ 4 =
      |W1| * (|omega| * h ^ 4 / 2) * q ^ 4 + |W2| / 2 * A ^ 2 * q ^ 4 +
      |W3| / 6 * (A ^ 3 + 12 * A) * q ^ 4 + M * ((A + 2) ^ 4 * q ^ 4) := by
    rw [hA3]; ring
  rw [hCq]
  refine (abs_add4 _ _ _ _).trans ?_
  linarith [b1, b2, b3, b4]

end AL107Aux

open AL107Aux in
theorem al107 (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (h : ℝ) (hh : 0 < h) (k : ℤ) :
    let W : ℝ → ℝ := weight c.val
    let omega : ℝ := alOmega38 h k
    let c0 : ℝ := Real.cos (Real.pi * (k : ℝ) * h)
    ∃ C delta : ℝ, 0 ≤ C ∧ 0 < delta ∧ h * delta ≤ 1 / 2 ∧
      ∀ q : ℝ, |q| ≤ delta →
      |(W (omega * Real.sqrt (1 - h ^ 2 * q ^ 2) + 2 * c0 * q) +
          W (omega * Real.sqrt (1 - h ^ 2 * q ^ 2) - 2 * c0 * q)) / 2 -
        (W omega + (-h ^ 2 * omega * deriv W omega / 2 +
          2 * c0 ^ 2 * deriv (deriv W) omega) * q ^ 2)| ≤ C * q ^ 4 := by
  intro W omega c0
  obtain ⟨hW1, hW2, hW3, hW4, hWc⟩ := weight_chain38 c.property
  obtain ⟨M, hM0, hM⟩ := taylor4_38 hW1 hW2 hW3 hW4 hWc omega
  set W1 := deriv W omega with hW1d
  set W2 := deriv (deriv W) omega with hW2d
  set W3 := deriv (deriv (deriv W)) omega with hW3d
  have hc0 : |c0| ≤ 1 := Real.abs_cos_le_one _
  set A : ℝ := |omega| * h ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  set delta : ℝ := min (min (1 / (2 * h)) (1 / 4)) (1 / (2 * (A + 1))) with hdelta
  have hδ1 : delta ≤ 1 / (2 * h) := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : delta ≤ 1 / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : delta ≤ 1 / (2 * (A + 1)) := min_le_right _ _
  have hδpos : 0 < delta := lt_min (lt_min (by positivity) (by norm_num)) (by positivity)
  have hhδ : h * delta ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hδ1 hh.le
    calc h * delta ≤ h * (1 / (2 * h)) := this
      _ = 1 / 2 := by field_simp
  -- the constant
  set C : ℝ := |W1| * (|omega| * h ^ 4 / 2) + |W2| / 2 * (A ^ 2) +
      |W3| / 6 * (|omega| ^ 3 * h ^ 6 + 12 * A) + M * (A + 2) ^ 4 with hC
  have hCnn : 0 ≤ C := by positivity
  refine ⟨C, delta, hCnn, hδpos, hhδ, fun q hq => ?_⟩
  have hM' : ∀ s : ℝ, |s| ≤ 1 →
      |W (omega + s) - (W omega + W1 * s + W2 * s ^ 2 / 2 + W3 * s ^ 3 / 6)| ≤ M * s ^ 4 := hM
  have hu1 : h * |q| ≤ 1 / 2 := (mul_le_mul_of_nonneg_left hq hh.le).trans hhδ
  obtain ⟨hd1, hd2⟩ := geom_d (omega := omega) (h := h) (q := q)
    (d := omega * Real.sqrt (1 - h ^ 2 * q ^ 2) - omega) hh hu1 rfl
  obtain ⟨hq2, g1, g2, g3, g4⟩ := geom_s (c0 := c0) (delta := delta) hA0 hd1 hq hδ2 hδ3 hc0
  have hq1 : q ^ 2 ≤ 1 := by
    have : |q| ≤ 1 / 4 := hq.trans hδ2
    nlinarith [abs_nonneg q]
  have hRp := (hM' _ g1).trans (mul_le_mul_of_nonneg_left (pow4_bound g3) hM0)
  have hRm := (hM' _ g2).trans (mul_le_mul_of_nonneg_left (pow4_bound g4) hM0)
  have ep : omega * Real.sqrt (1 - h ^ 2 * q ^ 2) + 2 * c0 * q =
      omega + ((omega * Real.sqrt (1 - h ^ 2 * q ^ 2) - omega) + 2 * c0 * q) := by ring
  have em : omega * Real.sqrt (1 - h ^ 2 * q ^ 2) - 2 * c0 * q =
      omega + ((omega * Real.sqrt (1 - h ^ 2 * q ^ 2) - omega) - 2 * c0 * q) := by ring
  have key := err_bound (W0 := W omega) (omega := omega) (h := h) (c0 := c0) (q := q)
    (A := A) (W1 := W1) (W2 := W2) (W3 := W3) (M := M) hA hM0 hA0 hq1 hd1 hd2 hc0 hRp hRm
  rw [ep, em]
  exact key

end
end NlsGge.ThirdConsultation.AL
