import Mathlib

/-!
# R-F9AB39A7 `QG:lem:haar-offgrid-bessel`: the square-sum estimates

(`source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:641-650`)  Pure real/complex analysis, no operators:

* `hasSum_odd_sq`: `∑_{j≥0} (j+1/2)^{-2} = π²/2` (from `hasSum_zeta_two`);
* `sum_int_le`: if `v ∈ ℂ` has distance `≥ 1/4` from `-ℤ` then every finite sum `∑_{n∈F} |n+v|^{-2} ≤ 16 + π²`
  ("the central term of the square resolvent sum is at most 16, the other terms give π²");
* `sum_prod_le`: for `r ≥ 1` distinct (indeed arbitrary) integers `k_i`, `∑_{n∈F} ∏_i |n-k_i+v|^{-2} ≤ 16^{r-1}(16+π²)`
  (each factor `≤ 16`, one factor summed).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open Finset
open scoped BigOperators

namespace QuantumNLS.Offgrid

theorem hasSum_odd_sq : HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1 / 2) ^ 2) (Real.pi ^ 2 / 2) := by
  have hz : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6) := hasSum_zeta_two
  have he : HasSum (fun j : ℕ => (1 / 4 : ℝ) * (1 / (j : ℝ) ^ 2)) ((1 / 4) * (Real.pi ^ 2 / 6)) :=
    hz.mul_left _
  have he' : HasSum (fun j : ℕ => 1 / ((2 * j : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 24) := by
    have e : (fun j : ℕ => 1 / ((2 * j : ℕ) : ℝ) ^ 2) = fun j : ℕ => (1 / 4 : ℝ) * (1 / (j : ℝ) ^ 2) := by
      funext j
      by_cases hj : (j : ℝ) = 0
      · simp [hj]
      · push_cast
        field_simp
        norm_num
    rw [e]
    convert he using 1
    ring
  have hodd_s : Summable (fun j : ℕ => 1 / ((2 * j + 1 : ℕ) : ℝ) ^ 2) :=
    hz.summable.comp_injective (i := fun j : ℕ => 2 * j + 1) (fun a b h => by simpa using h)
  have htot := HasSum.even_add_odd (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) he' hodd_s.hasSum
  have hb : ∑' j : ℕ, 1 / ((2 * j + 1 : ℕ) : ℝ) ^ 2 = Real.pi ^ 2 / 8 := by
    have := htot.unique hz
    linarith
  have hodd : HasSum (fun j : ℕ => 1 / ((2 * j + 1 : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 8) := by
    rw [← hb]; exact hodd_s.hasSum
  have h4 := hodd.mul_left 4
  have e2 : (fun j : ℕ => 4 * (1 / ((2 * j + 1 : ℕ) : ℝ) ^ 2)) =
      fun j : ℕ => 1 / ((j : ℝ) + 1 / 2) ^ 2 := by
    funext j
    push_cast
    have : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  rw [e2] at h4
  convert h4 using 1
  ring

/-- The majorant: `16` at the center, `(|j| - 1/2)^{-2}` elsewhere. -/
def Hm (j : ℤ) : ℝ := if j = 0 then 16 else 1 / (|(j : ℝ)| - 1 / 2) ^ 2

theorem Hm_nonneg (j : ℤ) : 0 ≤ Hm j := by
  unfold Hm; split_ifs <;> positivity

theorem hasSum_Hm : HasSum Hm (16 + Real.pi ^ 2) := by
  have hpos : HasSum (fun n : ℕ => Hm ((n + 1 : ℕ) : ℤ)) (Real.pi ^ 2 / 2) := by
    have e : (fun n : ℕ => Hm ((n + 1 : ℕ) : ℤ)) = fun n : ℕ => 1 / ((n : ℝ) + 1 / 2) ^ 2 := by
      funext n
      unfold Hm
      rw [if_neg (by omega)]
      congr 2
      push_cast
      rw [abs_of_nonneg (by positivity)]
      ring
    rw [e]; exact hasSum_odd_sq
  have hnat : HasSum (fun n : ℕ => Hm (n : ℤ)) (Real.pi ^ 2 / 2 + 16) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa [Hm] using hpos
  have hneg : HasSum (fun n : ℕ => Hm (-((n : ℤ) + 1))) (Real.pi ^ 2 / 2) := by
    have e : (fun n : ℕ => Hm (-((n : ℤ) + 1))) = fun n : ℕ => Hm ((n + 1 : ℕ) : ℤ) := by
      funext n
      unfold Hm
      rw [if_neg (by omega), if_neg (by omega)]
      congr 2
      push_cast
      rw [abs_neg]
    rw [e]; exact hpos
  have := HasSum.of_nat_of_neg_add_one hnat hneg
  convert this using 1
  ring

theorem sum_Hm_le (F : Finset ℤ) : ∑ j ∈ F, Hm j ≤ 16 + Real.pi ^ 2 :=
  sum_le_hasSum F (fun j _ => Hm_nonneg j) hasSum_Hm

/-- `v` has distance at least `1/4` from `-ℤ`. -/
def Far (v : ℂ) : Prop := ∀ m : ℤ, 1 / 4 ≤ ‖(m : ℂ) + v‖

theorem term_le_Hm {v : ℂ} (hv : Far v) (n : ℤ) :
    1 / ‖(n : ℂ) + v‖ ^ 2 ≤ Hm (n + round v.re) := by
  set c : ℤ := round v.re with hcdef
  have hc : |v.re - c| ≤ 1 / 2 := abs_sub_round v.re
  by_cases h : n + c = 0
  · unfold Hm
    rw [if_pos h]
    have h1 := hv n
    have : 1 / ‖(n : ℂ) + v‖ ^ 2 ≤ 1 / (1 / 4 : ℝ) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by norm_num) h1 2)
    refine this.trans (le_of_eq ?_)
    norm_num
  · unfold Hm
    rw [if_neg h]
    have hj : (1 : ℝ) ≤ |((n + c : ℤ) : ℝ)| := by
      have : (1 : ℤ) ≤ |n + c| := Int.one_le_abs h
      have h2 : ((1 : ℤ) : ℝ) ≤ ((|n + c| : ℤ) : ℝ) := by exact_mod_cast this
      simpa [Int.cast_abs] using h2
    have hre : |(n : ℝ) + v.re| ≥ |((n + c : ℤ) : ℝ)| - 1 / 2 := by
      have : (n : ℝ) + v.re = ((n + c : ℤ) : ℝ) + (v.re - c) := by push_cast; ring
      rw [this]
      have := abs_add_le (((n + c : ℤ) : ℝ) + (v.re - c)) (-(v.re - c))
      have h3 : |((n + c : ℤ) : ℝ)| ≤ |((n + c : ℤ) : ℝ) + (v.re - c)| + |v.re - c| := by
        calc |((n + c : ℤ) : ℝ)| = |(((n + c : ℤ) : ℝ) + (v.re - c)) - (v.re - c)| := by ring_nf
          _ ≤ _ := abs_sub _ _
      linarith
    have hnorm : |(n : ℝ) + v.re| ≤ ‖(n : ℂ) + v‖ := by
      have := Complex.abs_re_le_norm ((n : ℂ) + v)
      simpa using this
    have hpos : 0 < |((n + c : ℤ) : ℝ)| - 1 / 2 := by linarith
    have hge : |((n + c : ℤ) : ℝ)| - 1 / 2 ≤ ‖(n : ℂ) + v‖ := by linarith
    have e : |(((n + c : ℤ)) : ℝ)| = |((n + c : ℤ) : ℝ)| := rfl
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hpos.le hge 2)

theorem sum_int_le {v : ℂ} (hv : Far v) (F : Finset ℤ) :
    ∑ n ∈ F, 1 / ‖(n : ℂ) + v‖ ^ 2 ≤ 16 + Real.pi ^ 2 := by
  set c : ℤ := round v.re
  calc ∑ n ∈ F, 1 / ‖(n : ℂ) + v‖ ^ 2 ≤ ∑ n ∈ F, Hm (n + c) :=
        sum_le_sum (fun n _ => term_le_Hm hv n)
    _ = ∑ j ∈ F.map (addRightEmbedding c), Hm j := by
        rw [Finset.sum_map]; rfl
    _ ≤ 16 + Real.pi ^ 2 := sum_Hm_le _

theorem sum_prod_le {r : ℕ} (hr : 1 ≤ r) {v : ℂ} (hv : Far v) (k : Fin r → ℤ) (F : Finset ℤ) :
    ∑ n ∈ F, ∏ i : Fin r, 1 / ‖(n : ℂ) - k i + v‖ ^ 2 ≤ 16 ^ (r - 1) * (16 + Real.pi ^ 2) := by
  set i0 : Fin r := ⟨0, hr⟩
  have hfac : ∀ (n : ℤ) (i : Fin r), 1 / ‖(n : ℂ) - k i + v‖ ^ 2 ≤ 16 := by
    intro n i
    have h1 : (n : ℂ) - k i + v = ((n - k i : ℤ) : ℂ) + v := by push_cast; ring
    rw [h1]
    have h2 := hv (n - k i)
    have : 1 / ‖((n - k i : ℤ) : ℂ) + v‖ ^ 2 ≤ 1 / (1 / 4 : ℝ) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by norm_num) h2 2)
    refine this.trans (le_of_eq ?_)
    norm_num
  have hterm : ∀ n : ℤ, ∏ i : Fin r, 1 / ‖(n : ℂ) - k i + v‖ ^ 2 ≤
      16 ^ (r - 1) * (1 / ‖((n - k i0 : ℤ) : ℂ) + v‖ ^ 2) := by
    intro n
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0)]
    have h1 : ∏ i ∈ Finset.univ.erase i0, 1 / ‖(n : ℂ) - k i + v‖ ^ 2 ≤ 16 ^ (r - 1) := by
      calc ∏ i ∈ Finset.univ.erase i0, 1 / ‖(n : ℂ) - k i + v‖ ^ 2
          ≤ ∏ i ∈ Finset.univ.erase i0, (16 : ℝ) :=
            Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => hfac n i)
        _ = 16 ^ (r - 1) := by
            rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _)]
            simp
    have h2 : 1 / ‖(n : ℂ) - k i0 + v‖ ^ 2 = 1 / ‖((n - k i0 : ℤ) : ℂ) + v‖ ^ 2 := by
      congr 3; push_cast; ring
    rw [h2, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  calc ∑ n ∈ F, ∏ i : Fin r, 1 / ‖(n : ℂ) - k i + v‖ ^ 2
      ≤ ∑ n ∈ F, 16 ^ (r - 1) * (1 / ‖((n - k i0 : ℤ) : ℂ) + v‖ ^ 2) := sum_le_sum (fun n _ => hterm n)
    _ = 16 ^ (r - 1) * ∑ n ∈ F, 1 / ‖((n - k i0 : ℤ) : ℂ) + v‖ ^ 2 := by rw [← Finset.mul_sum]
    _ = 16 ^ (r - 1) * ∑ m ∈ F.map (Equiv.subRight (k i0)).toEmbedding, 1 / ‖(m : ℂ) + v‖ ^ 2 := by
        rw [Finset.sum_map]; rfl
    _ ≤ 16 ^ (r - 1) * (16 + Real.pi ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_int_le hv _) (by positivity)

#print axioms sum_prod_le

end QuantumNLS.Offgrid
