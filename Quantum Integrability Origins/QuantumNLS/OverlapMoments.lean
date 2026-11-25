import QuantumNLS.PlacementFusion
import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# R-32EBD5C1 `lem:root-overlap` (ROOT_transfer_involution.tex:25) -- SCALAR/COMBINATORIAL CONSTITUENT ONLY

Source facts used in the printed proof, proved here for the realized hypergeometric coefficient
`overlapCoefficient N p q s = C(p,s) C(N-p,q-s) / C(N,q)` (PlacementFusion, read-only):
* `first_moment`: `E|I∩J| = Σ s c_{N,s} = pq/N`; `prob_intersect_le`: `ℙ(I∩J≠∅) = Σ_{s≥1} c_s ≤ pq/N`;
* `second_moment`: `Σ s(s-1) c_s = p(p-1)q(q-1)/(N(N-1))`; `tail_two_le`:
  `Σ_{s≥2} c_s ≤ p(p-1)q(q-1)/(2N(N-1))` (the printed `E C(|I∩J|,2)` bound);
* `tendsto_N_c_one`: `N c_{N,1} → pq`; `tendsto_N_tail`: `N Σ_{s≥2} c_s → 0` (fixed `p,q`).
NOT PROVED (operator part of the lemma): that placements on disjoint slot sets commute, the commutator
bound `N‖[Q_{N,p}(A),Q_{N,q}(B)]‖ ≤ 2pq‖A‖‖B‖`, the single-overlap expectation `⟨α,β⟩` in `u^{⊗N}`,
and the identification with the bracket `{a,b}`.
-/

set_option autoImplicit false
noncomputable section
open Finset Filter Topology
open QuantumNLS.PlacementFusion

namespace QuantumNLS.OverlapMoments

/-- Vandermonde in the form `∑_{s ≤ q} C(a,s) C(b,q-s) = C(a+b,q)`. -/
theorem vandermonde_range (a b q : ℕ) :
    ∑ s ∈ range (q + 1), a.choose s * b.choose (q - s) = (a + b).choose q := by
  rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
    (fun ij : ℕ × ℕ => a.choose ij.1 * b.choose ij.2) q, ← Nat.add_choose_eq]

/-- First factorial moment, natural-number form. -/
theorem nat_first_moment (p M q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ∑ s ∈ range (q + 1), s * (p.choose s * M.choose (q - s)) =
      p * (p - 1 + M).choose (q - 1) := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  rw [Finset.sum_range_succ']
  simp only [zero_mul, add_zero]
  have h : ∀ s ∈ range (q' + 1), (s + 1) * ((p' + 1).choose (s + 1) * M.choose (q' + 1 - (s + 1))) =
      (p' + 1) * (p'.choose s * M.choose (q' - s)) := by
    intro s hs
    have h1 := Nat.add_one_mul_choose_eq p' s
    have : q' + 1 - (s + 1) = q' - s := by omega
    rw [this]
    calc (s + 1) * ((p' + 1).choose (s + 1) * M.choose (q' - s))
        = ((p' + 1).choose (s + 1) * (s + 1)) * M.choose (q' - s) := by ring
      _ = ((p' + 1) * p'.choose s) * M.choose (q' - s) := by rw [← h1]
      _ = _ := by ring
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, vandermonde_range]
  simp

/-- Second factorial moment, natural-number form. -/
theorem nat_second_moment (p M q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    ∑ s ∈ range (q + 1), (s * (s - 1)) * (p.choose s * M.choose (q - s)) =
      (p * (p - 1)) * (p - 2 + M).choose (q - 2) := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 2 := ⟨p - 2, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 2 := ⟨q - 2, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.mul_zero, zero_mul, add_zero, Nat.sub_self, Nat.add_sub_cancel_left,
    Nat.zero_add, Nat.sub_zero, Nat.add_sub_cancel]
  have h : ∀ s ∈ range (q' + 1),
      ((s + 1 + 1) * (s + 1)) * ((p' + 2).choose (s + 1 + 1) *
        M.choose (q' + 2 - (s + 1 + 1))) =
      ((p' + 2) * (p' + 2 - 1)) * (p'.choose s * M.choose (q' - s)) := by
    intro s hs
    have h1 := Nat.add_one_mul_choose_eq (p' + 1) (s + 1)
    have h2 := Nat.add_one_mul_choose_eq p' s
    have e : q' + 2 - (s + 1 + 1) = q' - s := by omega
    rw [e]
    have e3 : p' + 2 - 1 = p' + 1 := by omega
    rw [e3]
    calc (s + 1 + 1) * (s + 1) * ((p' + 2).choose (s + 1 + 1) * M.choose (q' - s))
        = ((p' + 2).choose (s + 1 + 1) * (s + 1 + 1)) * (s + 1) * M.choose (q' - s) := by ring
      _ = ((p' + 1 + 1) * (p' + 1).choose (s + 1)) * (s + 1) * M.choose (q' - s) := by
          rw [← h1]
      _ = (p' + 2) * ((p' + 1).choose (s + 1) * (s + 1)) * M.choose (q' - s) := by ring
      _ = (p' + 2) * ((p' + 1) * p'.choose s) * M.choose (q' - s) := by rw [← h2]
      _ = _ := by ring
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, vandermonde_range]

theorem choose_ne_zero_real {N q : ℕ} (hq : q ≤ N) : (N.choose q : ℝ) ≠ 0 := by
  exact_mod_cast Nat.choose_ne_zero hq

theorem overlapCoefficient_of_le {N p q s : ℕ} (hs : s ≤ q) :
    overlapCoefficient N p q s =
      ((p.choose s * (N - p).choose (q - s) : ℕ) : ℝ) / (N.choose q : ℝ) := by
  simp [overlapCoefficient, hs]

theorem overlapCoefficient_eq_zero_of_gt {N p q s : ℕ} (hs : p < s) :
    overlapCoefficient N p q s = 0 := by
  unfold overlapCoefficient
  split_ifs
  · simp [Nat.choose_eq_zero_of_lt hs]
  · rfl

/-- First moment of the overlap law: `E|I ∩ J| = pq/N`. -/
theorem first_moment {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N) (hN : 1 ≤ N) :
    ∑ s ∈ range (q + 1), (s : ℝ) * overlapCoefficient N p q s = (p * q : ℝ) / N := by
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have hden := choose_ne_zero_real (N := N) hq
  rcases Nat.eq_zero_or_pos p with rfl | hp1
  · have : ∀ s ∈ range (q + 1), (s : ℝ) * overlapCoefficient N 0 q s = 0 := by
      intro s hs
      rcases Nat.eq_zero_or_pos s with rfl | hs1
      · simp
      · rw [overlapCoefficient_eq_zero_of_gt hs1]; simp
    rw [Finset.sum_eq_zero this]; simp
  rcases Nat.eq_zero_or_pos q with rfl | hq1
  · simp
  have hnat := nat_first_moment p (N - p) q hp1 hq1
  have e1 : p - 1 + (N - p) = N - 1 := by omega
  rw [e1] at hnat
  have h2 : ∀ s ∈ range (q + 1), (s : ℝ) * overlapCoefficient N p q s =
      ((s * (p.choose s * (N - p).choose (q - s)) : ℕ) : ℝ) / (N.choose q : ℝ) := by
    intro s hs
    have hsq : s ≤ q := by have := Finset.mem_range.mp hs; omega
    rw [overlapCoefficient_of_le hsq]
    push_cast; ring
  rw [Finset.sum_congr rfl h2, ← Finset.sum_div]
  have h3 : (∑ s ∈ range (q + 1), ((s * (p.choose s * (N - p).choose (q - s)) : ℕ) : ℝ)) =
      ((p * (N - 1).choose (q - 1) : ℕ) : ℝ) := by
    rw [← Nat.cast_sum, hnat]
  rw [h3]
  have h4 := Nat.add_one_mul_choose_eq (N - 1) (q - 1)
  have e2 : N - 1 + 1 = N := by omega
  have e3 : q - 1 + 1 = q := by omega
  rw [e2, e3] at h4
  have h4r : (N : ℝ) * ((N - 1).choose (q - 1) : ℝ) = (N.choose q : ℝ) * q := by exact_mod_cast h4
  push_cast
  field_simp
  nlinarith [h4r]

/-- Second factorial moment of the overlap law: `E[|I∩J|(|I∩J|-1)] = p(p-1)q(q-1)/(N(N-1))`. -/
theorem second_moment {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N) (hN : 2 ≤ N) :
    ∑ s ∈ range (q + 1), ((s * (s - 1) : ℕ) : ℝ) * overlapCoefficient N p q s =
      ((p : ℝ) * (p - 1) * q * (q - 1)) / ((N : ℝ) * (N - 1)) := by
  have hN1 : (N : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have hden := choose_ne_zero_real (N := N) hq
  by_cases hp2 : 2 ≤ p
  · by_cases hq2 : 2 ≤ q
    · have hnat := nat_second_moment p (N - p) q hp2 hq2
      have e1 : p - 2 + (N - p) = N - 2 := by omega
      rw [e1] at hnat
      have h2 : ∀ s ∈ range (q + 1), ((s * (s - 1) : ℕ) : ℝ) * overlapCoefficient N p q s =
          (((s * (s - 1)) * (p.choose s * (N - p).choose (q - s)) : ℕ) : ℝ) / (N.choose q : ℝ) := by
        intro s hs
        have hsq : s ≤ q := by have := Finset.mem_range.mp hs; omega
        rw [overlapCoefficient_of_le hsq]
        push_cast; ring
      rw [Finset.sum_congr rfl h2, ← Finset.sum_div, ← Nat.cast_sum, hnat]
      have h4 := Nat.add_one_mul_choose_eq (N - 1) (q - 1)
      have h5 := Nat.add_one_mul_choose_eq (N - 2) (q - 2)
      have e2 : N - 1 + 1 = N := by omega
      have e3 : q - 1 + 1 = q := by omega
      have e4 : N - 2 + 1 = N - 1 := by omega
      have e5 : q - 2 + 1 = q - 1 := by omega
      rw [e2, e3] at h4
      rw [e4, e5] at h5
      have h4r : (N : ℝ) * ((N - 1).choose (q - 1) : ℝ) = (N.choose q : ℝ) * q := by
        exact_mod_cast h4
      have h5r : ((N : ℝ) - 1) * ((N - 2).choose (q - 2) : ℝ) =
          ((N - 1).choose (q - 1) : ℝ) * ((q : ℝ) - 1) := by
        have : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        have hq1 : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [← this, ← hq1]; exact_mod_cast h5
      have hp1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      push_cast [hp1]
      rw [div_eq_div_iff hden (mul_ne_zero hNr hN1)]
      have : (N : ℝ) * (((N : ℝ) - 1) * ((N - 2).choose (q - 2) : ℝ)) =
          (N.choose q : ℝ) * q * ((q : ℝ) - 1) := by
        rw [h5r, ← mul_assoc, h4r]
      linear_combination (p * (p - 1 : ℝ)) * this
    · have : ∀ s ∈ range (q + 1), ((s * (s - 1) : ℕ) : ℝ) * overlapCoefficient N p q s = 0 := by
        intro s hs
        have hsq : s ≤ q := by have := Finset.mem_range.mp hs; omega
        have : s * (s - 1) = 0 := by
          have : s ≤ 1 := by omega
          interval_cases s <;> simp
        simp [this]
      rw [Finset.sum_eq_zero this]
      have : (q : ℝ) * ((q : ℝ) - 1) = 0 := by
        have : q ≤ 1 := by omega
        interval_cases q <;> simp
      rw [mul_assoc (p * ((p : ℝ) - 1)) (q : ℝ), this]; simp
  · have : ∀ s ∈ range (q + 1), ((s * (s - 1) : ℕ) : ℝ) * overlapCoefficient N p q s = 0 := by
      intro s hs
      by_cases hs2 : 2 ≤ s
      · rw [overlapCoefficient_eq_zero_of_gt (by omega)]; simp
      · have : s * (s - 1) = 0 := by
          have : s ≤ 1 := by omega
          interval_cases s <;> simp
        simp [this]
    rw [Finset.sum_eq_zero this]
    have : (p : ℝ) * ((p : ℝ) - 1) = 0 := by
      have : p ≤ 1 := by omega
      interval_cases p <;> simp
    rw [this]; simp

/-- `P(I ∩ J ≠ ∅) ≤ E|I ∩ J| = pq/N` (source: `ℙ(I∩J≠∅) ≤ 𝔼|I∩J| = pq/N`). -/
theorem prob_intersect_le {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N) (hN : 1 ≤ N) :
    ∑ s ∈ (range (q + 1)).filter (fun s => 1 ≤ s), overlapCoefficient N p q s ≤ (p * q : ℝ) / N := by
  rw [← first_moment hp hq hN]
  calc ∑ s ∈ (range (q + 1)).filter (fun s => 1 ≤ s), overlapCoefficient N p q s
      ≤ ∑ s ∈ (range (q + 1)).filter (fun s => 1 ≤ s), (s : ℝ) * overlapCoefficient N p q s := by
        refine Finset.sum_le_sum fun s hs => ?_
        have h1 : (1 : ℝ) ≤ s := by exact_mod_cast (Finset.mem_filter.mp hs).2
        nlinarith [overlapCoefficient_nonneg N p q s]
    _ ≤ ∑ s ∈ range (q + 1), (s : ℝ) * overlapCoefficient N p q s := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro s _ _
        exact mul_nonneg (Nat.cast_nonneg _) (overlapCoefficient_nonneg N p q s)

/-- `Σ_{r≥2} c_{N,r} ≤ E C(|I∩J|,2) = p(p-1)q(q-1)/(2N(N-1))`. -/
theorem tail_two_le {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N) (hN : 2 ≤ N) :
    ∑ s ∈ (range (q + 1)).filter (fun s => 2 ≤ s), overlapCoefficient N p q s ≤
      ((p : ℝ) * (p - 1) * q * (q - 1)) / (2 * ((N : ℝ) * (N - 1))) := by
  have hm := second_moment hp hq hN
  have hN1 : (0 : ℝ) < (N : ℝ) * (N - 1) := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have h1 : ∑ s ∈ (range (q + 1)).filter (fun s => 2 ≤ s), overlapCoefficient N p q s ≤
      (1 / 2 : ℝ) * ∑ s ∈ range (q + 1), ((s * (s - 1) : ℕ) : ℝ) * overlapCoefficient N p q s := by
    rw [Finset.mul_sum]
    calc ∑ s ∈ (range (q + 1)).filter (fun s => 2 ≤ s), overlapCoefficient N p q s
        ≤ ∑ s ∈ (range (q + 1)).filter (fun s => 2 ≤ s),
            (1 / 2 : ℝ) * (((s * (s - 1) : ℕ) : ℝ) * overlapCoefficient N p q s) := by
          refine Finset.sum_le_sum fun s hs => ?_
          have h2 : 2 ≤ s := (Finset.mem_filter.mp hs).2
          have h3 : (2 : ℝ) ≤ ((s * (s - 1) : ℕ) : ℝ) := by
            have : 2 ≤ s * (s - 1) := by
              have : 1 ≤ s - 1 := by omega
              nlinarith
            exact_mod_cast this
          nlinarith [overlapCoefficient_nonneg N p q s]
      _ ≤ ∑ s ∈ range (q + 1), (1 / 2 : ℝ) * (((s * (s - 1) : ℕ) : ℝ) * overlapCoefficient N p q s) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro s _ _
          exact mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (overlapCoefficient_nonneg N p q s))
  refine h1.trans (le_of_eq ?_)
  rw [hm]
  field_simp

/-- `N · Σ_{r ≥ 2} c_{N,r} → 0` for fixed `p, q`. -/
theorem tendsto_N_tail (p q : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) *
      ∑ s ∈ (range (q + 1)).filter (fun s => 2 ≤ s), overlapCoefficient N p q s)
      atTop (𝓝 0) := by
  set X : ℝ := (p : ℝ) * (p - 1) * q * (q - 1) with hX
  have hlim : Tendsto (fun N : ℕ => X / (2 * ((N : ℝ) - 1))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (N : ℝ) - 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun N : ℕ => 2 * ((N : ℝ) - 1)) atTop atTop :=
      h1.const_mul_atTop (by norm_num)
    have := h2.inv_tendsto_atTop.const_mul X
    simpa [div_eq_mul_inv] using this
  refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ hlim
  · exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun s _ => overlapCoefficient_nonneg N p q s)
  · filter_upwards [eventually_ge_atTop (max (max p q) 2)] with N hN
    have hp : p ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    have hq : q ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
    have h2 : 2 ≤ N := le_trans (le_max_right _ _) hN
    have hb := tail_two_le hp hq h2
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast h2
    have hNpos : (0 : ℝ) < N := by linarith
    have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
    calc (N : ℝ) * ∑ s ∈ (range (q + 1)).filter (fun s => 2 ≤ s), overlapCoefficient N p q s
        ≤ (N : ℝ) * (X / (2 * ((N : ℝ) * (N - 1)))) := mul_le_mul_of_nonneg_left hb hNpos.le
      _ = X / (2 * ((N : ℝ) - 1)) := by field_simp

/-- Splitting the first moment: for `q ≥ 1`,
`Σ_s s c_s = c_1 + Σ_{s ≥ 2} s c_s`. -/
theorem first_moment_split {N p q : ℕ} (hq : 1 ≤ q) :
    ∑ s ∈ range (q + 1), (s : ℝ) * overlapCoefficient N p q s =
      overlapCoefficient N p q 1 +
        ∑ s ∈ (range (q + 1)).filter (fun s => 2 ≤ s), (s : ℝ) * overlapCoefficient N p q s := by
  rw [Finset.sum_filter]
  have h : ∀ s ∈ range (q + 1), (s : ℝ) * overlapCoefficient N p q s =
      (if s = 1 then overlapCoefficient N p q 1 else 0) +
        (if 2 ≤ s then (s : ℝ) * overlapCoefficient N p q s else 0) := by
    intro s _
    rcases Nat.lt_or_ge s 2 with h | h
    · interval_cases s <;> simp
    · have : s ≠ 1 := by omega
      simp [this, h]
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_ite_eq']
  have : 1 ∈ range (q + 1) := by simp [Finset.mem_range]; omega
  rw [if_pos this]

/-- **Fixed-order limit coefficient.** `N c_{N,p,q,1} → pq`. -/
theorem tendsto_N_c_one (p q : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) * overlapCoefficient N p q 1) atTop (𝓝 ((p : ℝ) * q)) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [overlapCoefficient]
  have hT := tendsto_N_tail p q
  have hW : Tendsto (fun N : ℕ => (N : ℝ) *
      ∑ s ∈ (range (q + 1)).filter (fun s => 2 ≤ s), (s : ℝ) * overlapCoefficient N p q s)
      atTop (𝓝 0) := by
    have hT' := hT.const_mul (p : ℝ)
    rw [mul_zero] at hT'
    refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ hT'
    · exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun s _ =>
        mul_nonneg (Nat.cast_nonneg _) (overlapCoefficient_nonneg N p q s))
    · refine Eventually.of_forall fun N => ?_
      calc (N : ℝ) * ∑ s ∈ (range (q + 1)).filter (fun s => 2 ≤ s), (s : ℝ) * overlapCoefficient N p q s
          ≤ (N : ℝ) * ((p : ℝ) * ∑ s ∈ (range (q + 1)).filter (fun s => 2 ≤ s),
              overlapCoefficient N p q s) := by
            refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
            rw [Finset.mul_sum]
            refine Finset.sum_le_sum fun s hs => ?_
            by_cases hsp : s ≤ p
            · have : (s : ℝ) ≤ p := by exact_mod_cast hsp
              exact mul_le_mul_of_nonneg_right this (overlapCoefficient_nonneg N p q s)
            · rw [overlapCoefficient_eq_zero_of_gt (by omega)]; simp
        _ = (p : ℝ) * ((N : ℝ) * ∑ s ∈ (range (q + 1)).filter (fun s => 2 ≤ s),
              overlapCoefficient N p q s) := by ring
  have hlim : Tendsto (fun N : ℕ => (p : ℝ) * q - (N : ℝ) *
      ∑ s ∈ (range (q + 1)).filter (fun s => 2 ≤ s), (s : ℝ) * overlapCoefficient N p q s)
      atTop (𝓝 ((p : ℝ) * q)) := by
    simpa using (tendsto_const_nhds (x := (p : ℝ) * q)).sub hW
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (max (max p q) 1)] with N hN
  have hp : p ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hq' : q ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have h1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hm := first_moment hp hq' h1
  rw [first_moment_split hq] at hm
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have : overlapCoefficient N p q 1 = (p * q : ℝ) / N -
      ∑ s ∈ (range (q + 1)).filter (fun s => 2 ≤ s), (s : ℝ) * overlapCoefficient N p q s := by
    linarith
  rw [this]
  field_simp

end QuantumNLS.OverlapMoments

#print axioms QuantumNLS.OverlapMoments.first_moment
#print axioms QuantumNLS.OverlapMoments.second_moment
#print axioms QuantumNLS.OverlapMoments.prob_intersect_le
#print axioms QuantumNLS.OverlapMoments.tail_two_le
#print axioms QuantumNLS.OverlapMoments.tendsto_N_tail
#print axioms QuantumNLS.OverlapMoments.tendsto_N_c_one
