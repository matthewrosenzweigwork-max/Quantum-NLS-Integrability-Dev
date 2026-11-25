import Mathlib
import NlsGge.Atomic.KSTPath
open scoped BigOperators
set_option autoImplicit false
namespace NlsGge.Atomic.KST

open NlsGge.Atomic.KSTPath

structure SlowWeight (w : ℤ → ℝ) (Cw : ℝ) : Prop where
  one_le : ∀ n, 1 ≤ w n
  even : ∀ n, w (-n) = w n
  radial_mono : ∀ a b, a.natAbs ≤ b.natAbs → w a ≤ w b
  doubling : ∀ n, w (2 * n) ≤ Cw * w n

theorem slowWeight_Cw_one_le {w : ℤ → ℝ} {Cw : ℝ} (hw : SlowWeight w Cw) :
    1 ≤ Cw := by
  have hw0 := hw.doubling 0
  have hw0pos : 0 < w 0 := lt_of_lt_of_le zero_lt_one (hw.one_le 0)
  have hdiv : 1 ≤ (Cw * w 0) / w 0 := (le_div_iff₀ hw0pos).2 (by simpa using hw0)
  have hw0ne : w 0 ≠ 0 := ne_of_gt hw0pos
  rw [mul_div_cancel_right₀ Cw hw0ne] at hdiv
  exact hdiv

theorem slowWeight_add_bound {w : ℤ → ℝ} {Cw : ℝ}
    (hw : SlowWeight w Cw) (a b : ℤ) :
    w (a + b) ≤ Cw * w a * w b := by
  by_cases hab : a.natAbs ≤ b.natAbs
  · have hnat : (a + b).natAbs ≤ 2 * b.natAbs := by
      calc
        (a + b).natAbs ≤ a.natAbs + b.natAbs := Int.natAbs_add_le a b
        _ ≤ 2 * b.natAbs := by omega
    have harg : (a + b).natAbs ≤ (2 * b).natAbs := by
      simpa [Int.natAbs_mul] using hnat
    calc
      w (a + b) ≤ w (2 * b) := hw.radial_mono _ _ harg
      _ ≤ Cw * w b := hw.doubling b
      _ ≤ Cw * (w a * w b) := by
        apply mul_le_mul_of_nonneg_left
        · nlinarith [mul_nonneg (sub_nonneg.mpr (hw.one_le a)) (le_trans (by norm_num) (hw.one_le b))]
        · linarith [slowWeight_Cw_one_le hw]
      _ = Cw * w a * w b := by ring
  · have hba : b.natAbs ≤ a.natAbs := by omega
    have hnat : (a + b).natAbs ≤ 2 * a.natAbs := by
      calc
        (a + b).natAbs ≤ a.natAbs + b.natAbs := Int.natAbs_add_le a b
        _ ≤ 2 * a.natAbs := by omega
    have harg : (a + b).natAbs ≤ (2 * a).natAbs := by
      simpa [Int.natAbs_mul] using hnat
    calc
      w (a + b) ≤ w (2 * a) := hw.radial_mono _ _ harg
      _ ≤ Cw * w a := hw.doubling a
      _ ≤ Cw * (w a * w b) := by
        apply mul_le_mul_of_nonneg_left
        · nlinarith [mul_nonneg (sub_nonneg.mpr (hw.one_le b)) (le_trans (by norm_num) (hw.one_le a))]
        · linarith [slowWeight_Cw_one_le hw]
      _ = Cw * w a * w b := by ring

theorem slowWeight_scaled_submultiplicative {w : ℤ → ℝ} {Cw : ℝ}
    (hw : SlowWeight w Cw) (a b : ℤ) :
    Cw * w (a + b) ≤ (Cw * w a) * (Cw * w b) := by
  have hnonneg : 0 ≤ Cw := le_trans (by norm_num) (slowWeight_Cw_one_le hw)
  calc
    Cw * w (a + b) ≤ Cw * (Cw * w a * w b) :=
      mul_le_mul_of_nonneg_left (slowWeight_add_bound hw a b) hnonneg
    _ = (Cw * w a) * (Cw * w b) := by ring

theorem slowWeight_sum_finset {w : ℤ → ℝ} {Cw : ℝ} {α : Type*}
    [DecidableEq α] (hw : SlowWeight w Cw) (s : Finset α) (g : α → ℤ)
    (hne : s.Nonempty) :
    w (∑ i ∈ s, g i) ≤ Cw ^ (s.card - 1) * ∏ i ∈ s, w (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hne
  | @insert a s ha ih =>
      by_cases hs : s.Nonempty
      · have hih := ih hs
        have hadd := slowWeight_add_bound hw (g a) (∑ i ∈ s, g i)
        have hC : 0 ≤ Cw := le_trans (by norm_num) (slowWeight_Cw_one_le hw)
        have hwa : 0 ≤ w (g a) := le_trans (by norm_num) (hw.one_le (g a))
        have hcard_pos : 0 < s.card := Finset.card_pos.mpr hs
        rw [Finset.sum_insert ha, Finset.prod_insert ha]
        have hcard : (insert a s).card = s.card + 1 := by simp [ha]
        rw [hcard]
        calc
          w (g a + ∑ i ∈ s, g i) ≤
              Cw * w (g a) * (Cw ^ (s.card - 1) * ∏ i ∈ s, w (g i)) := by
            calc
              _ ≤ Cw * w (g a) * w (∑ i ∈ s, g i) := hadd
              _ ≤ _ := mul_le_mul_of_nonneg_left hih (mul_nonneg hC hwa)
          _ = Cw ^ s.card * (w (g a) * ∏ i ∈ s, w (g i)) := by
            have hpow : Cw * Cw ^ (s.card - 1) = Cw ^ s.card := by
              rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega)]
            calc
              _ = (Cw * Cw ^ (s.card - 1)) * (w (g a) * ∏ i ∈ s, w (g i)) := by ring
              _ = _ := by rw [hpow]
      · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst s
        simp

/-- An alternating signed sum of an odd number of path terms has the exact
`Cw^(2k)` product bound from KST (59). -/
theorem slowWeight_alternating_product {w : ℤ → ℝ} {Cw : ℝ}
    (hw : SlowWeight w Cw) {k : ℕ} {n : ℤ}
    (a : Fin (2 * k + 1) → ℤ)
    (hsum : (∑ j : Fin (2 * k + 1), (-1 : ℤ) ^ j.val * a j) = 2 * n) :
    w (2 * n) ≤ Cw ^ (2 * k) * ∏ j : Fin (2 * k + 1), w (a j) := by
  let g : Fin (2 * k + 1) → ℤ := fun j => (-1 : ℤ) ^ j.val * a j
  have hbound := slowWeight_sum_finset hw Finset.univ g Finset.univ_nonempty
  have hprod : (∏ j : Fin (2 * k + 1), w (g j)) =
      ∏ j : Fin (2 * k + 1), w (a j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rcases neg_one_pow_eq_or ℤ j.val with hpos | hneg
    · simp [g, hpos]
    · simp [g, hneg, hw.even]
  simpa [g, hsum, hprod] using hbound

private def pathVertices {k : ℕ} (hk : 0 < k) (n : ℤ) (ℓ : Path k) :
    Fin (2 * k + 2) → ℤ := fun i =>
  if i.val = 0 then n
  else if i.val = 2 * k + 1 then n
  else ℓ (vertexIndex hk (i.val - 1))

private theorem altEdgeSum (m : ℕ) (v : Fin (m + 1) → ℤ) :
    (∑ j : Fin m, (-1 : ℤ) ^ j.val *
      (v ⟨j.val, by omega⟩ + v ⟨j.val + 1, by omega⟩)) =
      v ⟨0, by omega⟩ + (-1 : ℤ) ^ (m + 1) * v ⟨m, by omega⟩ := by
  induction m with
  | zero => simp
  | succ m ih =>
      let v' : Fin (m + 1) → ℤ := fun i => v ⟨i.val + 1, by omega⟩
      rw [Fin.sum_univ_succ]
      have htail :
          (∑ i : Fin m, (-1 : ℤ) ^ i.succ.val *
            (v ⟨i.succ.val, by omega⟩ + v ⟨i.succ.val + 1, by omega⟩)) =
          - (∑ i : Fin m, (-1 : ℤ) ^ i.val *
            (v' ⟨i.val, by omega⟩ + v' ⟨i.val + 1, by omega⟩)) := by
        calc
          _ = ∑ i : Fin m, -((-1 : ℤ) ^ i.val *
              (v' ⟨i.val, by omega⟩ + v' ⟨i.val + 1, by omega⟩)) := by
                apply Finset.sum_congr rfl
                intro i hi
                simp [v', Fin.val_succ, pow_succ]
          _ = _ := by simp
      rw [htail, ih]
      simp [v']
      ring

/-- The alternating source path arguments telescope to the two external labels.
This is the signed identity in KST equation (59), proved for the actual lattice path. -/
theorem pathArgument_alt_sum {k : ℕ} (hk : 0 < k) (n : ℤ) (ℓ : Path k) :
    (∑ j : Fin (2 * k + 1), (-1 : ℤ) ^ j.val * pathArgument hk n ℓ j) = 2 * n := by
  let v := pathVertices hk n ℓ
  have hedge (j : Fin (2 * k + 1)) :
      pathArgument hk n ℓ j =
        v ⟨j.val, by omega⟩ + v ⟨j.val + 1, by omega⟩ := by
    have hjle : j.val ≤ 2 * k := by omega
    by_cases hj0 : j.val = 0
    · have hj : j = ⟨0, by omega⟩ := Fin.ext hj0
      rw [hj]
      rw [pathArgument_zero]
      have hk0 : k ≠ 0 := by omega
      simp [v, pathVertices, hk0]
      rw [vertexIndex_eq_mk hk (by omega)]
    · by_cases hjlast : j.val = 2 * k
      · have hj : j = ⟨2 * k, by omega⟩ := Fin.ext hjlast
        rw [hj]
        rw [pathArgument_last]
        simp [v, pathVertices, show k ≠ 0 by omega]
        rw [vertexIndex_eq_mk hk (by omega)]
      · have hjpos : 0 < j.val := by omega
        have hjlt : j.val < 2 * k := by omega
        have hjneEnd : j.val ≠ 2 * k + 1 := by omega
        have hjleft : j.val - 1 < 2 * k := by omega
        rw [pathArgument_interior hk n ℓ j hjpos hjlt]
        simp [v, pathVertices, hj0, hjlast, hjneEnd]
        rw [vertexIndex_eq_mk hk hjleft, vertexIndex_eq_mk hk hjlt]
  calc
    _ = ∑ j : Fin (2 * k + 1), (-1 : ℤ) ^ j.val *
        (v ⟨j.val, by omega⟩ + v ⟨j.val + 1, by omega⟩) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [← hedge j]
    _ = v ⟨0, by omega⟩ + (-1 : ℤ) ^ (2 * k + 2) * v ⟨2 * k + 1, by omega⟩ := by
          simpa [Nat.mul_add, Nat.add_assoc] using
            (altEdgeSum (2 * k + 1) v)
    _ = 2 * n := by
          have hsign : (-1 : ℤ) ^ (2 * k + 2) = 1 := by
            rw [show 2 * k + 2 = 2 * (k + 1) by omega, pow_mul]
            norm_num
          rw [hsign]
          simp [v, pathVertices, show 2 * k + 1 ≠ 0 by omega]
          ring

/-- KST's path-product estimate: the exact path sum is first established, then
the even weight is applied to its alternating signs and submultiplicativity is
iterated over all `2k+1` source arguments. -/
theorem slowWeight_path_product_le {w : ℤ → ℝ} {Cw : ℝ}
    (hw : SlowWeight w Cw) {k : ℕ} (hk : 0 < k) (n : ℤ) (ℓ : Path k) :
    w (2 * n) ≤ Cw ^ (2 * k) * ∏ j : Fin (2 * k + 1), w (pathArgument hk n ℓ j) := by
  apply slowWeight_alternating_product hw
  have hsum := pathArgument_alt_sum hk n ℓ
  simpa using hsum

end NlsGge.Atomic.KST
