import Mathlib
import QuantumNLS.AdjacentResponse
import QuantumNLS.BetheLabels

/-!
# REF88QuantumArrays: integer roundings and the arrays `k_N + r (e_a - e_b)` (R-EF8C2837, item (iii), assembly support)

Source: `source-text/chapters/global/physical_cubic.tex` (sha256 `64ec3e02...`), printed lines 232 and 264-285:
"Round `x` to integer occupations totaling `N` in the same finite set" and "Along a compact line `x + s(e_a - e_b)` in the
positive simplex, write `d = e_a - e_b`, choose integer arrays `k_N` with `k_N/N -> x`, and use the arrays `k_N + r d` for
consecutive integers `r` whose fractions lie on the chosen segment.  The other counts stay fixed and positivity holds
for large `N`."

* `l1_of_coord`: coordinatewise convergence on a finite support gives `l^1` convergence.
* `exists_rounding`: for a probability vector `x` on a finite set `F` there are arrays `k_n in M_{n+1}` supported in `F` with
  `k_n/(n+1) -> x` coordinatewise and in `l^1` (floors, the remainder on one site).
* `lineArr m a b r`: the array `m + r (e_a - e_b)` (when it is an array), with the coordinate formula `lineArr_apply`, the
  support statement `lineArr_support`, and the consecutive-step identity `lineArr_transfer`:
  `lineArr m a b r = transfer (lineArr m a b (r-1)) _ a` (the printed telescoping step `Q_2(k+(r+1)d)-Q_2(k+rd)` is a
  transfer of one `b` label to `a`).
* `line_l1`: for `r_n/(n+1) -> s` with `x_a + s > 0`, `x_b - s > 0` the arrays `lineArr (k_n) a b (r_n)` have fractions
  converging in `l^1` to `x + s (e_a - e_b)`, and eventually `r_n` lies in the range where `lineArr` is the genuine array.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open Filter Topology
open scoped BigOperators

namespace QuantumNLS.REF88QuantumArrays

open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.AdjacentResponse (transfer transfer_apply)

theorem l1_of_coord (F : Finset ℤ) (c : ℕ → ℤ → ℝ) (x : ℤ → ℝ) (hc : ∀ n k, k ∉ F → c n k = 0)
    (hx : ∀ k, k ∉ F → x k = 0) (h : ∀ k ∈ F, Tendsto (fun n => c n k) atTop (𝓝 (x k))) :
    Tendsto (fun n => ∑' k, |c n k - x k|) atTop (𝓝 0) := by
  have e : ∀ n, ∑' k, |c n k - x k| = ∑ k ∈ F, |c n k - x k| := fun n =>
    tsum_eq_sum (fun k hk => by simp [hc n k hk, hx k hk])
  simp_rw [e]
  have := tendsto_finset_sum F (fun k hk => ((h k hk).sub_const (x k)).abs)
  simpa using this

theorem tendsto_natFloor_div (y : ℝ) (hy : 0 ≤ y) :
    Tendsto (fun n : ℕ => ((⌊((n : ℝ) + 1) * y⌋₊ : ℕ) : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 y) := by
  have h1 : Tendsto (fun n : ℕ => y - 1 / ((n : ℝ) + 1)) atTop (𝓝 y) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) (a := y)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds (fun n => ?_) (fun n => ?_)
  · have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [le_div_iff₀ hN]
    have := Nat.lt_floor_add_one (((n : ℝ) + 1) * y)
    calc (y - 1 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) = ((n : ℝ) + 1) * y - 1 := by field_simp
      _ ≤ _ := by linarith
  · have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_le_iff₀ hN]
    calc ((⌊((n : ℝ) + 1) * y⌋₊ : ℕ) : ℝ) ≤ ((n : ℝ) + 1) * y := Nat.floor_le (by positivity)
      _ = y * ((n : ℝ) + 1) := by ring

/-! ### The rounding -/

def roundF (F : Finset ℤ) (j0 : ℤ) (x : ℤ → ℝ) (N : ℕ) (k : ℤ) : ℕ :=
  if k ∈ F then (if k = j0 then N - ∑ j ∈ F.erase j0, ⌊(N : ℝ) * x j⌋₊ else ⌊(N : ℝ) * x k⌋₊) else 0

def roundFin (F : Finset ℤ) (j0 : ℤ) (x : ℤ → ℝ) (N : ℕ) : ℤ →₀ ℕ :=
  Finsupp.onFinset F (roundF F j0 x N) (fun k hk => by
    by_contra h
    simp [roundF, h] at hk)

theorem sum_floor_le {F : Finset ℤ} {j0 : ℤ} (hj0 : j0 ∈ F) {x : ℤ → ℝ} (hx0 : ∀ k, 0 ≤ x k)
    (hx1 : ∑ k ∈ F, x k = 1) (N : ℕ) : ∑ j ∈ F.erase j0, ⌊(N : ℝ) * x j⌋₊ ≤ N := by
  have h1 : ((∑ j ∈ F.erase j0, ⌊(N : ℝ) * x j⌋₊ : ℕ) : ℝ) ≤ N := by
    push_cast
    calc ∑ j ∈ F.erase j0, (⌊(N : ℝ) * x j⌋₊ : ℝ) ≤ ∑ j ∈ F.erase j0, (N : ℝ) * x j :=
          Finset.sum_le_sum fun j _ => Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (hx0 j))
      _ = (N : ℝ) * ∑ j ∈ F.erase j0, x j := (Finset.mul_sum _ _ _).symm
      _ ≤ (N : ℝ) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          have := Finset.add_sum_erase F x hj0
          linarith [hx0 j0]
      _ = N := mul_one _
  exact_mod_cast h1

theorem roundFin_sum {F : Finset ℤ} {j0 : ℤ} (hj0 : j0 ∈ F) {x : ℤ → ℝ} (hx0 : ∀ k, 0 ≤ x k)
    (hx1 : ∑ k ∈ F, x k = 1) (N : ℕ) : (roundFin F j0 x N).sum (fun _ k => k) = N := by
  unfold roundFin
  rw [Finsupp.onFinset_sum _ (fun _ => rfl), ← Finset.add_sum_erase F _ hj0]
  have h2 : ∑ k ∈ F.erase j0, roundF F j0 x N k = ∑ j ∈ F.erase j0, ⌊(N : ℝ) * x j⌋₊ :=
    Finset.sum_congr rfl fun k hk => by
      have hk' := Finset.mem_erase.1 hk
      simp [roundF, hk'.2, hk'.1]
  rw [h2]
  have h3 : roundF F j0 x N j0 = N - ∑ j ∈ F.erase j0, ⌊(N : ℝ) * x j⌋₊ := by simp [roundF, hj0]
  rw [h3]
  exact Nat.sub_add_cancel (sum_floor_le hj0 hx0 hx1 N)

theorem exists_rounding (F : Finset ℤ) (j0 : ℤ) (hj0 : j0 ∈ F) (x : ℤ → ℝ) (hx0 : ∀ k, 0 ≤ x k)
    (hxF : ∀ k, k ∉ F → x k = 0) (hx1 : ∑ k ∈ F, x k = 1) :
    ∃ k : ∀ n : ℕ, MArr (n + 1), (∀ n j, j ∉ F → (k n).1 j = 0) ∧
      (∀ j, Tendsto (fun n : ℕ => (((k n).1 j : ℕ) : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (x j))) ∧
      Tendsto (fun n : ℕ => ∑' j : ℤ, |(((k n).1 j : ℕ) : ℝ) / ((n : ℝ) + 1) - x j|) atTop (𝓝 0) := by
  have hcoord : ∀ j, Tendsto (fun n : ℕ => (((roundFin F j0 x (n + 1)) j : ℕ) : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 (x j)) := by
    intro j
    by_cases hjF : j ∈ F
    · by_cases hj : j = j0
      · subst hj
        have hsum : Tendsto (fun n : ℕ => ∑ i ∈ F.erase j, ((⌊((n : ℝ) + 1) * x i⌋₊ : ℕ) : ℝ) / ((n : ℝ) + 1))
            atTop (𝓝 (∑ i ∈ F.erase j, x i)) :=
          tendsto_finset_sum _ fun i _ => tendsto_natFloor_div (x i) (hx0 i)
        have hlim : Tendsto (fun n : ℕ => 1 - ∑ i ∈ F.erase j, ((⌊((n : ℝ) + 1) * x i⌋₊ : ℕ) : ℝ) / ((n : ℝ) + 1))
            atTop (𝓝 (1 - ∑ i ∈ F.erase j, x i)) := tendsto_const_nhds.sub hsum
        have hxj : x j = 1 - ∑ i ∈ F.erase j, x i := by
          have := Finset.add_sum_erase F x hjF
          linarith
        rw [hxj]
        refine hlim.congr fun n => ?_
        have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have hle := sum_floor_le hjF hx0 hx1 (n + 1)
        have e : roundFin F j (x) (n + 1) j = (n + 1) - ∑ i ∈ F.erase j, ⌊(((n + 1 : ℕ) : ℝ)) * x i⌋₊ := by
          simp [roundFin, Finsupp.onFinset_apply, roundF, hjF]
        rw [e, Nat.cast_sub hle]
        push_cast
        rw [← Finset.sum_div]
        field_simp
      · have e : ∀ n : ℕ, roundFin F j0 x (n + 1) j = ⌊((n : ℝ) + 1) * x j⌋₊ := by
          intro n
          simp [roundFin, Finsupp.onFinset_apply, roundF, hjF, hj]
        simp_rw [e]
        exact tendsto_natFloor_div (x j) (hx0 j)
    · have e : ∀ n : ℕ, roundFin F j0 x (n + 1) j = 0 := by
        intro n; simp [roundFin, Finsupp.onFinset_apply, roundF, hjF]
      simp_rw [e]
      simp [hxF j hjF]
  refine ⟨fun n => ⟨roundFin F j0 x (n + 1), roundFin_sum hj0 hx0 hx1 (n + 1)⟩, ?_, hcoord, ?_⟩
  · intro n j hj
    show roundFin F j0 x (n + 1) j = 0
    simp [roundFin, Finsupp.onFinset_apply, roundF, hj]
  · refine l1_of_coord F _ x (fun n k hk => ?_) hxF (fun j _ => hcoord j)
    simp [roundFin, Finsupp.onFinset_apply, roundF, hk]


/-! ### The arrays `m + r (e_a - e_b)` -/

def lineFun (m : ℤ →₀ ℕ) (a b r : ℤ) (k : ℤ) : ℕ :=
  if k = a then ((m a : ℤ) + r).toNat else if k = b then ((m b : ℤ) - r).toNat else m k

def lineFin (m : ℤ →₀ ℕ) (a b r : ℤ) : ℤ →₀ ℕ :=
  Finsupp.onFinset (insert a (insert b m.support)) (lineFun m a b r) (by
    intro k hk
    by_contra h
    simp only [Finset.mem_insert, Finsupp.mem_support_iff, not_or, not_not] at h
    simp [lineFun, h.1, h.2.1, h.2.2] at hk)

theorem lineFun_cast {m : ℤ →₀ ℕ} {a b r : ℤ} (hab : a ≠ b) (ha : 0 ≤ (m a : ℤ) + r)
    (hb : 0 ≤ (m b : ℤ) - r) (k : ℤ) :
    (lineFun m a b r k : ℤ) = m k + (if k = a then r else 0) - (if k = b then r else 0) := by
  unfold lineFun
  by_cases h1 : k = a
  · subst h1; simp [hab] <;> omega
  · by_cases h2 : k = b
    · subst h2; simp [h1] <;> omega
    · simp [h1, h2]

theorem lineFin_sum {m : ℤ →₀ ℕ} {a b r : ℤ} (hab : a ≠ b) (ha : 0 ≤ (m a : ℤ) + r)
    (hb : 0 ≤ (m b : ℤ) - r) :
    (lineFin m a b r).sum (fun _ k => k) = m.sum (fun _ k => k) := by
  classical
  set S : Finset ℤ := insert a (insert b m.support) with hS
  have h1 : (lineFin m a b r).sum (fun _ k => k) = ∑ k ∈ S, lineFun m a b r k := by
    unfold lineFin; rw [Finsupp.onFinset_sum _ (fun _ => rfl)]
  have h2 : m.sum (fun _ k => k) = ∑ k ∈ S, m k :=
    Finsupp.sum_of_support_subset m (fun k hk => by simp [hS, hk]) _ (fun _ _ => rfl)
  rw [h1, h2]
  have haS : a ∈ S := by simp [hS]
  have hbS : b ∈ S := by simp [hS]
  have key : ((∑ k ∈ S, lineFun m a b r k : ℕ) : ℤ) = ((∑ k ∈ S, m k : ℕ) : ℤ) := by
    push_cast
    rw [Finset.sum_congr rfl (fun k _ => lineFun_cast hab ha hb k)]
    simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', haS, hbS]
  exact_mod_cast key

def lineArr {N : ℕ} (m : MArr N) (a b r : ℤ) : MArr N :=
  if h : a ≠ b ∧ 0 ≤ (m.1 a : ℤ) + r ∧ 0 ≤ (m.1 b : ℤ) - r then
    ⟨lineFin m.1 a b r, (lineFin_sum h.1 h.2.1 h.2.2).trans m.2⟩ else m

theorem lineArr_eq_pos {N : ℕ} (m : MArr N) {a b r : ℤ}
    (h : a ≠ b ∧ 0 ≤ (m.1 a : ℤ) + r ∧ 0 ≤ (m.1 b : ℤ) - r) :
    lineArr m a b r = ⟨lineFin m.1 a b r, (lineFin_sum h.1 h.2.1 h.2.2).trans m.2⟩ := dif_pos h

theorem lineArr_eq_neg {N : ℕ} (m : MArr N) {a b r : ℤ}
    (h : ¬ (a ≠ b ∧ 0 ≤ (m.1 a : ℤ) + r ∧ 0 ≤ (m.1 b : ℤ) - r)) : lineArr m a b r = m := dif_neg h

theorem lineArr_apply {N : ℕ} (m : MArr N) {a b r : ℤ} (hab : a ≠ b) (ha : 0 ≤ (m.1 a : ℤ) + r)
    (hb : 0 ≤ (m.1 b : ℤ) - r) (k : ℤ) :
    (((lineArr m a b r).1 k : ℕ) : ℤ) = m.1 k + (if k = a then r else 0) - (if k = b then r else 0) := by
  rw [lineArr_eq_pos m ⟨hab, ha, hb⟩]
  exact lineFun_cast hab ha hb k

theorem lineArr_apply_real {N : ℕ} (m : MArr N) {a b r : ℤ} (hab : a ≠ b) (ha : 0 ≤ (m.1 a : ℤ) + r)
    (hb : 0 ≤ (m.1 b : ℤ) - r) (k : ℤ) :
    (((lineArr m a b r).1 k : ℕ) : ℝ) =
      (m.1 k : ℝ) + (if k = a then (r : ℝ) else 0) - (if k = b then (r : ℝ) else 0) := by
  have e := lineArr_apply m hab ha hb k
  exact_mod_cast e

theorem lineArr_support {N : ℕ} (m : MArr N) (F : Finset ℤ) (hm : ∀ k, k ∉ F → m.1 k = 0)
    (a b r : ℤ) (ha : a ∈ F) (hb : b ∈ F) : ∀ k, k ∉ F → (lineArr m a b r).1 k = 0 := by
  intro k hk
  have hka : k ≠ a := fun e => hk (e ▸ ha)
  have hkb : k ≠ b := fun e => hk (e ▸ hb)
  by_cases h : a ≠ b ∧ 0 ≤ (m.1 a : ℤ) + r ∧ 0 ≤ (m.1 b : ℤ) - r
  · rw [lineArr_eq_pos m h]
    show lineFun m.1 a b r k = 0
    simp [lineFun, hka, hkb, hm k hk]
  · rw [lineArr_eq_neg m h]
    exact hm k hk

theorem lineArr_transfer {N : ℕ} (m : MArr N) {a b : ℤ} (hab : a ≠ b) {r : ℤ}
    (h1 : 0 ≤ (m.1 a : ℤ) + r - 1) (h2 : 0 ≤ (m.1 b : ℤ) - r)
    (hb : 1 ≤ (lineArr m a b (r - 1)).1 b) :
    lineArr m a b r = transfer (lineArr m a b (r - 1)) hb a := by
  have hr : 0 ≤ (m.1 a : ℤ) + r := by omega
  have hr1 : 0 ≤ (m.1 b : ℤ) - (r - 1) := by omega
  apply Subtype.ext
  apply Finsupp.ext
  intro k
  have e1 := lineArr_apply m hab hr h2 k
  have e2 := lineArr_apply m hab (r := r - 1) (by omega) hr1 k
  have e3 := transfer_apply (lineArr m a b (r - 1)) hb a k
  apply Nat.cast_injective (R := ℤ)
  show (((lineArr m a b r).1 k : ℕ) : ℤ) = (((transfer (lineArr m a b (r - 1)) hb a).1 k : ℕ) : ℤ)
  rw [e1, e3, e2]
  split_ifs <;> omega

theorem eventually_range (k : ∀ n : ℕ, MArr (n + 1)) (x : ℤ → ℝ)
    (hkx : ∀ j, Tendsto (fun n : ℕ => (((k n).1 j : ℕ) : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (x j)))
    {a b : ℤ} (r : ℕ → ℤ) {s : ℝ} (hr : Tendsto (fun n : ℕ => (r n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 s))
    (hxa : 0 < x a + s) (hxb : 0 < x b - s) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ ((k n).1 a : ℤ) + r n - 1 ∧ 0 ≤ ((k n).1 b : ℤ) - r n := by
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : Tendsto (fun n : ℕ => ((((k n).1 a : ℕ) : ℝ) / ((n : ℝ) + 1)) + (r n : ℝ) / ((n : ℝ) + 1) -
      1 / ((n : ℝ) + 1)) atTop (𝓝 (x a + s - 0)) := ((hkx a).add hr).sub hinv
  have h2 : Tendsto (fun n : ℕ => ((((k n).1 b : ℕ) : ℝ) / ((n : ℝ) + 1)) - (r n : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 (x b - s)) := (hkx b).sub hr
  filter_upwards [h1.eventually (lt_mem_nhds (show (0 : ℝ) < x a + s - 0 by linarith)), h2.eventually (lt_mem_nhds hxb)] with n hn1 hn2
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  constructor
  · have : (0 : ℝ) < (((k n).1 a : ℕ) : ℝ) + r n - 1 := by
      have := mul_pos hn1 hN
      have e : ((((k n).1 a : ℕ) : ℝ) / ((n : ℝ) + 1) + (r n : ℝ) / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1)) *
          ((n : ℝ) + 1) = (((k n).1 a : ℕ) : ℝ) + r n - 1 := by field_simp
      linarith
    have : (0 : ℤ) < (((k n).1 a : ℕ) : ℤ) + r n - 1 := by exact_mod_cast this
    omega
  · have : (0 : ℝ) < (((k n).1 b : ℕ) : ℝ) - r n := by
      have := mul_pos hn2 hN
      have e : ((((k n).1 b : ℕ) : ℝ) / ((n : ℝ) + 1) - (r n : ℝ) / ((n : ℝ) + 1)) * ((n : ℝ) + 1) =
          (((k n).1 b : ℕ) : ℝ) - r n := by field_simp
      linarith
    have : (0 : ℤ) < (((k n).1 b : ℕ) : ℤ) - r n := by exact_mod_cast this
    omega

theorem line_l1 (F : Finset ℤ) (k : ∀ n : ℕ, MArr (n + 1)) (hk : ∀ n j, j ∉ F → (k n).1 j = 0)
    (x : ℤ → ℝ) (hxF : ∀ j, j ∉ F → x j = 0)
    (hkx : ∀ j, Tendsto (fun n : ℕ => (((k n).1 j : ℕ) : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (x j)))
    {a b : ℤ} (haF : a ∈ F) (hbF : b ∈ F) (hab : a ≠ b)
    (r : ℕ → ℤ) {s : ℝ} (hr : Tendsto (fun n : ℕ => (r n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 s))
    (hrange : ∀ᶠ n : ℕ in atTop, 0 ≤ ((k n).1 a : ℤ) + r n ∧ 0 ≤ ((k n).1 b : ℤ) - r n) :
    Tendsto (fun n : ℕ => ∑' j : ℤ, |(((lineArr (k n) a b (r n)).1 j : ℕ) : ℝ) / ((n : ℝ) + 1) -
        (x j + s * ((if j = a then 1 else 0) - (if j = b then 1 else 0)))|) atTop (𝓝 0) := by
  refine l1_of_coord F _ _ (fun n j hj => ?_) ?_ (fun j _ => ?_)
  · simp [lineArr_support (k n) F (hk n) a b (r n) haF hbF j hj]
  · intro j hj
    have hja : j ≠ a := fun e => hj (e ▸ haF)
    have hjb : j ≠ b := fun e => hj (e ▸ hbF)
    simp [hxF j hj, hja, hjb]
  · have hra : Tendsto (fun n : ℕ => (if j = a then (r n : ℝ) else 0) / ((n : ℝ) + 1)) atTop
        (𝓝 (if j = a then s else 0)) := by
      split_ifs
      · exact hr
      · simp
    have hrb : Tendsto (fun n : ℕ => (if j = b then (r n : ℝ) else 0) / ((n : ℝ) + 1)) atTop
        (𝓝 (if j = b then s else 0)) := by
      split_ifs
      · exact hr
      · simp
    have hlim := ((hkx j).add hra).sub hrb
    have hv : x j + (if j = a then s else 0) - (if j = b then s else 0) =
        x j + s * ((if j = a then 1 else 0) - (if j = b then 1 else 0)) := by
      split_ifs <;> ring
    rw [hv] at hlim
    refine hlim.congr' ?_
    filter_upwards [hrange] with n hn
    rw [lineArr_apply_real (k n) hab hn.1 hn.2 j]
    split_ifs <;> ring

end QuantumNLS.REF88QuantumArrays

#print axioms QuantumNLS.REF88QuantumArrays.l1_of_coord
#print axioms QuantumNLS.REF88QuantumArrays.exists_rounding
#print axioms QuantumNLS.REF88QuantumArrays.lineArr_transfer
#print axioms QuantumNLS.REF88QuantumArrays.eventually_range
#print axioms QuantumNLS.REF88QuantumArrays.line_l1
