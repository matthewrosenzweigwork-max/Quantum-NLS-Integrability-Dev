import QuantumNLS.BetheConvexity
import Mathlib

/-!
# CC:F01:ground (R-39906D9E): all-zero Bose ground roots

Source: `source-text/chapters/root_response/F01.tex`, lemma `CC:F01:ground` (line 101), with
the Bose equation `CC:F01:bose` (line 9) and the smooth map `CC:F01:smooth` (line 12).
Source conventions: indices are one-based and increasing, `c, L > 0`, `s_1 < ... < s_M`.
Lean indices are zero-based (`Fin M`) and increasing; `Fin.rev` is `i ↦ M+1-i`.

Formal content.
* `boseSystem_iff_solves` (identification): for strictly increasing `q` and `c > 0`, the F01
  left-hand side satisfies `boseLHS L c q i = logMap L c q i - π (2 i - M + 1)`. Hence the F01
  Bose system with labels `n` is exactly the accepted `BetheAdmission.Solves L c n q`, whose label
  convention is `quantumNumbers n i = n_i + i - (M-1)/2` (zero-based `i`). For zero labels the
  right-hand side is `π (2i - M - 1)` in one-based indexing, the printed `T_i(q) = π(2i-M-1)`.
* `solution_negRev_eq` (symmetry): uniqueness of `logMap = b` (accepted `BetheConvexity.solutions_eq`,
  strict convexity of the Yang–Yang functional, imported read-only) applied to `x` and `-rev x`.
* `mom_catalan_bound` (moments): `∑ᵢ sᵢ^{2n} ≤ M C_n (cM/L)^n` with `C_n` the Catalan numbers.
* `ground_root_bound` (the lemma): `s_i = -s_{M+1-i}` and `max_i |s_i| ≤ 2 √(cM/L)`.

Only the Mathlib library and the frozen `QuantumNLS.BetheConvexity` module are used.
-/

noncomputable section
open scoped BigOperators
open Finset

namespace QuantumNLS.GroundRootBound

open QuantumNLS.BetheAdmission QuantumNLS.BetheConvexity

/-- F01 `CC:F01:bose` left-hand side, zero-based indices, sum over `j ≠ i`. -/
def boseLHS {M : ℕ} (L c : ℝ) (q : Fin M → ℝ) (i : Fin M) : ℝ :=
  L * q i - 2 * ∑ j ∈ Finset.univ.erase i, Real.arctan (c / (q i - q j))

/-- F01 `CC:F01:bose` as a system with integer Bose labels `n`. -/
def BoseSystem {M : ℕ} (L c : ℝ) (n : Fin M → ℤ) (q : Fin M → ℝ) : Prop :=
  ∀ i, boseLHS L c q i = 2 * Real.pi * (n i : ℝ)

/-- The reflection `x ↦ -rev x` used for the symmetry. -/
def negRev {M : ℕ} (x : Fin M → ℝ) : Fin M → ℝ := fun i => -x (Fin.rev i)

/-- Power sums `∑ᵢ sᵢ^r`. -/
def momentSum {M : ℕ} (s : Fin M → ℝ) (r : ℕ) : ℝ := ∑ i, s i ^ r

/-- Pair term `arctan (c / (sᵢ - sⱼ))` of the Bose equations. -/
def tArc {M : ℕ} (c : ℝ) (s : Fin M → ℝ) (i j : Fin M) : ℝ :=
  Real.arctan (c / (s i - s j))

/-- Kernel `∑_{r<2n+1} sᵢ^r sⱼ^{2n-r}`, the divided difference of `x^{2n+1}`. -/
def gsum {M : ℕ} (s : Fin M → ℝ) (n : ℕ) (i j : Fin M) : ℝ :=
  ∑ r ∈ Finset.range (2 * n + 1), s i ^ r * s j ^ (2 * n - r)

/-! ## 1. Identification of CC:F01:bose with the accepted Bethe map -/

/-- Inversion of arctan for `c > 0`: `arctan(c/d) = sgn(d) π/2 - arctan(d/c)`. -/
theorem arctan_div_eq {c d : ℝ} (hc : 0 < c) (hd : d ≠ 0) :
    Real.arctan (c / d) =
      (if 0 < d then Real.pi / 2 else -(Real.pi / 2)) - Real.arctan (d / c) := by
  rw [show c / d = (d / c)⁻¹ from (inv_div d c).symm]
  rcases lt_or_gt_of_ne hd with h | h
  · have hdc : d / c < 0 := div_neg_of_neg_of_pos h hc
    rw [Real.arctan_inv_of_neg hdc]
    simp [not_lt.mpr h.le]
  · have hdc : 0 < d / c := div_pos h hc
    rw [Real.arctan_inv_of_pos hdc]
    simp [h]

/-- Counting identity: for strictly increasing `q`, the signs of `qᵢ - qⱼ` over `j ≠ i`
sum to `2i - M + 1` (zero-based `i`). -/
theorem sum_sign_erase {M : ℕ} {q : Fin M → ℝ} (hq : StrictMono q) (i : Fin M) :
    ∑ j ∈ Finset.univ.erase i, (if 0 < q i - q j then (1 : ℝ) else -1)
      = 2 * (i.val : ℝ) - (M : ℝ) + 1 := by
  have h1 : ∀ j ∈ Finset.univ.erase i, (if 0 < q i - q j then (1 : ℝ) else -1) =
      (if j < i then (1 : ℝ) else 0) - (if i < j then (1 : ℝ) else 0) := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    rcases lt_or_gt_of_ne hji with h | h
    · have h' : q j < q i := hq h
      have hp : 0 < q i - q j := by linarith
      have hnlt : ¬ i < j := not_lt.mpr h.le
      simp [hp, h, hnlt]
    · have h' : q i < q j := hq h
      have hn : ¬ (0 < q i - q j) := by
        intro hh
        linarith
      have hnl : ¬ j < i := not_lt.mpr h.le
      simp [hn, hnl, h]
  have hA : ∑ j : Fin M, (if j < i then (1 : ℝ) else 0) = (i.val : ℝ) := by
    rw [Finset.sum_boole]
    have hset : (Finset.univ.filter fun j : Fin M => j < i) = Finset.Iio i := by
      ext j; simp
    rw [hset, Fin.card_Iio]
  have hB : ∑ j : Fin M, (if i < j then (1 : ℝ) else 0) = (M : ℝ) - 1 - (i.val : ℝ) := by
    rw [Finset.sum_boole]
    have hset : (Finset.univ.filter fun j : Fin M => i < j) = Finset.Ioi i := by
      ext j; simp
    rw [hset, Fin.card_Ioi]
    have hi := i.isLt
    have h1 : i.val ≤ M - 1 := by omega
    have h2 : 1 ≤ M := by omega
    rw [Nat.cast_sub h1, Nat.cast_sub h2]
    simp
  rw [Finset.sum_congr rfl h1, Finset.sum_erase_eq_sub (Finset.mem_univ i),
    Finset.sum_sub_distrib, hA, hB]
  have hdiag : ((if i < i then (1 : ℝ) else 0) - (if i < i then (1 : ℝ) else 0)) = 0 :=
    sub_self _
  rw [hdiag]
  ring

/-- For `c > 0` and strictly increasing `q`, the F01 left-hand side is the smooth Bethe map
`logMap` shifted by the printed term `π (2i - M + 1)`. -/
theorem boseLHS_eq_logMap {M : ℕ} {L c : ℝ} (hc : 0 < c) {q : Fin M → ℝ}
    (hq : StrictMono q) (i : Fin M) :
    boseLHS L c q i = logMap L c q i - Real.pi * (2 * (i.val : ℝ) - (M : ℝ) + 1) := by
  have hs : ∀ j ∈ Finset.univ.erase i, Real.arctan (c / (q i - q j)) =
      (Real.pi / 2) * (if 0 < q i - q j then (1 : ℝ) else -1)
        - Real.arctan ((q i - q j) / c) := by
    intro j hj
    have hne : q i - q j ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (hq.injective.ne (Finset.ne_of_mem_erase hj)))
    rw [arctan_div_eq hc hne]
    split_ifs <;> ring
  have hsum : ∑ j ∈ Finset.univ.erase i, Real.arctan (c / (q i - q j)) =
      (Real.pi / 2) * (2 * (i.val : ℝ) - (M : ℝ) + 1)
        - ∑ j ∈ Finset.univ.erase i, Real.arctan ((q i - q j) / c) := by
    rw [Finset.sum_congr rfl hs, Finset.sum_sub_distrib, ← Finset.mul_sum,
      sum_sign_erase hq i]
  unfold boseLHS
  rw [hsum, logMap_erase]
  ring

/-- Identification: for strictly increasing `q` and `c > 0`, the F01 Bose system with integer
labels `n` is exactly the accepted system `Solves L c n q` (`logMap L c q i = 2π · quantumNumbers n i`).
The zero-label case is `n = 0`, where `quantumNumbers 0 i = i - (M-1)/2`. -/
theorem boseSystem_iff_solves {M : ℕ} {L c : ℝ} (hc : 0 < c) {q : Fin M → ℝ}
    (hq : StrictMono q) (n : Fin M → ℤ) :
    BoseSystem L c n q ↔ Solves L c n q := by
  unfold BoseSystem Solves
  refine forall_congr' fun i => ?_
  have hrhs : 2 * Real.pi * quantumNumbers n i =
      2 * Real.pi * (n i : ℝ) + Real.pi * (2 * (i.val : ℝ) - (M : ℝ) + 1) := by
    unfold quantumNumbers
    ring
  rw [boseLHS_eq_logMap hc hq i, hrhs]
  constructor <;> intro h <;> linarith

/-- The accepted label convention sends the zero labels to an antisymmetric label set:
`quantumNumbers 0 (M+1-i) = - quantumNumbers 0 i`. -/
theorem quantumNumbers_rev_zero {M : ℕ} (n : Fin M → ℤ) (hn : ∀ i, n i = 0) (i : Fin M) :
    quantumNumbers n (Fin.rev i) = -quantumNumbers n i := by
  have h1 : i.val + 1 ≤ M := i.isLt
  unfold quantumNumbers
  simp only [hn, Int.cast_zero, Fin.val_rev]
  rw [Nat.cast_sub h1]
  push_cast
  ring

/-- The smooth map is equivariant under `x ↦ -rev x`, with the sign flip `logMap ↦ -logMap ∘ rev`. -/
theorem logMap_negRev {M : ℕ} (L c : ℝ) (x : Fin M → ℝ) (i : Fin M) :
    logMap L c (negRev x) i = - logMap L c x (Fin.rev i) := by
  have hreidx : ∑ j, Real.arctan ((-x (Fin.rev i) - -x (Fin.rev j)) / c) =
      ∑ j, Real.arctan ((-x (Fin.rev i) - -x j) / c) :=
    Equiv.sum_comp Fin.revPerm (fun j => Real.arctan ((-x (Fin.rev i) - -x j) / c))
  have hneg : ∑ j, Real.arctan ((-x (Fin.rev i) - -x j) / c) =
      -∑ j, Real.arctan ((x (Fin.rev i) - x j) / c) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Real.arctan_neg]
    congr 1
    ring
  show L * (-x (Fin.rev i)) + 2 * ∑ j, Real.arctan ((-x (Fin.rev i) - -x (Fin.rev j)) / c) =
    -(L * x (Fin.rev i) + 2 * ∑ j, Real.arctan ((x (Fin.rev i) - x j) / c))
  rw [hreidx, hneg]
  ring

/-- Reflection symmetry from uniqueness: a zero-label solution is fixed by `x ↦ -rev x`.
Uses the accepted strict-convexity uniqueness `BetheConvexity.solutions_eq`. -/
theorem solution_negRev_eq {M : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin M → ℤ} (hn : ∀ i, n i = 0) {s : Fin M → ℝ} (hs : Solves L c n s) :
    negRev s = s := by
  have hs' : ∀ i, logMap L c s i = 2 * Real.pi * quantumNumbers n i := hs
  have h1 : logMap L c (negRev s) = fun i => 2 * Real.pi * quantumNumbers n i := by
    funext i
    rw [logMap_negRev, hs' (Fin.rev i), quantumNumbers_rev_zero n hn i]
    ring
  have h2 : logMap L c s = fun i => 2 * Real.pi * quantumNumbers n i := funext hs'
  exact solutions_eq hL hc h1 h2

/-! ## 2. Elementary inequalities -/

/-- `d · arctan(c/d) ≤ c` for every real `d` when `c ≥ 0`. -/
theorem mul_arctan_le {c d : ℝ} (hc : 0 ≤ c) : d * Real.arctan (c / d) ≤ c := by
  rcases lt_trichotomy d 0 with h | h | h
  · have hd0 : d ≠ 0 := h.ne
    have hcd : c / d ≤ 0 := div_nonpos_of_nonneg_of_nonpos hc h.le
    have h1 : c / d ≤ Real.arctan (c / d) := Real.self_le_arctan hcd
    have h2 := mul_le_mul_of_nonpos_left h1 h.le
    have hdc : d * (c / d) = c := by field_simp
    linarith
  · subst h
    simpa using hc
  · have hd0 : d ≠ 0 := h.ne'
    have h1 : Real.arctan (c / d) ≤ c / d := Real.arctan_le_self (div_nonneg hc h.le)
    have h2 := mul_le_mul_of_nonneg_left h1 h.le
    have hdc : d * (c / d) = c := by field_simp
    linarith

theorem gsum_mul_sub {M : ℕ} (s : Fin M → ℝ) (n : ℕ) (i j : Fin M) :
    gsum s n i j * (s i - s j) = s i ^ (2 * n + 1) - s j ^ (2 * n + 1) := by
  unfold gsum
  have h := geom_sum₂_mul (s i) (s j) (2 * n + 1)
  simpa only [Nat.add_sub_cancel] using h

/-- Nonnegativity of the divided-difference kernel for odd power `2n+1` under strict monotonicity. -/
theorem gsum_nonneg {M : ℕ} {s : Fin M → ℝ} (hs : StrictMono s) (n : ℕ) (i j : Fin M) :
    0 ≤ gsum s n i j := by
  by_cases hij : i = j
  · subst hij
    unfold gsum
    apply Finset.sum_nonneg
    intro r hr
    have hr' : r ≤ 2 * n := by
      have := Finset.mem_range.mp hr
      omega
    rw [← pow_add, Nat.add_sub_of_le hr']
    exact Even.pow_nonneg (even_two_mul n) _
  · have hd : s i - s j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hs.injective h))
    have hd2 : 0 < (s i - s j) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hd))
    have hprod : 0 ≤ (s i ^ (2 * n + 1) - s j ^ (2 * n + 1)) * (s i - s j) := by
      rcases lt_or_gt_of_ne hd with h | h
      · have hlt : s i < s j := by linarith
        have hp : s i ^ (2 * n + 1) < s j ^ (2 * n + 1) :=
          Odd.strictMono_pow (odd_two_mul_add_one n) hlt
        nlinarith
      · have hlt : s j < s i := by linarith
        have hp : s j ^ (2 * n + 1) < s i ^ (2 * n + 1) :=
          Odd.strictMono_pow (odd_two_mul_add_one n) hlt
        nlinarith
    by_contra hneg
    rw [not_le] at hneg
    have h1 : gsum s n i j * (s i - s j) ^ 2 < 0 := mul_neg_of_neg_of_pos hneg hd2
    have h2 : gsum s n i j * (s i - s j) ^ 2 =
        (s i ^ (2 * n + 1) - s j ^ (2 * n + 1)) * (s i - s j) := by
      rw [← gsum_mul_sub s n i j]
      ring
    linarith

theorem sum_gsum {M : ℕ} (s : Fin M → ℝ) (n : ℕ) :
    ∑ i, ∑ j, gsum s n i j =
      ∑ r ∈ Finset.range (2 * n + 1), momentSum s r * momentSum s (2 * n - r) := by
  unfold gsum momentSum
  calc ∑ i, ∑ j, ∑ r ∈ Finset.range (2 * n + 1), s i ^ r * s j ^ (2 * n - r)
      = ∑ i, ∑ r ∈ Finset.range (2 * n + 1), ∑ j, s i ^ r * s j ^ (2 * n - r) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ r ∈ Finset.range (2 * n + 1), ∑ i, ∑ j, s i ^ r * s j ^ (2 * n - r) :=
        Finset.sum_comm
    _ = ∑ r ∈ Finset.range (2 * n + 1), (∑ i, s i ^ r) * (∑ j, s j ^ (2 * n - r)) :=
        Finset.sum_congr rfl fun r _ => (Finset.sum_mul_sum _ _ _ _).symm

theorem momentSum_even_nonneg {M : ℕ} (s : Fin M → ℝ) (k : ℕ) :
    0 ≤ momentSum s (2 * k) := by
  unfold momentSum
  exact Finset.sum_nonneg fun i _ => Even.pow_nonneg (even_two_mul k) (s i)

/-- Odd power sums vanish under the reflection symmetry `s_i = -s_{rev i}`. -/
theorem momentSum_odd_eq_zero {M : ℕ} {s : Fin M → ℝ} (hsym : ∀ i, s i = -s (Fin.rev i))
    {r : ℕ} (hr : Odd r) : momentSum s r = 0 := by
  have h1 : momentSum s r = ∑ i, s (Fin.rev i) ^ r := by
    unfold momentSum
    exact (Equiv.sum_comp Fin.revPerm (fun i => s i ^ r)).symm
  have h2 : ∑ i, s (Fin.rev i) ^ r = - momentSum s r := by
    unfold momentSum
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hneg : s (Fin.rev i) = - s i := by
      rw [hsym (Fin.rev i), Fin.rev_rev]
    rw [hneg, hr.neg_pow]
  linarith

/-- Odd-index vanishing: a range sum over `2n+1` of an odd-zero summand equals the even sum. -/
theorem sum_range_even_eq (h : ℕ → ℝ) (hodd : ∀ r, Odd r → h r = 0) (n : ℕ) :
    ∑ r ∈ Finset.range (2 * n + 1), h r = ∑ a ∈ Finset.range (n + 1), h (2 * a) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : h (2 * k + 1) = 0 := hodd _ (odd_two_mul_add_one k)
    have A : ∑ r ∈ Finset.range (2 * (k + 1) + 1), h r =
        ∑ r ∈ Finset.range (2 * k + 1), h r + h (2 * k + 1) + h (2 * k + 1 + 1) := by
      rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ]
    have B : ∑ a ∈ Finset.range (k + 1 + 1), h (2 * a) =
        ∑ a ∈ Finset.range (k + 1), h (2 * a) + h (2 * (k + 1)) :=
      Finset.sum_range_succ _ _
    rw [A, ih, B, h1, add_zero, show 2 * k + 1 + 1 = 2 * (k + 1) by ring]

theorem sum_mom_antidiag {M : ℕ} {s : Fin M → ℝ} (hsym : ∀ i, s i = -s (Fin.rev i)) (n : ℕ) :
    ∑ r ∈ Finset.range (2 * n + 1), momentSum s r * momentSum s (2 * n - r) =
      ∑ ab ∈ antidiagonal n, momentSum s (2 * ab.1) * momentSum s (2 * ab.2) := by
  have hodd : ∀ r, Odd r → momentSum s r * momentSum s (2 * n - r) = 0 := fun r hr => by
    rw [momentSum_odd_eq_zero hsym hr, zero_mul]
  have h1 := sum_range_even_eq (fun r => momentSum s r * momentSum s (2 * n - r)) hodd n
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine h1.trans (Finset.sum_congr rfl fun a ha => ?_)
  have ha' := Finset.mem_range.mp ha
  have e : 2 * n - 2 * a = 2 * (n - a) := by omega
  show momentSum s (2 * a) * momentSum s (2 * n - 2 * a) =
    momentSum s (2 * a) * momentSum s (2 * (n - a))
  rw [e]

/-! ## 3. Moment recursion (the printed Catalan argument) -/

theorem catalan_le_four_pow' (n : ℕ) : catalan n ≤ 4 ^ n := by
  have h := succ_mul_catalan_eq_centralBinom n
  have hb := Nat.centralBinom_le_four_pow n
  nlinarith

/-- Pair inequality. With `p = 2n+1` and `t_{ij} = arctan(c/(sᵢ - sⱼ))`, the zero-label Bose
equations give `L S_{2n+2} ≤ c ∑_r S_r S_{2n-r}`. -/
theorem key_ineq {M : ℕ} {L c : ℝ} (hc : 0 ≤ c) {s : Fin M → ℝ} (hs : StrictMono s)
    (hbose : ∀ i, L * s i - 2 * ∑ j ∈ Finset.univ.erase i, tArc c s i j = 0) (n : ℕ) :
    L * momentSum s (2 * n + 2) ≤
      c * ∑ r ∈ Finset.range (2 * n + 1), momentSum s r * momentSum s (2 * n - r) := by
  have hdiag : ∀ i, ∑ j ∈ Finset.univ.erase i, tArc c s i j = ∑ j, tArc c s i j := by
    intro i
    apply Finset.sum_erase
    simp [tArc]
  have hantisym : ∀ i j, tArc c s j i = - tArc c s i j := by
    intro i j
    unfold tArc
    rw [show s j - s i = -(s i - s j) by ring, div_neg, Real.arctan_neg]
  have hrow : ∀ i, L * s i = 2 * ∑ j, tArc c s i j := by
    intro i
    have h := hbose i
    rw [hdiag i] at h
    linarith
  have hA : L * momentSum s (2 * n + 2) =
      ∑ i, ∑ j, 2 * (s i ^ (2 * n + 1) * tArc c s i j) := by
    unfold momentSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum]
    have e : L * s i ^ (2 * n + 2) = s i ^ (2 * n + 1) * (L * s i) := by ring
    rw [e, hrow i]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hcomm : ∑ i, ∑ j, s i ^ (2 * n + 1) * tArc c s i j =
      ∑ i, ∑ j, s j ^ (2 * n + 1) * tArc c s j i := Finset.sum_comm
  have hpt : ∀ i j, (s i ^ (2 * n + 1) - s j ^ (2 * n + 1)) * tArc c s i j =
      s i ^ (2 * n + 1) * tArc c s i j + s j ^ (2 * n + 1) * tArc c s j i := by
    intro i j
    rw [hantisym i j]
    ring
  have hC : ∑ i, ∑ j, 2 * (s i ^ (2 * n + 1) * tArc c s i j) =
      ∑ i, ∑ j, (s i ^ (2 * n + 1) - s j ^ (2 * n + 1)) * tArc c s i j := by
    have e2 : ∑ i, ∑ j, (s i ^ (2 * n + 1) - s j ^ (2 * n + 1)) * tArc c s i j =
        ∑ i, ∑ j, (s i ^ (2 * n + 1) * tArc c s i j + s j ^ (2 * n + 1) * tArc c s j i) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpt i j
    rw [e2]
    simp only [Finset.sum_add_distrib]
    rw [← hcomm]
    simp only [two_mul, Finset.sum_add_distrib]
  have hLS : L * momentSum s (2 * n + 2) =
      ∑ i, ∑ j, (s i ^ (2 * n + 1) - s j ^ (2 * n + 1)) * tArc c s i j := by
    rw [hA, hC]
  have hterm : ∀ i j, (s i ^ (2 * n + 1) - s j ^ (2 * n + 1)) * tArc c s i j ≤
      gsum s n i j * c := by
    intro i j
    have hm : (s i - s j) * tArc c s i j ≤ c := mul_arctan_le hc
    calc (s i ^ (2 * n + 1) - s j ^ (2 * n + 1)) * tArc c s i j
        = gsum s n i j * ((s i - s j) * tArc c s i j) := by
          rw [← gsum_mul_sub s n i j]
          ring
      _ ≤ gsum s n i j * c := mul_le_mul_of_nonneg_left hm (gsum_nonneg hs n i j)
  calc L * momentSum s (2 * n + 2)
      = ∑ i, ∑ j, (s i ^ (2 * n + 1) - s j ^ (2 * n + 1)) * tArc c s i j := hLS
    _ ≤ ∑ i, ∑ j, gsum s n i j * c :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = (∑ i, ∑ j, gsum s n i j) * c := by simp only [Finset.sum_mul]
    _ = c * ∑ r ∈ Finset.range (2 * n + 1), momentSum s r * momentSum s (2 * n - r) := by
        rw [sum_gsum s n]
        ring

/-- The moment bound `S_{2n} ≤ M C_n (cM/L)^n` by strong induction on the Catalan recursion. -/
theorem mom_catalan_bound {M : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (hM : 1 ≤ M)
    {s : Fin M → ℝ} (hs : StrictMono s) (hsym : ∀ i, s i = -s (Fin.rev i))
    (hbose : ∀ i, L * s i - 2 * ∑ j ∈ Finset.univ.erase i, tArc c s i j = 0) :
    ∀ n : ℕ, momentSum s (2 * n) ≤ (M : ℝ) * (catalan n : ℝ) * (c * (M : ℝ) / L) ^ n := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hx0 : 0 ≤ c * (M : ℝ) / L := div_nonneg (mul_nonneg hc.le hMpos.le) hL.le
  have hL0 : L ≠ 0 := hL.ne'
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp [momentSum, catalan_zero]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have hkey := key_ineq hc.le hs hbose k
      rw [sum_mom_antidiag hsym k] at hkey
      have hS : ∑ ab ∈ antidiagonal k, momentSum s (2 * ab.1) * momentSum s (2 * ab.2) ≤
          ∑ ab ∈ antidiagonal k,
            ((M : ℝ) ^ 2 * (c * (M : ℝ) / L) ^ k) * ((catalan ab.1 : ℝ) * (catalan ab.2 : ℝ)) := by
        apply Finset.sum_le_sum
        intro ab hab
        rw [HasAntidiagonal.mem_antidiagonal] at hab
        have ha := ih ab.1 (by omega)
        have hb := ih ab.2 (by omega)
        have hXa : 0 ≤ (M : ℝ) * (catalan ab.1 : ℝ) * (c * (M : ℝ) / L) ^ ab.1 :=
          mul_nonneg (mul_nonneg hMpos.le (Nat.cast_nonneg _)) (pow_nonneg hx0 _)
        have hXb : 0 ≤ (M : ℝ) * (catalan ab.2 : ℝ) * (c * (M : ℝ) / L) ^ ab.2 :=
          mul_nonneg (mul_nonneg hMpos.le (Nat.cast_nonneg _)) (pow_nonneg hx0 _)
        have hx : (c * (M : ℝ) / L) ^ ab.1 * (c * (M : ℝ) / L) ^ ab.2 =
            (c * (M : ℝ) / L) ^ k := by
          rw [← pow_add, hab]
        calc momentSum s (2 * ab.1) * momentSum s (2 * ab.2)
            ≤ ((M : ℝ) * (catalan ab.1 : ℝ) * (c * (M : ℝ) / L) ^ ab.1) *
                ((M : ℝ) * (catalan ab.2 : ℝ) * (c * (M : ℝ) / L) ^ ab.2) :=
              mul_le_mul ha hb (momentSum_even_nonneg s ab.2) hXa
          _ = ((M : ℝ) ^ 2 * (c * (M : ℝ) / L) ^ k) *
                ((catalan ab.1 : ℝ) * (catalan ab.2 : ℝ)) := by
              rw [← hx]
              ring
      have hC : ∑ ab ∈ antidiagonal k,
            ((M : ℝ) ^ 2 * (c * (M : ℝ) / L) ^ k) * ((catalan ab.1 : ℝ) * (catalan ab.2 : ℝ)) =
          (M : ℝ) ^ 2 * (c * (M : ℝ) / L) ^ k * (catalan (k + 1) : ℝ) := by
        rw [← Finset.mul_sum]
        congr 1
        exact_mod_cast (catalan_succ' k).symm
      have hfin : L * momentSum s (2 * k + 2) ≤
          c * ((M : ℝ) ^ 2 * (c * (M : ℝ) / L) ^ k * (catalan (k + 1) : ℝ)) := by
        calc L * momentSum s (2 * k + 2)
            ≤ c * ∑ ab ∈ antidiagonal k,
                momentSum s (2 * ab.1) * momentSum s (2 * ab.2) := hkey
          _ ≤ c * ∑ ab ∈ antidiagonal k,
                ((M : ℝ) ^ 2 * (c * (M : ℝ) / L) ^ k) *
                  ((catalan ab.1 : ℝ) * (catalan ab.2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hS hc.le
          _ = c * ((M : ℝ) ^ 2 * (c * (M : ℝ) / L) ^ k * (catalan (k + 1) : ℝ)) := by
              rw [hC]
      have hxL : L * ((c : ℝ) * (M : ℝ) / L) = (c : ℝ) * (M : ℝ) := by
        field_simp
      have hid : L * ((M : ℝ) * (catalan (k + 1) : ℝ) * (c * (M : ℝ) / L) ^ (k + 1)) =
          c * ((M : ℝ) ^ 2 * (c * (M : ℝ) / L) ^ k * (catalan (k + 1) : ℝ)) := by
        rw [pow_succ]
        linear_combination ((M : ℝ) * (catalan (k + 1) : ℝ) * (c * (M : ℝ) / L) ^ k) * hxL
      have e : 2 * (k + 1) = 2 * k + 2 := by ring
      rw [e]
      refine le_of_mul_le_mul_left ?_ hL
      rw [hid]
      exact hfin

/-! ## 4. The lemma CC:F01:ground -/

/-- CC:F01:ground. For `M ≥ 1`, `0 < L`, `0 < c`, zero Bose labels `n`, and a strictly increasing
`s` solving the F01 Bose system: `s_i = -s_{M+1-i}` and `max_i |s_i| ≤ 2 √(cM/L)`. -/
theorem ground_root_bound {M : ℕ} (hM : 1 ≤ M) {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (n : Fin M → ℤ) (hn : ∀ i, n i = 0) (s : Fin M → ℝ) (hs : StrictMono s)
    (hsol : BoseSystem L c n s) :
    (∀ i, s i = -s (Fin.rev i)) ∧ ∀ i, |s i| ≤ 2 * Real.sqrt (c * (M : ℝ) / L) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hx_pos : 0 < c * (M : ℝ) / L := div_pos (mul_pos hc hMpos) hL
  have h4 : 0 < 4 * (c * (M : ℝ) / L) := mul_pos (by norm_num) hx_pos
  have hsolves : Solves L c n s := (boseSystem_iff_solves hc hs n).mp hsol
  have hfix : negRev s = s := solution_negRev_eq hL hc hn hsolves
  have hsym : ∀ i, s i = -s (Fin.rev i) := by
    intro i
    have h := congrFun hfix i
    simp only [negRev] at h
    linarith
  have hbose : ∀ i, L * s i - 2 * ∑ j ∈ Finset.univ.erase i, tArc c s i j = 0 := by
    intro i
    have h := hsol i
    unfold boseLHS at h
    rw [hn i] at h
    simp only [Int.cast_zero, mul_zero] at h
    simpa only [tArc] using h
  have hmom := mom_catalan_bound hL hc hM hs hsym hbose
  refine ⟨hsym, fun i => ?_⟩
  have hbd : ∀ m : ℕ, (s i ^ 2) ^ m ≤ (M : ℝ) * (4 * (c * (M : ℝ) / L)) ^ m := by
    intro m
    have h1 : s i ^ (2 * m) ≤ ∑ j, s j ^ (2 * m) :=
      Finset.single_le_sum (f := fun j => s j ^ (2 * m))
        (fun j _ => Even.pow_nonneg (even_two_mul m) (s j)) (Finset.mem_univ i)
    have h3 : (catalan m : ℝ) ≤ 4 ^ m := by exact_mod_cast catalan_le_four_pow' m
    calc (s i ^ 2) ^ m = s i ^ (2 * m) := by rw [← pow_mul]
      _ ≤ momentSum s (2 * m) := h1
      _ ≤ (M : ℝ) * (catalan m : ℝ) * (c * (M : ℝ) / L) ^ m := hmom m
      _ ≤ (M : ℝ) * 4 ^ m * (c * (M : ℝ) / L) ^ m := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hx_pos.le _)
          exact mul_le_mul_of_nonneg_left h3 hMpos.le
      _ = (M : ℝ) * (4 * (c * (M : ℝ) / L)) ^ m := by rw [mul_pow, mul_assoc]
  have hsq : s i ^ 2 ≤ 4 * (c * (M : ℝ) / L) := by
    by_contra hlt
    rw [not_le] at hlt
    have hy : 1 < s i ^ 2 / (4 * (c * (M : ℝ) / L)) := (one_lt_div h4).mpr hlt
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (M : ℝ) hy
    have hpos : 0 < (4 * (c * (M : ℝ) / L)) ^ m := pow_pos h4 m
    have heq : (s i ^ 2) ^ m =
        (s i ^ 2 / (4 * (c * (M : ℝ) / L))) ^ m * (4 * (c * (M : ℝ) / L)) ^ m := by
      rw [← mul_pow, div_mul_cancel₀ _ h4.ne']
    have hlt2 : (M : ℝ) * (4 * (c * (M : ℝ) / L)) ^ m < (s i ^ 2) ^ m := by
      rw [heq]
      exact mul_lt_mul_of_pos_right hm hpos
    linarith [hbd m]
  have hr0 : 0 ≤ Real.sqrt (c * (M : ℝ) / L) := Real.sqrt_nonneg _
  have hr2 : Real.sqrt (c * (M : ℝ) / L) ^ 2 = c * (M : ℝ) / L := Real.sq_sqrt hx_pos.le
  nlinarith [sq_abs (s i), abs_nonneg (s i)]

#print axioms QuantumNLS.GroundRootBound.arctan_div_eq
#print axioms QuantumNLS.GroundRootBound.sum_sign_erase
#print axioms QuantumNLS.GroundRootBound.boseLHS_eq_logMap
#print axioms QuantumNLS.GroundRootBound.boseSystem_iff_solves
#print axioms QuantumNLS.GroundRootBound.quantumNumbers_rev_zero
#print axioms QuantumNLS.GroundRootBound.logMap_negRev
#print axioms QuantumNLS.GroundRootBound.solution_negRev_eq
#print axioms QuantumNLS.GroundRootBound.mul_arctan_le
#print axioms QuantumNLS.GroundRootBound.gsum_nonneg
#print axioms QuantumNLS.GroundRootBound.sum_gsum
#print axioms QuantumNLS.GroundRootBound.momentSum_odd_eq_zero
#print axioms QuantumNLS.GroundRootBound.sum_mom_antidiag
#print axioms QuantumNLS.GroundRootBound.key_ineq
#print axioms QuantumNLS.GroundRootBound.mom_catalan_bound
#print axioms QuantumNLS.GroundRootBound.ground_root_bound

end QuantumNLS.GroundRootBound
