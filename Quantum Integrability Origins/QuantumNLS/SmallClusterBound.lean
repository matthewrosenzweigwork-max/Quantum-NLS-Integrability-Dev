import Mathlib

/-!
# QG:lem:B3-small-cluster (R-CFCD5A9D): a one-sided bound from the Bethe force

Source: `source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex`, Lemma `QG:lem:B3-small-cluster`
(lines 25-37) and its proof (lines 38-102).

Statement: let `x_1, …, x_k` be distinct reals and `c, L > 0`. Suppose that for every `j` with
`x_j > 0`, `L x_j ≤ 2 Σ_{ℓ≠j} arctan (c/(x_j − x_ℓ))` (`QG:eq:B3-force-inequality`). Then
`max_j (x_j)_+ ≤ 3 √(ck/L)` (`QG:eq:B3-cluster-bound`), including `k = 1`.

Lean indices are zero based (`Fin k`); `(x)_+ = max x 0`.

Route (as printed, `p`-th moments, `y_j = (x_j)_+`, power sums `P_p = Σ_j y_j^p`, `m_p = P_p/k`):
* `pair_term`: `(y^p − z^p) arctan (c/(x − w)) ≤ c Σ_{r<p} y^r z^{p−1−r}` (monotonicity of `(·)_+^p`,
  `|s arctan(c/s)| ≤ c`, and `QG:eq:B3-positive-divided-difference`, here in multiplied form);
* `paired_moment` (`QG:eq:B3-paired-moment` with the diagonal terms added):
  `L P_{p+1} ≤ c Σ_{r<p} P_r P_{p−1−r}`;
* `moment_recursion` (`QG:eq:B3-moment-recursion`), `m_one_le` (`m_1 ≤ √(ck/L)`, Cauchy–Schwarz);
* `bmaj` (the printed `b_p`), `moment_le_majorant` (`QG:eq:B3-majorant-moments`);
* `bmaj_le` : `b_p ≤ 2·3^p`; `small_cluster` (`QG:eq:B3-max-from-moments`, `p → ∞`).

Recorded deviations (none changes the statement):
* The divided-difference inequality is used multiplied out (no division), and ordered pairs
  `j ≠ ℓ` are used instead of `j < ℓ`; Lean's `arctan (c/0) = 0` makes the diagonal vanish.
* `b_p ≤ C 3^p` is proved without the closed form `QG:eq:B3-majorant-series`: the partial sums
  `S_P = Σ_{p≤P} b_p 3^{-p}` satisfy `S_P ≤ 1 + 1/3 + S_{P−2}²/9` (the functional equation
  `B = 1 + t + t²B²` at `t = 1/3`, truncated), hence `S_P ≤ 2` and `C = 2`.
* The final limit is taken as: `y_j > 3a` would make `(y_j/(3a))^p ≤ 2k` for all `p`, impossible.
* Distinctness of the `x_j` is a hypothesis as printed but is not used.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Filter

namespace QuantumNLS.SmallClusterBound

/-! ## 1. The pair term -/

lemma pos_part_sub_le {x w : ℝ} (h : w ≤ x) : max x 0 - max w 0 ≤ x - w := by
  have : max x 0 ≤ max w 0 + (x - w) :=
    max_le (by linarith [le_max_left w 0]) (by linarith [le_max_right w 0])
  linarith

/-- One-sided pair estimate for `x > w`. -/
lemma pair_term_gt {c x w : ℝ} (hc : 0 < c) (hxw : w < x) (p : ℕ) :
    (max x 0 ^ p - max w 0 ^ p) * Real.arctan (c / (x - w)) ≤
      c * ∑ i ∈ range p, max x 0 ^ i * max w 0 ^ (p - 1 - i) := by
  set u := max x 0
  set v := max w 0
  have hv0 : 0 ≤ v := le_max_right _ _
  have hu0 : 0 ≤ u := le_max_right _ _
  have huv : v ≤ u := max_le_max hxw.le le_rfl
  have hd : 0 < x - w := sub_pos.mpr hxw
  have hS : 0 ≤ ∑ i ∈ range p, u ^ i * v ^ (p - 1 - i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (pow_nonneg hu0 _) (pow_nonneg hv0 _)
  have hgeom := geom_sum₂_mul u v p
  have hat : Real.arctan (c / (x - w)) ≤ c / (x - w) := Real.arctan_le_self (div_pos hc hd).le
  have hat0 : 0 ≤ Real.arctan (c / (x - w)) := (Real.arctan_nonneg.mpr (div_pos hc hd).le)
  have hdiff : 0 ≤ u ^ p - v ^ p := sub_nonneg.mpr (pow_le_pow_left₀ hv0 huv p)
  have hlip : u - v ≤ x - w := pos_part_sub_le hxw.le
  calc (u ^ p - v ^ p) * Real.arctan (c / (x - w)) ≤ (u ^ p - v ^ p) * (c / (x - w)) :=
        mul_le_mul_of_nonneg_left hat hdiff
    _ = (∑ i ∈ range p, u ^ i * v ^ (p - 1 - i)) * (u - v) * (c / (x - w)) := by rw [hgeom]
    _ ≤ (∑ i ∈ range p, u ^ i * v ^ (p - 1 - i)) * (x - w) * (c / (x - w)) := by
        apply mul_le_mul_of_nonneg_right _ (div_pos hc hd).le
        exact mul_le_mul_of_nonneg_left hlip hS
    _ = c * ∑ i ∈ range p, u ^ i * v ^ (p - 1 - i) := by field_simp

/-- **Pair estimate** `(y^p − z^p) arctan (c/(x − w)) ≤ c Σ_{r<p} y^r z^{p−1−r}` for all reals
(`y = x_+`, `z = w_+`). -/
lemma pair_term {c : ℝ} (hc : 0 < c) (x w : ℝ) (p : ℕ) :
    (max x 0 ^ p - max w 0 ^ p) * Real.arctan (c / (x - w)) ≤
      c * ∑ i ∈ range p, max x 0 ^ i * max w 0 ^ (p - 1 - i) := by
  have hS : 0 ≤ ∑ i ∈ range p, max x 0 ^ i * max w 0 ^ (p - 1 - i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (pow_nonneg (le_max_right _ _) _)
      (pow_nonneg (le_max_right _ _) _)
  rcases lt_trichotomy w x with h | h | h
  · exact pair_term_gt hc h p
  · subst h; simp only [sub_self, zero_mul]; positivity
  · have h2 := pair_term_gt hc h p
    have e1 : (max x 0 ^ p - max w 0 ^ p) * Real.arctan (c / (x - w)) =
        (max w 0 ^ p - max x 0 ^ p) * Real.arctan (c / (w - x)) := by
      rw [show x - w = -(w - x) by ring, div_neg, Real.arctan_neg]; ring
    have e2 := geom_sum₂_comm (max w 0) (max x 0) p
    rw [e1, ← e2]
    exact h2

/-! ## 2. The paired moment inequality and the moment recursion -/

variable {k : ℕ}

/-- Power sums `P_p = Σ_j (x_j)_+^p` (so `P_0 = k`). -/
def P (x : Fin k → ℝ) (p : ℕ) : ℝ := ∑ j, max (x j) 0 ^ p

lemma P_nonneg (x : Fin k → ℝ) (p : ℕ) : 0 ≤ P x p :=
  Finset.sum_nonneg fun _ _ => pow_nonneg (le_max_right _ _) _

lemma P_zero (x : Fin k → ℝ) : P x 0 = k := by simp [P]

/-- **`QG:eq:B3-paired-moment`** (with the diagonal terms added):
`L P_{p+1} ≤ c Σ_{r<p} P_r P_{p−1−r}` for `p ≥ 1`. -/
theorem paired_moment {x : Fin k → ℝ} {c L : ℝ} (hc : 0 < c)
    (hforce : ∀ j, 0 < x j → L * x j ≤ 2 * ∑ l ∈ univ.erase j, Real.arctan (c / (x j - x l)))
    {p : ℕ} (hp : 1 ≤ p) :
    L * P x (p + 1) ≤ c * ∑ i ∈ range p, P x i * P x (p - 1 - i) := by
  set y := fun j => max (x j) 0
  set A := fun j l => Real.arctan (c / (x j - x l))
  have hA : ∀ j l, A l j = -A j l := by
    intro j l; simp only [A]
    rw [show x l - x j = -(x j - x l) by ring, div_neg, Real.arctan_neg]
  have hdiag : ∀ j, A j j = 0 := by intro j; simp [A]
  have herase : ∀ j, ∑ l ∈ univ.erase j, A j l = ∑ l, A j l := fun j =>
    Finset.sum_erase _ (hdiag j)
  -- step 1: multiply the force inequality by `y_j^p`
  have h1 : ∀ j, L * y j ^ (p + 1) ≤ y j ^ p * (2 * ∑ l, A j l) := by
    intro j
    by_cases hx : 0 < x j
    · have hy : y j = x j := max_eq_left hx.le
      have := hforce j hx
      rw [herase j] at this
      rw [hy, pow_succ]
      have := mul_le_mul_of_nonneg_left this (pow_nonneg hx.le p)
      linarith
    · have hy : y j = 0 := max_eq_right (not_lt.mp hx)
      rw [hy, zero_pow (by omega), zero_pow (by omega)]; simp
  -- step 2: pairing
  have h2 : ∑ j, y j ^ p * (2 * ∑ l, A j l) = ∑ j, ∑ l, (y j ^ p - y l ^ p) * A j l := by
    have hswap : ∑ j, ∑ l, y l ^ p * A j l = -∑ j, ∑ l, y j ^ p * A j l := by
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hA l j]; ring
    have e : ∑ j, ∑ l, (y j ^ p - y l ^ p) * A j l =
        ∑ j, ∑ l, y j ^ p * A j l - ∑ j, ∑ l, y l ^ p * A j l := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [e, hswap]
    have : ∑ j, y j ^ p * (2 * ∑ l, A j l) = 2 * ∑ j, ∑ l, y j ^ p * A j l := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [this]; ring
  -- step 3: the pair estimate and the product form
  have h3 : ∑ j, ∑ l, (y j ^ p - y l ^ p) * A j l ≤
      ∑ j, ∑ l, c * ∑ i ∈ range p, y j ^ i * y l ^ (p - 1 - i) :=
    Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => pair_term hc (x j) (x l) p
  have h4 : ∑ j, ∑ l, c * ∑ i ∈ range p, y j ^ i * y l ^ (p - 1 - i) =
      c * ∑ i ∈ range p, P x i * P x (p - 1 - i) := by
    unfold P
    simp_rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (univ : Finset (Fin k))) (t := range p)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul_sum]
    rw [Finset.sum_comm]
  have hL : L * P x (p + 1) = ∑ j, L * y j ^ (p + 1) := by unfold P; rw [Finset.mul_sum]
  rw [hL]
  calc ∑ j, L * y j ^ (p + 1) ≤ ∑ j, y j ^ p * (2 * ∑ l, A j l) := Finset.sum_le_sum fun j _ => h1 j
    _ = _ := h2
    _ ≤ _ := h3
    _ = _ := h4

/-- Normalized moments `m_p = P_p / k`. -/
def m (x : Fin k → ℝ) (p : ℕ) : ℝ := P x p / k

/-- **`QG:eq:B3-moment-recursion`**: `m_{p+1} ≤ (ck/L) Σ_{r<p} m_r m_{p−1−r}` (`p ≥ 1`, `k ≥ 1`). -/
theorem moment_recursion {x : Fin k → ℝ} {c L : ℝ} (hc : 0 < c) (hL : 0 < L) (hk : 1 ≤ k)
    (hforce : ∀ j, 0 < x j → L * x j ≤ 2 * ∑ l ∈ univ.erase j, Real.arctan (c / (x j - x l)))
    {p : ℕ} (hp : 1 ≤ p) :
    m x (p + 1) ≤ c * k / L * ∑ i ∈ range p, m x i * m x (p - 1 - i) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h := paired_moment hc hforce hp
  unfold m
  have e : c * k / L * ∑ i ∈ range p, P x i / k * (P x (p - 1 - i) / k) =
      (c * ∑ i ∈ range p, P x i * P x (p - 1 - i)) / (L * k) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  rw [e, div_le_div_iff₀ hk0 (mul_pos hL hk0)]
  nlinarith

/-- `m_1 ≤ √(ck/L)` (from `m_2 ≤ ck/L` and Cauchy–Schwarz `m_1² ≤ m_2`). -/
theorem m_one_le {x : Fin k → ℝ} {c L : ℝ} (hc : 0 < c) (hL : 0 < L) (hk : 1 ≤ k)
    (hforce : ∀ j, 0 < x j → L * x j ≤ 2 * ∑ l ∈ univ.erase j, Real.arctan (c / (x j - x l))) :
    m x 1 ≤ Real.sqrt (c * k / L) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h2 := moment_recursion hc hL hk hforce (le_refl 1)
  simp only [range_one, sum_singleton, Nat.sub_self] at h2
  have hm0 : m x 0 = 1 := by unfold m; rw [P_zero]; field_simp
  rw [hm0, one_mul, mul_one] at h2
  -- Cauchy–Schwarz: P_1² ≤ k P_2
  have hcs : P x 1 ^ 2 ≤ k * P x 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin k))) (f := fun j => max (x j) 0)
    simpa [P] using this
  have hm1 : 0 ≤ m x 1 := div_nonneg (P_nonneg x 1) hk0.le
  apply Real.le_sqrt_of_sq_le
  unfold m at h2 ⊢
  rw [div_pow]
  rw [div_le_iff₀ (by positivity)]
  have : P x 2 / k ≤ c * k / L := h2
  rw [div_le_iff₀ hk0] at this
  nlinarith

/-! ## 3. The majorant `b_p` -/

/-- The printed majorant: `b_0 = b_1 = 1`, `b_p = Σ_{r=0}^{p−2} b_r b_{p−2−r}`. -/
def bmaj : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | (p + 2) => ∑ r ∈ (range (p + 1)).attach, bmaj r.1 * bmaj (p - r.1)
  decreasing_by
    all_goals
      (have h := Finset.mem_range.mp r.2; omega)

lemma bmaj_zero : bmaj 0 = 1 := by rw [bmaj]

lemma bmaj_one : bmaj 1 = 1 := by rw [bmaj]

lemma bmaj_succ (p : ℕ) : bmaj (p + 2) = ∑ r ∈ range (p + 1), bmaj r * bmaj (p - r) := by
  rw [bmaj]
  exact Finset.sum_attach (range (p + 1)) (fun r => bmaj r * bmaj (p - r))

lemma bmaj_nonneg (p : ℕ) : 0 ≤ bmaj p := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    match p, ih with
    | 0, _ => simp [bmaj_zero]
    | 1, _ => simp [bmaj_one]
    | q + 2, ih =>
      rw [bmaj_succ]
      exact Finset.sum_nonneg fun r hr => mul_nonneg (ih r (by
        have := Finset.mem_range.mp hr; omega)) (ih _ (by omega))

/-- **`QG:eq:B3-majorant-moments`**: `m_p ≤ (ck/L)^{p/2} b_p`, written with `a = √(ck/L)`. -/
theorem moment_le_majorant {x : Fin k → ℝ} {c L : ℝ} (hc : 0 < c) (hL : 0 < L) (hk : 1 ≤ k)
    (hforce : ∀ j, 0 < x j → L * x j ≤ 2 * ∑ l ∈ univ.erase j, Real.arctan (c / (x j - x l)))
    (p : ℕ) : m x p ≤ Real.sqrt (c * k / L) ^ p * bmaj p := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set a := Real.sqrt (c * k / L)
  have ha2 : a ^ 2 = c * k / L := Real.sq_sqrt (by positivity)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    match p, ih with
    | 0, _ =>
      have : m x 0 = 1 := by unfold m; rw [P_zero]; field_simp
      simp [this, bmaj_zero]
    | 1, _ => simpa [bmaj_one] using m_one_le hc hL hk hforce
    | q + 2, ih =>
      have hrec := moment_recursion hc hL hk hforce (p := q + 1) (by omega)
      rw [show q + 1 + 1 = q + 2 by rfl] at hrec
      rw [bmaj_succ, Finset.mul_sum]
      refine hrec.trans ?_
      rw [← ha2, Finset.mul_sum]
      refine Finset.sum_le_sum fun r hr => ?_
      have hr' := Finset.mem_range.mp hr
      have hm1 := ih r (by omega)
      have hm2 := ih (q + 1 - 1 - r) (by omega)
      have hmr : 0 ≤ m x r := div_nonneg (P_nonneg x r) hk0.le
      have hms : 0 ≤ m x (q + 1 - 1 - r) := div_nonneg (P_nonneg x _) hk0.le
      have e : q + 1 - 1 - r = q - r := by omega
      rw [e] at hm2 hms
      have hpow : a ^ (q + 2) = a ^ 2 * (a ^ r * a ^ (q - r)) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      rw [e, hpow]
      have := mul_le_mul hm1 hm2 hms (mul_nonneg (pow_nonneg ha0 _) (bmaj_nonneg _))
      have h2 : 0 ≤ a ^ 2 := sq_nonneg a
      calc a ^ 2 * (m x r * m x (q - r)) ≤ a ^ 2 * (a ^ r * bmaj r * (a ^ (q - r) * bmaj (q - r))) :=
            mul_le_mul_of_nonneg_left this h2
        _ = _ := by ring

/-- Convolution partial sums are dominated by the square of the partial sum. -/
lemma conv_le_sq (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (Q : ℕ) :
    ∑ q ∈ range (Q + 1), ∑ r ∈ range (q + 1), f r * f (q - r) ≤ (∑ r ∈ range (Q + 1), f r) ^ 2 := by
  rw [Finset.sum_comm' (t' := range (Q + 1)) (s' := fun r => Ico r (Q + 1))]
  · rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun r hr => ?_
    rw [Finset.sum_Ico_eq_sum_range]
    have e : ∀ j ∈ range (Q + 1 - r), f r * f (r + j - r) = f r * f j := fun j _ => by
      rw [Nat.add_sub_cancel_left]
    rw [Finset.sum_congr rfl e]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega))
      (fun j _ _ => mul_nonneg (hf r) (hf j))
  · intro q r
    simp only [mem_range, mem_Ico]
    omega

/-- **`b_p ≤ 2·3^p`** (deviation: partial-sum form of the functional equation at `t = 1/3`). -/
theorem bmaj_partial (P0 : ℕ) : ∑ p ∈ range (P0 + 1), bmaj p / 3 ^ p ≤ 2 := by
  induction P0 using Nat.strong_induction_on with
  | _ P0 ih =>
    match P0, ih with
    | 0, _ => simp [bmaj_zero]
    | 1, _ => norm_num [Finset.sum_range_succ, bmaj_zero, bmaj_one]
    | Q + 2, ih =>
      have hQ := ih Q (by omega)
      have hsplit : ∑ p ∈ range (Q + 2 + 1), bmaj p / 3 ^ p =
          1 + 1 / 3 + ∑ q ∈ range (Q + 1), bmaj (q + 2) / 3 ^ (q + 2) := by
        rw [show Q + 2 + 1 = 2 + (Q + 1) by ring, Finset.sum_range_add, Finset.sum_range_succ,
          Finset.sum_range_one, bmaj_zero, bmaj_one]
        have e : ∑ q ∈ range (Q + 1), bmaj (2 + q) / 3 ^ (2 + q) =
            ∑ q ∈ range (Q + 1), bmaj (q + 2) / 3 ^ (q + 2) :=
          Finset.sum_congr rfl fun q _ => by rw [add_comm 2 q]
        rw [e]
        norm_num
      have hconv : ∑ q ∈ range (Q + 1), bmaj (q + 2) / 3 ^ (q + 2) =
          1 / 9 * ∑ q ∈ range (Q + 1), ∑ r ∈ range (q + 1),
            (bmaj r / 3 ^ r) * (bmaj (q - r) / 3 ^ (q - r)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [bmaj_succ, Finset.sum_div, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r hr => ?_
        have hr' := Finset.mem_range.mp hr
        have : (3 : ℝ) ^ (q + 2) = 9 * (3 ^ r * 3 ^ (q - r)) := by
          rw [← pow_add, show r + (q - r) = q by omega, pow_add]; norm_num; ring
        rw [this]; field_simp
      have hle := conv_le_sq (fun r => bmaj r / 3 ^ r)
        (fun n => div_nonneg (bmaj_nonneg n) (by positivity)) Q
      have h0 : 0 ≤ ∑ r ∈ range (Q + 1), bmaj r / 3 ^ r :=
        Finset.sum_nonneg fun n _ => div_nonneg (bmaj_nonneg n) (by positivity)
      rw [hsplit, hconv]
      nlinarith

theorem bmaj_le (p : ℕ) : bmaj p ≤ 2 * 3 ^ p := by
  have h := bmaj_partial p
  have hle : bmaj p / 3 ^ p ≤ ∑ q ∈ range (p + 1), bmaj q / 3 ^ q :=
    Finset.single_le_sum (f := fun q => bmaj q / 3 ^ q)
      (fun n _ => div_nonneg (bmaj_nonneg n) (by positivity)) (Finset.self_mem_range_succ p)
  have h3 : (0 : ℝ) < 3 ^ p := by positivity
  rw [div_le_iff₀ h3] at hle
  nlinarith

/-! ## 4. The lemma -/

/-- **QG:lem:B3-small-cluster** (R-CFCD5A9D): `(x_j)_+ ≤ 3 √(ck/L)` for every `j`. -/
theorem small_cluster {x : Fin k → ℝ} (_hx : Function.Injective x) {c L : ℝ} (hc : 0 < c)
    (hL : 0 < L)
    (hforce : ∀ j, 0 < x j → L * x j ≤ 2 * ∑ l ∈ univ.erase j, Real.arctan (c / (x j - x l))) :
    ∀ j, max (x j) 0 ≤ 3 * Real.sqrt (c * k / L) := by
  intro j
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (fun h => (h ▸ j).elim0)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set a := Real.sqrt (c * k / L)
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  by_contra hcon
  push Not at hcon
  set y := max (x j) 0
  have hρ : 1 < y / (3 * a) := by rw [one_lt_div (by positivity)]; exact hcon
  -- `y^p ≤ P_p = k m_p ≤ k a^p b_p ≤ 2k (3a)^p`
  have hbound : ∀ p : ℕ, (y / (3 * a)) ^ p ≤ 2 * k := by
    intro p
    have h1 : y ^ p ≤ P x p := by
      unfold P
      exact Finset.single_le_sum (f := fun l => max (x l) 0 ^ p)
        (fun l _ => pow_nonneg (le_max_right _ _) _) (mem_univ j)
    have h2 := moment_le_majorant hc hL hk hforce p
    have h3 := bmaj_le p
    unfold m at h2
    rw [div_le_iff₀ hk0] at h2
    have h4 : P x p ≤ 2 * k * (3 * a) ^ p := by
      have := mul_le_mul_of_nonneg_left h3 (pow_nonneg ha.le p)
      rw [mul_pow]
      nlinarith
    rw [div_pow, div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨p, hp⟩ := (tendsto_pow_atTop_atTop_of_one_lt hρ).eventually_gt_atTop (2 * (k : ℝ)) |>.exists
  linarith [hbound p]

/-- The printed form `max_j (x_j)_+ ≤ 3 √(ck/L)` (`k ≥ 1`, so the maximum exists). -/
theorem small_cluster_max {x : Fin k → ℝ} (hx : Function.Injective x) {c L : ℝ} (hc : 0 < c)
    (hL : 0 < L) (hk : 1 ≤ k)
    (hforce : ∀ j, 0 < x j → L * x j ≤ 2 * ∑ l ∈ univ.erase j, Real.arctan (c / (x j - x l))) :
    (univ.sup' (univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩) fun j => max (x j) 0) ≤
      3 * Real.sqrt (c * k / L) :=
  Finset.sup'_le _ _ fun j _ => small_cluster hx hc hL hforce j

/-! Kernel axiom audit (checkpoint SC1). -/
#print axioms pos_part_sub_le
#print axioms pair_term_gt
#print axioms pair_term
#print axioms P_nonneg
#print axioms P_zero
#print axioms paired_moment
#print axioms moment_recursion
#print axioms m_one_le
#print axioms bmaj_succ
#print axioms bmaj_nonneg
#print axioms moment_le_majorant
#print axioms conv_le_sq
#print axioms bmaj_partial
#print axioms bmaj_le
#print axioms small_cluster
#print axioms small_cluster_max

end QuantumNLS.SmallClusterBound
