import QuantumNLS.BetheLabels
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# R-B0F552E0: finite-particle root displacement estimate (`lem:root-displacement`)

Source: `source/chapters/foundations/ROOT_occupation_energy.tex`, lines 9--38 (statement and printed proof).
Printed statement: for every on-shell repulsive configuration with `c = κ/N`, ordered roots `q_j` and
ordered labels `n_j`,
  `(1/N) Σ_j (q_j - p_{n_j})^2 ≤ (κ/L) (1 - 1/N)`, with `p_n = 2πn/L` (source line 4).

Convention bridge (proved in this module, not assumed):
* The labels are the DEF-006 corrected integers `n_j = correctedInt ℓ j`, i.e. `I_J - J + (N+1)/2` with the
  source's one-based `J`, equivalently `I_j - (j+1) + (N+1)/2` with Lean's zero-based `j`. They are
  nondecreasing by `correctedInt_monotone`. The uncorrected logarithmic labels `I_j` enter only through
  the on-shell condition.
* On-shell means the literal DEF-006 rapidity equation `RapidityEq L (κ/N) ℓ.I q`, i.e.
  `L q_j + 2 Σ_{k≠j} arctan((q_j-q_k)/c) = 2π I_j`.
* The accepted R-4C8D7C9E identification (`rapidityEq_iff_roots`, `roots_strictMono_labels`) shows that
  this solution is the unique accepted root vector, hence strictly increasing. Ordering is derived.
* The printed Bethe form `L q_j - 2 Σ_{k≠j} arctan(c/(q_j-q_k)) = 2π n_j` is derived from DEF-006 by the
  arctan inversion identity and the sign count of the ordering (`bethe_printed`).

The printed proof is then carried out with `d_j = q_j - p_{n_j}`:
* `Σ_j d_j = 0`, and the tail sums `Σ_{j ≥ m} d_j ≥ 0` (antisymmetry cancels internal pairs);
* Abel summation with monotone `p_{n_j}` gives `Σ_j p_{n_j} d_j ≥ 0` (`abel_fin`);
* symmetrization and `x arctan(c/x) ≤ c` give `L Σ_j q_j d_j ≤ κ(N-1)` (`mat_bound`).

Read-only imports: `BetheLabels` (DEF-006) and, through it, `BetheConvexity`, `BetheSmooth`, `BetheRoots`,
`BetheAdmission` (all accepted). No frozen file is edited.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace QuantumNLS.RootDisplacementEstimate

open QuantumNLS.BetheLabels

/-- The momentum label map `p_n = 2πn/L` (source line 4). -/
def pn (L : ℝ) (n : ℤ) : ℝ := 2 * Real.pi * (n : ℝ) / L

/-- On-shell repulsive configuration (source line 11): `N ≥ 1`, torus length `L > 0`, repulsive coupling
`κ > 0`, DEF-006 labels `ℓ`, and real rapidities `q` solving the literal DEF-006 rapidity equation at
`c = κ/N`. -/
def OnShellRepulsive {N : ℕ} (L κ : ℝ) (ℓ : LogLabels N) (q : Fin N → ℝ) : Prop :=
  0 < N ∧ 0 < L ∧ 0 < κ ∧ RapidityEq L (κ / N) ℓ.I q

/-! ### Generic finite-sum lemmas -/

theorem sum_antisymm_zero {N : ℕ} (h : Fin N → Fin N → ℝ) (hh : ∀ i k, h k i = -h i k) :
    ∑ i, ∑ k, h i k = 0 := by
  have h1 : ∑ i, ∑ k, h i k = ∑ i, ∑ k, h k i := Finset.sum_comm
  have h2 : ∑ i, ∑ k, h k i = -∑ i, ∑ k, h i k := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun k _ => hh i k)
  linarith

/-! ### Abel summation on ℕ-indexed sequences -/

/-- Prefix sum `Σ_{i<m} d i`. -/
def pref (d : ℕ → ℝ) (m : ℕ) : ℝ := ∑ i ∈ Finset.range m, d i

theorem abel_prefix (p d : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), p i * d i =
      p n * pref d (n + 1) - ∑ i ∈ Finset.range n, (p (i + 1) - p i) * pref d (i + 1) := by
  induction n with
  | zero => simp [pref]
  | succ n ih =>
    have h2 : pref d (n + 1 + 1) = pref d (n + 1) + d (n + 1) := by
      unfold pref; exact Finset.sum_range_succ _ _
    have e1 : ∑ i ∈ Finset.range (n + 1 + 1), p i * d i =
        ∑ i ∈ Finset.range (n + 1), p i * d i + p (n + 1) * d (n + 1) :=
      Finset.sum_range_succ _ _
    have e2 : ∑ i ∈ Finset.range (n + 1), (p (i + 1) - p i) * pref d (i + 1) =
        ∑ i ∈ Finset.range n, (p (i + 1) - p i) * pref d (i + 1) +
          (p (n + 1) - p n) * pref d (n + 1) :=
      Finset.sum_range_succ _ _
    rw [e1, ih, e2, h2]
    ring

theorem pref_eq_neg_tail (d : ℕ → ℝ) (M m : ℕ) (hm : m ≤ M + 1)
    (hsum : ∑ i ∈ Finset.range (M + 1), d i = 0) :
    ∑ i ∈ Finset.range (M + 1), (if m ≤ i then d i else 0) = -pref d m := by
  have hlt : ∀ K, m ≤ K → ∑ i ∈ Finset.range K, (if i < m then d i else 0) = pref d m := by
    intro K hK
    induction K, hK using Nat.le_induction with
    | base => exact Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.1 hi))
    | succ K hK ih =>
      rw [Finset.sum_range_succ, ih, if_neg (show ¬ K < m by omega), add_zero]
  have hsplit : ∑ i ∈ Finset.range (M + 1), (if m ≤ i then d i else 0) +
      ∑ i ∈ Finset.range (M + 1), (if i < m then d i else 0) =
      ∑ i ∈ Finset.range (M + 1), d i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : m ≤ i
    · rw [if_pos h, if_neg (not_lt.2 h), add_zero]
    · rw [if_neg h, if_pos (not_le.1 h), zero_add]
  rw [hlt (M + 1) hm, hsum] at hsplit
  linarith

theorem abel_nonneg (p d : ℕ → ℝ) (M : ℕ) (hmono : ∀ i, i < M → p i ≤ p (i + 1))
    (hsum : ∑ i ∈ Finset.range (M + 1), d i = 0)
    (htail : ∀ m, m ≤ M + 1 → 0 ≤ ∑ i ∈ Finset.range (M + 1), (if m ≤ i then d i else 0)) :
    0 ≤ ∑ i ∈ Finset.range (M + 1), p i * d i := by
  rw [abel_prefix p d M]
  have hpref : pref d (M + 1) = 0 := hsum
  rw [hpref, mul_zero, zero_sub, neg_nonneg]
  apply Finset.sum_nonpos
  intro i hi
  have hiM : i < M := Finset.mem_range.1 hi
  have h1 : pref d (i + 1) ≤ 0 := by
    have h := htail (i + 1) (by omega)
    rw [pref_eq_neg_tail d M (i + 1) (by omega) hsum] at h
    linarith
  exact mul_nonpos_of_nonneg_of_nonpos (by linarith [hmono i hiM]) h1

/-! ### Transfer from `Fin (M+1)` to `ℕ` -/

theorem sum_fin_eq_sum_range {M : ℕ} (φ : Fin (M + 1) → ℝ) (ψ : ℕ → ℝ)
    (hψ : ∀ (i : ℕ) (h : i < M + 1), ψ i = φ ⟨i, h⟩) :
    ∑ i, φ i = ∑ m ∈ Finset.range (M + 1), ψ m := by
  rw [← Fin.sum_univ_eq_sum_range ψ (M + 1)]
  exact Finset.sum_congr rfl (fun i _ => (hψ i i.isLt).symm)

/-- Abel-type lower bound on `Fin (M+1)`: monotone weights against a zero-sum sequence with nonnegative
tail sums are nonnegative. -/
theorem abel_fin {M : ℕ} (p d : Fin (M + 1) → ℝ) (hp : Monotone p)
    (hsum : ∑ i, d i = 0)
    (htail : ∀ m, m ≤ M + 1 → 0 ≤ ∑ i, (if m ≤ i.val then d i else 0)) :
    0 ≤ ∑ i, p i * d i := by
  obtain ⟨P, hP⟩ : ∃ P : ℕ → ℝ, P = fun m => if h : m < M + 1 then p ⟨m, h⟩ else 0 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ, D = fun m => if h : m < M + 1 then d ⟨m, h⟩ else 0 := ⟨_, rfl⟩
  have e1 : ∑ i, p i * d i = ∑ m ∈ Finset.range (M + 1), P m * D m :=
    sum_fin_eq_sum_range (fun i => p i * d i) (fun m => P m * D m)
      (fun i h => by simp only [hP, hD, dif_pos h])
  have key2 : ∑ i, d i = ∑ m ∈ Finset.range (M + 1), D m :=
    sum_fin_eq_sum_range d D (fun i h => by simp only [hD, dif_pos h])
  have e2 : ∑ m ∈ Finset.range (M + 1), D m = 0 := key2.symm.trans hsum
  have hmono : ∀ i, i < M → P i ≤ P (i + 1) := by
    intro i hi
    have h1 : i < M + 1 := by omega
    have h2 : i + 1 < M + 1 := by omega
    simp only [hP, dif_pos h1, dif_pos h2]
    exact hp (Fin.mk_le_mk.2 (Nat.le_succ i))
  have htail' : ∀ m, m ≤ M + 1 → 0 ≤ ∑ i ∈ Finset.range (M + 1), (if m ≤ i then D i else 0) := by
    intro m hm
    have key : ∑ i : Fin (M + 1), (if m ≤ i.val then d i else 0) =
        ∑ j ∈ Finset.range (M + 1), (if m ≤ j then D j else 0) :=
      sum_fin_eq_sum_range (fun i : Fin (M + 1) => if m ≤ i.val then d i else 0)
        (fun j => if m ≤ j then D j else 0) (fun i h => by simp only [hD, dif_pos h])
    exact (htail m hm).trans_eq key
  rw [e1]
  exact abel_nonneg P D M hmono e2 htail'

/-! ### Arctangent identities -/

theorem arctan_div_pos_eq {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    Real.arctan (x / c) = Real.pi / 2 - Real.arctan (c / x) := by
  rw [← inv_div c x]
  exact Real.arctan_inv_of_pos (div_pos hc hx)

theorem arctan_div_neg_eq {c x : ℝ} (hc : 0 < c) (hx : x < 0) :
    Real.arctan (x / c) = -(Real.pi / 2) - Real.arctan (c / x) := by
  rw [← inv_div c x]
  exact Real.arctan_inv_of_neg (div_neg_of_pos_of_neg hc hx)

/-- Inversion identity: `2 arctan(x/c) + 2 arctan(c/x) = π sgn(x)` for `x ≠ 0`, `c > 0`. -/
theorem pair_identity {c x : ℝ} (hc : 0 < c) (hx : x ≠ 0) :
    2 * Real.arctan (x / c) + 2 * Real.arctan (c / x) = if 0 < x then Real.pi else -Real.pi := by
  rcases lt_or_gt_of_ne hx with h | h
  · rw [arctan_div_neg_eq hc h, if_neg (not_lt.2 h.le)]
    ring
  · rw [arctan_div_pos_eq hc h, if_pos h]
    ring

/-- `x arctan(c/x) ≤ c` for `x ≠ 0`, `c > 0`. -/
theorem mul_arctan_div_le {c x : ℝ} (hc : 0 < c) (hx : x ≠ 0) :
    x * Real.arctan (c / x) ≤ c := by
  rcases lt_or_gt_of_ne hx with h | h
  · have hy : 0 ≤ -(c / x) := by
      have : c / x < 0 := div_neg_of_pos_of_neg hc h
      linarith
    have h1 : c / x ≤ Real.arctan (c / x) := by
      have h2 := Real.arctan_le_self hy
      rw [Real.arctan_neg] at h2
      linarith
    have h3 : x * (c / x) = c := by field_simp
    have h4 : x * Real.arctan (c / x) ≤ x * (c / x) := mul_le_mul_of_nonpos_left h1 h.le
    linarith
  · have hy : 0 ≤ c / x := (div_pos hc h).le
    have h1 : Real.arctan (c / x) ≤ c / x := Real.arctan_le_self hy
    have h3 : x * (c / x) = c := by field_simp
    have h4 : x * Real.arctan (c / x) ≤ x * (c / x) := mul_le_mul_of_nonneg_left h1 h.le
    linarith

/-! ### The antisymmetric pair matrix -/

/-- `g_{ik} = 2 arctan(c/(q_i - q_k))` off the diagonal, zero on the diagonal. -/
def gmat {N : ℕ} (c : ℝ) (q : Fin N → ℝ) (i k : Fin N) : ℝ :=
  if i = k then 0 else 2 * Real.arctan (c / (q i - q k))

theorem gmat_self {N : ℕ} (c : ℝ) (q : Fin N → ℝ) (i : Fin N) : gmat c q i i = 0 := by
  simp [gmat]

theorem gmat_antisymm {N : ℕ} (c : ℝ) (q : Fin N → ℝ) (i k : Fin N) :
    gmat c q k i = -gmat c q i k := by
  by_cases h : i = k
  · subst h; simp [gmat]
  · have hki : ¬ k = i := fun e => h e.symm
    simp only [gmat, if_neg h, if_neg hki]
    have e : q k - q i = -(q i - q k) := by ring
    rw [e, div_neg, Real.arctan_neg]
    ring

theorem gmat_nonneg_of_lt {N : ℕ} {c : ℝ} (hc : 0 < c) {q : Fin N → ℝ} (hq : StrictMono q)
    {i k : Fin N} (hki : k < i) : 0 ≤ gmat c q i k := by
  have hne : i ≠ k := hki.ne'
  have hpos : 0 < q i - q k := sub_pos.2 (hq hki)
  simp only [gmat, if_neg hne]
  exact mul_nonneg (by norm_num) (Real.arctan_nonneg.2 (div_pos hc hpos).le)

theorem gmat_mul_le {N : ℕ} {c : ℝ} (hc : 0 < c) (q : Fin N → ℝ) (i k : Fin N) :
    (q i - q k) * gmat c q i k ≤ if i = k then 0 else 2 * c := by
  by_cases h : i = k
  · subst h; simp [gmat]
  · rw [if_neg h]
    by_cases hx : q i - q k = 0
    · rw [hx, zero_mul]; exact (mul_pos two_pos hc).le
    · simp only [gmat, if_neg h]
      have h5 := mul_arctan_div_le hc hx
      linarith [show (q i - q k) * (2 * Real.arctan (c / (q i - q k))) =
        2 * ((q i - q k) * Real.arctan (c / (q i - q k))) by ring]

theorem sum_gmat_eq_erase {N : ℕ} (c : ℝ) (q : Fin N → ℝ) (i : Fin N) :
    ∑ k, gmat c q i k = 2 * ∑ k ∈ Finset.univ.erase i, Real.arctan (c / (q i - q k)) := by
  rw [← Finset.sum_erase Finset.univ (f := gmat c q i) (gmat_self c q i), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hki : k ≠ i := Finset.ne_of_mem_erase hk
  simp only [gmat, if_neg hki.symm]

/-! ### Counting the sign pattern of an ordered configuration -/

theorem card_filter_lt_fin {M : ℕ} (i : Fin (M + 1)) :
    (Finset.univ.filter (fun k : Fin (M + 1) => k < i)).card = i.val := by
  have h : Finset.univ.filter (fun k : Fin (M + 1) => k < i) = Finset.Iio i := by
    ext k; simp
  rw [h, Fin.card_Iio]

theorem card_filter_gt_fin {M : ℕ} (i : Fin (M + 1)) :
    (Finset.univ.filter (fun k : Fin (M + 1) => i < k)).card = M - i.val := by
  have h : Finset.univ.filter (fun k : Fin (M + 1) => i < k) = Finset.Ioi i := by
    ext k; simp
  rw [h, Fin.card_Ioi]
  omega

theorem sum_pi_ite_lt {M : ℕ} (i : Fin (M + 1)) :
    ∑ k : Fin (M + 1), (if k < i then Real.pi else 0) = Real.pi * (i.val : ℝ) := by
  rw [← Finset.sum_filter, Finset.sum_const, card_filter_lt_fin, nsmul_eq_mul]
  ring

theorem sum_pi_ite_gt {M : ℕ} (i : Fin (M + 1)) :
    ∑ k : Fin (M + 1), (if i < k then Real.pi else 0) =
      Real.pi * ((M : ℝ) - (i.val : ℝ)) := by
  rw [← Finset.sum_filter, Finset.sum_const, card_filter_gt_fin, nsmul_eq_mul,
    Nat.cast_sub (show i.val ≤ M by have := i.isLt; omega)]
  ring

theorem count_erase {M : ℕ} (i : Fin (M + 1)) :
    ∑ k ∈ Finset.univ.erase i, (if k < i then Real.pi else -Real.pi) =
      Real.pi * (i.val : ℝ) - Real.pi * ((M : ℝ) - (i.val : ℝ)) := by
  have h1 : ∀ k ∈ Finset.univ.erase i,
      (if k < i then Real.pi else -Real.pi) =
        (if k < i then Real.pi else 0) - (if i < k then Real.pi else 0) := by
    intro k hk
    have hne : k ≠ i := Finset.ne_of_mem_erase hk
    rcases lt_or_gt_of_ne hne with h | h
    · simp [h, not_lt.2 h.le]
    · simp [h, lt_asymm h]
  have hA : ∑ k ∈ Finset.univ.erase i, (if k < i then Real.pi else 0) =
      ∑ k, (if k < i then Real.pi else 0) := Finset.sum_erase _ (by simp)
  have hB : ∑ k ∈ Finset.univ.erase i, (if i < k then Real.pi else 0) =
      ∑ k, (if i < k then Real.pi else 0) := Finset.sum_erase _ (by simp)
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, hA, hB, sum_pi_ite_lt, sum_pi_ite_gt]

/-- **Printed Bethe form.** From the DEF-006 rapidity equation with ordered roots, the corrected
labels satisfy `L q_i - 2 Σ_{k≠i} arctan(c/(q_i-q_k)) = 2π n_i`. -/
theorem bethe_printed {M : ℕ} {c : ℝ} (hc : 0 < c) (ℓ : LogLabels (M + 1)) (q : Fin (M + 1) → ℝ)
    (L : ℝ) (hmono : StrictMono q) (hE : RapidityEq L c ℓ.I q) (i : Fin (M + 1)) :
    L * q i - 2 * ∑ k ∈ Finset.univ.erase i, Real.arctan (c / (q i - q k)) =
      2 * Real.pi * (correctedInt ℓ i : ℝ) := by
  have hpair : ∀ k ∈ Finset.univ.erase i,
      2 * Real.arctan ((q i - q k) / c) + 2 * Real.arctan (c / (q i - q k)) =
        if k < i then Real.pi else -Real.pi := by
    intro k hk
    have hne : k ≠ i := Finset.ne_of_mem_erase hk
    have hx : q i - q k ≠ 0 := by
      intro e
      exact hne (hmono.injective (sub_eq_zero.1 e)).symm
    rw [pair_identity hc hx]
    simp only [sub_pos, hmono.lt_iff_lt]
  have hsplit : ∑ k ∈ Finset.univ.erase i,
      (2 * Real.arctan ((q i - q k) / c) + 2 * Real.arctan (c / (q i - q k))) =
        ∑ k ∈ Finset.univ.erase i, (if k < i then Real.pi else -Real.pi) :=
    Finset.sum_congr rfl hpair
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, count_erase] at hsplit
  have hE' := hE i
  have hn := correctedInt_spec ℓ i
  push_cast at hn
  rw [hn]
  linear_combination hE' - hsplit

/-! ### Matrix bound and tail positivity -/

/-- Tail positivity for the pair matrix: `Σ_{i ≥ m} Σ_k g_{ik} ≥ 0`. -/
theorem tail_gmat_nonneg {M : ℕ} {c : ℝ} (hc : 0 < c) (q : Fin (M + 1) → ℝ) (hq : StrictMono q)
    (m : ℕ) : 0 ≤ ∑ i, ∑ k, (if m ≤ i.val then gmat c q i k else 0) := by
  have hsplit : ∀ i k : Fin (M + 1), (if m ≤ i.val then gmat c q i k else 0) =
      (if m ≤ i.val ∧ m ≤ k.val then gmat c q i k else 0) +
      (if m ≤ i.val ∧ k.val < m then gmat c q i k else 0) := by
    intro i k
    split_ifs <;> first | omega | ring1
  have hanti : ∀ i k : Fin (M + 1),
      (if m ≤ k.val ∧ m ≤ i.val then gmat c q k i else 0) =
        -(if m ≤ i.val ∧ m ≤ k.val then gmat c q i k else 0) := by
    intro i k
    by_cases h : m ≤ i.val ∧ m ≤ k.val
    · have h' : m ≤ k.val ∧ m ≤ i.val := ⟨h.2, h.1⟩
      rw [if_pos h', if_pos h, gmat_antisymm]
    · have h' : ¬ (m ≤ k.val ∧ m ≤ i.val) := fun e => h ⟨e.2, e.1⟩
      rw [if_neg h, if_neg h', neg_zero]
  have h1 : ∑ i, ∑ k, (if m ≤ i.val ∧ m ≤ k.val then gmat c q i k else 0) = 0 :=
    sum_antisymm_zero (fun i k => if m ≤ i.val ∧ m ≤ k.val then gmat c q i k else 0) hanti
  have h2 : 0 ≤ ∑ i, ∑ k, (if m ≤ i.val ∧ k.val < m then gmat c q i k else 0) := by
    refine Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => ?_))
    by_cases h : m ≤ i.val ∧ k.val < m
    · rw [if_pos h]
      exact gmat_nonneg_of_lt hc hq (Fin.lt_iff_val_lt_val.2 (lt_of_lt_of_le h.2 h.1))
    · rw [if_neg h]
  simp only [hsplit, Finset.sum_add_distrib]
  linarith

theorem sum_erase_const_eq {M : ℕ} (c : ℝ) (i : Fin (M + 1)) :
    ∑ k, (if i = k then (0 : ℝ) else 2 * c) = (M : ℝ) * (2 * c) := by
  have hs : ∑ k ∈ Finset.univ.erase i, (if i = k then (0 : ℝ) else 2 * c) =
      ∑ k ∈ Finset.univ.erase i, (2 * c) :=
    Finset.sum_congr rfl (fun k hk => if_neg (Finset.ne_of_mem_erase hk).symm)
  have h0 : (if i = i then (0 : ℝ) else 2 * c) = 0 := by simp
  rw [← Finset.sum_erase (f := fun k => if i = k then (0 : ℝ) else 2 * c) (a := i) Finset.univ h0, hs]
  simp

/-! ### The main estimate -/

/-- **R-B0F552E0 (`lem:root-displacement`).** For an on-shell repulsive configuration with DEF-006
corrected labels `n_j = correctedInt ℓ j` and `c = κ/N`,
`(1/N) Σ_j (q_j - p_{n_j})^2 ≤ (κ/L)(1 - 1/N)` with `p_n = 2πn/L`. -/
theorem root_displacement_estimate {N : ℕ} {L κ : ℝ} (ℓ : LogLabels N) (q : Fin N → ℝ)
    (h : OnShellRepulsive L κ ℓ q) :
    (1 / (N : ℝ)) * ∑ j, (q j - pn L (correctedInt ℓ j)) ^ 2 ≤
      (κ / L) * (1 - 1 / (N : ℝ)) := by
  obtain ⟨hN, hL, hκ, hq⟩ := h
  have hcN : 0 < κ / (N : ℝ) := div_pos hκ (by exact_mod_cast hN)
  have hroots : q = BetheSmooth.roots L (correctedInt ℓ) (κ / N) :=
    (rapidityEq_iff_roots hL hcN ℓ q).1 hq
  have hSM : StrictMono q := by
    rw [hroots]; exact roots_strictMono_labels hL hcN ℓ
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = κ / ((M + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hcdef] at hq
  have hc : 0 < c := by rw [hcdef]; exact div_pos hκ (by positivity)
  obtain ⟨n, hndef⟩ : ∃ n : Fin (M + 1) → ℤ, n = correctedInt ℓ := ⟨_, rfl⟩
  have hnmono : Monotone n := by rw [hndef]; exact correctedInt_monotone ℓ
  -- Printed Bethe form with the corrected labels.
  have hBethe : ∀ i, L * q i - 2 * ∑ k ∈ Finset.univ.erase i, Real.arctan (c / (q i - q k)) =
      2 * Real.pi * (n i : ℝ) := by
    intro i; rw [hndef]; exact bethe_printed hc ℓ q L hSM hq i
  have hpmono : Monotone (fun i => pn L (n i)) := by
    intro a b hab
    have hz : (n a : ℝ) ≤ (n b : ℝ) := by exact_mod_cast hnmono hab
    show pn L (n a) ≤ pn L (n b)
    unfold pn
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hz (by positivity)) hL.le
  -- L d_i = Σ_k g_{ik}, with d_i = q_i - p_{n_i}.
  have hEd : ∀ i, L * (q i - pn L (n i)) = ∑ k, gmat c q i k := by
    intro i
    have h2 : L * pn L (n i) = 2 * Real.pi * (n i : ℝ) := by
      unfold pn; field_simp
    have e : L * (q i - pn L (n i)) = L * q i - 2 * Real.pi * (n i : ℝ) := by
      rw [mul_sub, h2]
    rw [e, sum_gmat_eq_erase]
    linarith [hBethe i]
  -- Σ_j d_j = 0.
  have hsum_d : ∑ i, (q i - pn L (n i)) = 0 := by
    have h1 : L * ∑ i, (q i - pn L (n i)) = 0 := by
      rw [Finset.mul_sum]
      calc ∑ i, L * (q i - pn L (n i)) = ∑ i, ∑ k, gmat c q i k :=
            Finset.sum_congr rfl (fun i _ => hEd i)
        _ = 0 := sum_antisymm_zero (gmat c q) (gmat_antisymm c q)
    rcases mul_eq_zero.1 h1 with h0 | h0
    · exact absurd h0 hL.ne'
    · exact h0
  -- Tail sums of d are nonnegative.
  have htail : ∀ m, m ≤ M + 1 → 0 ≤ ∑ i, (if m ≤ i.val then (q i - pn L (n i)) else 0) := by
    intro m _
    have hrel : ∀ i : Fin (M + 1), (if m ≤ i.val then (q i - pn L (n i)) else 0) * L =
        ∑ k, (if m ≤ i.val then gmat c q i k else 0) := by
      intro i
      by_cases h : m ≤ i.val
      · have e1 : ∑ k, (if m ≤ i.val then gmat c q i k else 0) = ∑ k, gmat c q i k :=
          Finset.sum_congr rfl (fun k _ => if_pos h)
        rw [e1, if_pos h, ← hEd i]
        ring
      · have e1 : ∑ k, (if m ≤ i.val then gmat c q i k else 0) = 0 :=
          Finset.sum_eq_zero (fun k _ => if_neg h)
        rw [e1, if_neg h, zero_mul]
    have hsumL : (∑ i, (if m ≤ i.val then (q i - pn L (n i)) else 0)) * L =
        ∑ i, ∑ k, (if m ≤ i.val then gmat c q i k else 0) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => hrel i)
    have hT := tail_gmat_nonneg hc q hSM m
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_neg_of_pos hneg hL
    linarith
  -- Abel summation: Σ_j p_{n_j} d_j ≥ 0.
  have hAbel : 0 ≤ ∑ i, pn L (n i) * (q i - pn L (n i)) :=
    abel_fin (fun i => pn L (n i)) (fun i => q i - pn L (n i)) hpmono hsum_d htail
  -- The matrix bound: 2 A ≤ (M+1) · M · 2c with A = Σ_{i,k} q_i g_{ik}.
  have hBA : ∑ i, ∑ k, q k * gmat c q i k = -∑ i, ∑ k, q i * gmat c q i k := by
    calc ∑ i, ∑ k, q k * gmat c q i k = ∑ k, ∑ i, q k * gmat c q i k := Finset.sum_comm
      _ = ∑ k, ∑ i, -(q k * gmat c q k i) := by
          refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i _ => ?_))
          rw [gmat_antisymm c q k i, mul_neg]
      _ = -∑ k, ∑ i, q k * gmat c q k i := by
          simp only [Finset.sum_neg_distrib]
      _ = -∑ i, ∑ k, q i * gmat c q i k := rfl
  have hsplit2 : ∑ i, ∑ k, (q i - q k) * gmat c q i k =
      2 * ∑ i, ∑ k, q i * gmat c q i k := by
    have e : ∑ i, ∑ k, (q i - q k) * gmat c q i k =
        ∑ i, ∑ k, q i * gmat c q i k - ∑ i, ∑ k, q k * gmat c q i k := by
      simp only [sub_mul, Finset.sum_sub_distrib]
    rw [e, hBA]
    ring
  have hle : ∑ i, ∑ k, (q i - q k) * gmat c q i k ≤
      ∑ i : Fin (M + 1), ∑ k, (if i = k then (0 : ℝ) else 2 * c) :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ => gmat_mul_le hc q i k))
  have hR2 : ∑ i : Fin (M + 1), ∑ k, (if i = k then (0 : ℝ) else 2 * c) =
      ((M : ℝ) + 1) * ((M : ℝ) * (2 * c)) := by
    simp only [sum_erase_const_eq]
    simp
  have hA : ∑ i, ∑ k, q i * gmat c q i k ≤ ((M : ℝ) + 1) * (M : ℝ) * c := by
    have e3 : ((M : ℝ) + 1) * ((M : ℝ) * (2 * c)) = 2 * (((M : ℝ) + 1) * (M : ℝ) * c) := by ring
    linarith [hle, hsplit2, hR2, e3]
  -- L Σ_j q_j d_j = A.
  have hLB : L * ∑ i, q i * (q i - pn L (n i)) = ∑ i, ∑ k, q i * gmat c q i k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    calc L * (q i * (q i - pn L (n i))) = q i * (L * (q i - pn L (n i))) := by ring
      _ = q i * ∑ k, gmat c q i k := by rw [hEd i]
      _ = ∑ k, q i * gmat c q i k := Finset.mul_sum _ _ _
  -- Σ d² = Σ q d - Σ p d ≤ Σ q d.
  have hkey : ∑ i, (q i - pn L (n i)) ^ 2 ≤ ∑ i, q i * (q i - pn L (n i)) := by
    have e : ∑ i, q i * (q i - pn L (n i)) =
        ∑ i, (q i - pn L (n i)) ^ 2 + ∑ i, pn L (n i) * (q i - pn L (n i)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    linarith
  have hMc : ((M : ℝ) + 1) * (M : ℝ) * c = (M : ℝ) * κ := by
    rw [hcdef]; push_cast; field_simp
  have hB : ∑ i, q i * (q i - pn L (n i)) ≤ (M : ℝ) * κ / L := by
    rw [le_div_iff₀ hL]
    linarith [hLB, hA, hMc]
  have hS : ∑ i, (q i - pn L (n i)) ^ 2 ≤ (M : ℝ) * κ / L := hkey.trans hB
  have hsum_eq : ∑ j, (q j - pn L (correctedInt ℓ j)) ^ 2 = ∑ j, (q j - pn L (n j)) ^ 2 :=
    Finset.sum_congr rfl (fun j _ => by rw [hndef])
  rw [hsum_eq]
  have hfin : (1 / ((M + 1 : ℕ) : ℝ)) * ∑ j, (q j - pn L (n j)) ^ 2 ≤
      (1 / ((M + 1 : ℕ) : ℝ)) * ((M : ℝ) * κ / L) :=
    mul_le_mul_of_nonneg_left hS (by positivity)
  refine hfin.trans (le_of_eq ?_)
  push_cast
  field_simp
  ring

/-- Identification of the on-shell configuration with the accepted root vector (R-4C8D7C9E):
the rapidities are the unique solution, equal to `BetheSmooth.roots`, and strictly increasing. -/
theorem onshell_identification {N : ℕ} {L κ : ℝ} (ℓ : LogLabels N) (q : Fin N → ℝ)
    (h : OnShellRepulsive L κ ℓ q) :
    q = BetheSmooth.roots L (correctedInt ℓ) (κ / N) ∧ StrictMono q := by
  obtain ⟨hN, hL, hκ, hq⟩ := h
  have hc : 0 < κ / (N : ℝ) := div_pos hκ (by exact_mod_cast hN)
  have hroots : q = BetheSmooth.roots L (correctedInt ℓ) (κ / N) :=
    (rapidityEq_iff_roots hL hc ℓ q).1 hq
  refine ⟨hroots, ?_⟩
  rw [hroots]
  exact roots_strictMono_labels hL hc ℓ


/-! ### Axiom audit (every declaration in this module) -/
#print axioms QuantumNLS.RootDisplacementEstimate.sum_antisymm_zero
#print axioms QuantumNLS.RootDisplacementEstimate.abel_prefix
#print axioms QuantumNLS.RootDisplacementEstimate.pref_eq_neg_tail
#print axioms QuantumNLS.RootDisplacementEstimate.abel_nonneg
#print axioms QuantumNLS.RootDisplacementEstimate.sum_fin_eq_sum_range
#print axioms QuantumNLS.RootDisplacementEstimate.abel_fin
#print axioms QuantumNLS.RootDisplacementEstimate.arctan_div_pos_eq
#print axioms QuantumNLS.RootDisplacementEstimate.arctan_div_neg_eq
#print axioms QuantumNLS.RootDisplacementEstimate.pair_identity
#print axioms QuantumNLS.RootDisplacementEstimate.mul_arctan_div_le
#print axioms QuantumNLS.RootDisplacementEstimate.gmat_self
#print axioms QuantumNLS.RootDisplacementEstimate.gmat_antisymm
#print axioms QuantumNLS.RootDisplacementEstimate.gmat_nonneg_of_lt
#print axioms QuantumNLS.RootDisplacementEstimate.gmat_mul_le
#print axioms QuantumNLS.RootDisplacementEstimate.sum_gmat_eq_erase
#print axioms QuantumNLS.RootDisplacementEstimate.card_filter_lt_fin
#print axioms QuantumNLS.RootDisplacementEstimate.card_filter_gt_fin
#print axioms QuantumNLS.RootDisplacementEstimate.sum_pi_ite_lt
#print axioms QuantumNLS.RootDisplacementEstimate.sum_pi_ite_gt
#print axioms QuantumNLS.RootDisplacementEstimate.count_erase
#print axioms QuantumNLS.RootDisplacementEstimate.bethe_printed
#print axioms QuantumNLS.RootDisplacementEstimate.tail_gmat_nonneg
#print axioms QuantumNLS.RootDisplacementEstimate.sum_erase_const_eq
#print axioms QuantumNLS.RootDisplacementEstimate.root_displacement_estimate
#print axioms QuantumNLS.RootDisplacementEstimate.onshell_identification

end QuantumNLS.RootDisplacementEstimate
