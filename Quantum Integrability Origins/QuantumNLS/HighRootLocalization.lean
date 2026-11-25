import QuantumNLS.UniformLabelDistance

/-!
# QG:prop:high-root-localization (R-9A585DC2): high roots are uniformly close to their free labels

Source: `source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex`, subsection `QG:sec:high-roots`
(lines 128-142: `ω = 2π/L`, `c = κ/N`, `QG:eq:our-bethe`, `QG:eq:our-global-root-bound` with
`D = 3√(κ/L)`), Proposition `QG:prop:high-root-localization` (lines 144-156) and its proof
(lines 157-221).

Statement: fix `E > 0`. There are constants `C_E`, `R_E` depending only on `L, κ, E` such that
for every `N`, every on-shell configuration (`RootContraction.IsActualConfig L (κ/N) n q`) with
`N^{-1} Σ_j q_j² ≤ E`, and every occurring label `n` with `|n| ≥ R_E`,
`|q_j − ωn| ≤ C_E/|ωn|` for every `j` with `n_j = n`.

The constants are the printed ones: `A = D + ω + 1`, `R_E = max(2A, 1)/ω` (i.e. `p = ωn ≥
max(2A, 1)`), `F_E(p) = 4κ/p + 8κE/(Ap²)`, `C_E = 4κ/L + 8κE/(LA) + 6√(κE/L)`.

Route (as printed): reduction to `n > 0` by simultaneous reflection (`reflect_actual`); the cluster
`J = {j : n_j ≤ n, q_j > p − A}` with `|J| ≤ 4EN/p²`; exterior forces split into negative ones
(larger labels) and left ones bounded by `F_E(p)` (split `|q_ℓ| ≤ p/2` / `> p/2`,
`0 < arctan(c/t) ≤ c/t`); the accepted small-cluster lemma (via `UniformLabelDistance.cluster_small`)
gives `QG:eq:high-upper`; the mirrored cluster `J' = {j : n_j ≥ n, q_j < p + A}` gives
`QG:eq:high-lower`.

Recorded deviations (none changes the statement): the two exterior groups are bounded termwise by
the single majorant `2c/p + [q_ℓ² > p²/4]·c/A` summed over all roots; the energy hypothesis is used
in the form `Σ q_j² ≤ N E`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset

namespace QuantumNLS.HighRootLocalization

open QuantumNLS.RootContraction QuantumNLS.UniformLabelDistance

variable {N : ℕ}

/-! ## 1. Counting and exterior-force estimates -/

/-- `#{ℓ : q_ℓ² > p²/4} ≤ 4EN/p²` from `Σ q² ≤ NE`. -/
lemma count_high (q : Fin N → ℝ) {E p : ℝ} (hp : 0 < p) (hE : ∑ l, q l ^ 2 ≤ N * E) :
    ((univ.filter fun l => p ^ 2 / 4 < q l ^ 2).card : ℝ) ≤ 4 * E * N / p ^ 2 := by
  have h1 : (univ.filter fun l => p ^ 2 / 4 < q l ^ 2).card * (p ^ 2 / 4) ≤ ∑ l, q l ^ 2 := by
    calc ((univ.filter fun l => p ^ 2 / 4 < q l ^ 2).card : ℝ) * (p ^ 2 / 4)
        = ∑ l ∈ univ.filter (fun l => p ^ 2 / 4 < q l ^ 2), p ^ 2 / 4 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ l ∈ univ.filter (fun l => p ^ 2 / 4 < q l ^ 2), q l ^ 2 :=
          Finset.sum_le_sum fun l hl => (Finset.mem_filter.mp hl).2.le
      _ ≤ ∑ l, q l ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun l _ _ => sq_nonneg _)
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- The termwise majorant of an exterior force. -/
def gmaj (c p A x : ℝ) : ℝ := 2 * c / p + (if p ^ 2 / 4 < x ^ 2 then c / A else 0)

lemma gmaj_nonneg {c p A : ℝ} (hc : 0 ≤ c) (hp : 0 < p) (hA : 0 < A) (x : ℝ) :
    0 ≤ gmaj c p A x := by
  unfold gmaj; split_ifs <;> positivity

/-- `arctan (c/t) ≤ gmaj` when `t ≥ p/2`, or `t ≥ A` and `x² > p²/4`. -/
lemma arctan_le_gmaj {c p A t x : ℝ} (hc : 0 ≤ c) (hp : 0 < p) (hA : 0 < A) (ht : 0 < t)
    (h : p / 2 ≤ t ∨ (A ≤ t ∧ p ^ 2 / 4 < x ^ 2)) : Real.arctan (c / t) ≤ gmaj c p A x := by
  have h0 : Real.arctan (c / t) ≤ c / t := Real.arctan_le_self (div_nonneg hc ht.le)
  unfold gmaj
  rcases h with h | ⟨h1, h2⟩
  · have : c / t ≤ 2 * c / p := by
      rw [div_le_div_iff₀ ht hp]; nlinarith
    split_ifs
    · have : 0 ≤ c / A := by positivity
      linarith
    · linarith
  · simp only [h2, ↓reduceIte]
    have : c / t ≤ c / A := div_le_div_of_nonneg_left hc hA h1
    have : 0 ≤ 2 * c / p := by positivity
    linarith

/-- Summing the majorant: `2 Σ_ℓ gmaj ≤ F_E(p)` at `c = κ/N`. -/
lemma sum_gmaj_le {κ E p A : ℝ} (hκ : 0 < κ) (hp : 0 < p) (hA : 0 < A) (hN : 1 ≤ N)
    (q : Fin N → ℝ) (hE : ∑ l, q l ^ 2 ≤ N * E) :
    2 * ∑ l, gmaj (κ / N) p A (q l) ≤ 4 * κ / p + 8 * κ * E / (A * p ^ 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hcnt := count_high q hp hE
  unfold gmaj
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have e1 : (N : ℝ) * (2 * (κ / N) / p) = 2 * κ / p := by field_simp
  rw [e1]
  have h2 : ((univ.filter fun l => p ^ 2 / 4 < q l ^ 2).card : ℝ) * (κ / N / A) ≤
      4 * E * N / p ^ 2 * (κ / N / A) :=
    mul_le_mul_of_nonneg_right hcnt (by positivity)
  have e2 : 4 * E * N / p ^ 2 * (κ / N / A) = 4 * κ * E / (A * p ^ 2) := by field_simp
  rw [e2] at h2
  have e3 : 2 * (2 * κ / p + 4 * κ * E / (A * p ^ 2)) = 4 * κ / p + 8 * κ * E / (A * p ^ 2) := by
    ring
  linarith

/-- `3 √(c |J| / L) ≤ 6 √(κE/L)/p` when `|J| ≤ 4EN/p²`, `c = κ/N`. -/
lemma cluster_sqrt_le {κ E L p : ℝ} (hκ : 0 < κ) (hE : 0 < E) (hL : 0 < L) (hp : 0 < p)
    (hN : 1 ≤ N) {k : ℕ} (hk : (k : ℝ) ≤ 4 * E * N / p ^ 2) :
    3 * Real.sqrt (κ / N * k / L) ≤ 6 * Real.sqrt (κ * E / L) / p := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hX : κ / N * k / L ≤ (2 * Real.sqrt (κ * E / L) / p) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
    have : κ / N * k ≤ κ / N * (4 * E * N / p ^ 2) := mul_le_mul_of_nonneg_left hk (by positivity)
    have e : κ / N * (4 * E * N / p ^ 2) / L = 2 ^ 2 * (κ * E / L) / p ^ 2 := by
      field_simp; ring
    calc κ / N * k / L ≤ κ / N * (4 * E * N / p ^ 2) / L := div_le_div_of_nonneg_right this hL.le
      _ = _ := e
  have := Real.sqrt_le_sqrt hX
  rw [Real.sqrt_sq (by positivity)] at this
  have e : 3 * (2 * Real.sqrt (κ * E / L) / p) = 6 * Real.sqrt (κ * E / L) / p := by ring
  linarith [mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 3)]

/-! ## 2. The positive case -/

/-- The printed constants. -/
def Dc (L κ : ℝ) : ℝ := 3 * Real.sqrt (κ / L)
def Ac (L κ : ℝ) : ℝ := Dc L κ + 2 * Real.pi / L + 1
def Fc (L κ E p : ℝ) : ℝ := 4 * κ / p + 8 * κ * E / (Ac L κ * p ^ 2)

lemma Ac_pos (L κ : ℝ) (hL : 0 < L) : 0 < Ac L κ := by
  unfold Ac Dc; have := Real.sqrt_nonneg (κ / L); have := Real.pi_pos; positivity

/-- **`QG:eq:high-upper`** for a label `n_j = n` with `p = ωn ≥ max(2A, 1)`. -/
theorem high_upper {L κ E : ℝ} (hL : 0 < L) (hκ : 0 < κ) (hE : 0 < E) {n : Fin N → ℤ}
    {q : Fin N → ℝ} (h : IsActualConfig L (κ / N) n q) (hen : ∑ l, q l ^ 2 ≤ N * E) (j0 : Fin N)
    (hp : max (2 * Ac L κ) 1 ≤ 2 * Real.pi / L * n j0) :
    q j0 ≤ 2 * Real.pi / L * n j0 + Fc L κ E (2 * Real.pi / L * n j0) / L +
      6 * Real.sqrt (κ * E / L) / (2 * Real.pi / L * n j0) := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (fun h0 => (h0 ▸ j0).elim0)
  set p := 2 * Real.pi / L * n j0 with hpdef
  set A := Ac L κ
  have hA : 0 < A := Ac_pos L κ hL
  have hp1 : 1 ≤ p := (le_max_right _ _).trans hp
  have hp2A : 2 * A ≤ p := (le_max_left _ _).trans hp
  have hp0 : 0 < p := by linarith
  set c := κ / (N : ℝ)
  have hc : 0 < c := h.c_pos
  set F := Fc L κ E p
  have hF : 0 ≤ F := by unfold F Fc; positivity
  have hDA : Dc L κ < A := by
    unfold A Ac; have := Real.pi_pos; have : 0 < 2 * Real.pi / L := by positivity
    linarith
  have hUL := uniform_label_distance hN hL hκ h
  set J := univ.filter fun l => n l ≤ n j0 ∧ p - A < q l
  have hj0 : j0 ∈ J := by
    refine Finset.mem_filter.mpr ⟨mem_univ _, le_rfl, ?_⟩
    have := (abs_le.mp (hUL j0)).1
    have e : 2 * Real.pi * n j0 / L = p := by rw [hpdef]; ring
    rw [e] at this
    unfold Dc at hDA
    linarith
  -- size of the cluster
  have hJcard : (J.card : ℝ) ≤ 4 * E * N / p ^ 2 := by
    refine le_trans ?_ (count_high q hp0 hen)
    exact_mod_cast Finset.card_le_card fun l hl => by
      have hl' := (Finset.mem_filter.mp hl).2.2
      refine Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩
      have : p / 2 < q l := by linarith
      nlinarith
  -- the force inequality on the cluster
  set y : Fin N → ℝ := fun l => q l - p - F / L
  have hyinj : Function.Injective y := fun l1 l2 h' => h.sorted.injective (by simp only [y] at h'; linarith)
  have hforce : ∀ l ∈ J, 0 < y l → L * y l ≤ 2 * ∑ m ∈ J.erase l, Real.arctan (c / (y l - y m)) := by
    intro l hl hyl
    obtain ⟨hnl, -⟩ := (Finset.mem_filter.mp hl).2
    have hql : p + F / L < q l := by simp only [y] at hyl; linarith
    have hFL : 0 ≤ F / L := div_nonneg hF hL.le
    have hB := h.bethe l
    have hsp := sum_split J (fun m => Real.arctan (c / (q l - q m))) hl
    have hext : ∑ m ∈ univ.filter (fun m => m ∉ J), Real.arctan (c / (q l - q m)) ≤
        ∑ m, gmaj c p A (q m) := by
      refine (Finset.sum_le_sum fun m hm => ?_).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun m _ _ => gmaj_nonneg hc.le hp0 hA _)
      have hmJ : m ∉ J := (Finset.mem_filter.mp hm).2
      simp only [J, mem_filter, mem_univ, true_and, not_and_or, not_le, not_lt] at hmJ
      rcases hmJ with hnm | hqm
      · have hlm : l < m := by
          by_contra hh; push Not at hh; have := h.labels_sorted hh; omega
        have : q l < q m := h.sorted hlm
        have : c / (q l - q m) < 0 := div_neg_of_pos_of_neg hc (by linarith)
        exact (Real.arctan_lt_zero.mpr this).le.trans (gmaj_nonneg hc.le hp0 hA _)
      · refine arctan_le_gmaj hc.le hp0 hA (by linarith) ?_
        by_cases hq : |q m| ≤ p / 2
        · left; have := (abs_le.mp hq).2; linarith
        · right
          push Not at hq
          refine ⟨by linarith, ?_⟩
          have : (p / 2) ^ 2 < |q m| ^ 2 := pow_lt_pow_left₀ hq (by positivity) two_ne_zero
          rw [sq_abs] at this; nlinarith
    have hsum : 2 * ∑ m, gmaj c p A (q m) ≤ F := sum_gmaj_le hκ hp0 hA hN q hen
    have hcl : ∑ m ∈ J.erase l, Real.arctan (c / (y l - y m)) =
        ∑ m ∈ J.erase l, Real.arctan (c / (q l - q m)) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [y]; rw [show q l - p - F / L - (q m - p - F / L) = q l - q m by ring]
    rw [hcl]
    have hnl' : 2 * Real.pi * (n l : ℝ) ≤ L * p := by
      have : (n l : ℝ) ≤ n j0 := by exact_mod_cast hnl
      rw [hpdef]; field_simp; nlinarith [Real.pi_pos]
    have hLF : L * (F / L) = F := by field_simp
    simp only [y]
    rw [mul_sub, mul_sub, hLF]
    linarith
  have hb := cluster_small hyinj hc hL hforce hj0
  have hk : 3 * Real.sqrt (c * J.card / L) ≤ 6 * Real.sqrt (κ * E / L) / p :=
    cluster_sqrt_le hκ hE hL hp0 hN hJcard
  have := le_max_left (y j0) 0
  simp only [y] at this
  linarith

/-- **`QG:eq:high-lower`** for a label `n_j = n` with `p = ωn ≥ max(2A, 1)`. -/
theorem high_lower {L κ E : ℝ} (hL : 0 < L) (hκ : 0 < κ) (hE : 0 < E) {n : Fin N → ℤ}
    {q : Fin N → ℝ} (h : IsActualConfig L (κ / N) n q) (hen : ∑ l, q l ^ 2 ≤ N * E) (j0 : Fin N)
    (hp : max (2 * Ac L κ) 1 ≤ 2 * Real.pi / L * n j0) :
    2 * Real.pi / L * n j0 - Fc L κ E (2 * Real.pi / L * n j0) / L -
      6 * Real.sqrt (κ * E / L) / (2 * Real.pi / L * n j0) ≤ q j0 := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (fun h0 => (h0 ▸ j0).elim0)
  set p := 2 * Real.pi / L * n j0 with hpdef
  set A := Ac L κ
  have hA : 0 < A := Ac_pos L κ hL
  have hp1 : 1 ≤ p := (le_max_right _ _).trans hp
  have hp2A : 2 * A ≤ p := (le_max_left _ _).trans hp
  have hp0 : 0 < p := by linarith
  set c := κ / (N : ℝ)
  have hc : 0 < c := h.c_pos
  set F := Fc L κ E p
  have hF : 0 ≤ F := by unfold F Fc; positivity
  have hω : 0 < 2 * Real.pi / L := by have := Real.pi_pos; positivity
  have hDA : Dc L κ < A := by
    unfold A Ac; linarith
  have hUL := uniform_label_distance hN hL hκ h
  set J := univ.filter fun l => n j0 ≤ n l ∧ q l < p + A
  have hj0 : j0 ∈ J := by
    refine Finset.mem_filter.mpr ⟨mem_univ _, le_rfl, ?_⟩
    have := (abs_le.mp (hUL j0)).2
    have e : 2 * Real.pi * n j0 / L = p := by rw [hpdef]; ring
    rw [e] at this
    unfold Dc at hDA
    linarith
  have hJcard : (J.card : ℝ) ≤ 4 * E * N / p ^ 2 := by
    refine le_trans ?_ (count_high q hp0 hen)
    exact_mod_cast Finset.card_le_card fun l hl => by
      have hnl := (Finset.mem_filter.mp hl).2.1
      refine Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩
      have h1 := (abs_le.mp (hUL l)).1
      have h2 : p ≤ 2 * Real.pi * n l / L := by
        have : (n j0 : ℝ) ≤ n l := by exact_mod_cast hnl
        rw [hpdef, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hL]
        nlinarith [Real.pi_pos]
      unfold Dc at hDA
      have : p / 2 < q l := by linarith
      nlinarith
  set y : Fin N → ℝ := fun l => p - q l - F / L
  have hyinj : Function.Injective y := fun l1 l2 h' =>
    h.sorted.injective (by simp only [y] at h'; linarith)
  have hforce : ∀ l ∈ J, 0 < y l → L * y l ≤ 2 * ∑ m ∈ J.erase l, Real.arctan (c / (y l - y m)) := by
    intro l hl hyl
    obtain ⟨hnl, -⟩ := (Finset.mem_filter.mp hl).2
    have hql : q l < p - F / L := by simp only [y] at hyl; linarith
    have hFL : 0 ≤ F / L := div_nonneg hF hL.le
    have hB := h.bethe l
    have hsp := sum_split J (fun m => Real.arctan (c / (q l - q m))) hl
    have hext : ∑ m ∈ univ.filter (fun m => m ∉ J), -Real.arctan (c / (q l - q m)) ≤
        ∑ m, gmaj c p A (q m) := by
      refine (Finset.sum_le_sum fun m hm => ?_).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun m _ _ => gmaj_nonneg hc.le hp0 hA _)
      have hmJ : m ∉ J := (Finset.mem_filter.mp hm).2
      simp only [J, mem_filter, mem_univ, true_and, not_and_or, not_le, not_lt] at hmJ
      rcases hmJ with hnm | hqm
      · have hml : m < l := by
          by_contra hh; push Not at hh; have := h.labels_sorted hh; omega
        have : q m < q l := h.sorted hml
        have : 0 < c / (q l - q m) := div_pos hc (by linarith)
        have := Real.arctan_pos.mpr this
        linarith [gmaj_nonneg hc.le hp0 hA (q m)]
      · rw [show -Real.arctan (c / (q l - q m)) = Real.arctan (c / (q m - q l)) by
          rw [← Real.arctan_neg, ← div_neg, neg_sub]]
        refine arctan_le_gmaj hc.le hp0 hA (by linarith) (Or.inr ⟨by linarith, ?_⟩)
        have : p / 2 < q m := by linarith
        nlinarith
    have hsum : 2 * ∑ m, gmaj c p A (q m) ≤ F := sum_gmaj_le hκ hp0 hA hN q hen
    have hcl : ∑ m ∈ J.erase l, Real.arctan (c / (y l - y m)) =
        -∑ m ∈ J.erase l, Real.arctan (c / (q l - q m)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [y]
      rw [show p - q l - F / L - (p - q m - F / L) = -(q l - q m) by ring, div_neg, Real.arctan_neg]
    rw [hcl]
    rw [Finset.sum_neg_distrib] at hext
    have hnl' : L * p ≤ 2 * Real.pi * (n l : ℝ) := by
      have : (n j0 : ℝ) ≤ n l := by exact_mod_cast hnl
      rw [hpdef]; field_simp; nlinarith [Real.pi_pos]
    have hLF : L * (F / L) = F := by field_simp
    simp only [y]
    rw [mul_sub, mul_sub, hLF]
    linarith
  have hb := cluster_small hyinj hc hL hforce hj0
  have hk : 3 * Real.sqrt (c * J.card / L) ≤ 6 * Real.sqrt (κ * E / L) / p :=
    cluster_sqrt_le hκ hE hL hp0 hN hJcard
  have := le_max_left (y j0) 0
  simp only [y] at this
  linarith

/-! ## 3. Reflection and the proposition -/

lemma sum_erase_eq_sum {c : ℝ} (x : Fin N → ℝ) (j : Fin N) :
    ∑ m ∈ univ.erase j, Real.arctan (c / (x j - x m)) = ∑ m, Real.arctan (c / (x j - x m)) :=
  Finset.sum_erase _ (by simp)

/-- Simultaneous reflection of roots and labels preserves `QG:eq:our-bethe`. -/
lemma reflect_actual {L c : ℝ} {n : Fin N → ℤ} {q : Fin N → ℝ} (h : IsActualConfig L c n q) :
    IsActualConfig L c (fun j => -n (Fin.rev j)) (fun j => -q (Fin.rev j)) where
  c_pos := h.c_pos
  sorted := fun i j hij => by
    simp only [neg_lt_neg_iff]; exact h.sorted (Fin.rev_lt_rev.mpr hij)
  labels_sorted := fun i j hij => by
    simp only [neg_le_neg_iff]; exact h.labels_sorted (Fin.rev_le_rev.mpr hij)
  bethe := by
    intro j
    have hB := h.bethe (Fin.rev j)
    rw [sum_erase_eq_sum] at hB
    rw [sum_erase_eq_sum (x := fun j => -q (Fin.rev j))]
    have e : ∑ m, Real.arctan (c / (-q (Fin.rev j) - -q (Fin.rev m))) =
        -∑ k, Real.arctan (c / (q (Fin.rev j) - q k)) := by
      rw [← Finset.sum_neg_distrib]
      refine Fintype.sum_equiv Fin.revPerm _ _ fun m => ?_
      simp only [Fin.revPerm_apply]
      rw [show -q (Fin.rev j) - -q (Fin.rev m) = -(q (Fin.rev j) - q (Fin.rev m)) by ring,
        div_neg, Real.arctan_neg]
    rw [e]
    push_cast
    linarith

/-- The printed constant `C_E`. -/
def CE (L κ E : ℝ) : ℝ := 4 * κ / L + 8 * κ * E / (L * Ac L κ) + 6 * Real.sqrt (κ * E / L)

/-- The printed threshold `R_E` (`ωn ≥ max(2A, 1)`). -/
def RE (L κ : ℝ) : ℝ := max (2 * Ac L κ) 1 / (2 * Real.pi / L)

/-- The positive case: `|q_j − p| ≤ C_E/p` for `p = ωn_j ≥ max(2A, 1)`. -/
lemma pos_case {L κ E : ℝ} (hL : 0 < L) (hκ : 0 < κ) (hE : 0 < E) {n : Fin N → ℤ}
    {q : Fin N → ℝ} (h : IsActualConfig L (κ / N) n q) (hen : ∑ l, q l ^ 2 ≤ N * E) (j0 : Fin N)
    (hp : max (2 * Ac L κ) 1 ≤ 2 * Real.pi / L * n j0) :
    |q j0 - 2 * Real.pi / L * n j0| ≤ CE L κ E / (2 * Real.pi / L * n j0) := by
  have hu := high_upper hL hκ hE h hen j0 hp
  have hl := high_lower hL hκ hE h hen j0 hp
  set p := 2 * Real.pi / L * n j0
  have hA := Ac_pos L κ hL
  have hp1 : 1 ≤ p := (le_max_right _ _).trans hp
  have hp0 : 0 < p := by linarith
  have hFL : Fc L κ E p / L ≤ (4 * κ / L + 8 * κ * E / (L * Ac L κ)) / p := by
    unfold Fc
    have h1 : 8 * κ * E / (Ac L κ * p ^ 2) ≤ 8 * κ * E / (Ac L κ * p) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have : p ≤ p ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left this hA.le
    have e : (4 * κ / p + 8 * κ * E / (Ac L κ * p)) / L =
        (4 * κ / L + 8 * κ * E / (L * Ac L κ)) / p := by field_simp
    calc Fc L κ E p / L = (4 * κ / p + 8 * κ * E / (Ac L κ * p ^ 2)) / L := rfl
      _ ≤ (4 * κ / p + 8 * κ * E / (Ac L κ * p)) / L := by gcongr
      _ = _ := e
  have hC : Fc L κ E p / L + 6 * Real.sqrt (κ * E / L) / p ≤ CE L κ E / p := by
    unfold CE
    rw [add_div (4 * κ / L + 8 * κ * E / (L * Ac L κ))]
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- **QG:prop:high-root-localization** (R-9A585DC2). For `E > 0` there are `C_E`, `R_E`
(depending only on `L, κ, E`) such that for every `N`, every on-shell configuration with
`N^{-1} Σ q_j² ≤ E`, and every `j` whose label satisfies `|n_j| ≥ R_E`,
`|q_j − ωn_j| ≤ C_E/|ωn_j|`, `ω = 2π/L`. -/
theorem high_root_localization {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) (E : ℝ) (hE : 0 < E) :
    ∃ C R : ℝ, 0 < R ∧ ∀ (N : ℕ) (n : Fin N → ℤ) (q : Fin N → ℝ),
      IsActualConfig L (κ / N) n q → (N : ℝ)⁻¹ * ∑ j, q j ^ 2 ≤ E →
      ∀ j, R ≤ |(n j : ℝ)| →
        |q j - 2 * Real.pi / L * n j| ≤ C / |2 * Real.pi / L * n j| := by
  have hω : 0 < 2 * Real.pi / L := by have := Real.pi_pos; positivity
  refine ⟨CE L κ E, RE L κ, div_pos (lt_max_of_lt_right one_pos) hω, ?_⟩
  intro N n q h hE' j hR
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (fun h0 => (h0 ▸ j).elim0)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hen : ∑ l, q l ^ 2 ≤ N * E := by
    rw [inv_mul_le_iff₀ hN0] at hE'; exact hE'
  have hR' : max (2 * Ac L κ) 1 ≤ 2 * Real.pi / L * |(n j : ℝ)| := by
    unfold RE at hR; rw [div_le_iff₀ hω] at hR; linarith
  have hRpos : 0 < RE L κ := div_pos (lt_max_of_lt_right one_pos) hω
  rcases lt_or_gt_of_ne (show (n j : ℝ) ≠ 0 by
    intro h0; rw [h0, abs_zero] at hR; linarith) with hneg | hpos
  · -- reflection
    have hr := reflect_actual h
    have hen' : ∑ l, (-q (Fin.rev l)) ^ 2 ≤ N * E := by
      have : ∑ l, (-q (Fin.rev l)) ^ 2 = ∑ l, q l ^ 2 :=
        Fintype.sum_equiv Fin.revPerm _ _ fun l => by simp
      rw [this]; exact hen
    have hp : max (2 * Ac L κ) 1 ≤ 2 * Real.pi / L * ((-n (Fin.rev (Fin.rev j)) : ℤ) : ℝ) := by
      rw [Fin.rev_rev, abs_of_neg hneg] at *
      push_cast; linarith
    have := pos_case hL hκ hE hr hen' (Fin.rev j) hp
    simp only [Fin.rev_rev] at this
    push_cast at this
    rw [abs_of_neg (mul_neg_of_pos_of_neg hω hneg)]
    rw [show |q j - 2 * Real.pi / L * n j| = |-q j - 2 * Real.pi / L * -(n j : ℝ)| by
      rw [← abs_neg]; congr 1; ring]
    rw [show -(2 * Real.pi / L * (n j : ℝ)) = 2 * Real.pi / L * -(n j : ℝ) by ring]
    exact this
  · have hp : max (2 * Ac L κ) 1 ≤ 2 * Real.pi / L * n j := by
      rw [abs_of_pos hpos] at hR'; exact hR'
    rw [abs_of_pos (mul_pos hω hpos)]
    exact pos_case hL hκ hE h hen j hp

/-! Kernel axiom audit (checkpoint HR1). -/
#print axioms count_high
#print axioms gmaj_nonneg
#print axioms arctan_le_gmaj
#print axioms sum_gmaj_le
#print axioms cluster_sqrt_le
#print axioms Ac_pos
#print axioms high_lower
#print axioms sum_erase_eq_sum
#print axioms reflect_actual
#print axioms pos_case
#print axioms high_root_localization
#print axioms high_upper

end QuantumNLS.HighRootLocalization
