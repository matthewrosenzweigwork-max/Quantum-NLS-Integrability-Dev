import QuantumNLS.OrderComparison

/-!
# CC:F01:response (R-9D98846E): adjacent response with vacancies retained

Source: `source/chapters/root_response/F01.tex`, standing assumptions (lines 4-18: `L, c > 0`,
`N ≥ 1`, Bose labels `n_1 ≤ ⋯ ≤ n_N`, repulsive roots `q_1 < ⋯ < q_N`, the map `T`), Theorem
`CC:F01:response` (lines 40-67) and its proof (lines 68-94).

Occupation conventions (DEF-006, accepted `BetheLabels`): an occupation vector of total `N` is
`η : MArr N` (`ℤ →₀ ℕ` with `Σ η_n = N`); its ordered Bose labels are
`labs η = correctedInt (labelsEquivArr.symm η)` (nondecreasing, with multiplicities `η`), and its
ordered roots are `arrRoots L c η = roots L (labs η) c` (R-4C8D7C9E).

Lean indices are zero based: the source's rank `C_k` (one based) is the Lean index `i` with
`i + 1 = C_k`, and `e_{C_k}` is the indicator of that index. `Σ_{k=b}^{a-1} e_{C_k}` is
`rankVec η b a i = Σ_{k ∈ [b, a)} [i + 1 = C_k]`, which keeps every `C_k` with its multiplicity.

Route (as printed): the cumulative counts (`labs_le_iff`, `Ccum_transfer`), the indicator identity
and its sum (`label_shift`: `ñ_i − n_i = Σ_{k=b}^{a−1} [i = C_k]`), subtraction of `CC:F01:smooth`
(`Tmap_diff`), Lemma `CC:F01:comparison` (accepted-in-review OC1: sign, column sums), symmetry of
`B^{-1}` and `Q_2(m) − Q_2(η) = (q + q̃)ᵀ(q̃ − q)`, the rank localisation, and the reversed
transfer via `B` being unchanged by reversing the segment (`avgJac_symm_segment`).
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open Finset

namespace QuantumNLS.AdjacentResponse

open QuantumNLS.BetheLabels QuantumNLS.BetheSmooth QuantumNLS.RootContraction
open QuantumNLS.OrderComparison QuantumNLS.GaudinResponse

variable {N : ℕ}

/-! ## 1. Occupation vectors, ordered labels and cumulative counts -/

/-- The ordered Bose labels of an occupation vector (DEF-006). -/
def labs (μ : MArr N) : Fin N → ℤ := correctedInt (labelsEquivArr.symm μ)

lemma labs_mono (μ : MArr N) : Monotone (labs μ) := correctedInt_monotone _

lemma count_labs (μ : MArr N) (l : ℤ) : (μ.1 l : ℕ) = (univ.filter fun j => labs μ j = l).card := by
  have := labelsEquivArr_apply (labelsEquivArr.symm μ) l
  rwa [Equiv.apply_symm_apply] at this

/-- The printed cumulative count `C_k = Σ_{ℓ ≤ k} μ_ℓ`. -/
def Ccum (μ : MArr N) (k : ℤ) : ℕ := ∑ l ∈ μ.1.support.filter (· ≤ k), μ.1 l

/-- `C_k` counts the labels `≤ k`. -/
lemma Ccum_eq_card (μ : MArr N) (k : ℤ) :
    Ccum μ k = (univ.filter fun j => labs μ j ≤ k).card := by
  rw [Finset.card_eq_sum_card_image (labs μ)]
  unfold Ccum
  have himg : (univ.filter fun j => labs μ j ≤ k).image (labs μ) = μ.1.support.filter (· ≤ k) := by
    ext l
    simp only [mem_image, mem_filter, mem_univ, true_and, Finsupp.mem_support_iff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨?_, hj⟩
      rw [count_labs]
      exact Finset.card_ne_zero.mpr ⟨j, by simp⟩
    · rintro ⟨h1, h2⟩
      rw [count_labs] at h1
      obtain ⟨j, hj⟩ := Finset.card_ne_zero.mp h1
      exact ⟨j, by simp only [mem_filter, mem_univ, true_and] at hj; rw [hj]; exact h2,
        by simp only [mem_filter, mem_univ, true_and] at hj; exact hj⟩
  rw [himg]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [count_labs]
  congr 1
  ext j
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro rfl; exact ⟨(Finset.mem_filter.mp hl).2, rfl⟩
  · rintro ⟨-, h⟩; exact h

/-- For a monotone array the set `{j : n_j ≤ k}` is an initial segment: `n_i ≤ k ↔ i < C`. -/
lemma le_iff_lt_card {n : Fin N → ℤ} (hn : Monotone n) (i : Fin N) (k : ℤ) :
    n i ≤ k ↔ i.val < (univ.filter fun j => n j ≤ k).card := by
  constructor
  · intro h
    have hsub : (univ.filter fun j : Fin N => j ≤ i) ⊆ univ.filter fun j => n j ≤ k := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj ⊢
      exact (hn hj).trans h
    have hc : (univ.filter fun j : Fin N => j ≤ i).card = i.val + 1 := by
      rw [Finset.filter_ge_eq_Iic, Fin.card_Iic]
    have := Finset.card_le_card hsub
    omega
  · intro h
    by_contra hk
    push Not at hk
    have hsub : (univ.filter fun j => n j ≤ k) ⊆ univ.filter fun j : Fin N => j < i := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj ⊢
      by_contra hji
      push Not at hji
      have := hn hji
      omega
    have hc : (univ.filter fun j : Fin N => j < i).card = i.val := by
      rw [Finset.filter_gt_eq_Iio, Fin.card_Iio]
    have := Finset.card_le_card hsub
    omega

lemma labs_le_iff (μ : MArr N) (i : Fin N) (k : ℤ) : labs μ i ≤ k ↔ i.val < Ccum μ k := by
  rw [Ccum_eq_card]; exact le_iff_lt_card (labs_mono μ) i k

lemma Ccum_mono (μ : MArr N) {k k' : ℤ} (h : k ≤ k') : Ccum μ k ≤ Ccum μ k' := by
  rw [Ccum_eq_card, Ccum_eq_card]
  exact Finset.card_le_card fun j hj => by
    simp only [mem_filter, mem_univ, true_and] at hj ⊢; exact hj.trans h

lemma Ccum_le_N (μ : MArr N) (k : ℤ) : Ccum μ k ≤ N := by
  rw [Ccum_eq_card]
  exact (Finset.card_le_univ _).trans (by simp)

/-- The jump at `b`: `C_{b−1} + μ_b ≤ C_k` for `k ≥ b`. -/
lemma Ccum_jump (μ : MArr N) {b k : ℤ} (h : b ≤ k) : Ccum μ (b - 1) + μ.1 b ≤ Ccum μ k := by
  rw [Ccum_eq_card, Ccum_eq_card, count_labs]
  rw [← Finset.card_union_of_disjoint]
  · refine Finset.card_le_card fun j hj => ?_
    simp only [mem_union, mem_filter, mem_univ, true_and] at hj ⊢
    rcases hj with hj | hj <;> omega
  · rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    omega

/-- Sum of an occupation vector over any finite set containing its support. -/
lemma Ccum_eq_sum (μ : MArr N) (F : Finset ℤ) (hF : μ.1.support ⊆ F) (k : ℤ) :
    (Ccum μ k : ℤ) = ∑ l ∈ F.filter (· ≤ k), (μ.1 l : ℤ) := by
  unfold Ccum
  push_cast
  refine Finset.sum_subset (fun l hl => ?_) (fun l hl hl' => ?_)
  · simp only [mem_filter] at hl ⊢; exact ⟨hF hl.1, hl.2⟩
  · simp only [mem_filter, Finsupp.mem_support_iff, not_and] at hl hl'
    have h0 : μ.1 l = 0 := by
      by_contra h; exact hl' h hl.2
    rw [h0]; simp

/-! ## 2. The adjacent transfer `m = η − e_b + e_a` -/

lemma sum_tsub_single (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) :
    ((η.1 - Finsupp.single b 1) + Finsupp.single b 1) = η.1 := by
  ext l
  simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
  split_ifs with h
  · subst h; omega
  · omega

lemma transfer_sum (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) (a : ℤ) :
    ((η.1 - Finsupp.single b 1 + Finsupp.single a 1).sum fun _ k => k) = N := by
  have h0 := η.2
  have hadd : ∀ f g : ℤ →₀ ℕ, ((f + g).sum fun _ k => k) = (f.sum fun _ k => k) + g.sum fun _ k => k :=
    fun f g => Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)
  have h1 := hadd (η.1 - Finsupp.single b 1) (Finsupp.single b 1)
  rw [sum_tsub_single η hb, h0, Finsupp.sum_single_index rfl] at h1
  rw [hadd, Finsupp.sum_single_index rfl]
  omega

/-- The transferred occupation vector `m = η − e_b + e_a` (requires `η_b ≥ 1`). -/
def transfer (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) (a : ℤ) : MArr N :=
  ⟨η.1 - Finsupp.single b 1 + Finsupp.single a 1, transfer_sum η hb a⟩

lemma transfer_apply (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) (a l : ℤ) :
    ((transfer η hb a).1 l : ℤ) = η.1 l - (if l = b then 1 else 0) + (if l = a then 1 else 0) := by
  simp only [transfer, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
    Finsupp.single_apply]
  split_ifs with h1 h2 h2 <;> subst_vars <;> push_cast [Nat.cast_sub hb] <;> omega

/-- `C̃_k = C_k − [b ≤ k] + [a ≤ k]`. -/
lemma Ccum_transfer (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) (a k : ℤ) :
    (Ccum (transfer η hb a) k : ℤ) =
      Ccum η k - (if b ≤ k then 1 else 0) + (if a ≤ k then 1 else 0) := by
  set F := η.1.support ∪ {a, b}
  have hF1 : η.1.support ⊆ F := Finset.subset_union_left
  have hF2 : (transfer η hb a).1.support ⊆ F := by
    intro l hl
    rw [Finsupp.mem_support_iff] at hl
    by_cases hla : l = a
    · simp [F, hla]
    · by_cases hlb : l = b
      · simp [F, hlb]
      · have := transfer_apply η hb a l
        simp only [hlb, hla, ↓reduceIte] at this
        apply Finset.mem_union_left
        rw [Finsupp.mem_support_iff]
        intro h0; rw [h0] at this; push_cast at this
        exact hl (by exact_mod_cast this)
  rw [Ccum_eq_sum _ F hF2, Ccum_eq_sum _ F hF1]
  simp_rw [transfer_apply]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hb' : b ∈ F := by simp [F]
  have ha' : a ∈ F := by simp [F]
  rw [Finset.sum_ite_eq' (F.filter (· ≤ k)), Finset.sum_ite_eq' (F.filter (· ≤ k))]
  simp only [mem_filter, hb', ha', true_and]

/-! ## 3. The label shift `ñ_i − n_i = Σ_{k=b}^{a−1} [i = C_k]` -/

lemma sum_ind_le (u M1 M2 : ℤ) (h1 : M1 ≤ u) (h2 : u ≤ M2) :
    ∑ k ∈ Finset.Ico M1 M2, (if u ≤ k then (1 : ℤ) else 0) = M2 - u := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  have : (Finset.Ico M1 M2).filter (fun k => u ≤ k) = Finset.Ico u M2 := by
    ext k; simp only [mem_filter, mem_Ico]; omega
  rw [this, Int.card_Ico]
  omega

/-- **The label shift** (printed indicator identity summed over `k`). -/
theorem label_shift (η : MArr N) {b a : ℤ} (hb : 1 ≤ η.1 b) (hab : b < a) (i : Fin N) :
    (labs (transfer η hb a) i : ℤ) - labs η i =
      ∑ k ∈ Finset.Ico b a, (if (i.val : ℤ) + 1 = Ccum η k then 1 else 0) := by
  set u := labs η i
  set v := labs (transfer η hb a) i
  set M1 := min (min u v) b
  set M2 := max (max u v) a
  have hind : ∀ k : ℤ, ((if u ≤ k then (1 : ℤ) else 0) - if v ≤ k then 1 else 0) =
      if b ≤ k ∧ k < a ∧ (i.val : ℤ) + 1 = Ccum η k then 1 else 0 := by
    intro k
    have hu : u ≤ k ↔ (i.val : ℤ) < Ccum η k := by
      rw [labs_le_iff η i k]; exact_mod_cast Iff.rfl
    have hv : v ≤ k ↔ (i.val : ℤ) < Ccum (transfer η hb a) k := by
      rw [labs_le_iff _ i k]; exact_mod_cast Iff.rfl
    have hC := Ccum_transfer η hb a k
    have hJ : b ≤ k → 1 ≤ (Ccum η k : ℤ) := fun h => by
      have := Ccum_jump η h; omega
    split_ifs at hC ⊢ <;> omega
  have h1 := sum_ind_le u M1 M2 (by omega) (by omega)
  have h2 := sum_ind_le v M1 M2 (by omega) (by omega)
  have hsum : v - u = ∑ k ∈ Finset.Ico M1 M2,
      (if b ≤ k ∧ k < a ∧ (i.val : ℤ) + 1 = Ccum η k then (1 : ℤ) else 0) := by
    rw [← Finset.sum_congr rfl fun k _ => hind k, Finset.sum_sub_distrib, h1, h2]; ring
  rw [hsum, ← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_Ico]
  omega

/-! ## 4. The response formulas -/

variable {L c : ℝ}

/-- `Σ_{k=b}^{a−1} e_{C_k}`, ranks repeated with their multiplicities (zero-based index `i`
stands for the rank `i + 1`). -/
def rankVec (η : MArr N) (b a : ℤ) (i : Fin N) : ℝ :=
  ∑ k ∈ Finset.Ico b a, (if (i.val : ℤ) + 1 = Ccum η k then 1 else 0)

lemma rankVec_eq (η : MArr N) {b a : ℤ} (hb : 1 ≤ η.1 b) (hab : b < a) (i : Fin N) :
    rankVec η b a i = (labs (transfer η hb a) i : ℝ) - labs η i := by
  have h := label_shift η hb hab i
  have h' : ((labs (transfer η hb a) i - labs η i : ℤ) : ℝ) =
      ((∑ k ∈ Finset.Ico b a, (if (i.val : ℤ) + 1 = Ccum η k then (1 : ℤ) else 0) : ℤ) : ℝ) := by
    rw [h]
  push_cast at h'
  unfold rankVec
  rw [h']

lemma rankVec_nonneg (η : MArr N) (b a : ℤ) (i : Fin N) : 0 ≤ rankVec η b a i :=
  Finset.sum_nonneg fun k _ => by split_ifs <;> norm_num

/-- `Σ_i [i + 1 = C] = 1` for `1 ≤ C ≤ N`. -/
lemma sum_rank_ind {C : ℕ} (h1 : 1 ≤ C) (h2 : C ≤ N) :
    ∑ i : Fin N, (if (i.val : ℤ) + 1 = C then (1 : ℝ) else 0) = 1 := by
  rw [Finset.sum_eq_single (⟨C - 1, by omega⟩ : Fin N)]
  · simp only [show ((C - 1 : ℕ) : ℤ) + 1 = C by omega, ↓reduceIte]
  · intro j _ hj
    have : ¬ ((j.val : ℤ) + 1 = C) := by
      intro h; apply hj; ext; simp only; omega
    simp only [this, ↓reduceIte]
  · intro h; exact absurd (mem_univ _) h

lemma sum_rankVec (η : MArr N) {b a : ℤ} (hb : 1 ≤ η.1 b) (hab : b < a) :
    ∑ i, rankVec η b a i = (a - b : ℝ) := by
  unfold rankVec
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun k hk => sum_rank_ind (C := Ccum η k)
    (by have := Ccum_jump η (Finset.mem_Ico.mp hk).1; omega) (Ccum_le_N η k)]
  rw [Finset.sum_const, Int.card_Ico, nsmul_eq_mul, mul_one]
  rw [show ((a - b).toNat : ℝ) = ((a - b : ℤ) : ℝ) from by
    exact_mod_cast Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ a - b)]
  push_cast; ring

/-- Subtracting `CC:F01:smooth`: `T(q̃) − T(q) = 2π (ñ − n)`. -/
lemma Tmap_diff (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b a : ℤ} (hb : 1 ≤ η.1 b) (hab : b < a)
    (i : Fin N) :
    Tsmooth L c (arrRoots L c (transfer η hb a)) i - Tsmooth L c (arrRoots L c η) i =
      2 * Real.pi * rankVec η b a i := by
  have h1 := log_equation (isActual_roots hL hc (labs_mono (transfer η hb a))) i
  have h2 := log_equation (isActual_roots hL hc (labs_mono η)) i
  rw [rankVec_eq η hb hab i]
  show Tmap L c (roots L (labs (transfer η hb a)) c) i - Tmap L c (roots L (labs η) c) i = _
  rw [h1, h2]; ring

/-- `B (q̃ − q) = 2π Σ_{k=b}^{a−1} e_{C_k}`. -/
lemma B_response (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b a : ℤ} (hb : 1 ≤ η.1 b) (hab : b < a) :
    avgJac L c (arrRoots L c η) (arrRoots L c (transfer η hb a)) *ᵥ
      (arrRoots L c (transfer η hb a) - arrRoots L c η) = (2 * Real.pi) • rankVec η b a := by
  funext i
  rw [avgJac_response hc, Tmap_diff hL hc η hb hab, Pi.smul_apply, smul_eq_mul]

/-- **`CC:F01:root-response`** (identity part): `q̃ − q = 2π B^{-1} Σ_{k=b}^{a−1} e_{C_k}`. -/
theorem root_response (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b a : ℤ} (hb : 1 ≤ η.1 b)
    (hab : b < a) :
    arrRoots L c (transfer η hb a) - arrRoots L c η =
      (2 * Real.pi) • ((avgJac L c (arrRoots L c η) (arrRoots L c (transfer η hb a)))⁻¹ *ᵥ
        rankVec η b a) := by
  set B := avgJac L c (arrRoots L c η) (arrRoots L c (transfer η hb a))
  have hu := avgJac_isUnit_det hL hc (arrRoots L c η) (arrRoots L c (transfer η hb a))
  rw [← Matrix.mulVec_smul, ← B_response hL hc η hb hab, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

/-- **`CC:F01:root-response`** (sign part): `q̃ − q ≥ 0`. -/
theorem root_response_nonneg (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b a : ℤ}
    (hb : 1 ≤ η.1 b) (hab : b < a) (i : Fin N) :
    arrRoots L c η i ≤ arrRoots L c (transfer η hb a) i := by
  have h := avgJac_nonneg_of_nonneg hL hc (arrRoots L c η) (arrRoots L c (transfer η hb a))
    (arrRoots L c (transfer η hb a) - arrRoots L c η) (fun j => by
      rw [B_response hL hc η hb hab, Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (by positivity) (rankVec_nonneg η b a j)) i
  simp only [Pi.sub_apply] at h
  linarith

/-- **`CC:F01:l1`**: `‖q̃ − q‖₁ = 2π (a − b)/L`. -/
theorem l1_response (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b a : ℤ} (hb : 1 ≤ η.1 b)
    (hab : b < a) :
    ∑ i, |arrRoots L c (transfer η hb a) i - arrRoots L c η i| = 2 * Real.pi / L * (a - b) := by
  set q := arrRoots L c η
  set qt := arrRoots L c (transfer η hb a)
  set B := avgJac L c q qt
  have habs : ∀ i, |qt i - q i| = qt i - q i := fun i =>
    abs_of_nonneg (sub_nonneg.mpr (root_response_nonneg hL hc η hb hab i))
  simp_rw [habs]
  have hr := root_response hL hc η hb hab
  have e : ∀ i, qt i - q i = 2 * Real.pi * (B⁻¹ *ᵥ rankVec η b a) i := fun i => by
    have := congrFun hr i
    simpa using this
  simp_rw [e]
  rw [← Finset.mul_sum]
  have hcol : ∑ i, (B⁻¹ *ᵥ rankVec η b a) i = (1 / L) * ∑ k, rankVec η b a k := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_mul, avgJac_inv_col_sum hL hc q qt k]
  rw [hcol, sum_rankVec η hb hab]
  ring

/-- **`CC:F01:energy-response`**: `Q_2(m) − Q_2(η) = 2π Σ_{k=b}^{a−1} [B^{-1}(q + q̃)]_{C_k}`. -/
theorem energy_response (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b a : ℤ} (hb : 1 ≤ η.1 b)
    (hab : b < a) :
    ∑ i, arrRoots L c (transfer η hb a) i ^ 2 - ∑ i, arrRoots L c η i ^ 2 =
      2 * Real.pi * ∑ k ∈ Finset.Ico b a, ∑ i : Fin N,
        (if (i.val : ℤ) + 1 = Ccum η k then
          ((avgJac L c (arrRoots L c η) (arrRoots L c (transfer η hb a)))⁻¹ *ᵥ
            (arrRoots L c η + arrRoots L c (transfer η hb a))) i else 0) := by
  set q := arrRoots L c η
  set qt := arrRoots L c (transfer η hb a)
  set B := avgJac L c q qt
  have hsym : (B⁻¹)ᵀ = B⁻¹ := by rw [Matrix.transpose_nonsing_inv, avgJac_transpose hc]
  have hQ : ∑ i, qt i ^ 2 - ∑ i, q i ^ 2 = (q + qt) ⬝ᵥ (qt - q) := by
    unfold dotProduct
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [hQ, root_response hL hc η hb hab, dotProduct_smul, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, hsym, smul_eq_mul]
  congr 1
  unfold dotProduct rankVec
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

/-- **Rank localisation**: at every rank `C_k` (`b ≤ k < a`) both the old and the new Bose labels
lie in `[b, a]`. -/
theorem rank_labels (η : MArr N) {b a : ℤ} (hb : 1 ≤ η.1 b) (hab : b < a) {k : ℤ}
    (hk : k ∈ Finset.Ico b a) (i : Fin N) (hi : (i.val : ℤ) + 1 = Ccum η k) :
    b ≤ labs η i ∧ labs η i ≤ a ∧ b ≤ labs (transfer η hb a) i ∧
      labs (transfer η hb a) i ≤ a := by
  obtain ⟨hbk, hka⟩ := Finset.mem_Ico.mp hk
  have h1 : labs η i ≤ k := (labs_le_iff η i k).mpr (by omega)
  have h2 : b ≤ labs η i := by
    by_contra h
    push Not at h
    have := (labs_le_iff η i (b - 1)).mp (by omega)
    have hj := Ccum_jump η hbk
    omega
  have h3 : labs η i ≤ labs (transfer η hb a) i := by
    have := label_shift η hb hab i
    have h0 : 0 ≤ ∑ k ∈ Finset.Ico b a, (if (i.val : ℤ) + 1 = Ccum η k then (1 : ℤ) else 0) :=
      Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    omega
  have h4 : labs (transfer η hb a) i ≤ a := by
    rw [labs_le_iff]
    have hC := Ccum_transfer η hb a a
    simp only [hab.le, le_refl, ↓reduceIte] at hC
    have hm := Ccum_mono η hka.le
    omega
  exact ⟨h2, by omega, by omega, h4⟩

/-! ## 5. The reversed transfer `a < b` -/

/-- `B` is unchanged by reversing the line segment. -/
theorem avgJac_segment_symm (L c : ℝ) (x y : Fin N → ℝ) : avgJac L c x y = avgJac L c y x := by
  ext i k
  unfold avgJac Bavg
  simp only [Matrix.of_apply]
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
    (fun t => OrderedResponse.Bmat L c (fun j => y j + t * (x j - y j)) i k) (1 : ℝ)
  simp only [sub_zero, sub_self] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun t _ => ?_
  congr 2
  funext j
  ring

lemma transfer_receiver (η : MArr N) {b a : ℤ} (hb : 1 ≤ η.1 b) (hab : a ≠ b) :
    1 ≤ (transfer η hb a).1 a := by
  have := transfer_apply η hb a a
  simp only [hab, ↓reduceIte] at this
  omega

lemma transfer_transfer (η : MArr N) {b a : ℤ} (hb : 1 ≤ η.1 b) (hab : a ≠ b) :
    transfer (transfer η hb a) (transfer_receiver η hb hab) b = η := by
  apply Subtype.ext
  ext l
  have h1 := transfer_apply (transfer η hb a) (transfer_receiver η hb hab) b l
  have h2 := transfer_apply η hb a l
  have : (((transfer (transfer η hb a) (transfer_receiver η hb hab) b).1 l : ℕ) : ℤ) =
      ((η.1 l : ℕ) : ℤ) := by
    rw [h1, h2]; ring
  exact_mod_cast this

/-- **Reversed transfer** (`a < b`): the analogous formula with the opposite sign, all roots
decrease, and `‖q̃ − q‖₁ = 2π|a − b|/L`; `B` is the same averaged matrix. -/
theorem reverse_response (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b a : ℤ} (hb : 1 ≤ η.1 b)
    (hab : a < b) :
    arrRoots L c (transfer η hb a) - arrRoots L c η =
      -((2 * Real.pi) • ((avgJac L c (arrRoots L c η) (arrRoots L c (transfer η hb a)))⁻¹ *ᵥ
        rankVec (transfer η hb a) a b)) ∧
    (∀ i, arrRoots L c (transfer η hb a) i ≤ arrRoots L c η i) ∧
    ∑ i, |arrRoots L c (transfer η hb a) i - arrRoots L c η i| = 2 * Real.pi / L * |a - b| := by
  have hne : a ≠ b := hab.ne
  set m := transfer η hb a
  have hb' := transfer_receiver η hb hne
  have heq := transfer_transfer η hb hne
  have r1 := root_response hL hc m hb' hab
  have r2 := root_response_nonneg hL hc m hb' hab
  have r3 := l1_response hL hc m hb' hab
  rw [heq] at r1 r2 r3
  rw [avgJac_segment_symm] at r1
  refine ⟨?_, r2, ?_⟩
  · rw [← r1]; abel
  · rw [abs_of_neg (sub_neg.mpr hab), neg_sub]
    push_cast
    rw [← r3]
    exact Finset.sum_congr rfl fun i _ => abs_sub_comm _ _

/-! ## 6. The theorem -/

/-- **CC:F01:response** (R-9D98846E), all printed conclusions for `a > b`. -/
theorem adjacent_response (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b a : ℤ} (hb : 1 ≤ η.1 b)
    (hab : b < a) :
    arrRoots L c (transfer η hb a) - arrRoots L c η =
      (2 * Real.pi) • ((avgJac L c (arrRoots L c η) (arrRoots L c (transfer η hb a)))⁻¹ *ᵥ
        rankVec η b a) ∧
    (∀ i, arrRoots L c η i ≤ arrRoots L c (transfer η hb a) i) ∧
    ∑ i, |arrRoots L c (transfer η hb a) i - arrRoots L c η i| = 2 * Real.pi / L * (a - b) ∧
    ∑ i, arrRoots L c (transfer η hb a) i ^ 2 - ∑ i, arrRoots L c η i ^ 2 =
      2 * Real.pi * ∑ k ∈ Finset.Ico b a, ∑ i : Fin N,
        (if (i.val : ℤ) + 1 = Ccum η k then
          ((avgJac L c (arrRoots L c η) (arrRoots L c (transfer η hb a)))⁻¹ *ᵥ
            (arrRoots L c η + arrRoots L c (transfer η hb a))) i else 0) ∧
    (∀ k ∈ Finset.Ico b a, ∀ i : Fin N, (i.val : ℤ) + 1 = Ccum η k →
      b ≤ labs η i ∧ labs η i ≤ a ∧ b ≤ labs (transfer η hb a) i ∧
        labs (transfer η hb a) i ≤ a) :=
  ⟨root_response hL hc η hb hab, root_response_nonneg hL hc η hb hab,
    l1_response hL hc η hb hab, energy_response hL hc η hb hab,
    fun _ hk i hi => rank_labels η hb hab hk i hi⟩

/-! Kernel axiom audit (checkpoint AR1). -/
#print axioms labs_mono
#print axioms count_labs
#print axioms Ccum_eq_card
#print axioms le_iff_lt_card
#print axioms labs_le_iff
#print axioms Ccum_mono
#print axioms Ccum_le_N
#print axioms Ccum_jump
#print axioms Ccum_eq_sum
#print axioms transfer_sum
#print axioms transfer_apply
#print axioms Ccum_transfer
#print axioms sum_ind_le
#print axioms rankVec_eq
#print axioms sum_rankVec
#print axioms Tmap_diff
#print axioms B_response
#print axioms root_response
#print axioms root_response_nonneg
#print axioms l1_response
#print axioms energy_response
#print axioms rank_labels
#print axioms avgJac_segment_symm
#print axioms transfer_transfer
#print axioms reverse_response
#print axioms adjacent_response
#print axioms label_shift

end QuantumNLS.AdjacentResponse
