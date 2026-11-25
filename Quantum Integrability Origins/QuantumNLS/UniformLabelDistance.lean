import QuantumNLS.SmallClusterBound
import QuantumNLS.ExternalConfinement

/-!
# QG:cor:B3-uniform-label-distance (R-274B2C0D)

Source: `source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex`, standing convention of the
subsection (line 23: `c = κ/N` for an actual `N`-particle configuration), Corollary
`QG:cor:B3-uniform-label-distance` (lines 99-106) and its proof (lines 107-121):
"Every on-shell configuration satisfies `|q_j − 2πn_j/L| ≤ 3√(κ/L)`, `1 ≤ j ≤ N`."

An on-shell (actual) configuration is the accepted `RootContraction.IsActualConfig L c n q`
(strictly ordered real roots, nondecreasing integer labels, the Bethe equations
`L q_j = 2πn_j + 2 Σ_{ℓ≠j} arctan (c/(q_j − q_ℓ))`, the same as `QG:eq:our-bethe`) at `c = κ/N`.
Lean indices are zero based (`Fin N`).

Route (as printed): for a label `a` take the cluster `{ℓ : n_ℓ ≤ a}`; exterior roots lie to the
right, so their arctangent contributions are negative (`QG:eq:B3-global-force-bound`); the accepted
Lemma `QG:lem:B3-small-cluster` (R-CFCD5A9D, `SmallClusterBound.small_cluster`) gives
`q_j ≤ 2πa/L + 3√(ck/L)`; take `a = n_j` and `ck ≤ κ`. The lower bound is the mirror argument.

Recorded deviation: the lower bound ("reflection of roots and labels") is proved by the mirrored
cluster `{ℓ : n_ℓ ≥ a}` and the variables `2πa/L − q_ℓ` directly, rather than by building the
reflected configuration; the estimate used is the same lemma.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset

namespace QuantumNLS.UniformLabelDistance

open QuantumNLS.RootContraction

variable {N : ℕ}

/-- The small-cluster lemma transported to an index subset `S ⊆ Fin N`. -/
lemma cluster_small {S : Finset (Fin N)} {y : Fin N → ℝ} (hy : Function.Injective y) {c L : ℝ}
    (hc : 0 < c) (hL : 0 < L)
    (hforce : ∀ l ∈ S, 0 < y l → L * y l ≤ 2 * ∑ m ∈ S.erase l, Real.arctan (c / (y l - y m)))
    {l : Fin N} (hl : l ∈ S) : max (y l) 0 ≤ 3 * Real.sqrt (c * S.card / L) := by
  set e := S.orderIsoOfFin (k := S.card) rfl
  have hinj : Function.Injective (fun k => y (e k)) := fun k1 k2 h =>
    e.injective (Subtype.ext (hy h))
  have hf : ∀ k, 0 < y (e k) →
      L * y (e k) ≤ 2 * ∑ m ∈ univ.erase k, Real.arctan (c / (y (e k) - y (e m))) := by
    intro k hk
    have := hforce (e k) (e k).2 hk
    rwa [ExternalConfinement.sum_erase_transport e (fun m => Real.arctan (c / (y (e k) - y m)))]
      at this
  obtain ⟨k, hk⟩ : ∃ k, e k = ⟨l, hl⟩ := e.surjective _
  have := SmallClusterBound.small_cluster hinj hc hL hf k
  rw [hk] at this
  exact this

/-- Splitting the full Bethe sum into the cluster and its exterior. -/
lemma sum_split (S : Finset (Fin N)) (f : Fin N → ℝ) {l : Fin N} (hl : l ∈ S) :
    ∑ m ∈ univ.erase l, f m = ∑ m ∈ S.erase l, f m + ∑ m ∈ univ.filter (fun m => m ∉ S), f m := by
  rw [← Finset.sum_filter_add_sum_filter_not (univ.erase l) (fun m => m ∈ S)]
  congr 1
  · congr 1; ext m; simp [and_comm]
  · congr 1; ext m; simp only [mem_filter, mem_erase, mem_univ, and_true, true_and]
    exact ⟨fun h => h.2, fun h => ⟨fun hm => h (hm ▸ hl), h⟩⟩

lemma sqrt_le_kappa {κ L : ℝ} (hκ : 0 < κ) (hL : 0 < L) {k : ℕ} (hk : k ≤ N) (hN : 1 ≤ N) :
    3 * Real.sqrt (κ / N * k / L) ≤ 3 * Real.sqrt (κ / L) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk
  have : κ / N * k / L ≤ κ / L := by
    rw [div_le_div_iff_of_pos_right hL, div_mul_eq_mul_div, div_le_iff₀ hN0]
    exact mul_le_mul_of_nonneg_left hkN hκ.le
  gcongr

/-- **QG:cor:B3-uniform-label-distance** (R-274B2C0D): for every on-shell configuration
(`c = κ/N`), `|q_j − 2πn_j/L| ≤ 3√(κ/L)`. -/
theorem uniform_label_distance (hN : 1 ≤ N) {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ)
    {n : Fin N → ℤ} {q : Fin N → ℝ} (h : IsActualConfig L (κ / N) n q) (j : Fin N) :
    |q j - 2 * Real.pi * n j / L| ≤ 3 * Real.sqrt (κ / L) := by
  set c := κ / (N : ℝ)
  have hc : 0 < c := h.c_pos
  have hinj : Function.Injective q := h.sorted.injective
  have hcardle : ∀ S : Finset (Fin N), S.card ≤ N := fun S =>
    (Finset.card_le_univ S).trans (by simp)
  rw [abs_le]
  constructor
  · -- lower bound: mirrored cluster `{ℓ : n_ℓ ≥ n_j}`, `y_ℓ = 2πn_j/L − q_ℓ`
    set a := n j
    set S := univ.filter fun l => a ≤ n l
    set y : Fin N → ℝ := fun l => 2 * Real.pi * a / L - q l
    have hyinj : Function.Injective y := fun l1 l2 h' => hinj (by simp only [y] at h'; linarith)
    have hf : ∀ l ∈ S, 0 < y l → L * y l ≤ 2 * ∑ m ∈ S.erase l, Real.arctan (c / (y l - y m)) := by
      intro l hl _
      have hal : a ≤ n l := (Finset.mem_filter.mp hl).2
      have hB := h.bethe l
      have hsp := sum_split S (fun m => Real.arctan (c / (q l - q m))) hl
      have hext : 0 ≤ ∑ m ∈ univ.filter (fun m => m ∉ S), Real.arctan (c / (q l - q m)) := by
        refine Finset.sum_nonneg fun m hm => ?_
        have hm' : n m < a := by
          have := (Finset.mem_filter.mp hm).2; simp only [S, mem_filter, mem_univ, true_and] at this
          omega
        have hml : m < l := by
          by_contra hh; push Not at hh; have := h.labels_sorted hh; omega
        have : q m < q l := h.sorted hml
        have : 0 < c / (q l - q m) := div_pos hc (by linarith)
        exact (Real.arctan_pos.mpr this).le
      have hcl : ∑ m ∈ S.erase l, Real.arctan (c / (y l - y m)) =
          -∑ m ∈ S.erase l, Real.arctan (c / (q l - q m)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [y]
        rw [show 2 * Real.pi * a / L - q l - (2 * Real.pi * a / L - q m) = -(q l - q m) by ring,
          div_neg, Real.arctan_neg]
      rw [hcl]
      have hLa : L * (2 * Real.pi * a / L) = 2 * Real.pi * a := by field_simp
      have hna : (2 * Real.pi * a : ℝ) ≤ 2 * Real.pi * n l := by
        have : (a : ℝ) ≤ n l := by exact_mod_cast hal
        nlinarith [Real.pi_pos]
      simp only [y]
      rw [mul_sub, hLa]
      linarith
    have hj : j ∈ S := Finset.mem_filter.mpr ⟨mem_univ _, le_rfl⟩
    have hb := cluster_small hyinj hc hL hf hj
    have hk := sqrt_le_kappa hκ hL (hcardle S) hN
    have := le_max_left (y j) 0
    simp only [y] at this
    linarith
  · -- upper bound: cluster `{ℓ : n_ℓ ≤ n_j}`, `y_ℓ = q_ℓ − 2πn_j/L`
    set a := n j
    set S := univ.filter fun l => n l ≤ a
    set y : Fin N → ℝ := fun l => q l - 2 * Real.pi * a / L
    have hyinj : Function.Injective y := fun l1 l2 h' => hinj (by simp only [y] at h'; linarith)
    have hf : ∀ l ∈ S, 0 < y l → L * y l ≤ 2 * ∑ m ∈ S.erase l, Real.arctan (c / (y l - y m)) := by
      intro l hl _
      have hal : n l ≤ a := (Finset.mem_filter.mp hl).2
      have hB := h.bethe l
      have hsp := sum_split S (fun m => Real.arctan (c / (q l - q m))) hl
      have hext : ∑ m ∈ univ.filter (fun m => m ∉ S), Real.arctan (c / (q l - q m)) ≤ 0 := by
        refine Finset.sum_nonpos fun m hm => ?_
        have hm' : a < n m := by
          have := (Finset.mem_filter.mp hm).2; simp only [S, mem_filter, mem_univ, true_and] at this
          omega
        have hml : l < m := by
          by_contra hh; push Not at hh; have := h.labels_sorted hh; omega
        have : q l < q m := h.sorted hml
        have : c / (q l - q m) < 0 := div_neg_of_pos_of_neg hc (by linarith)
        exact (Real.arctan_lt_zero.mpr this).le
      have hcl : ∑ m ∈ S.erase l, Real.arctan (c / (y l - y m)) =
          ∑ m ∈ S.erase l, Real.arctan (c / (q l - q m)) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [y]
        rw [show q l - 2 * Real.pi * a / L - (q m - 2 * Real.pi * a / L) = q l - q m by ring]
      rw [hcl]
      have hLa : L * (2 * Real.pi * a / L) = 2 * Real.pi * a := by field_simp
      have hna : (2 * Real.pi * n l : ℝ) ≤ 2 * Real.pi * a := by
        have : (n l : ℝ) ≤ a := by exact_mod_cast hal
        nlinarith [Real.pi_pos]
      simp only [y]
      rw [mul_sub, hLa]
      linarith
    have hj : j ∈ S := Finset.mem_filter.mpr ⟨mem_univ _, le_rfl⟩
    have hb := cluster_small hyinj hc hL hf hj
    have hk := sqrt_le_kappa hκ hL (hcardle S) hN
    have := le_max_left (y j) 0
    simp only [y] at this
    linarith

/-- The same bound for the accepted roots `roots L n (κ/N)` (R-4C8D7C9E) of any nondecreasing
integer labels. -/
theorem uniform_label_distance_roots (hN : 1 ≤ N) {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ)
    {n : Fin N → ℤ} (hn : Monotone n) (j : Fin N) :
    |BetheSmooth.roots L n (κ / N) j - 2 * Real.pi * n j / L| ≤ 3 * Real.sqrt (κ / L) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  exact uniform_label_distance hN hL hκ (isActual_roots hL (div_pos hκ hN0) hn) j

/-! Kernel axiom audit (checkpoint UL1). -/
#print axioms cluster_small
#print axioms sum_split
#print axioms sqrt_le_kappa
#print axioms uniform_label_distance
#print axioms uniform_label_distance_roots

end QuantumNLS.UniformLabelDistance
