import NlsGge.GK38.PeriodicLabellingWindows

/-! # S2: unique Lex sorting of fixed integer windows -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

def integerWindow38 (L : ℤ → ℂ) (a b : ℤ) : List ℂ :=
  (List.range (b + 1 - a).toNat).map fun i : ℕ => L (a + (i : ℤ))

theorem integerWindow_multiset38 (L : ℤ → ℂ) (a b : ℤ) :
    (integerWindow38 L a b : Multiset ℂ) = (Finset.Icc a b).val.map L := by
  rw [Int.Icc_eq_finset_map]
  simp only [Finset.map_val, Multiset.map_map]
  rfl

theorem integerWindow_pairwise38 (L : ℤ → ℂ)
    (hL : ∀ i j : ℤ, i ≤ j → complexLexLE38 (L i) (L j)) (a b : ℤ) :
    (integerWindow38 L a b).Pairwise complexLexLE38 := by
  unfold integerWindow38
  rw [List.pairwise_map]
  apply (List.sortedLT_range _).pairwise.imp
  intro i j hij
  apply hL
  have hc : (i : ℤ) ≤ (j : ℤ) := by exact_mod_cast hij.le
  omega

theorem sortComplexRoots_eq_pairwise38 (l : List ℂ) (hl : l.Pairwise complexLexLE38) :
    sortComplexRoots38 (l : Multiset ℂ) = l := by
  unfold sortComplexRoots38
  rw [Multiset.map_coe, Multiset.coe_sort, List.mergeSort_eq_self]
  · simp [List.map_map, Function.comp_def]
  · unfold complexLexLE38 at hl
    simpa only [List.pairwise_map] using hl

theorem integerWindow_eq_sort38 (L : ℤ → ℂ)
    (hL : ∀ i j : ℤ, i ≤ j → complexLexLE38 (L i) (L j)) (a b : ℤ) (s : Multiset ℂ)
    (hs : (Finset.Icc a b).val.map L = s) : integerWindow38 L a b = sortComplexRoots38 s := by
  rw [← hs, ← integerWindow_multiset38]
  exact (sortComplexRoots_eq_pairwise38 _ (integerWindow_pairwise38 L hL a b)).symm

theorem integerWindow_getD38 (L : ℤ → ℂ) {a b k : ℤ} (hk : a ≤ k ∧ k ≤ b) :
    (integerWindow38 L a b).getD (k - a).toNat 0 = L k := by
  have hi : (k - a).toNat < (b + 1 - a).toNat := by omega
  have hlen : (k - a).toNat < (integerWindow38 L a b).length := by
    simpa [integerWindow38] using hi
  rw [List.getD_eq_getElem _ _ hlen]
  simp only [integerWindow38, List.getElem_map, List.getElem_range]
  have he : a + ((k - a).toNat : ℤ) = k := by omega
  rw [he]

/-- Two ordered sequences with the same finite-window multiset agree throughout that window. -/
theorem integerWindow_unique38 (L K : ℤ → ℂ)
    (hL : ∀ i j : ℤ, i ≤ j → complexLexLE38 (L i) (L j))
    (hK : ∀ i j : ℤ, i ≤ j → complexLexLE38 (K i) (K j))
    (a b : ℤ) (hs : (Finset.Icc a b).val.map L = (Finset.Icc a b).val.map K)
    {k : ℤ} (hk : a ≤ k ∧ k ≤ b) : L k = K k := by
  have he : integerWindow38 L a b = integerWindow38 K a b := by
    rw [integerWindow_eq_sort38 L hL a b _ rfl, integerWindow_eq_sort38 K hK a b _ rfl, hs]
  have hv := congrArg (fun l : List ℂ => l.getD (k - a).toNat 0) he
  simpa only [integerWindow_getD38 L hk, integerWindow_getD38 K hk] using hv

end
end NlsGge.GK38
