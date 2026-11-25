import NlsGge.GK38.RealTypeSpectrumClusters

/-! # S5: sorting the real cluster blocks preserves every occurrence

A monotone projection of actual nearby roots onto their reference clusters
preserves the entire multiset. Sorted lists then agree after projection.
-/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem realType_complexLex_antisymm38 {a b : ℂ}
    (hab : complexLexLE38 a b) (hba : complexLexLE38 b a) : a = b := by
  apply Complex.equivRealProd.injective
  exact congrArg ofLex (le_antisymm hab hba)

/-- Sorting commutes with a monotone multiset projection, including repeated values. -/
theorem realType_sorted_projection38 (s t : Multiset ℂ) (p : ℂ → ℂ)
    (hmap : t.map p = s)
    (hmono : ∀ a ∈ t, ∀ b ∈ t, complexLexLE38 a b → complexLexLE38 (p a) (p b)) :
    (sortComplexRoots38 t).map p = sortComplexRoots38 s := by
  have hpair : ((sortComplexRoots38 t).map p).Pairwise complexLexLE38 := by
    rw [List.pairwise_map]
    exact (sortComplexRoots_pairwise38 t).imp_of_mem
      (fun {a b} ha hb hab => hmono a ((sortComplexRoots_mem38 t a).mp ha)
        b ((sortComplexRoots_mem38 t b).mp hb) hab)
  have he : (((sortComplexRoots38 t).map p : List ℂ) : Multiset ℂ) =
      (sortComplexRoots38 s : Multiset ℂ) := by
    rw [← Multiset.map_coe, sortComplexRoots_multiset38, sortComplexRoots_multiset38, hmap]
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ => realType_complexLex_antisymm38)
    hpair (sortComplexRoots_pairwise38 s) (Quotient.exact he)

open Classical in
/-- Restricting a central zero multiset to a contained cluster preserves its counts. -/
theorem periodic_cluster_filter38 (u : PhysicalL2) (N : ℕ)
    (hN : RootCountingAt38 (perChar (realSlice u)) 2 N) (a : ℂ) (r : ℝ)
    (hsub : ball a r ⊆ ball 0 (countingRadius38 N)) :
    (Lib.zeroMultiset (perChar (realSlice u)) (ball 0 (countingRadius38 N))).filter
      (fun z => z ∈ ball a r) = Lib.zeroMultiset (perChar (realSlice u)) (ball a r) := by
  classical
  apply Multiset.ext'
  intro z
  rw [Multiset.count_filter, Lib.count_zeroMultiset_ball (hN.2.1.mono (subset_univ _)),
    Lib.count_zeroMultiset_ball (hN.2.1.mono (subset_univ _))]
  by_cases hz : z ∈ ball a r
  · simp [hz, hsub hz]
  · simp [hz]

/-- A valid sorted index is compared with its corresponding reference after projection. -/
theorem realType_sorted_close38 (s t : Multiset ℂ) (p : ℂ → ℂ) (ε : ℝ)
    (hmap : t.map p = s)
    (hmono : ∀ a ∈ t, ∀ b ∈ t, complexLexLE38 a b → complexLexLE38 (p a) (p b))
    (hclose : ∀ z ∈ t, ‖z - p z‖ < ε) (j : ℕ) (hj : j < s.card) :
    ‖(sortComplexRoots38 t).getD j 0 - (sortComplexRoots38 s).getD j 0‖ < ε := by
  have ht : j < (sortComplexRoots38 t).length := by
    rw [sortComplexRoots_length38]
    have hcard : t.card = s.card := by rw [← hmap, Multiset.card_map]
    rwa [hcard]
  have hs : j < (sortComplexRoots38 s).length := by rwa [sortComplexRoots_length38]
  have hz : (sortComplexRoots38 t).getD j 0 ∈ t := by
    rw [← sortComplexRoots_mem38, List.getD_eq_getElem _ _ ht]
    exact List.getElem_mem ht
  have he := realType_sorted_projection38 s t p hmap hmono
  have heget := congrArg (fun l : List ℂ => l.getD j (p 0)) he
  rw [List.getD_map] at heget
  have hdefaults : (sortComplexRoots38 s).getD j (p 0) = (sortComplexRoots38 s).getD j 0 := by
    rw [List.getD_eq_getElem _ _ hs, List.getD_eq_getElem _ _ hs]
  rw [hdefaults] at heget
  rw [← heget]
  exact hclose _ hz

end
end NlsGge.GK38
