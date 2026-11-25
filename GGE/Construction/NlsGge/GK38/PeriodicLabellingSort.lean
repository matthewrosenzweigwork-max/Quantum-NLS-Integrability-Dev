import NlsGge.GK38.PeriodicLabellingIndices

/-! # S2: complex Lex sorting preserves the complete multiset -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem complexLexLE_iff38 (z w : ℂ) :
    complexLexLE38 z w ↔ z.re < w.re ∨ z.re = w.re ∧ z.im ≤ w.im := by
  exact Prod.Lex.toLex_le_toLex

theorem sortComplexRoots_multiset38 (s : Multiset ℂ) :
    (sortComplexRoots38 s : Multiset ℂ) = s := by
  unfold sortComplexRoots38
  rw [← Multiset.map_coe, Multiset.sort_eq, Multiset.map_map]
  simp

theorem sortComplexRoots_pairwise38 (s : Multiset ℂ) :
    (sortComplexRoots38 s).Pairwise complexLexLE38 := by
  unfold sortComplexRoots38
  rw [List.pairwise_map]
  simpa only [complexLexLE38, Equiv.apply_symm_apply, toLex_ofLex] using
    (Multiset.pairwise_sort (s.map (fun z => toLex (Complex.equivRealProd z))) (fun a b => a ≤ b))

theorem sortComplexRoots_mem38 (s : Multiset ℂ) (z : ℂ) :
    z ∈ sortComplexRoots38 s ↔ z ∈ s := by
  rw [← Multiset.mem_coe, sortComplexRoots_multiset38]

theorem sortComplexRoots_singleton38 (z : ℂ) :
    sortComplexRoots38 {z} = [z] := by
  simp [sortComplexRoots38]

theorem sortComplexRoots_replicate38 (m : ℕ) (z : ℂ) :
    sortComplexRoots38 (Multiset.replicate m z) = List.replicate m z := by
  induction m with
  | zero => simp [sortComplexRoots38]
  | succ m hm =>
    unfold sortComplexRoots38 at *
    simp only [Multiset.replicate_succ, Multiset.map_cons, Multiset.map_replicate]
    rw [Multiset.sort_cons]
    · simpa only [List.map_cons, Equiv.symm_apply_apply, ofLex_toLex,
        Multiset.map_replicate, List.replicate_succ] using
        congrArg (List.cons z) hm
    · intro b hb
      have hb' : b = toLex (Complex.equivRealProd z) := Multiset.mem_replicate.mp hb |>.2
      rw [hb']

theorem sortComplexRoots_repeated_probe38 :
    sortComplexRoots38 ({(1 : ℂ), 1} : Multiset ℂ) = [1, 1] := by
  simpa using sortComplexRoots_replicate38 2 (1 : ℂ)

end
end NlsGge.GK38
