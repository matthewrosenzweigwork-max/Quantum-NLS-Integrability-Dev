import QuantumNLS.FullWickH4

/-! FullWickH6 (haiku_inventory, R-140AE34B `thm:full-wick`, Stage 3, item 1: ordered products).

For a finite list `l` of factors `i`, with operators `f i` and companion adjoints `f' i` and time-indexed
symbols `s i u t`, the ordered product `(l.map f).prod` has, as companion, the reversed product
`((l.map f').reverse).prod` (the adjoint of `f i₁ ⋯ f iₙ` is `f' iₙ ⋯ f' i₁`), and symbol
`(l.map s).prod`. The main theorem `pair_list_prod` proves this by induction on the list, using
`FullWickH4.pair_mul` at each step, and carries the eventual norm bounds `C^length` on the operators
and the uniform symbol bounds `K^length`.

Each factor must satisfy `GoodFactor`: eventual norm bounds `≤ C` on `f i` and `f' i`, a uniform symbol
bound `≤ K`, and a uniform strong-symbol pair on the common preparation. The printed "every fixed
ordered product" follows for every finite list of generators (for example, the words in
eq:full-product), with C and K the finite maxima over the generators.

Standard axioms only.
-/

noncomputable section
open Filter Topology
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace QuantumNLS.FullWickH6

open QuantumNLS.FullWickH4

variable {H : ℕ → Type*} [∀ N, NormedAddCommGroup (H N)] [∀ N, NormedSpace ℂ (H N)]

/-- One admissible factor: eventual norm bounds `≤ C` for the operator and its adjoint, a uniform
symbol bound `≤ K`, and a uniform strong-symbol pair on the common preparation. -/
def GoodFactor {ι X Θ : Type*} (f f' : ι → ∀ N, H N →L[ℂ] H N) (s : ι → X → Θ → ℂ)
    (S : Set X) (Tb : Set Θ) (ψ : X → Θ → ∀ N, H N) (C K : ℝ) (i : ι) : Prop :=
  (∀ᶠ N in atTop, ‖f i N‖ ≤ C) ∧ (∀ᶠ N in atTop, ‖f' i N‖ ≤ C) ∧
    (∀ u ∈ S, ∀ t ∈ Tb, ‖s i u t‖ ≤ K) ∧ HasUniformPairT (f i) (f' i) S Tb ψ (s i)

/-- **Ordered products of arbitrary finite length.** For a list `l` of admissible factors with the
same bounds `C, K` (nonnegative), the ordered product is a uniform strong-symbol pair with the
product symbol, and its operator norm, adjoint norm and symbol are bounded by `C^length`, `C^length`,
`K^length`. -/
theorem pair_list_prod {ι X Θ : Type*} (f f' : ι → ∀ N, H N →L[ℂ] H N)
    (s : ι → X → Θ → ℂ) (S : Set X) (Tb : Set Θ) (ψ : X → Θ → ∀ N, H N) (C K : ℝ)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (l : List ι) :
    (∀ i ∈ l, GoodFactor f f' s S Tb ψ C K i) →
      HasUniformPairT (fun N => (l.map (fun i => f i N)).prod)
          (fun N => ((l.map (fun i => f' i N)).reverse).prod) S Tb ψ
          (fun u t => (l.map (fun i => s i u t)).prod)
        ∧ (∀ᶠ N in atTop, ‖(l.map (fun i => f i N)).prod‖ ≤ C ^ l.length)
        ∧ (∀ᶠ N in atTop, ‖((l.map (fun i => f' i N)).reverse).prod‖ ≤ C ^ l.length)
        ∧ (∀ u ∈ S, ∀ t ∈ Tb, ‖(l.map (fun i => s i u t)).prod‖ ≤ K ^ l.length) := by
  induction l with
  | nil =>
    intro _
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [List.map_nil, List.prod_nil, List.reverse_nil, map_one]
      refine ⟨?_, ?_⟩
      · intro ε hε
        refine Eventually.of_forall (fun N => ?_)
        intro u _ t _
        simp [hε.le]
      · intro ε hε
        refine Eventually.of_forall (fun N => ?_)
        intro u _ t _
        simp [hε.le]
    · refine Eventually.of_forall (fun N => ?_)
      simp only [List.map_nil, List.prod_nil, List.length_nil, pow_zero]
      rw [ContinuousLinearMap.one_def]
      simpa using ContinuousLinearMap.norm_id_le
    · refine Eventually.of_forall (fun N => ?_)
      simp only [List.map_nil, List.prod_nil, List.reverse_nil, List.length_nil, pow_zero]
      rw [ContinuousLinearMap.one_def]
      simpa using ContinuousLinearMap.norm_id_le
    · intro u _ t _
      simp
  | cons i rest ih =>
    intro hgood
    obtain ⟨hPb, hP'b, hsb, hpairi⟩ := hgood i (by simp)
    have hrest : ∀ j ∈ rest, GoodFactor f f' s S Tb ψ C K j :=
      fun j hj => hgood j (by simp [hj])
    obtain ⟨hpair, hnorm, hadj, hsym⟩ := ih hrest
    simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.prod_append,
      List.prod_singleton, List.length_cons]
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- pair: apply pair_mul with bounds raised to a common maximum
      have hPmax : ∀ᶠ N in atTop, ‖f i N‖ ≤ max C (C ^ rest.length) :=
        hPb.mono (fun N h => h.trans (le_max_left _ _))
      have hQmax : ∀ᶠ N in atTop, ‖((rest.map (fun j => f' j N)).reverse).prod‖
          ≤ max C (C ^ rest.length) :=
        hadj.mono (fun N h => h.trans (le_max_right _ _))
      have hpmax : ∀ u ∈ S, ∀ t ∈ Tb, ‖s i u t‖ ≤ max K (K ^ rest.length) :=
        fun u hu t ht => (hsb u hu t ht).trans (le_max_left _ _)
      have hqmax : ∀ u ∈ S, ∀ t ∈ Tb, ‖(rest.map (fun j => s j u t)).prod‖
          ≤ max K (K ^ rest.length) :=
        fun u hu t ht => (hsym u hu t ht).trans (le_max_right _ _)
      exact pair_mul hPmax hQmax hpmax hqmax hpairi hpair
    · -- operator norm
      refine (hPb.and hnorm).mono (fun N h => ?_)
      obtain ⟨h1, h2⟩ := h
      calc ‖f i N * (rest.map (fun j => f j N)).prod‖
          ≤ ‖f i N‖ * ‖(rest.map (fun j => f j N)).prod‖ := norm_mul_le _ _
        _ ≤ C * C ^ rest.length := mul_le_mul h1 h2 (norm_nonneg _) hC
        _ = C ^ (rest.length + 1) := by ring
    · -- adjoint norm
      refine (hadj.and hP'b).mono (fun N h => ?_)
      obtain ⟨h2, h1⟩ := h
      calc ‖((rest.map (fun j => f' j N)).reverse).prod * f' i N‖
          ≤ ‖((rest.map (fun j => f' j N)).reverse).prod‖ * ‖f' i N‖ := norm_mul_le _ _
        _ ≤ C ^ rest.length * C := mul_le_mul h2 h1 (norm_nonneg _) (pow_nonneg hC _)
        _ = C ^ (rest.length + 1) := by ring
    · -- symbol
      intro u hu t ht
      calc ‖s i u t * (rest.map (fun j => s j u t)).prod‖
          ≤ ‖s i u t‖ * ‖(rest.map (fun j => s j u t)).prod‖ := norm_mul_le _ _
        _ ≤ K * K ^ rest.length :=
            mul_le_mul (hsb u hu t ht) (hsym u hu t ht) (norm_nonneg _) hK
        _ = K ^ (rest.length + 1) := by ring

/-- Packaged form for a fixed list: the uniform strong-symbol pair of the ordered product. -/
theorem pair_list_prod_pair {ι X Θ : Type*} (f f' : ι → ∀ N, H N →L[ℂ] H N)
    (s : ι → X → Θ → ℂ) (S : Set X) (Tb : Set Θ) (ψ : X → Θ → ∀ N, H N) (C K : ℝ)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (l : List ι) (hgood : ∀ i ∈ l, GoodFactor f f' s S Tb ψ C K i) :
    HasUniformPairT (fun N => (l.map (fun i => f i N)).prod)
        (fun N => ((l.map (fun i => f' i N)).reverse).prod) S Tb ψ
        (fun u t => (l.map (fun i => s i u t)).prod) :=
  (pair_list_prod f f' s S Tb ψ C K hC hK l hgood).1

end QuantumNLS.FullWickH6

#print axioms QuantumNLS.FullWickH6.pair_list_prod
#print axioms QuantumNLS.FullWickH6.pair_list_prod_pair
