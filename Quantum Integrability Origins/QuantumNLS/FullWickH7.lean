import QuantumNLS.FullWickH6

/-! FullWickH7 (haiku_inventory, R-140AE34B `thm:full-wick`, Stage 3, item 5: norm-close preparations).

The time-indexed uniform strong-symbol predicate `FullWickH4.HasUniformStrongT` is transferred from a
reference preparation `φ` to any normalized preparation `ψ` that is uniformly norm-close to `φ` over the
profile class `S` and the time set `Tb`, under uniform operator-norm bounds (printed: "uniformly
norm-close preparations preserve the static uniform statements"; "every norm-close preparation").

Contents:
  * `IsNormClosePrepT ψ φ S Tb`: time-indexed normalized preparation, uniformly norm-close to `φ`
    (the time-indexed analogue of StrongSymbolDef.IsNormClosePrep).
  * `hasUniformStrongT_of_normClose`: transfer of the uniform strong symbol to `ψ`.
  * `hasUniformPairT_of_normClose`: the same for the adjoint pair (operator and companion).
  * `list_prod_normClose`: an ordered product of admissible factors keeps its uniform strong symbol
    on any norm-close normalized preparation, using FullWickH6.pair_list_prod.

Standard axioms only.
-/

noncomputable section
open Filter Topology
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace QuantumNLS.FullWickH7

open QuantumNLS.FullWickH4 QuantumNLS.FullWickH6

variable {H : ℕ → Type*} [∀ N, NormedAddCommGroup (H N)] [∀ N, NormedSpace ℂ (H N)]

/-- Time-indexed normalized preparation, uniformly norm-close to the reference `φ` over `S × Tb`. -/
def IsNormClosePrepT {X Θ : Type*} (ψ φ : X → Θ → ∀ N, H N) (S : Set X) (Tb : Set Θ) : Prop :=
  (∀ u ∈ S, ∀ t ∈ Tb, ∀ N, ‖ψ u t N‖ = 1) ∧
    (∀ ε > 0, ∀ᶠ N in atTop, ∀ u ∈ S, ∀ t ∈ Tb, ‖ψ u t N - φ u t N‖ ≤ ε)

/-- Operator-norm estimate `‖(A − c·1) v‖ ≤ (‖A‖ + ‖c‖)‖v‖`. -/
lemma sub_smul_id_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : E →L[ℂ] E) (c : ℂ) (v : E) :
    ‖(A - c • ContinuousLinearMap.id ℂ E) v‖ ≤ (‖A‖ + ‖c‖) * ‖v‖ := by
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply]
  calc ‖A v - c • v‖ ≤ ‖A v‖ + ‖c • v‖ := norm_sub_le _ _
    _ ≤ ‖A‖ * ‖v‖ + ‖c‖ * ‖v‖ :=
        add_le_add (A.le_opNorm v) (by rw [norm_smul])
    _ = (‖A‖ + ‖c‖) * ‖v‖ := by ring

/-- **Norm-close transfer of a uniform strong symbol.** If `A` has eventually bounded norm `≤ C`,
its symbol is bounded by `K` on `S × Tb`, `A` has uniform strong symbol `a` on the reference `φ`, and
`ψ` is uniformly norm-close to `φ`, then `A` has uniform strong symbol `a` on `ψ`. -/
theorem hasUniformStrongT_of_normClose {X Θ : Type*} {A : ∀ N, H N →L[ℂ] H N} {S : Set X}
    {Tb : Set Θ} {ψ φ : X → Θ → ∀ N, H N} {a : X → Θ → ℂ} {C K : ℝ}
    (hA : ∀ᶠ N in atTop, ‖A N‖ ≤ C) (hK : ∀ u ∈ S, ∀ t ∈ Tb, ‖a u t‖ ≤ K)
    (hφ : HasUniformStrongT A S Tb φ a)
    (hψφ : ∀ ε > 0, ∀ᶠ N in atTop, ∀ u ∈ S, ∀ t ∈ Tb, ‖ψ u t N - φ u t N‖ ≤ ε) :
    HasUniformStrongT A S Tb ψ a := by
  intro ε hε
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε / (2 * (|C| + |K| + 1)) := ⟨_, rfl⟩
  have hne : 2 * (|C| + |K| + 1) ≠ 0 := by positivity
  have hδpos : 0 < δ := by
    rw [hδ]
    exact div_pos hε (by positivity)
  have hδ2 : 2 * (|C| + |K| + 1) * δ = ε := by
    rw [hδ]
    field_simp
  filter_upwards [hA, hφ (ε / 2) (half_pos hε), hψφ δ hδpos] with N hAN hφN hψN
  intro u hu t ht
  have hsplit : (A N - a u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N)
      = (A N - a u t • ContinuousLinearMap.id ℂ (H N)) (φ u t N)
        + (A N - a u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N - φ u t N) := by
    rw [← map_add]
    congr 1
    abel
  have hbd : ‖A N‖ + ‖a u t‖ ≤ |C| + |K| :=
    add_le_add ((hAN).trans (le_abs_self C)) ((hK u hu t ht).trans (le_abs_self K))
  have h3 : ‖(A N - a u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N - φ u t N)‖ ≤ ε / 2 := by
    refine (sub_smul_id_norm_le (A N) (a u t) (ψ u t N - φ u t N)).trans ?_
    refine (mul_le_mul hbd (hψN u hu t ht) (norm_nonneg _) (by positivity)).trans ?_
    nlinarith [abs_nonneg C, abs_nonneg K]
  rw [hsplit]
  calc ‖(A N - a u t • ContinuousLinearMap.id ℂ (H N)) (φ u t N)
        + (A N - a u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N - φ u t N)‖
      ≤ ‖(A N - a u t • ContinuousLinearMap.id ℂ (H N)) (φ u t N)‖
        + ‖(A N - a u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N - φ u t N)‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (hφN u hu t ht) h3
    _ = ε := by ring

/-- **Norm-close transfer for an adjoint pair.** The operator and its companion each have bounds, and
the pair transfers from `φ` to `ψ`. -/
theorem hasUniformPairT_of_normClose {X Θ : Type*} {A A' : ∀ N, H N →L[ℂ] H N} {S : Set X}
    {Tb : Set Θ} {ψ φ : X → Θ → ∀ N, H N} {a : X → Θ → ℂ} {C K : ℝ}
    (hA : ∀ᶠ N in atTop, ‖A N‖ ≤ C) (hA' : ∀ᶠ N in atTop, ‖A' N‖ ≤ C)
    (hK : ∀ u ∈ S, ∀ t ∈ Tb, ‖a u t‖ ≤ K)
    (hφ : HasUniformPairT A A' S Tb φ a)
    (hψφ : ∀ ε > 0, ∀ᶠ N in atTop, ∀ u ∈ S, ∀ t ∈ Tb, ‖ψ u t N - φ u t N‖ ≤ ε) :
    HasUniformPairT A A' S Tb ψ a := by
  refine ⟨hasUniformStrongT_of_normClose hA hK hφ.1 hψφ, ?_⟩
  exact hasUniformStrongT_of_normClose hA' (fun u hu t ht => by
    rw [Complex.norm_conj]; exact hK u hu t ht) hφ.2 hψφ

/-- **Ordered product on a norm-close preparation.** For an admissible list of factors on the
reference `φ`, the ordered product has the product uniform strong symbol on any normalized
preparation `ψ` that is uniformly norm-close to `φ`. -/
theorem list_prod_normClose {ι X Θ : Type*} (f f' : ι → ∀ N, H N →L[ℂ] H N)
    (s : ι → X → Θ → ℂ) (S : Set X) (Tb : Set Θ) (ψ φ : X → Θ → ∀ N, H N) (C K : ℝ)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (l : List ι) (hgood : ∀ i ∈ l, GoodFactor f f' s S Tb φ C K i)
    (hprep : IsNormClosePrepT ψ φ S Tb) :
    HasUniformStrongT (fun N => (l.map (fun i => f i N)).prod) S Tb ψ
      (fun u t => (l.map (fun i => s i u t)).prod) := by
  obtain ⟨hpair, hnorm, _, hsym⟩ := pair_list_prod f f' s S Tb φ C K hC hK l hgood
  exact hasUniformStrongT_of_normClose hnorm hsym hpair.1 hprep.2

end QuantumNLS.FullWickH7

#print axioms QuantumNLS.FullWickH7.sub_smul_id_norm_le
#print axioms QuantumNLS.FullWickH7.hasUniformStrongT_of_normClose
#print axioms QuantumNLS.FullWickH7.hasUniformPairT_of_normClose
#print axioms QuantumNLS.FullWickH7.list_prod_normClose
