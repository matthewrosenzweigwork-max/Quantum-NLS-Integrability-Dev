import QuantumNLS.FullWickH1
import QuantumNLS.FullWickH6
import QuantumNLS.FullWickH7
import QuantumNLS.FullWickH8

/-! FullWickH11 (haiku_inventory, R-140AE34B `thm:full-wick`, addendum 6: norm-close static word and Dirac clauses).

Printed source (source-text/chapters/core/wick_calculus.tex): lines 84-86 state that the strong symbols hold for
"every norm-close preparation" and that "every fixed ordered product and the scaled Dirac commutator" have the
corresponding symbols; line 89 states that "uniformly norm-close preparations preserve the static uniform statements".

Lean content (static setting: parameter predicate `UniformStaticR49b.UniformStatic hκ j q`, reference product
preparation `UniformStaticR49b.product`, Q06 gauge `FullWickO1.staticGauge q`, region `UR R`):
  * `static_word_bounds`: the eventual norm bounds `≤ 1` on the ordered word and its companion, and the symbol
    bound `≤ 1` on `UR R × Tb`, from `FullWickH6.pair_list_prod` on the Cartesian generators (C = K = 1).
  * `static_word_normClose`: the ordered word of generators has the uniform strong pair with symbol
    `evalSym (chart Φ u) (wordSym w)` and conjugate companion on every `IsNormClosePrepT ψ' product (UR R) Tb`.
    Route: `FullWickH8.static_word_pair` (reference pair) transferred by `FullWickH7.hasUniformPairT_of_normClose`,
    exactly as `FullWickH8.static_poly_normClose` does for the polynomial clause.
  * `static_word_normClose_strong`: the operator component alone, by `FullWickH7.list_prod_normClose` (a
    consistency corollary; the headline uses the pair form).
  * `static_dirac_normClose`: the scaled Dirac commutator `-iN[W^q_N f, W^q_N g]` has the uniform strong symbol
    `evalSym (chart Φ u) (pb S f g)` on every such preparation. Route: `FullWickH8.static_dirac` (reference) with the
    eventual operator bound `coeffNorm (pb S f g) + |Cfg f g + Cfg g f|` from `FullWickH1.quantization_Dirac_bound`
    and `FullWickH1.quantization_coeff_bound`, and the symbol bound `coeffNorm (pb S f g)` from
    `FullWickH8.chart_evalSym_norm_le`, transferred by `FullWickH7.hasUniformStrongT_of_normClose`.

Nothing is assumed beyond the parameter predicate `hU`. Standard dependencies only.
-/

noncomputable section
open Filter Topology
open scoped ComplexConjugate BigOperators InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace QuantumNLS.FullWickH11

open QuantumNLS.FullWickH4 (HasUniformStrongT HasUniformPairT)
open QuantumNLS.FullWickH6 (GoodFactor pair_list_prod)
open QuantumNLS.FullWickH7 (IsNormClosePrepT hasUniformPairT_of_normClose hasUniformStrongT_of_normClose
  list_prod_normClose)
open QuantumNLS.FullWickO1 (bilinear staticGauge)
open QuantumNLS.FullWickO2 (UR)
open QuantumNLS.FullWickS1 (orderedWord)
open QuantumNLS.WickSymbols (Sym Balanced coeffNorm pb)
open QuantumNLS.WickBounds (gensym wordSym labelsOf Cfg balanced_pb)
open QuantumNLS.WickSpectralBridge (evalSym evalSym_wordSym evalSym_gensym)
open QuantumNLS.UniformStaticR49b (UniformStatic)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheCoefficientTransform (HN)

section NormClose

variable {L κ : ℝ} [Fact (0 < L)]

/-- **Bounds for the static ordered word.** For a fixed word `w` of Cartesian generators, the ordered product
and its companion have eventual operator norm `≤ 1`, and the chart symbol of the word is bounded by `1` on
`UR R × Tb`. Proof: `FullWickH6.pair_list_prod` on the generators `bilinear p.1 p.2` with `C = K = 1`, where each
generator is good by `FullWickH8.static_gen_good`; the powers `1 ^ length` reduce to `1`. -/
theorem static_word_bounds (hκ : 0 < κ) {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}
    (hU : UniformStatic (L := L) hκ j q) {Θ : Type*} (Tb : Set Θ) (R : ℝ) (w : List (ℤ × ℤ)) :
    (∀ᶠ n : ℕ in atTop,
        ‖orderedWord (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) w‖ ≤ 1) ∧
    (∀ᶠ n : ℕ in atTop,
        ‖((w.map fun p => BalancedWickDefinition.quantization
          (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) (gensym p.2 p.1)).reverse).prod‖ ≤ 1) ∧
    (∀ u ∈ UR (L := L) R, ∀ t ∈ Tb,
        ‖evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (wordSym w)‖ ≤ 1) := by
  have hgood : ∀ p ∈ w, GoodFactor (H := fun n => HN L (n + 1))
      (fun (p : ℤ × ℤ) (n : ℕ) => BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) (bilinear p.1 p.2))
      (fun (p : ℤ × ℤ) (n : ℕ) => BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) (bilinear p.2 p.1))
      (fun (p : ℤ × ℤ) (u : L2T L) (_ : Θ) =>
        evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (gensym p.1 p.2))
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u) 1 1 p :=
    fun p _ => FullWickH8.static_gen_good hκ hU Tb R p
  obtain ⟨_, hnorm, hnorm', hsym⟩ := pair_list_prod (H := fun n => HN L (n + 1)) _ _ _
    (UR (L := L) R) Tb _ 1 1 zero_le_one zero_le_one w hgood
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hnorm] with n hn
    rw [one_pow] at hn
    exact hn
  · filter_upwards [hnorm'] with n hn
    rw [one_pow] at hn
    exact hn
  · intro u hu t ht
    have h := hsym u hu t ht
    rw [one_pow] at h
    have e : evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (wordSym w)
        = (w.map fun p => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (gensym p.1 p.2)).prod := by
      rw [evalSym_wordSym]
      congr 1
      apply List.map_congr_left
      intro p _
      exact (evalSym_gensym _ _ _).symm
    rw [e]
    exact h

/-- **Ordered words, norm-close preparations (static).** For every fixed word `w` of Cartesian generators,
the ordered product `E_{a_1 b_1} ⋯ E_{a_k b_k}` on the Q06 static gauge has the uniform strong pair with symbol
`evalSym (chart Φ u) (wordSym w)` on `UR R × Tb`, and its companion (the reversed product of adjoints) has the
conjugate symbol, on every uniformly norm-close normalized preparation `ψ'`. -/
theorem static_word_normClose (hκ : 0 < κ) {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}
    (hU : UniformStatic (L := L) hκ j q) {Θ : Type*} (Tb : Set Θ) (R : ℝ) (w : List (ℤ × ℤ))
    {ψ' : L2T L → Θ → ∀ n : ℕ, HN L (n + 1)}
    (hprep : IsNormClosePrepT (H := fun n => HN L (n + 1)) ψ'
      (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u) (UR (L := L) R) Tb) :
    HasUniformPairT (H := fun n => HN L (n + 1))
      (fun n => orderedWord (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) w)
      (fun n => ((w.map fun p => BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) (gensym p.2 p.1)).reverse).prod)
      (UR (L := L) R) Tb ψ'
      (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (wordSym w)) := by
  obtain ⟨hA, hA', hK⟩ := static_word_bounds hκ hU Tb R w
  exact hasUniformPairT_of_normClose (C := 1) (K := 1) hA hA' hK
    (FullWickH8.static_word_pair hκ hU Tb R w) hprep.2

/-- **Operator component on norm-close preparations (static), via the ordered-product transfer.**
`FullWickH7.list_prod_normClose` applied to the same list of good generators gives the uniform strong symbol of the
ordered product on `ψ'` directly. Consistency corollary of `static_word_normClose`. -/
theorem static_word_normClose_strong (hκ : 0 < κ) {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}
    (hU : UniformStatic (L := L) hκ j q) {Θ : Type*} (Tb : Set Θ) (R : ℝ) (w : List (ℤ × ℤ))
    {ψ' : L2T L → Θ → ∀ n : ℕ, HN L (n + 1)}
    (hprep : IsNormClosePrepT (H := fun n => HN L (n + 1)) ψ'
      (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u) (UR (L := L) R) Tb) :
    HasUniformStrongT (H := fun n => HN L (n + 1))
      (fun n => orderedWord (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) w)
      (UR (L := L) R) Tb ψ'
      (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (wordSym w)) := by
  have hgood : ∀ p ∈ w, GoodFactor (H := fun n => HN L (n + 1))
      (fun (p : ℤ × ℤ) (n : ℕ) => BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) (bilinear p.1 p.2))
      (fun (p : ℤ × ℤ) (n : ℕ) => BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) (bilinear p.2 p.1))
      (fun (p : ℤ × ℤ) (u : L2T L) (_ : Θ) =>
        evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (gensym p.1 p.2))
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u) 1 1 p :=
    fun p _ => FullWickH8.static_gen_good hκ hU Tb R p
  have h := list_prod_normClose (H := fun n => HN L (n + 1)) _ _ _ (UR (L := L) R) Tb ψ'
    (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u) 1 1 zero_le_one zero_le_one w hgood hprep
  have e : (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (wordSym w))
      = (fun (u : L2T L) (_ : Θ) => (w.map fun p =>
          evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (gensym p.1 p.2)).prod) := by
    funext u t
    rw [evalSym_wordSym]
    congr 1
    apply List.map_congr_left
    intro p _
    exact (evalSym_gensym _ _ _).symm
  rw [e]
  exact h

/-- **Scaled Dirac commutator on norm-close preparations (static).** For balanced `f, g` with labels in `S`,
`-iN[W^q_N(f), W^q_N(g)]` (with `N = n + 1`) has the uniform strong symbol `evalSym (chart Φ u) (pb S f g)`,
the bracket polynomial `{f,g}`, on `UR R × Tb` and on every uniformly norm-close normalized preparation `ψ'`. -/
theorem static_dirac_normClose (hκ : 0 < κ) {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}
    (hU : UniformStatic (L := L) hκ j q) {Θ : Type*} (Tb : Set Θ) (R : ℝ) {f g : Sym}
    (hf : Balanced f) (hg : Balanced g) {S : Finset ℤ} (hSf : labelsOf f ⊆ S) (hSg : labelsOf g ⊆ S)
    {ψ' : L2T L → Θ → ∀ n : ℕ, HN L (n + 1)}
    (hprep : IsNormClosePrepT (H := fun n => HN L (n + 1)) ψ'
      (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u) (UR (L := L) R) Tb) :
    HasUniformStrongT (H := fun n => HN L (n + 1))
      (fun n => (-(Complex.I) * ((n + 1 : ℕ) : ℂ)) •
        (BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) f
          * BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g
          - BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g
          * BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) f))
      (UR (L := L) R) Tb ψ'
      (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (pb S f g)) := by
  have hA : ∀ n : ℕ, ‖(-(Complex.I) * ((n + 1 : ℕ) : ℂ)) •
        (BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) f
          * BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g
          - BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g
          * BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) f)‖
      ≤ coeffNorm (pb S f g) + |Cfg f g + Cfg g f| := by
    intro n
    have hN : 0 < n + 1 := Nat.succ_pos n
    have h := FullWickH1.quantization_Dirac_bound (N := n + 1) hN
      (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) hf hg hSf hSg
    have hQ := FullWickH1.quantization_coeff_bound (N := n + 1) hN
      (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) (balanced_pb S hf hg)
    have hT := norm_sub_norm_le ((-(Complex.I) * ((n + 1 : ℕ) : ℂ)) •
        (BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) f
          * BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g
          - BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g
          * BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) f))
      (BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q)
        (pb S f g))
    have hy0 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
    have hy1 : ((n + 1 : ℕ) : ℝ)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hD : (Cfg f g + Cfg g f) * ((n + 1 : ℕ) : ℝ)⁻¹ ≤ |Cfg f g + Cfg g f| :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) hy0).trans
        (mul_le_of_le_one_right (abs_nonneg _) hy1)
    linarith
  exact hasUniformStrongT_of_normClose (Filter.Eventually.of_forall hA)
    (fun u hu t _ => FullWickH8.chart_evalSym_norm_le hκ hu.1 (pb S f g))
    (FullWickH8.static_dirac hκ hU Tb R hf hg hSf hSg) hprep.2

end NormClose

end QuantumNLS.FullWickH11

#print axioms QuantumNLS.FullWickH11.static_word_bounds
#print axioms QuantumNLS.FullWickH11.static_word_normClose
#print axioms QuantumNLS.FullWickH11.static_word_normClose_strong
#print axioms QuantumNLS.FullWickH11.static_dirac_normClose
