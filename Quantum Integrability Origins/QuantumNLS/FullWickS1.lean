import QuantumNLS.FullWickH1

/-! FullWickS1 (sonnet_fourier, R-140AE34B `thm:full-wick`, Stage 3, ITEM 3: monomial-to-ordered-word
comparison for the DEF-032 operator).

Printed source: source-text/chapters/core/wick_calculus.tex, proof of `thm:full-wick`:
  * lines 120-123: "A balanced monomial can be factored into bilinears `c_{ab}`. Repeated use of
    \eqref{eq:full-normal-order} shows that any fixed ordered product of the corresponding
    `E^q_{N,ab}` differs from its Wick monomial by `O(N^{-1})` in operator norm. All shorter terms
    are bounded by \eqref{eq:full-coefficient-bound}. This is a finite algebraic comparison depending
    only on the chosen monomial."
  * lines 182-183: "Each fixed Wick monomial is an ordered product of Cartesian generators plus a
    bounded `O(N^{-1})` error."

Formal reading.  `E^q_{N,ab} = W_N^q(c_{ab})` with `c_{ab} = z_a z̄_b` (printed eq:gauge-conjugation,
DEF-026; the identification of this operator with the realized RD-level generator is NOT claimed
here, it is the separate gauge-conjugation item).  `W_N^q` is the DEF-032 operator
`BalancedWickDefinition.quantization b G`, for ANY Bethe basis `b` and occupation gauge `G` (so also
the selected full gauge `q_N`), any `L > 0` and every `N ≥ 1`.  The constant depends only on the
chosen ordered word (explicit recursion `wordConst`), never on `L`, `N`, `b`, `G`.

Contents:
  * `wordAlpha`, `wordBeta`, `wordSym_eq_zm`: the ordered word `∏ z_{a_j} z̄_{b_j}` is the monomial
    `z^α z̄^β` with `α = Σ e_{a_j}`, `β = Σ e_{b_j}`.
  * `exists_word`: every balanced monomial (`|α| = |β|`) factors into bilinears (the printed
    "can be factored into bilinears").
  * `ordered_word_comparison`: `‖∏_j Q(c_{a_j b_j}) − Q(wordSym w)‖ ≤ wordConst w / N` for the DEF-032
    operator `Q = quantization b G`, built from `FullWickH1.quantization_product_bound` (the exact
    normal-ordering identity eq:full-product at `|γ| ≤ 1`, remainder by eq:full-Cfg) and
    `FullWickH1.quantization_coeff_bound` (shorter terms).
  * `monomial_ordered_word_comparison`: the printed statement for a monomial `z^α z̄^β`.
  * `poly_ordered_word_comparison`, `balanced_ordered_word_comparison`: the same for finite linear
    combinations, in particular for the Wick operator of an arbitrary balanced polynomial `f`
    (and for `BalancedWickDefinition.wick b G f` via `wick_ordered_word_comparison`).

Standard axioms only (no placeholder proofs, no added hypotheses beyond the stated ones); reuses frozen FullWickH1, WickBounds, WickSpectralBridge,
BalancedWickDefinition (read/import only).
-/

noncomputable section
open scoped BigOperators InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace QuantumNLS.FullWickS1

open QuantumNLS.Occupation QuantumNLS.WickSymbols QuantumNLS.WickBounds
open QuantumNLS.WickSpectralBridge QuantumNLS.OccupationHilbert
open QuantumNLS.BalancedWickDefinition QuantumNLS.BetheCoefficientTransform
open QuantumNLS.FullWickH1

/-! ### Words, monomials and the factorization into bilinears -/

/-- The `z`-exponent `Σ_j e_{a_j}` of the word `∏_j z_{a_j} z̄_{b_j}`. -/
def wordAlpha (w : List (ℤ × ℤ)) : ℤ →₀ ℕ := (w.map fun p => Finsupp.single p.1 1).sum

/-- The `z̄`-exponent `Σ_j e_{b_j}` of the word `∏_j z_{a_j} z̄_{b_j}`. -/
def wordBeta (w : List (ℤ × ℤ)) : ℤ →₀ ℕ := (w.map fun p => Finsupp.single p.2 1).sum

lemma wordAlpha_nil : wordAlpha [] = 0 := by simp [wordAlpha]
lemma wordBeta_nil : wordBeta [] = 0 := by simp [wordBeta]

lemma wordAlpha_cons (p : ℤ × ℤ) (w : List (ℤ × ℤ)) :
    wordAlpha (p :: w) = Finsupp.single p.1 1 + wordAlpha w := by simp [wordAlpha]

lemma wordBeta_cons (p : ℤ × ℤ) (w : List (ℤ × ℤ)) :
    wordBeta (p :: w) = Finsupp.single p.2 1 + wordBeta w := by simp [wordBeta]

/-- The ordered word of generators is the monomial `z^α z̄^β` with the exponents of the word. -/
theorem wordSym_eq_zm (w : List (ℤ × ℤ)) : wordSym w = zm (wordAlpha w) (wordBeta w) := by
  induction w with
  | nil => rw [wordAlpha_nil, wordBeta_nil, zm_zero_zero]; rfl
  | cons p w ih =>
    show gensym p.1 p.2 * wordSym w = _
    rw [ih, gensym, zm_mul, wordAlpha_cons, wordBeta_cons]

lemma toMultiset_wordAlpha (w : List (ℤ × ℤ)) :
    Finsupp.toMultiset (wordAlpha w) = ((w.map Prod.fst : List ℤ) : Multiset ℤ) := by
  induction w with
  | nil => rw [wordAlpha_nil]; simp
  | cons p w ih =>
    rw [wordAlpha_cons, map_add, ih, Finsupp.toMultiset_single, one_smul]
    simp

lemma toMultiset_wordBeta (w : List (ℤ × ℤ)) :
    Finsupp.toMultiset (wordBeta w) = ((w.map Prod.snd : List ℤ) : Multiset ℤ) := by
  induction w with
  | nil => rw [wordBeta_nil]; simp
  | cons p w ih =>
    rw [wordBeta_cons, map_add, ih, Finsupp.toMultiset_single, one_smul]
    simp

lemma card_toMultiset_eq_degree (f : ℤ →₀ ℕ) : Multiset.card (Finsupp.toMultiset f) = f.degree := by
  rw [Finsupp.card_toMultiset]
  simp [Finsupp.sum, Finsupp.degree_apply]

/-- **A balanced monomial can be factored into bilinears** (printed, proof of `thm:full-wick`):
for `|α| = |β|` there is a finite list of pairs `(a_j, b_j)` with `Σ e_{a_j} = α` and
`Σ e_{b_j} = β`, i.e. `z^α z̄^β = ∏_j z_{a_j} z̄_{b_j} = ∏_j c_{a_j b_j}`. -/
theorem exists_word (α β : ℤ →₀ ℕ) (h : α.degree = β.degree) :
    ∃ w : List (ℤ × ℤ), wordAlpha w = α ∧ wordBeta w = β := by
  classical
  have hla : ((Finsupp.toMultiset α).toList).length = α.degree := by
    rw [Multiset.length_toList, card_toMultiset_eq_degree]
  have hlb : ((Finsupp.toMultiset β).toList).length = β.degree := by
    rw [Multiset.length_toList, card_toMultiset_eq_degree]
  refine ⟨(Finsupp.toMultiset α).toList.zip (Finsupp.toMultiset β).toList, ?_, ?_⟩
  · have hm : Finsupp.toMultiset (wordAlpha ((Finsupp.toMultiset α).toList.zip
          (Finsupp.toMultiset β).toList)) = Finsupp.toMultiset α := by
      rw [toMultiset_wordAlpha, List.map_fst_zip (by rw [hla, hlb, h])]
      exact Multiset.coe_toList _
    calc wordAlpha ((Finsupp.toMultiset α).toList.zip (Finsupp.toMultiset β).toList)
        = Multiset.toFinsupp (Finsupp.toMultiset (wordAlpha ((Finsupp.toMultiset α).toList.zip
            (Finsupp.toMultiset β).toList))) := (Finsupp.toMultiset_toFinsupp _).symm
      _ = Multiset.toFinsupp (Finsupp.toMultiset α) := by rw [hm]
      _ = α := Finsupp.toMultiset_toFinsupp _
  · have hm : Finsupp.toMultiset (wordBeta ((Finsupp.toMultiset α).toList.zip
          (Finsupp.toMultiset β).toList)) = Finsupp.toMultiset β := by
      rw [toMultiset_wordBeta, List.map_snd_zip (by rw [hla, hlb, h])]
      exact Multiset.coe_toList _
    calc wordBeta ((Finsupp.toMultiset α).toList.zip (Finsupp.toMultiset β).toList)
        = Multiset.toFinsupp (Finsupp.toMultiset (wordBeta ((Finsupp.toMultiset α).toList.zip
            (Finsupp.toMultiset β).toList))) := (Finsupp.toMultiset_toFinsupp _).symm
      _ = Multiset.toFinsupp (Finsupp.toMultiset β) := by rw [hm]
      _ = β := Finsupp.toMultiset_toFinsupp _

/-! ### Norm of a monomial operator and the explicit constant -/

lemma coeffNorm_zm (α β : ℤ →₀ ℕ) : coeffNorm (zm α β) = 1 := by
  unfold coeffNorm zm
  have hs : (AddMonoidAlgebra.single (α, β) (1 : ℂ)).coeff.support = {(α, β)} := by
    rw [AddMonoidAlgebra.coeff_single, Finsupp.support_single_ne_zero _ one_ne_zero]
  rw [hs, Finset.sum_singleton, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  simp

/-- Every monomial operator has norm at most one (printed, after eq:full-Wick). -/
theorem quantization_zm_norm_le {L : ℝ} [Fact (0 < L)] {N : ℕ} (hN : 0 < N) (b : BetheBasis L N)
    (G : BetheOccupationGauge.Gauge) (α β : ℤ →₀ ℕ) (h : α.degree = β.degree) :
    ‖quantization b G (zm α β)‖ ≤ 1 :=
  (quantization_coeff_bound hN b G (balanced_monomial α β h)).trans (coeffNorm_zm α β).le

theorem quantization_gensym_norm_le {L : ℝ} [Fact (0 < L)] {N : ℕ} (hN : 0 < N)
    (b : BetheBasis L N) (G : BetheOccupationGauge.Gauge) (a c : ℤ) :
    ‖quantization b G (gensym a c)‖ ≤ 1 :=
  quantization_zm_norm_le hN b G _ _ (by simp)

/-- The first-order symbol `S_1 + i{·,·}/2 = C_1` of the printed product bound, for the pair
`(c_{ab}, word)`. -/
def stepSym (p : ℤ × ℤ) (w : List (ℤ × ℤ)) : Sym :=
  S1 {p.1} (gensym p.1 p.2) (wordSym w) + (Complex.I / 2) • pb {p.1} (gensym p.1 p.2) (wordSym w)

/-- The explicit constant of the ordered-word comparison: it depends only on the word. -/
def wordConst : List (ℤ × ℤ) → ℝ
  | [] => 0
  | p :: w => wordConst w + Cfg (gensym p.1 p.2) (wordSym w) + coeffNorm (stepSym p w)

lemma coeffNorm_nonneg (f : Sym) : 0 ≤ coeffNorm f :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem wordConst_nonneg (w : List (ℤ × ℤ)) : 0 ≤ wordConst w := by
  induction w with
  | nil => exact le_refl _
  | cons p w ih =>
    exact add_nonneg (add_nonneg ih (Cfg_nonneg _ _)) (coeffNorm_nonneg _)

/-- The ordered product `E_{a_1 b_1} ⋯ E_{a_k b_k}` of the DEF-032 generators
`E_{ab} = Q(c_{ab}) = Q(z_a z̄_b)`. -/
def orderedWord {L : ℝ} [Fact (0 < L)] {N : ℕ} (b : BetheBasis L N)
    (G : BetheOccupationGauge.Gauge) (w : List (ℤ × ℤ)) : HN L N →L[ℂ] HN L N :=
  (w.map fun p => quantization b G (gensym p.1 p.2)).prod

lemma orderedWord_nil {L : ℝ} [Fact (0 < L)] {N : ℕ} (b : BetheBasis L N)
    (G : BetheOccupationGauge.Gauge) : orderedWord b G [] = 1 := by
  simp [orderedWord]

lemma orderedWord_cons {L : ℝ} [Fact (0 < L)] {N : ℕ} (b : BetheBasis L N)
    (G : BetheOccupationGauge.Gauge) (p : ℤ × ℤ) (w : List (ℤ × ℤ)) :
    orderedWord b G (p :: w) = quantization b G (gensym p.1 p.2) * orderedWord b G w := by
  simp [orderedWord]

/-! ### The comparison (abstract normed-space form) -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Abstract form of the ordered-word comparison: any family `Q : Sym → E →L E` with `Q 1 = 1`, the
coefficient bound and the product bound of `eq:full-product-bound` satisfies the comparison with the
explicit constant `wordConst`. -/
theorem ordered_word_abstract (Q : Sym → E →L[ℂ] E) (N : ℕ) (hN : 0 < N) (h1 : Q 1 = 1)
    (hnorm : ∀ f : Sym, Balanced f → ‖Q f‖ ≤ coeffNorm f)
    (hprod : ∀ {f g : Sym}, Balanced f → Balanced g → ∀ {S : Finset ℤ}, labelsOf f ⊆ S →
      ‖Q f * Q g - Q (f * g) - (N : ℂ)⁻¹ • Q (S1 S f g + (Complex.I / 2) • pb S f g)‖
        ≤ Cfg f g * ((N : ℝ)⁻¹) ^ 2)
    (w : List (ℤ × ℤ)) :
    ‖(w.map fun p => Q (gensym p.1 p.2)).prod - Q (wordSym w)‖ ≤ wordConst w * (N : ℝ)⁻¹ := by
  induction w with
  | nil =>
    have h1' : Q (wordSym ([] : List (ℤ × ℤ))) = 1 := h1
    rw [List.map_nil, List.prod_nil, h1', sub_self, norm_zero]
    simp [wordConst]
  | cons p w ih =>
    set f := gensym p.1 p.2 with hf
    set g := wordSym w with hg
    have hfb : Balanced f := balanced_zm_ab p.1 p.2
    have hgb : Balanced g := balanced_wordSym w
    have hS : labelsOf f ⊆ ({p.1} : Finset ℤ) := labelsOf_gensym p.1 p.2
    set q' : Sym := stepSym p w with hq'
    have hq'b : Balanced q' :=
      balanced_add (balanced_S1 _ hfb hgb) (balanced_smul _ (balanced_pb _ hfb hgb))
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNp : (0 : ℝ) < (N : ℝ)⁻¹ := by positivity
    have hinv : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hNr
    set P := (w.map fun p => Q (gensym p.1 p.2)).prod with hP
    have hws : wordSym (p :: w) = f * g := rfl
    have hQf : ‖Q f‖ ≤ 1 := by
      refine (hnorm f hfb).trans ?_
      rw [hf, gensym, coeffNorm_zm]
    have hprodc : (((p :: w).map fun p => Q (gensym p.1 p.2)).prod) = Q f * P := by
      simp [hP, hf]
    rw [hprodc, hws]
    have hsplit : Q f * P - Q (f * g)
        = Q f * (P - Q g)
          + ((Q f * Q g - Q (f * g) - (N : ℂ)⁻¹ • Q q') + (N : ℂ)⁻¹ • Q q') := by
      rw [mul_sub]; abel
    rw [hsplit]
    have b1 : ‖Q f * (P - Q g)‖ ≤ wordConst w * (N : ℝ)⁻¹ := by
      calc _ ≤ ‖Q f‖ * ‖P - Q g‖ := norm_mul_le _ _
        _ ≤ 1 * (wordConst w * (N : ℝ)⁻¹) :=
            mul_le_mul hQf ih (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    have b2 : ‖Q f * Q g - Q (f * g) - (N : ℂ)⁻¹ • Q q'‖ ≤ Cfg f g * (N : ℝ)⁻¹ := by
      have := hprod hfb hgb hS
      calc _ ≤ Cfg f g * ((N : ℝ)⁻¹) ^ 2 := this
        _ ≤ Cfg f g * (N : ℝ)⁻¹ := by
            apply mul_le_mul_of_nonneg_left _ (Cfg_nonneg _ _)
            nlinarith
    have b3 : ‖(N : ℂ)⁻¹ • Q q'‖ ≤ coeffNorm q' * (N : ℝ)⁻¹ := by
      rw [norm_smul]
      have : ‖(N : ℂ)⁻¹‖ = (N : ℝ)⁻¹ := by simp
      rw [this, mul_comm]
      exact mul_le_mul_of_nonneg_right (hnorm q' hq'b) hNp.le
    calc _ ≤ ‖Q f * (P - Q g)‖
          + ‖(Q f * Q g - Q (f * g) - (N : ℂ)⁻¹ • Q q') + (N : ℂ)⁻¹ • Q q'‖ := norm_add_le _ _
      _ ≤ wordConst w * (N : ℝ)⁻¹
          + (‖Q f * Q g - Q (f * g) - (N : ℂ)⁻¹ • Q q'‖ + ‖(N : ℂ)⁻¹ • Q q'‖) :=
          add_le_add b1 (norm_add_le _ _)
      _ ≤ wordConst w * (N : ℝ)⁻¹ + (Cfg f g * (N : ℝ)⁻¹ + coeffNorm q' * (N : ℝ)⁻¹) :=
          add_le_add_right (add_le_add b2 b3) _
      _ = (wordConst w + Cfg f g + coeffNorm q') * (N : ℝ)⁻¹ := by ring
      _ = wordConst (p :: w) * (N : ℝ)⁻¹ := rfl

/-- Abstract finite-combination form (linearity of `Q` on the combination is a hypothesis). -/
theorem poly_abstract {κ : Type*} (Q : Sym → E →L[ℂ] E) (N : ℕ) (hN : 0 < N) (h1 : Q 1 = 1)
    (hnorm : ∀ f : Sym, Balanced f → ‖Q f‖ ≤ coeffNorm f)
    (hprod : ∀ {f g : Sym}, Balanced f → Balanced g → ∀ {S : Finset ℤ}, labelsOf f ⊆ S →
      ‖Q f * Q g - Q (f * g) - (N : ℂ)⁻¹ • Q (S1 S f g + (Complex.I / 2) • pb S f g)‖
        ≤ Cfg f g * ((N : ℝ)⁻¹) ^ 2)
    (s : Finset κ) (c : κ → ℂ) (w : κ → List (ℤ × ℤ))
    (hlin : Q (polySym s c w) = ∑ k ∈ s, c k • Q (wordSym (w k))) :
    ‖(∑ k ∈ s, c k • (((w k).map fun p => Q (gensym p.1 p.2)).prod)) - Q (polySym s c w)‖
      ≤ (∑ k ∈ s, ‖c k‖ * wordConst (w k)) * (N : ℝ)⁻¹ := by
  rw [hlin, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun k _ => ?_)
  rw [← smul_sub, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (ordered_word_abstract Q N hN h1 hnorm hprod (w k))
    (norm_nonneg _)

end Abstract

/-! ### The comparison for the DEF-032 operator -/

/-- **Ordered-word comparison, explicit constant.**  For every word, every `L > 0`, `N ≥ 1`, Bethe
basis `b` and occupation gauge `G`:
`‖E_{a_1 b_1} ⋯ E_{a_k b_k} − Q(∏_j z_{a_j} z̄_{b_j})‖ ≤ wordConst w · N⁻¹`. -/
theorem ordered_word_comparison {L : ℝ} [Fact (0 < L)] {N : ℕ} (hN : 0 < N) (b : BetheBasis L N)
    (G : BetheOccupationGauge.Gauge) (w : List (ℤ × ℤ)) :
    ‖orderedWord b G w - quantization b G (wordSym w)‖ ≤ wordConst w * (N : ℝ)⁻¹ :=
  ordered_word_abstract (quantization b G) N hN (quantization_constant b G)
    (fun f hf => quantization_coeff_bound hN b G hf)
    (fun hf hg _ hS => quantization_product_bound hN b G hf hg hS) w

/-- **Ordered-word comparison, uniform `O(N⁻¹)` form** (printed: "differs from its Wick monomial by
`O(N^{-1})` in operator norm ... depending only on the chosen monomial"): the constant is chosen
before `L`, `N`, the Bethe basis and the gauge. -/
theorem ordered_word_comparison_uniform (w : List (ℤ × ℤ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) [Fact (0 < L)] (N : ℕ), 0 < N →
      ∀ (b : BetheBasis L N) (G : BetheOccupationGauge.Gauge),
        ‖orderedWord b G w - quantization b G (wordSym w)‖ ≤ C * (N : ℝ)⁻¹ :=
  ⟨wordConst w, wordConst_nonneg w, fun _ _ _ hN b G => ordered_word_comparison hN b G w⟩

/-- **Printed statement for a monomial `z^α z̄^β`.**  (a) The monomial factors into bilinears.
(b) For every factorization `w` (every order of the bilinears, equivalently every word with
`wordAlpha w = α`, `wordBeta w = β`), the ordered product of the DEF-032 generators differs from the
DEF-032 Wick operator `W_N^q(z^α z̄^β) = quantization b G (zm α β)` by at most `wordConst w / N`
in operator norm, for all `L > 0`, `N ≥ 1`, bases and gauges. -/
theorem monomial_ordered_word_comparison (α β : ℤ →₀ ℕ) (h : α.degree = β.degree) :
    (∃ w : List (ℤ × ℤ), wordAlpha w = α ∧ wordBeta w = β) ∧
    ∀ w : List (ℤ × ℤ), wordAlpha w = α → wordBeta w = β →
      ∀ (L : ℝ) [Fact (0 < L)] (N : ℕ), 0 < N →
        ∀ (b : BetheBasis L N) (G : BetheOccupationGauge.Gauge),
          ‖orderedWord b G w - quantization b G (zm α β)‖ ≤ wordConst w * (N : ℝ)⁻¹ := by
  refine ⟨exists_word α β h, fun w hα hβ L _ N hN b G => ?_⟩
  have := ordered_word_comparison hN b G w
  rwa [wordSym_eq_zm, hα, hβ] at this

/-! ### Finite linear combinations: the Wick operator of a balanced polynomial -/

/-- `Q` of a finite combination of words is the combination of the `Q`'s of the words (DEF-032
operator, `N ≥ 1`). -/
theorem quantization_polySym {κ : Type*} {L : ℝ} [Fact (0 < L)] {N : ℕ} (hN : 0 < N)
    (b : BetheBasis L N) (G : BetheOccupationGauge.Gauge) (s : Finset κ) (c : κ → ℂ)
    (w : κ → List (ℤ × ℤ)) :
    quantization b G (polySym s c w) = ∑ k ∈ s, c k • quantization b G (wordSym (w k)) := by
  rw [quantization_eq_conj hN, WHil_polySym hN, conjBy_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [quantization_eq_conj hN]

/-- **Polynomial ordered-word comparison**: for a finite combination `Σ_k c_k ∏_j z z̄` of ordered
words, `‖Σ_k c_k (E-word_k) − Q(Σ_k c_k ∏ z z̄)‖ ≤ (Σ_k |c_k| wordConst w_k) / N`. -/
theorem poly_ordered_word_comparison {κ : Type*} {L : ℝ} [Fact (0 < L)] {N : ℕ} (hN : 0 < N)
    (b : BetheBasis L N) (G : BetheOccupationGauge.Gauge) (s : Finset κ) (c : κ → ℂ)
    (w : κ → List (ℤ × ℤ)) :
    ‖(∑ k ∈ s, c k • orderedWord b G (w k)) - quantization b G (polySym s c w)‖
      ≤ (∑ k ∈ s, ‖c k‖ * wordConst (w k)) * (N : ℝ)⁻¹ :=
  poly_abstract (quantization b G) N hN (quantization_constant b G)
    (fun f hf => quantization_coeff_bound hN b G hf)
    (fun hf hg _ hS => quantization_product_bound hN b G hf hg hS) s c w
    (quantization_polySym hN b G s c w)

/-- A fixed choice of factorization of the monomial `p = (α, β)` into bilinears (empty word when
`p` is not balanced). -/
def monomialWord (p : Mon) : List (ℤ × ℤ) :=
  if h : p.1.degree = p.2.degree then Classical.choose (exists_word p.1 p.2 h) else []

theorem wordSym_monomialWord (p : Mon) (h : p.1.degree = p.2.degree) :
    wordSym (monomialWord p) = zm p.1 p.2 := by
  have hs := Classical.choose_spec (exists_word p.1 p.2 h)
  rw [wordSym_eq_zm]
  have e : monomialWord p = Classical.choose (exists_word p.1 p.2 h) := by
    unfold monomialWord; rw [dif_pos h]
  rw [e, hs.1, hs.2]

/-- A balanced symbol is the combination of its monomials, each written as its chosen word. -/
theorem polySym_monomialWord (f : Sym) (hf : Balanced f) :
    polySym f.coeff.support f.coeff monomialWord = f := by
  unfold polySym
  conv_rhs => rw [sym_expand f]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [wordSym_monomialWord p (hf p hp)]
  simp [zm, AddMonoidAlgebra.smul_single']

/-- The ordered-word operator of a balanced polynomial `f`: `Σ_p f_p · (E-word of p)`. -/
def polyWordOp {L : ℝ} [Fact (0 < L)] {N : ℕ} (b : BetheBasis L N)
    (G : BetheOccupationGauge.Gauge) (f : Sym) : HN L N →L[ℂ] HN L N :=
  ∑ p ∈ f.coeff.support, f.coeff p • orderedWord b G (monomialWord p)

/-- The explicit constant for the polynomial comparison. -/
def polyConst (f : Sym) : ℝ :=
  ∑ p ∈ f.coeff.support, ‖f.coeff p‖ * wordConst (monomialWord p)

theorem polyConst_nonneg (f : Sym) : 0 ≤ polyConst f :=
  Finset.sum_nonneg (fun p _ => mul_nonneg (norm_nonneg _) (wordConst_nonneg _))

/-- **`W(f)` against its ordered-word realization** (the strong-symbol statement of `thm:full-wick`
for `W(f)` itself reduces to the ordered words by this comparison): for a balanced polynomial `f`,
`‖Σ_p f_p E-word(p) − W_N^q(f)‖ ≤ polyConst f / N`, for all `L > 0`, `N ≥ 1`, Bethe bases and
gauges. -/
theorem balanced_ordered_word_comparison {L : ℝ} [Fact (0 < L)] {N : ℕ} (hN : 0 < N)
    (b : BetheBasis L N) (G : BetheOccupationGauge.Gauge) (f : Sym) (hf : Balanced f) :
    ‖polyWordOp b G f - quantization b G f‖ ≤ polyConst f * (N : ℝ)⁻¹ := by
  have h := poly_ordered_word_comparison hN b G f.coeff.support f.coeff monomialWord
  rw [polySym_monomialWord f hf] at h
  exact h

/-- Uniform `O(N⁻¹)` form for a balanced polynomial. -/
theorem balanced_ordered_word_comparison_uniform (f : Sym) (hf : Balanced f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (L : ℝ) [Fact (0 < L)] (N : ℕ), 0 < N →
      ∀ (b : BetheBasis L N) (G : BetheOccupationGauge.Gauge),
        ‖polyWordOp b G f - quantization b G f‖ ≤ K * (N : ℝ)⁻¹ :=
  ⟨polyConst f, polyConst_nonneg f, fun _ _ _ hN b G =>
    balanced_ordered_word_comparison hN b G f hf⟩

/-- The same for the DEF-032 operator `wick b G f` of a `BalancedWickDefinition.Polynomial`. -/
theorem wick_ordered_word_comparison (f : BalancedWickDefinition.Polynomial) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (L : ℝ) [Fact (0 < L)] (N : ℕ), 0 < N →
      ∀ (b : BetheBasis L N) (G : BetheOccupationGauge.Gauge),
        ‖polyWordOp b G f.symbol - wick b G f‖ ≤ K * (N : ℝ)⁻¹ :=
  balanced_ordered_word_comparison_uniform f.symbol f.balanced

end QuantumNLS.FullWickS1

#print axioms QuantumNLS.FullWickS1.wordSym_eq_zm
#print axioms QuantumNLS.FullWickS1.exists_word
#print axioms QuantumNLS.FullWickS1.coeffNorm_zm
#print axioms QuantumNLS.FullWickS1.quantization_zm_norm_le
#print axioms QuantumNLS.FullWickS1.wordConst_nonneg
#print axioms QuantumNLS.FullWickS1.ordered_word_comparison
#print axioms QuantumNLS.FullWickS1.ordered_word_comparison_uniform
#print axioms QuantumNLS.FullWickS1.monomial_ordered_word_comparison
#print axioms QuantumNLS.FullWickS1.quantization_polySym
#print axioms QuantumNLS.FullWickS1.poly_ordered_word_comparison
#print axioms QuantumNLS.FullWickS1.wordSym_monomialWord
#print axioms QuantumNLS.FullWickS1.polySym_monomialWord
#print axioms QuantumNLS.FullWickS1.balanced_ordered_word_comparison
#print axioms QuantumNLS.FullWickS1.balanced_ordered_word_comparison_uniform
#print axioms QuantumNLS.FullWickS1.wick_ordered_word_comparison
