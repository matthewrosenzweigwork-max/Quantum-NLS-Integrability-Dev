import QuantumNLS.WickBounds

/-!
# Bounded Wick sequences versus `SpectralUpperBound` ordered polynomials

Source: `chapters/core/wick_calculus.tex` (`thm:full-wick`, proof: "any fixed ordered product of the
corresponding `E^q_{N,ab}` differs from its Wick monomial by `O(N⁻¹)` in operator norm"; the
`C*`-quotient step).  This module closes, for FINITE LINEAR COMBINATIONS of ordered words in the
Cartesian generators, the comparison hypothesis of
`SpectralUpperBound.limsup_le_sup_of_inv_nat_comparison`: the actual bounded Wick sequence
`N ↦ W^q_N(∑ c_k ∏ z_{a} z̄_{b})` (normalized Hilbert operators of `WickBounds`) differs from the
ordered polynomial sequence of gauged transfers `E^q_{N,ab}` by `O(N⁻¹)`.  The comparison is
PROVED from `WickBounds.word_comparison` and linearity of `W^q_N`, not assumed.

Qualifications: the gauge is any supplied unit-modulus family `q N` (no Bethe gauge is selected);
no physical U4/U5 identification, no coherent-state lower bound and no equality
`eq:full-norm-limit` is asserted -- only the upper bound by the classical unit-ball supremum.
-/

namespace QuantumNLS.WickSpectralBridge

open QuantumNLS.Occupation QuantumNLS.WickSymbols QuantumNLS.WickBounds
open QuantumNLS.OccupationHilbert Filter

noncomputable section

/-! ### Linearity of `h ↦ W_N(h)` on balanced symbols -/

lemma WS_add {N : ℕ} {f g : Sym} (hf : Balanced f) (hg : Balanced g) (v : Sector N) :
    WS N (f + g) v = WS N f v + WS N g v := by
  apply emb_injective N
  simp only [map_add, emb_WS (balanced_add hf hg), emb_WS hf, emb_WS hg, LinearMap.add_apply]

lemma WS_smul {N : ℕ} (c : ℂ) {f : Sym} (hf : Balanced f) (v : Sector N) :
    WS N (c • f) v = c • WS N f v := by
  apply emb_injective N
  simp only [map_smul, emb_WS (balanced_smul c hf), emb_WS hf, LinearMap.smul_apply]

lemma WS_zero {N : ℕ} (v : Sector N) : WS N (0 : Sym) v = 0 := by
  apply emb_injective N
  rw [emb_WS balanced_zero, map_zero, map_zero, LinearMap.zero_apply]

theorem WHil_add {N : ℕ} (hN : 0 < N) {f g : Sym} (hf : Balanced f) (hg : Balanced g) :
    WHil N (f + g) = WHil N f + WHil N g := by
  apply ext_core N
  intro v
  rw [WHil_core hN (balanced_add hf hg), add_apply, WHil_core hN hf,
    WHil_core hN hg, WS_add hf hg, map_add]

theorem WHil_smul {N : ℕ} (hN : 0 < N) (c : ℂ) {f : Sym} (hf : Balanced f) :
    WHil N (c • f) = c • WHil N f := by
  apply ext_core N
  intro v
  rw [WHil_core hN (balanced_smul c hf), smul_apply, WHil_core hN hf,
    WS_smul c hf, map_smul]

theorem WHil_zero {N : ℕ} (hN : 0 < N) : WHil N (0 : Sym) = 0 := by
  apply ext_core N
  intro v
  rw [WHil_core hN balanced_zero, WS_zero, map_zero]; rfl

/-! ### Polynomial symbols and their gauged Wick operators -/

variable {κ : Type*}

/-- `∑_k c_k ∏_j z_{a_{kj}} z̄_{b_{kj}}`: the symbol of a finite combination of ordered words. -/
def polySym (s : Finset κ) (c : κ → ℂ) (w : κ → List (ℤ × ℤ)) : Sym :=
  ∑ k ∈ s, c k • wordSym (w k)

theorem balanced_polySym (s : Finset κ) (c : κ → ℂ) (w : κ → List (ℤ × ℤ)) :
    Balanced (polySym s c w) :=
  balanced_sum _ _ (fun k _ => balanced_smul _ (balanced_wordSym (w k)))

theorem WHil_polySym {N : ℕ} (hN : 0 < N) (s : Finset κ) (c : κ → ℂ) (w : κ → List (ℤ × ℤ)) :
    WHil N (polySym s c w) = ∑ k ∈ s, c k • WHil N (wordSym (w k)) := by
  classical
  unfold polySym
  induction s using Finset.induction_on with
  | empty => simpa using WHil_zero hN
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      WHil_add hN (balanced_smul _ (balanced_wordSym (w a)))
        (balanced_sum _ _ (fun k _ => balanced_smul _ (balanced_wordSym (w k)))),
      WHil_smul hN _ (balanced_wordSym (w a)), ih]

theorem WHilq_polySym {N : ℕ} (hN : 0 < N) (q : Occ → ℂ) (hq : UnitGauge q) (s : Finset κ)
    (c : κ → ℂ) (w : κ → List (ℤ × ℤ)) :
    WHilq N q hq (polySym s c w) = ∑ k ∈ s, c k • WHilq N q hq (wordSym (w k)) := by
  unfold WHilq
  rw [WHil_polySym hN, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [mul_smul_comm, smul_mul_assoc]

/-- **Polynomial ordered-word comparison**: for every finite combination of ordered words there is
`C ≥ 0` with `‖∑_k c_k ∏ E^q_{N,ab} − W^q_N(∑_k c_k ∏ z z̄)‖ ≤ C/N` for all `N ≥ 1`. -/
theorem poly_comparison (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (s : Finset κ)
    (c : κ → ℂ) (w : κ → List (ℤ × ℤ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N →
      ‖(∑ k ∈ s, c k • (((w k).map fun p => OccupationHilbert.Eq N (q N) (hq N) p.1 p.2).prod))
          - WHilq N (q N) (hq N) (polySym s c w)‖ ≤ C * (N : ℝ)⁻¹ := by
  have hw := fun k => word_comparison q hq (w k)
  choose C hC0 hC using hw
  refine ⟨∑ k ∈ s, ‖c k‖ * C k, Finset.sum_nonneg (fun k _ => mul_nonneg (norm_nonneg _) (hC0 k)),
    fun N hN => ?_⟩
  rw [WHilq_polySym hN]
  have e : (∑ k ∈ s, c k • (((w k).map fun p => OccupationHilbert.Eq N (q N) (hq N) p.1 p.2).prod))
      - ∑ k ∈ s, c k • WHilq N (q N) (hq N) (wordSym (w k))
      = ∑ k ∈ s, c k • ((((w k).map fun p => OccupationHilbert.Eq N (q N) (hq N) p.1 p.2).prod)
          - WHilq N (q N) (hq N) (wordSym (w k))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [smul_sub]
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun k _ => ?_)
  rw [norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC k N hN) (norm_nonneg _)

/-! ### The bounded Wick sequence and the `SpectralUpperBound` interface -/

/-- The bounded operator sequence `N ↦ W^q_N(∑_k c_k ∏ z z̄)` (the `N = 0` component is the
explicit Hilbert operator of the extension; it does not affect any tail statement). -/
@[irreducible] def wickPolySequence (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (s : Finset κ)
    (c : κ → ℂ) (w : κ → List (ℤ × ℤ)) : Gelfand.BoundedSequence OccupationHilbert.Fiber :=
  ⟨fun N => WHilq N (q N) (hq N) (polySym s c w), by
    apply memℓp_infty
    refine ⟨max ‖WHilq 0 (q 0) (hq 0) (polySym s c w)‖ (coeffNorm (polySym s c w)), ?_⟩
    rintro _ ⟨N, rfl⟩
    by_cases hN : N = 0
    · subst hN; exact le_max_left _ _
    · exact (WHilq_norm_le (Nat.pos_of_ne_zero hN) (q N) (hq N) (balanced_polySym s c w)).trans
        (le_max_right _ _)⟩

lemma wickPolySequence_apply (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (s : Finset κ)
    (c : κ → ℂ) (w : κ → List (ℤ × ℤ)) (N : ℕ) :
    wickPolySequence q hq s c w N = WHilq N (q N) (hq N) (polySym s c w) := by
  unfold wickPolySequence; rfl

lemma comp_eventually_poly (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (I : Finset ℤ)
    (s : Finset κ) (c : κ → ℂ) (w : κ → List (I × I)) (X : ∀ N, OccupationHilbert.Fiber N) (C : ℝ)
    (hC : ∀ N : ℕ, 0 < N →
      ‖(∑ k ∈ s, c k • ((((w k).map fun p => ((p.1 : ℤ), (p.2 : ℤ))).map
          fun p => OccupationHilbert.Eq N (q N) (hq N) p.1 p.2).prod)) - X N‖ ≤ C * (N : ℝ)⁻¹) :
    ∀ᶠ N in atTop,
      ‖X N - (SpectralUpperBound.polynomialSequence q hq I s c w) N‖ ≤ (N : ℝ)⁻¹ * C := by
  rw [Filter.eventually_atTop]
  refine ⟨1, fun N hN => ?_⟩
  have h1 := hC N hN
  have hmap : ∀ k, (((w k).map fun p => ((p.1 : ℤ), (p.2 : ℤ))).map
      fun p => OccupationHilbert.Eq N (q N) (hq N) p.1 p.2)
      = (w k).map fun p => OccupationHilbert.Eq N (q N) (hq N) p.1.1 p.2.1 := by
    intro k; rw [List.map_map]; rfl
  simp only [hmap] at h1
  rw [SpectralUpperBound.polynomialSequence_apply, norm_sub_rev, mul_comm]
  exact h1

/-- **Concrete `O(N⁻¹)` comparison.** For every finite combination of ordered words in the
generators `z_a z̄_b` with labels in `I`, the actual bounded Wick sequence differs from the
`SpectralUpperBound.polynomialSequence` (ordered polynomial in the gauged transfers `E^q_{N,ab}`)
by `O(N⁻¹)` in operator norm, for all `N ≥ 1`. -/
theorem wickPoly_comparison (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (I : Finset ℤ)
    (s : Finset κ) (c : κ → ℂ) (w : κ → List (I × I)) :
    ∃ C : ℝ, ∀ᶠ N in atTop,
      ‖(wickPolySequence q hq s c (fun k => (w k).map fun p => ((p.1 : ℤ), (p.2 : ℤ)))) N
        - (SpectralUpperBound.polynomialSequence q hq I s c w) N‖ ≤ (N : ℝ)⁻¹ * C := by
  obtain ⟨C, _, hC⟩ := poly_comparison q hq s c (fun k => (w k).map fun p => ((p.1 : ℤ), (p.2 : ℤ)))
  refine ⟨C, comp_eventually_poly q hq I s c w _ C ?_⟩
  intro N hN
  rw [wickPolySequence_apply]
  exact hC N hN

/-- The Wick sequence and the ordered polynomial sequence define the same class in the
norm-null quotient (the exact interface consumed by `SpectralUpperBound`). -/
theorem wickPoly_normNull (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (I : Finset ℤ)
    (s : Finset κ) (c : κ → ℂ) (w : κ → List (I × I)) :
    Gelfand.NormNull OccupationHilbert.Fiber
      (wickPolySequence q hq s c (fun k => (w k).map fun p => ((p.1 : ℤ), (p.2 : ℤ)))
        - SpectralUpperBound.polynomialSequence q hq I s c w) := by
  obtain ⟨C, hC⟩ := wickPoly_comparison q hq I s c w
  exact Gelfand.normNull_of_eventually_norm_le_inv_nat_mul _ _ C hC

/-- **Upper bound for bounded Wick polynomials by the classical unit-ball supremum**:
`limsup_N ‖W^q_N(f)‖ ≤ sup_{‖z‖≤1} |f(z)|` for `f = ∑_k c_k ∏_j z_{a_{kj}} conj z_{b_{kj}}`
(the upper half of `eq:full-norm-limit` for polynomials built from ordered words).
No comparison hypothesis is assumed; it is `wickPoly_comparison`. -/
theorem wick_poly_limsup_le (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (I : Finset ℤ)
    (s : Finset κ) (c : κ → ℂ) (w : κ → List (I × I)) :
    limsup (fun N =>
        ‖wickPolySequence q hq s c (fun k => (w k).map fun p => ((p.1 : ℤ), (p.2 : ℤ))) N‖) atTop
      ≤ SpectralUpperBound.unitBallSup I (SpectralUpperBound.polynomialSymbol I s c w) := by
  obtain ⟨C, hC⟩ := wickPoly_comparison q hq I s c w
  exact SpectralUpperBound.limsup_le_sup_of_inv_nat_comparison q hq I _ s c w C hC

/-! ### Exact symbol factorisation: the classical function of a Wick symbol -/

/-- Classical value of the monomial `z^α z̄^β` at `z : ℤ → ℂ`. -/
def evalMon (z : ℤ → ℂ) (p : Mon) : ℂ :=
  p.1.prod (fun a k => z a ^ k) * p.2.prod (fun a k => (starRingEnd ℂ) (z a) ^ k)

lemma evalMon_add (z : ℤ → ℂ) (p q : Mon) : evalMon z (p + q) = evalMon z p * evalMon z q := by
  unfold evalMon
  have h1 : (p + q).1 = p.1 + q.1 := rfl
  have h2 : (p + q).2 = p.2 + q.2 := rfl
  rw [h1, h2, Finsupp.prod_add_index' (by simp) (fun a m n => pow_add _ _ _),
    Finsupp.prod_add_index' (by simp) (fun a m n => pow_add _ _ _)]
  ring

/-- Evaluation of a polynomial symbol at a point (`z^α z̄^β ↦ ∏ z_a^{α_a} conj(z_a)^{β_a}`). -/
def evalSym (z : ℤ → ℂ) : Sym →ₗ[ℂ] ℂ := symLin (evalMon z)

lemma evalSym_zm (z : ℤ → ℂ) (α β : ℤ →₀ ℕ) : evalSym z (zm α β) = evalMon z (α, β) := by
  unfold evalSym; rw [symLin_zm]

lemma evalSym_mul (z : ℤ → ℂ) (f g : Sym) : evalSym z (f * g) = evalSym z f * evalSym z g := by
  have e : ∀ h : Sym, evalSym z h = ∑ p ∈ h.coeff.support, h.coeff p * evalMon z p := by
    intro h
    exact (symLin_expand _ h).trans (Finset.sum_congr rfl (fun p _ => by simp))
  rw [mul_expand, map_sum, e f, e g, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  rw [map_smul, evalSym_zm, smul_eq_mul]
  show _ * evalMon z (p + q) = _
  rw [evalMon_add]; ring

lemma evalSym_one (z : ℤ → ℂ) : evalSym z (1 : Sym) = 1 := by
  rw [← zm_zero_zero, evalSym_zm]; simp [evalMon]

lemma evalSym_gensym (z : ℤ → ℂ) (a b : ℤ) :
    evalSym z (gensym a b) = z a * (starRingEnd ℂ) (z b) := by
  unfold gensym
  rw [evalSym_zm]
  simp [evalMon, Finsupp.prod_single_index]

/-- The classical function of the ordered-word symbol is the product of `z_a conj z_b`. -/
theorem evalSym_wordSym (z : ℤ → ℂ) (w : List (ℤ × ℤ)) :
    evalSym z (wordSym w) = (w.map fun p => z p.1 * (starRingEnd ℂ) (z p.2)).prod := by
  induction w with
  | nil => exact evalSym_one z
  | cons p w ih =>
    show evalSym z (gensym p.1 p.2 * wordSym w) = _
    rw [evalSym_mul, evalSym_gensym, ih]; simp

/-- Extension of a point of `ℂ^I` by zero to all labels. -/
def zext (I : Finset ℤ) (z : EuclideanSpace ℂ I) : ℤ → ℂ :=
  fun a => if h : a ∈ I then z ⟨a, h⟩ else 0

/-- **Exact symbol factorisation**: the classical function of the Wick symbol
`∑_k c_k ∏_j z_{a_{kj}} z̄_{b_{kj}}` at (the zero-extension of) `z ∈ ℂ^I` is exactly
`SpectralUpperBound.polynomialSymbol` (so the supremum in `wick_poly_limsup_le` is the supremum of
the classical Wick symbol over the unit ball). -/
theorem evalSym_polySym (I : Finset ℤ) (s : Finset κ) (c : κ → ℂ) (w : κ → List (I × I))
    (z : EuclideanSpace ℂ I) :
    evalSym (zext I z) (polySym s c (fun k => (w k).map fun p => ((p.1 : ℤ), (p.2 : ℤ))))
      = SpectralUpperBound.polynomialSymbol I s c w z := by
  unfold polySym SpectralUpperBound.polynomialSymbol
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, evalSym_wordSym, smul_eq_mul]
  congr 1
  unfold SpectralUpperBound.wordSymbol
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp [zext, Function.comp]

/-! ### Arbitrary balanced symbols: pairing into ordered words -/

lemma list_single_sum_apply (l : List ℤ) (x : ℤ) :
    ((l.map fun a => (Finsupp.single a 1 : ℤ →₀ ℕ)).sum) x = l.count x := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, Finsupp.add_apply, ih, Finsupp.single_apply, List.count_cons]
    by_cases h : a = x <;> simp [h, add_comm]

lemma sum_labels (α : ℤ →₀ ℕ) : ((labels α).map fun a => (Finsupp.single a 1 : ℤ →₀ ℕ)).sum = α := by
  ext x
  rw [list_single_sum_apply]
  unfold labels
  rw [← Multiset.coe_count, Multiset.coe_toList, Finsupp.count_toMultiset]

lemma zm_zip (la lb : List ℤ) (h : la.length = lb.length) :
    zm ((la.map fun a => (Finsupp.single a 1 : ℤ →₀ ℕ)).sum)
        ((lb.map fun a => (Finsupp.single a 1 : ℤ →₀ ℕ)).sum) = wordSym (la.zip lb) := by
  induction la generalizing lb with
  | nil =>
    cases lb with
    | nil => simpa [wordSym] using zm_zero_zero
    | cons _ _ => simp at h
  | cons a la ih =>
    cases lb with
    | nil => simp at h
    | cons b lb =>
      simp only [List.map_cons, List.sum_cons, List.zip_cons_cons]
      rw [← zm_mul]
      exact congrArg (zm (Finsupp.single a 1) (Finsupp.single b 1) * ·) (ih lb (by simpa using h))

/-- **Exact symbol factorisation of a balanced monomial**: `z^α z̄^β` is the ordered word obtained
by pairing the label lists of `α` and `β` (any pairing gives the same symbol; `|α| = |β|`). -/
theorem zm_eq_wordSym {α β : ℤ →₀ ℕ} (h : α.degree = β.degree) :
    zm α β = wordSym ((labels α).zip (labels β)) := by
  have := zm_zip (labels α) (labels β) (by rw [labels_length, labels_length, h])
  rwa [sum_labels, sum_labels] at this

/-- Every balanced symbol is a finite combination of ordered words (one word per monomial). -/
theorem balanced_eq_polySym {f : Sym} (hf : Balanced f) :
    f = polySym f.coeff.support f.coeff (fun p => (labels p.1).zip (labels p.2)) := by
  conv_lhs => rw [sym_expand f]
  unfold polySym
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [← zm_eq_wordSym (hf p hp)]
  unfold zm
  rw [AddMonoidAlgebra.smul_single', mul_one]

/-- The ordered `I × I`-word of a monomial (pairs of labels outside `I` are dropped; irrelevant
when all labels lie in `I`, see `map_wordI`). -/
def wordI (I : Finset ℤ) (p : Mon) : List (I × I) :=
  ((labels p.1).zip (labels p.2)).filterMap fun ab =>
    if ha : ab.1 ∈ I then (if hb : ab.2 ∈ I then some (⟨ab.1, ha⟩, ⟨ab.2, hb⟩) else none) else none

lemma map_filterMap_wordI (I : Finset ℤ) (l : List (ℤ × ℤ)) (hl : ∀ ab ∈ l, ab.1 ∈ I ∧ ab.2 ∈ I) :
    (l.filterMap fun ab =>
      if ha : ab.1 ∈ I then (if hb : ab.2 ∈ I then some (⟨ab.1, ha⟩, ⟨ab.2, hb⟩) else none)
        else none).map (fun p : I × I => ((p.1 : ℤ), (p.2 : ℤ))) = l := by
  induction l with
  | nil => simp
  | cons ab l ih =>
    have h1 := hl ab (List.mem_cons_self)
    have ih' := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    simp [h1.1, h1.2, ih']

/-- Labels of a monomial lie in `I`. -/
def LabelsIn (I : Finset ℤ) (f : Sym) : Prop :=
  ∀ p ∈ f.coeff.support, ∀ a, (p.1 a ≠ 0 ∨ p.2 a ≠ 0) → a ∈ I

lemma map_wordI (I : Finset ℤ) {f : Sym} (hI : LabelsIn I f) (p : Mon) (hp : p ∈ f.coeff.support) :
    (wordI I p).map (fun q : I × I => ((q.1 : ℤ), (q.2 : ℤ))) = (labels p.1).zip (labels p.2) := by
  unfold wordI
  apply map_filterMap_wordI
  intro ab hab
  exact ⟨hI p hp ab.1 (Or.inl (mem_labels (List.of_mem_zip hab).1)),
    hI p hp ab.2 (Or.inr (mem_labels (List.of_mem_zip hab).2))⟩

theorem balanced_eq_polySym_I (I : Finset ℤ) {f : Sym} (hb : Balanced f) (hI : LabelsIn I f) :
    f = polySym f.coeff.support f.coeff
      (fun p => (wordI I p).map fun q : I × I => ((q.1 : ℤ), (q.2 : ℤ))) := by
  conv_lhs => rw [balanced_eq_polySym hb]
  unfold polySym
  refine Finset.sum_congr rfl (fun p hp => ?_)
  beta_reduce
  rw [map_wordI I hI p hp]

/-- **Concrete `O(N⁻¹)` comparison for an arbitrary balanced symbol** whose labels lie in `I`:
`W^q_N(f)` differs from the ordered polynomial in the gauged transfers `E^q_{N,ab}` (one ordered
word per monomial) by `O(N⁻¹)`. -/
theorem wickBalanced_comparison (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (I : Finset ℤ)
    {f : Sym} (hb : Balanced f) (hI : LabelsIn I f) :
    ∃ C : ℝ, ∀ᶠ N in atTop,
      ‖WHilq N (q N) (hq N) f
        - (SpectralUpperBound.polynomialSequence q hq I f.coeff.support f.coeff (wordI I)) N‖
          ≤ (N : ℝ)⁻¹ * C := by
  obtain ⟨C, hC⟩ := wickPoly_comparison q hq I f.coeff.support f.coeff (wordI I)
  refine ⟨C, ?_⟩
  have e := balanced_eq_polySym_I I hb hI
  filter_upwards [hC] with N hN
  rw [wickPolySequence_apply, ← e] at hN
  exact hN

/-- **Upper bound for an arbitrary balanced Wick symbol**: for a balanced polynomial symbol `f`
with labels in `I`,
`limsup_N ‖W^q_N(f)‖ ≤ sup_{‖z‖≤1} |f(z)|`, where `f(z) = evalSym (zext I z) f` is the classical
function of the symbol on `ℂ^I` (one-sided: no lower bound, no equality `eq:full-norm-limit`). -/
theorem wick_balanced_limsup_le (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (I : Finset ℤ)
    {f : Sym} (hb : Balanced f) (hI : LabelsIn I f) :
    limsup (fun N => ‖WHilq N (q N) (hq N) f‖) atTop
      ≤ SpectralUpperBound.unitBallSup I (fun z => evalSym (zext I z) f) := by
  have e := balanced_eq_polySym_I I hb hI
  have h := wick_poly_limsup_le q hq I f.coeff.support f.coeff (wordI I)
  have hfun : SpectralUpperBound.polynomialSymbol I f.coeff.support f.coeff (wordI I)
      = fun z => evalSym (zext I z) f := by
    funext z
    rw [← evalSym_polySym]
    exact congrArg (fun g => evalSym (zext I z) g) e.symm
  rw [hfun] at h
  simp only [wickPolySequence_apply, ← e] at h
  exact h

/-! Axiom audit (printed at compile time). -/
#print axioms WHil_add
#print axioms WHil_smul
#print axioms WHil_zero
#print axioms WHil_polySym
#print axioms WHilq_polySym
#print axioms poly_comparison
#print axioms wickPoly_comparison
#print axioms wickPoly_normNull
#print axioms wick_poly_limsup_le
#print axioms evalSym_mul
#print axioms evalSym_wordSym
#print axioms evalSym_polySym
#print axioms zm_eq_wordSym
#print axioms balanced_eq_polySym
#print axioms wickBalanced_comparison
#print axioms wick_balanced_limsup_le

end

end QuantumNLS.WickSpectralBridge
