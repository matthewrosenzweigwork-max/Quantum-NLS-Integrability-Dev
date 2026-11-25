import QuantumNLS.CharacterBridge

/-!
# Spectral upper bounds for ordered polynomials

PR11 `3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f`,
`source/chapters/core/wick_calculus.tex:117–158`, R-140AE34B / FIN-EXT025-GP-02.
This is the upper-bound step on the complete occupation coefficient carrier.
The frozen character representation and isometric Gelfand map imply the bound
for finite linear combinations of ordered words in the bilinear generators.
Words retain multiplicity and order before passage to the quotient. Their
classical values are balanced polynomials `z_a conj(z_b)`.

This generic evaluation interface is independent of the balanced Wick-symbol
algebra. Transport to a Wick sequence requires an explicitly proved norm-null
comparison. Physical U4/U5, the selected gauge and the coherent lower bound
are separate obligations.
-/

noncomputable section
open scoped ComplexConjugate Classical ENNReal
open Filter

namespace QuantumNLS.SpectralUpperBound
open Occupation OccupationHilbert CharacterBridge Gelfand

variable (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (I : Finset ℤ)

/-- The frozen Gelfand isometry preserves the norm of every algebra element. -/
theorem quotientGelfand_norm (a : quotientAlgebra q hq I) :
    ‖quotientGelfand q hq I a‖ = ‖a‖ := by
  have h := (quotientGelfand_isometry q hq I).dist_eq a 0
  simpa only [map_zero, dist_zero_right] using h

/-- Generic spectral interface: every character has a unit-ball representative;
it suffices to identify the element's evaluation at that representative. -/
theorem norm_le_of_character_representation
    (a : quotientAlgebra q hq I) (f : EuclideanSpace ℂ I → ℂ)
    (heval : ∀ (φ : WeakDual.characterSpace ℂ (quotientAlgebra q hq I))
      (z : EuclideanSpace ℂ I),
      (∀ a b, characterMatrix q hq I φ a b = z a * conj (z b)) → φ a = f z)
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ z, ‖z‖ ≤ 1 → ‖f z‖ ≤ M) : ‖a‖ ≤ M := by
  rw [← quotientGelfand_norm q hq I a]
  apply (ContinuousMap.norm_le _ hM).mpr
  intro φ
  obtain ⟨z, hz, hzn⟩ := characterMatrix_exists_unitBall_vector q hq I φ
  change ‖φ a‖ ≤ M
  rw [heval φ z hz]
  exact hf z hzn

/-- An ordered word, evaluated in the actual bounded operator sequences. -/
def wordSequence (w : List (I × I)) : BoundedSequence Fiber :=
  (w.map fun p => EqSequence q hq p.1.1 p.2.1).prod

/-- The same word in the closed generated quotient algebra. -/
def wordElement (w : List (I × I)) : quotientAlgebra q hq I :=
  (w.map fun p => generator q hq I p.1 p.2).prod

/-- The classical balanced word, with the source donor/receiver convention. -/
def wordSymbol (w : List (I × I)) (z : EuclideanSpace ℂ I) : ℂ :=
  (w.map fun p => z p.1 * conj (z p.2)).prod

theorem wordSequence_apply (w : List (I × I)) (N : ℕ) :
    wordSequence q hq I w N =
      (w.map fun p => Eq N (q N) (hq N) p.1.1 p.2.1).prod := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    change Eq N (q N) (hq N) p.1.1 p.2.1 * wordSequence q hq I w N = _
    simpa only [List.map_cons, List.prod_cons] using
      congrArg (fun T => Eq N (q N) (hq N) p.1.1 p.2.1 * T) ih

theorem wordElement_coe (w : List (I × I)) :
    (wordElement q hq I w : OccupationQuotient) =
      sequenceQuotientMk Fiber (wordSequence q hq I w) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    change quotientGenerator q hq p.1.1 p.2.1 *
        (wordElement q hq I w : OccupationQuotient) =
      sequenceQuotientMk Fiber (EqSequence q hq p.1.1 p.2.1 * wordSequence q hq I w)
    rw [map_mul, ih]
    rfl

theorem character_wordElement
    (φ : WeakDual.characterSpace ℂ (quotientAlgebra q hq I))
    (z : EuclideanSpace ℂ I)
    (hz : ∀ a b, characterMatrix q hq I φ a b = z a * conj (z b))
    (w : List (I × I)) : φ (wordElement q hq I w) = wordSymbol I w z := by
  induction w with
  | nil =>
    change φ (1 : quotientAlgebra q hq I) = (1 : ℂ)
    exact map_one φ
  | cons p w ih =>
    change φ (generator q hq I p.1 p.2 * wordElement q hq I w) =
      (z p.1 * conj (z p.2)) * wordSymbol I w z
    rw [map_mul]
    exact congrArg₂ (· * ·) (hz p.1 p.2) ih

variable {κ : Type*}

/-- A finite linear combination of ordered words; this is a generic interface,
not a second implementation of the Wick-symbol algebra. -/
def polynomialSequence (s : Finset κ) (c : κ → ℂ) (w : κ → List (I × I)) :
    BoundedSequence Fiber := ∑ k ∈ s, c k • wordSequence q hq I (w k)

def polynomialElement (s : Finset κ) (c : κ → ℂ) (w : κ → List (I × I)) :
    quotientAlgebra q hq I := ∑ k ∈ s, c k • wordElement q hq I (w k)

def polynomialSymbol (s : Finset κ) (c : κ → ℂ) (w : κ → List (I × I))
    (z : EuclideanSpace ℂ I) : ℂ := ∑ k ∈ s, c k * wordSymbol I (w k) z

theorem polynomialSequence_apply (s : Finset κ) (c : κ → ℂ)
    (w : κ → List (I × I)) (N : ℕ) :
    polynomialSequence q hq I s c w N =
      ∑ k ∈ s, c k • ((w k).map fun p => Eq N (q N) (hq N) p.1.1 p.2.1).prod := by
  simp only [polynomialSequence, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, wordSequence_apply]

theorem polynomialElement_coe (s : Finset κ) (c : κ → ℂ) (w : κ → List (I × I)) :
    (polynomialElement q hq I s c w : OccupationQuotient) =
      sequenceQuotientMk Fiber (polynomialSequence q hq I s c w) := by
  change (quotientAlgebra q hq I).subtype (polynomialElement q hq I s c w) = _
  simp only [polynomialElement, polynomialSequence, map_sum, map_smul,
    StarSubalgebra.coe_subtype, wordElement_coe]

theorem character_polynomialElement
    (φ : WeakDual.characterSpace ℂ (quotientAlgebra q hq I))
    (z : EuclideanSpace ℂ I)
    (hz : ∀ a b, characterMatrix q hq I φ a b = z a * conj (z b))
    (s : Finset κ) (c : κ → ℂ) (w : κ → List (I × I)) :
    φ (polynomialElement q hq I s c w) = polynomialSymbol I s c w z := by
  simp only [polynomialElement, polynomialSymbol, map_sum, map_smul, smul_eq_mul,
    character_wordElement q hq I φ z hz]

/-- Uniform polynomial bounds on the finite Euclidean unit ball control the
quotient norm. No surjectivity onto all unit-ball vectors is assumed. -/
theorem polynomialElement_norm_le (s : Finset κ) (c : κ → ℂ)
    (w : κ → List (I × I)) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ z : EuclideanSpace ℂ I, ‖z‖ ≤ 1 → ‖polynomialSymbol I s c w z‖ ≤ M) :
    ‖polynomialElement q hq I s c w‖ ≤ M :=
  norm_le_of_character_representation q hq I _ _
    (fun φ z hz => character_polynomialElement q hq I φ z hz s c w) hM hf

/-- On bounded operator sequences the quotient norm is the actual limsup over
all particle numbers, so this is already a spectral upper bound for words. -/
theorem polynomialSequence_limsup_le (s : Finset κ) (c : κ → ℂ)
    (w : κ → List (I × I)) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ z : EuclideanSpace ℂ I, ‖z‖ ≤ 1 → ‖polynomialSymbol I s c w z‖ ≤ M) :
    limsup (fun N => ‖polynomialSequence q hq I s c w N‖) atTop ≤ M := by
  have h := polynomialElement_norm_le q hq I s c w hM hf
  have heq : ‖polynomialElement q hq I s c w‖ =
      limsup (fun N => ‖polynomialSequence q hq I s c w N‖) atTop := by
    calc
      _ = ‖(polynomialElement q hq I s c w : OccupationQuotient)‖ := rfl
      _ = ‖sequenceQuotientMk Fiber (polynomialSequence q hq I s c w)‖ := by
        rw [polynomialElement_coe]
      _ = _ := sequenceQuotient_norm Fiber _
  rwa [heq] at h

/-- The finite-coordinate unit-ball supremum, in the Euclidean norm. -/
def unitBallSup (f : EuclideanSpace ℂ I → ℂ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' Metric.closedBall (0 : EuclideanSpace ℂ I) 1)

theorem le_unitBallSup (f : EuclideanSpace ℂ I → ℂ) (hf : Continuous f)
    (z : EuclideanSpace ℂ I) (hz : ‖z‖ ≤ 1) : ‖f z‖ ≤ unitBallSup I f := by
  apply le_csSup ((isCompact_closedBall (0 : EuclideanSpace ℂ I) 1).bddAbove_image
    hf.norm.continuousOn)
  exact ⟨z, by simpa only [Metric.mem_closedBall, dist_zero_right] using hz, rfl⟩

theorem unitBallSup_nonneg (f : EuclideanSpace ℂ I → ℂ) (hf : Continuous f) :
    0 ≤ unitBallSup I f :=
  (norm_nonneg (f 0)).trans (le_unitBallSup I f hf 0 (by simp))

/-- The supremum is a maximum, including the empty label set. -/
theorem unitBallSup_attained (f : EuclideanSpace ℂ I → ℂ) (hf : Continuous f) :
    ∃ z : EuclideanSpace ℂ I, ‖z‖ ≤ 1 ∧ unitBallSup I f = ‖f z‖ := by
  obtain ⟨z, hz, hmax⟩ := (isCompact_closedBall (0 : EuclideanSpace ℂ I) 1).exists_isMaxOn
    ⟨0, by simp⟩ hf.norm.continuousOn
  have hzn : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  refine ⟨z, hzn, le_antisymm ?_ (le_unitBallSup I f hf z hzn)⟩
  apply csSup_le
  · exact ⟨‖f 0‖, 0, by simp, rfl⟩
  · rintro r ⟨y, hy, rfl⟩
    exact hmax hy

theorem continuous_wordSymbol (w : List (I × I)) : Continuous (wordSymbol I w) := by
  induction w with
  | nil => exact continuous_const
  | cons p w ih =>
    change Continuous (fun z : EuclideanSpace ℂ I =>
      (z p.1 * conj (z p.2)) * wordSymbol I w z)
    exact ((PiLp.continuous_apply 2 (fun _ : I => ℂ) p.1).mul
      ((PiLp.continuous_apply 2 (fun _ : I => ℂ) p.2).star)).mul ih

theorem continuous_polynomialSymbol (s : Finset κ) (c : κ → ℂ)
    (w : κ → List (I × I)) : Continuous (polynomialSymbol I s c w) := by
  apply continuous_finsetSum
  intro k _
  exact continuous_const.mul (continuous_wordSymbol I (w k))

/-- The isometric Gelfand upper bound with the actual classical supremum. -/
theorem polynomialElement_norm_le_sup (s : Finset κ) (c : κ → ℂ)
    (w : κ → List (I × I)) :
    ‖polynomialElement q hq I s c w‖ ≤ unitBallSup I (polynomialSymbol I s c w) :=
  polynomialElement_norm_le q hq I s c w
    (unitBallSup_nonneg I _ (continuous_polynomialSymbol I s c w))
    (le_unitBallSup I _ (continuous_polynomialSymbol I s c w))

theorem polynomialSequence_limsup_le_sup (s : Finset κ) (c : κ → ℂ)
    (w : κ → List (I × I)) :
    limsup (fun N => ‖polynomialSequence q hq I s c w N‖) atTop ≤
      unitBallSup I (polynomialSymbol I s c w) :=
  polynomialSequence_limsup_le q hq I s c w
    (unitBallSup_nonneg I _ (continuous_polynomialSymbol I s c w))
    (le_unitBallSup I _ (continuous_polynomialSymbol I s c w))

/-- A proved norm-null error preserves the quotient class and hence the limsup
of norms. This is the exact remaining interface for a bounded Wick sequence. -/
theorem limsup_norm_eq_of_normNull (x y : BoundedSequence Fiber)
    (hxy : NormNull Fiber (x - y)) :
    limsup (fun N => ‖x N‖) atTop = limsup (fun N => ‖y N‖) atTop := by
  have heq : sequenceQuotientMk Fiber x = sequenceQuotientMk Fiber y :=
    Ideal.Quotient.eq.mpr hxy
  calc
    _ = ‖sequenceQuotientMk Fiber x‖ := (sequenceQuotient_norm Fiber x).symm
    _ = ‖sequenceQuotientMk Fiber y‖ := congrArg norm heq
    _ = _ := sequenceQuotient_norm Fiber y

/-- Consumer for a Wick comparison proved upstream. The error premise is not
proved or assumed for any concrete Wick map in this module. -/
theorem limsup_le_sup_of_normNull_comparison (x : BoundedSequence Fiber)
    (s : Finset κ) (c : κ → ℂ) (w : κ → List (I × I))
    (hcomp : NormNull Fiber (x - polynomialSequence q hq I s c w)) :
    limsup (fun N => ‖x N‖) atTop ≤ unitBallSup I (polynomialSymbol I s c w) := by
  rw [limsup_norm_eq_of_normNull x _ hcomp]
  exact polynomialSequence_limsup_le_sup q hq I s c w

/-- The source's eventual `O(N⁻¹)` comparison is enough. The comparison estimate
must be supplied by a proof about the concrete Wick realization. -/
theorem limsup_le_sup_of_inv_nat_comparison (x : BoundedSequence Fiber)
    (s : Finset κ) (c : κ → ℂ) (w : κ → List (I × I)) (C : ℝ)
    (hcomp : ∀ᶠ N in atTop,
      ‖x N - polynomialSequence q hq I s c w N‖ ≤ (N : ℝ)⁻¹ * C) :
    limsup (fun N => ‖x N‖) atTop ≤ unitBallSup I (polynomialSymbol I s c w) :=
  limsup_le_sup_of_normNull_comparison q hq I x s c w
    (normNull_of_eventually_norm_le_inv_nat_mul Fiber _ C hcomp)

/-- Different ordered factorizations of the same unit-ball polynomial give
the same quotient element. This makes the generic interface independent of
the choice of bilinear factors, without defining a Wick-symbol algebra. -/
theorem polynomialElement_eq_of_symbol_eq {ι : Type*}
    (s : Finset κ) (c : κ → ℂ) (w : κ → List (I × I))
    (t : Finset ι) (d : ι → ℂ) (v : ι → List (I × I))
    (hfg : ∀ z : EuclideanSpace ℂ I, ‖z‖ ≤ 1 →
      polynomialSymbol I s c w z = polynomialSymbol I t d v z) :
    polynomialElement q hq I s c w = polynomialElement q hq I t d v := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply norm_le_of_character_representation q hq I _
    (fun z => polynomialSymbol I s c w z - polynomialSymbol I t d v z) ?_ (by rfl) ?_
  · intro φ z hz
    rw [map_sub, character_polynomialElement q hq I φ z hz,
      character_polynomialElement q hq I φ z hz]
  · intro z hz
    simp only [hfg z hz, sub_self, norm_zero, le_refl]

#print axioms quotientGelfand_norm
#print axioms norm_le_of_character_representation
#print axioms wordSequence
#print axioms wordElement
#print axioms wordSymbol
#print axioms wordSequence_apply
#print axioms wordElement_coe
#print axioms character_wordElement
#print axioms polynomialSequence
#print axioms polynomialElement
#print axioms polynomialSymbol
#print axioms polynomialSequence_apply
#print axioms polynomialElement_coe
#print axioms character_polynomialElement
#print axioms polynomialElement_norm_le
#print axioms polynomialSequence_limsup_le
#print axioms unitBallSup
#print axioms le_unitBallSup
#print axioms unitBallSup_nonneg
#print axioms unitBallSup_attained
#print axioms continuous_wordSymbol
#print axioms continuous_polynomialSymbol
#print axioms polynomialElement_norm_le_sup
#print axioms polynomialSequence_limsup_le_sup
#print axioms limsup_norm_eq_of_normNull
#print axioms limsup_le_sup_of_normNull_comparison
#print axioms limsup_le_sup_of_inv_nat_comparison
#print axioms polynomialElement_eq_of_symbol_eq

end QuantumNLS.SpectralUpperBound
