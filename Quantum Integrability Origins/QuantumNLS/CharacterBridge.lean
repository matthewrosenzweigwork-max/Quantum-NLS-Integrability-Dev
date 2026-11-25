import QuantumNLS.OccupationHilbert
import QuantumNLS.Gelfand
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Character matrices on the occupation sequence quotient

PR11 `3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f`,
`chapters/core/wick_calculus.tex:128–153`, FIN-EXT025-GP-02 / R-140AE34B.
The positive cone is explicitly the set of star squares. Bounded pointwise
square roots transport operator positivity to the norm-null quotient; spectral
permanence reflects this cone into the closed generated subalgebra. Characters
then give positive semidefinite matrices of trace at most one, and the frozen
rank-one lemma applies. Gauges are supplied unit phases. Physical U4/U5,
the selected Bethe gauge, Wick polynomial comparison and the coherent lower
bound remain separate obligations.
-/

noncomputable section
open scoped ComplexConjugate ComplexOrder Classical ENNReal

namespace QuantumNLS.CharacterBridge

/-- The intrinsic C*-positive cone, with its witness made explicit. -/
def PositiveCone {A : Type*} [Mul A] [Star A] (x : A) : Prop :=
  ∃ y : A, x = star y * y

theorem positiveCone_iff_nonneg {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (x : A) :
    PositiveCone x ↔ 0 ≤ x :=
  CStarAlgebra.nonneg_iff_eq_star_mul_self.symm

theorem PositiveCone.map {A B : Type*}
    [Semiring A] [Star A] [Algebra ℂ A] [Semiring B] [Star B] [Algebra ℂ B]
    {x : A} (hx : PositiveCone x) (f : A →⋆ₐ[ℂ] B) : PositiveCone (f x) := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨f y, by simp only [map_mul, map_star]⟩

/-- An injective C*-homomorphism reflects the intrinsic positive cone. -/
theorem positiveCone_map_iff {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (f : A →⋆ₐ[ℂ] B) (hf : Function.Injective f) (x : A) :
    PositiveCone (f x) ↔ PositiveCone x := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  have : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  have : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  rw [positiveCone_iff_nonneg, positiveCone_iff_nonneg]
  simpa only [map_zero] using
    (NonUnitalStarAlgHom.map_le_map_iff f hf (x := 0) (y := x))

/-- Positivity reflects along a closed C*-subalgebra inclusion. This uses
spectral permanence; the square root need not be a generator. -/
theorem positiveCone_subalgebra_iff {A : Type*} [CStarAlgebra A]
    (S : StarSubalgebra ℂ A) (hS : IsClosed (S : Set A)) (x : S) :
    PositiveCone (x : A) ↔ PositiveCone x := by
  let : CStarAlgebra S := StarSubalgebra.cstarAlgebra S (h_closed := hS)
  exact positiveCone_map_iff S.subtype Subtype.val_injective x

/-- Characters are nonnegative on star squares, including zero. -/
theorem PositiveCone.character_nonneg {A : Type*} [CStarAlgebra A]
    {x : A} (hx : PositiveCone x) (φ : WeakDual.characterSpace ℂ A) : 0 ≤ φ x := by
  obtain ⟨y, rfl⟩ := hx
  rw [map_mul, map_star]
  exact star_mul_self_nonneg _

section Sequences
open Gelfand
variable {B : ℕ → Type*} [∀ n, CStarAlgebra (B n)]
  [∀ n, PartialOrder (B n)] [∀ n, StarOrderedRing (B n)]

/-- Pointwise positive bounded sequences have a bounded sequence of square
roots: the C*-identity bounds its squared norm by the original uniform norm. -/
theorem sequence_positiveCone (x : BoundedSequence B) (hx : ∀ n, 0 ≤ x n) :
    PositiveCone x := by
  let y : BoundedSequence B := ⟨fun n => CFC.sqrt (x n),
    memℓp_infty ⟨‖x‖ + 1, by
      rintro _ ⟨n, rfl⟩
      have hs : ‖CFC.sqrt (x n)‖ ^ 2 = ‖x n‖ := by
        rw [sq, ← CStarRing.norm_star_mul_self,
          (CFC.sqrt_nonneg (x n)).star_eq, CFC.sqrt_mul_sqrt_self (x n) (hx n)]
      have hb := lp.norm_apply_le_norm ENNReal.top_ne_zero x n
      nlinarith [norm_nonneg x, norm_nonneg (CFC.sqrt (x n))]⟩⟩
  refine ⟨y, ?_⟩
  apply lp.ext
  funext n
  change x n = star (CFC.sqrt (x n)) * CFC.sqrt (x n)
  rw [(CFC.sqrt_nonneg (x n)).star_eq, CFC.sqrt_mul_sqrt_self (x n) (hx n)]

variable [∀ n, Nontrivial (B n)]

theorem quotient_positiveCone (x : BoundedSequence B) (hx : ∀ n, 0 ≤ x n) :
    PositiveCone (sequenceQuotientMk B x) :=
  PositiveCone.map (A := BoundedSequence B) (B := SequenceQuotient B)
    (x := x) (sequence_positiveCone x hx) (sequenceQuotientMk B)

/-- Finitely many sectors are irrelevant, including the source's exceptional
zero sector. Truncate first, then transport an actual positive square. -/
theorem quotient_positiveCone_of_tail (x : BoundedSequence B) (N : ℕ)
    (hx : ∀ n, N ≤ n → 0 ≤ x n) : PositiveCone (sequenceQuotientMk B x) := by
  have h := quotient_positiveCone (sequenceTail B x N) (fun n => by
    change 0 ≤ if N ≤ n then x n else 0
    split_ifs with hn
    · exact hx n hn
    · exact le_rfl)
  change PositiveCone (Ideal.Quotient.mk (normNullIdeal B) (sequenceTail B x N)) at h
  rw [sequenceTail_mk] at h
  exact h

end Sequences

section OccupationCharacters
open Occupation OccupationHilbert Gelfand

variable (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (I : Finset ℤ)

/-- Each actual quotient generator, regarded as an element of the generated algebra. -/
def generator (a b : I) : quotientAlgebra q hq I :=
  ⟨quotientGenerator q hq a.1 b.1, generator_mem _ a b⟩

@[simp] theorem generator_coe (a b : I) :
    (generator q hq I a b : OccupationQuotient) = quotientGenerator q hq a.1 b.1 := rfl

@[simp] theorem generator_star (a b : I) :
    star (generator q hq I a b) = generator q hq I b a := by
  apply Subtype.ext
  exact quotientGenerator_star q hq a.1 b.1

/-- The character matrix retains the source donor/receiver order. -/
def characterMatrix (φ : WeakDual.characterSpace ℂ (quotientAlgebra q hq I)) :
    Matrix I I ℂ := fun a b => φ (generator q hq I a b)

/-- Extend a finite-coordinate test vector without altering its coordinates on I. -/
def extendVector (v : I → ℂ) (a : ℤ) : ℂ :=
  if h : a ∈ I then v ⟨a, h⟩ else 0

@[simp] theorem extendVector_coe (v : I → ℂ) (a : I) :
    extendVector I v a.1 = v a := by simp [extendVector, a.2]

/-- The finite quadratic combination as an actual bounded operator sequence. -/
def quadraticSequence (v : I → ℂ) : BoundedSequence Fiber :=
  ∑ a : I, ∑ b : I, (conj (v a) * v b) • EqSequence q hq a.1 b.1

@[simp] theorem quadraticSequence_apply (v : I → ℂ) (N : ℕ) :
    quadraticSequence q hq I v N = matrixOpq N (q N) (hq N) I (extendVector I v) := by
  simp only [quadraticSequence, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply]
  simp only [matrixOpq, ← Finset.sum_coe_sort I, extendVector_coe]
  rfl

/-- Positivity of the quadratic quotient element comes from the proved
annihilation sum of squares on the complete coefficient carrier. -/
theorem quadratic_quotient_positiveCone (v : I → ℂ) :
    PositiveCone (∑ a : I, ∑ b : I,
      (conj (v a) * v b) • quotientGenerator q hq a.1 b.1) := by
  have h := quotient_positiveCone (quadraticSequence q hq I v) (fun N => by
    rw [quadraticSequence_apply, ContinuousLinearMap.nonneg_iff_isPositive]
    exact matrixOpq_positive N (q N) (hq N) I (extendVector I v))
  simpa only [quadraticSequence, map_sum, map_smul, quotientGenerator] using h

/-- The same positive element inside the closed generated subalgebra. -/
theorem quadratic_algebra_positiveCone (v : I → ℂ) :
    PositiveCone (∑ a : I, ∑ b : I,
      (conj (v a) * v b) • generator q hq I a b) := by
  apply (positiveCone_subalgebra_iff (quotientAlgebra q hq I)
    (generatedAlgebra_isClosed _) _).mp
  change PositiveCone ((quotientAlgebra q hq I).subtype
    (∑ a : I, ∑ b : I, (conj (v a) * v b) • generator q hq I a b))
  simpa only [map_sum, map_smul, StarSubalgebra.coe_subtype, generator_coe] using quadratic_quotient_positiveCone q hq I v

/-- The trace-defect sequence. Only its positive tail is used. -/
def traceDefectSequence : BoundedSequence Fiber :=
  1 - ∑ a : I, EqSequence q hq a.1 a.1

@[simp] theorem traceDefectSequence_apply (N : ℕ) :
    traceDefectSequence q hq I N = 1 - ∑ a ∈ I, Eq N (q N) (hq N) a a := by
  simp only [traceDefectSequence, lp.coeFn_sub, Pi.sub_apply, lp.infty_coeFn_one, Pi.one_apply,
    lp.coeFn_sum, Finset.sum_apply]
  change 1 - ∑ a : I, Eq N (q N) (hq N) a.1 a.1 = _
  rw [Finset.sum_coe_sort I (fun a => Eq N (q N) (hq N) a a)]

/-- The finite-label trace defect is positive in the sequence quotient. -/
theorem traceDefect_quotient_positiveCone :
    PositiveCone (1 - ∑ a : I, quotientGenerator q hq a.1 a.1) := by
  have h := quotient_positiveCone_of_tail (traceDefectSequence q hq I) 1 (fun N hN => by
    rw [traceDefectSequence_apply, ContinuousLinearMap.nonneg_iff_isPositive]
    exact one_sub_sum_diagq_positive (by omega) (q N) (hq N) I)
  change PositiveCone (sequenceQuotientMk Fiber (1 - ∑ a : I, EqSequence q hq a.1 a.1)) at h
  have hone : sequenceQuotientMk Fiber (1 : BoundedSequence Fiber) =
      (1 : OccupationQuotient) := rfl
  rw [map_sub, hone, map_sum] at h
  exact h

/-- Spectral permanence transports the trace defect into the generated algebra. -/
theorem traceDefect_algebra_positiveCone :
    PositiveCone (1 - ∑ a : I, generator q hq I a a) := by
  apply (positiveCone_subalgebra_iff (quotientAlgebra q hq I)
    (generatedAlgebra_isClosed _) _).mp
  change PositiveCone ((quotientAlgebra q hq I).subtype (1 - ∑ a : I, generator q hq I a a))
  have hone : (quotientAlgebra q hq I).subtype 1 = (1 : OccupationQuotient) := rfl
  simpa only [map_sub, hone, map_sum, StarSubalgebra.coe_subtype, generator_coe] using
    traceDefect_quotient_positiveCone q hq I

variable (φ : WeakDual.characterSpace ℂ (quotientAlgebra q hq I))

theorem characterMatrix_hermitian : (characterMatrix q hq I φ).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro a b
  change star (φ (generator q hq I b a)) = φ (generator q hq I a b)
  rw [← map_star, generator_star]

/-- The matrix is positive semidefinite, with no matrix-positivity hypothesis. -/
theorem characterMatrix_posSemidef : (characterMatrix q hq I φ).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (characterMatrix_hermitian q hq I φ)
  intro v
  have h := (quadratic_algebra_positiveCone q hq I v).character_nonneg φ
  simp only [map_sum, map_smul, smul_eq_mul] at h
  have heq : dotProduct (star v) (Matrix.mulVec (characterMatrix q hq I φ) v) =
      ∑ a : I, ∑ b : I, (conj (v a) * v b) * φ (generator q hq I a b) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, characterMatrix]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [Complex.star_def]
    ring
  rw [heq]
  exact h

/-- The trace bound follows by applying the character to the positive trace
defect, rather than postulating a source conclusion. -/
theorem characterMatrix_trace_le_one : ∑ a : I, (characterMatrix q hq I φ a a).re ≤ 1 := by
  have h := (traceDefect_algebra_positiveCone q hq I).character_nonneg φ
  rw [map_sub, map_one, map_sum] at h
  have hr := (Complex.nonneg_iff.mp h).1
  have hr' : 0 ≤ 1 - ∑ a : I, (characterMatrix q hq I φ a a).re := by
    simpa [characterMatrix] using hr
  exact sub_nonneg.mp hr'

/-- Vanishing two-by-two minors descend from the finite-N identities. -/
theorem characterMatrix_minors (a b c d : I) :
    characterMatrix q hq I φ a b * characterMatrix q hq I φ c d =
      characterMatrix q hq I φ a d * characterMatrix q hq I φ c b := by
  have h : generator q hq I a b * generator q hq I c d =
      generator q hq I a d * generator q hq I c b := by
    apply Subtype.ext
    exact quotientGenerator_minors q hq a.1 b.1 c.1 d.1
  exact (map_mul φ _ _).symm.trans ((congrArg φ h).trans (map_mul φ _ _))

/-- Each character is represented on the bilinear generators by a vector in
ℂ^I with Euclidean norm at most one; includes empty I and the zero matrix. -/
theorem characterMatrix_exists_unitBall_vector :
    ∃ z : EuclideanSpace ℂ I,
      (∀ a b, characterMatrix q hq I φ a b = z a * conj (z b)) ∧ ‖z‖ ≤ 1 :=
  exists_unitBall_vector_of_posSemidef_minors (characterMatrix_posSemidef q hq I φ)
    (characterMatrix_trace_le_one q hq I φ) (characterMatrix_minors q hq I φ)

/-- The generator entries are exactly evaluations of the frozen Gelfand map. -/
@[simp] theorem quotientGelfand_generator_apply (a b : I) :
    quotientGelfand q hq I (generator q hq I a b) φ = characterMatrix q hq I φ a b := rfl

/-- Direct interface for the isometric Gelfand representation. -/
theorem quotientGelfand_exists_unitBall_vector :
    ∃ z : EuclideanSpace ℂ I,
      (∀ a b, quotientGelfand q hq I (generator q hq I a b) φ = z a * conj (z b)) ∧
        ‖z‖ ≤ 1 :=
  characterMatrix_exists_unitBall_vector q hq I φ

/-- The character quantifier is nonvacuous, even for the empty label set:
the generated algebra is unital in a nonzero quotient. -/
theorem characterSpace_nonempty : Nonempty (WeakDual.characterSpace ℂ (quotientAlgebra q hq I)) := by
  let : CommCStarAlgebra (quotientAlgebra q hq I) :=
    generatedCommCStarAlgebra _ (fun a b => quotientGenerator_star q hq a.1 b.1)
      (fun a b c d => quotientGenerator_commute q hq a.1 b.1 c.1 d.1)
  infer_instance

end OccupationCharacters

#print axioms PositiveCone
#print axioms positiveCone_iff_nonneg
#print axioms PositiveCone.map
#print axioms positiveCone_map_iff
#print axioms positiveCone_subalgebra_iff
#print axioms PositiveCone.character_nonneg
#print axioms sequence_positiveCone
#print axioms quotient_positiveCone
#print axioms quotient_positiveCone_of_tail
#print axioms generator
#print axioms generator_coe
#print axioms generator_star
#print axioms characterMatrix
#print axioms extendVector
#print axioms extendVector_coe
#print axioms quadraticSequence
#print axioms quadraticSequence_apply
#print axioms quadratic_quotient_positiveCone
#print axioms quadratic_algebra_positiveCone
#print axioms traceDefectSequence
#print axioms traceDefectSequence_apply
#print axioms traceDefect_quotient_positiveCone
#print axioms traceDefect_algebra_positiveCone
#print axioms characterMatrix_hermitian
#print axioms characterMatrix_posSemidef
#print axioms characterMatrix_trace_le_one
#print axioms characterMatrix_minors
#print axioms characterMatrix_exists_unitBall_vector
#print axioms quotientGelfand_generator_apply
#print axioms quotientGelfand_exists_unitBall_vector
#print axioms characterSpace_nonempty

end QuantumNLS.CharacterBridge
