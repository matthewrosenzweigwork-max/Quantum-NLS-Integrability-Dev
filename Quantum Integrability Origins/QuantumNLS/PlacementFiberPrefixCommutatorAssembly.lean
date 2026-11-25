/-
QuantumNLS.PlacementFiberPrefixCommutatorAssembly — degreewise candidate
kernel list for the LOCAL-011 scaled commutator.

This module imports the frozen LOCAL-011 placement and positive-overlap
commutator chain without modifying it.  It records the canonical-prefix
raw-term identity in its requested pointwise form and constructs the
degreewise finite kernel list from the positive-overlap contributions.
-/
import QuantumNLS.PlacementFiberPrefixCommutator

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct
  QuantumNLS.PlacementUnionReindex QuantumNLS.PlacementFiberTransport
  QuantumNLS.PlacementFiberOperator QuantumNLS.PlacementFiberCanonicalPrefix
  QuantumNLS.PlacementFiberPrefixAlignedTransport
  QuantumNLS.PlacementFiberPrefixCommutator QuantumNLS.RadiusBound
  QuantumNLS.LocalPlacement

noncomputable section

namespace QuantumNLS.PlacementFiberPrefixCommutatorAssembly

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Insert one degree-`n` kernel into a kernel list at total particle
number `N`, leaving every other degree zero. -/
def kernelSpike {N n : ℕ} (K : BoundedSymmetricKernel H n) :
    KernelList (H := H) N := fun j =>
  if h : j.1 = n then castSymSectorOperator h.symm K else 0

/-- The finite degreewise list obtained by grouping all feasible positive
overlap commutator kernels by their union degree.  Each summand is the
source-scaled kernel `i N c_{N,p,q,s}` times the explicit antisymmetric
overlap kernel. -/
def positiveOverlapCommutatorList (N : ℕ)
    (A B : KernelList (H := H) N) : KernelList (H := H) N :=
  ∑ p : Fin (N + 1), ∑ q : Fin (N + 1), ∑ s : Fin (N + 1),
    if h : 1 ≤ s.1 ∧ s.1 ≤ min p.1 q.1 ∧
        unionSize p.1 q.1 s.1 ≤ N then
      kernelSpike (H := H)
        (((Complex.I : ℂ) * (N : ℂ) *
          ((overlapCoefficient N p.1 q.1 s.1 : ℝ) : ℂ)) •
          overlapCommutatorKernel
            (le_trans h.2.1 (min_le_left _ _))
            (le_trans h.2.1 (min_le_right _ _)) (A p) (B q))
    else 0

/-- The exact kernel-level gap required to cancel the zero-overlap degree
before the positive-overlap list represents the commutator.  This is a
proposition, not an assumption of the candidate-list construction. -/
def ZeroOverlapKernelIdentity : Prop :=
  ∀ (p q : ℕ) (A : BoundedSymmetricKernel H p)
      (Bop : BoundedSymmetricKernel H q),
    averagedOverlapKernel (Nat.zero_le p) (Nat.zero_le q) A Bop =
      (by
        have h : unionSize p q 0 = unionSize q p 0 := by
          dsimp [unionSize]
          omega
        exact castSymSectorOperator h.symm
          (averagedOverlapKernel (Nat.zero_le q) (Nat.zero_le p) Bop A))

/-- The coefficient symmetry needed to cancel the source's zero-overlap
terms after swapping the two kernel degrees. -/
def OverlapCoefficientSymmetry : Prop :=
  ∀ (N p q s : ℕ), p ≤ N → q ≤ N → s ≤ p → s ≤ q →
    overlapCoefficient N p q s = overlapCoefficient N q p s

/-- The local pair-configuration count is symmetric under swapping the two
degrees. -/
private theorem overlapConfigurationCount_symm (p q s : ℕ)
    (hsp : s ≤ p) (hsq : s ≤ q) :
    Nat.choose (unionSize p q s) p * Nat.choose p s =
      Nat.choose (unionSize p q s) q * Nat.choose q s := by
  let u := unionSize p q s
  have hleft : Nat.choose u p * Nat.choose p s =
      Nat.choose u s * Nat.choose (u - s) (p - s) := by
    exact Nat.choose_mul (n := u) (k := p) (s := s) hsp
  have hright : Nat.choose u q * Nat.choose q s =
      Nat.choose u s * Nat.choose (u - s) (q - s) := by
    exact Nat.choose_mul (n := u) (k := q) (s := s) hsq
  have hcomp : u - s - (p - s) = q - s := by
    dsimp [u, unionSize]
    omega
  have hsym : Nat.choose (u - s) (p - s) =
      Nat.choose (u - s) (q - s) := by
    rw [(Nat.choose_symm (show p - s ≤ u - s by dsimp [u, unionSize]; omega)).symm]
    rw [hcomp]
  rw [hleft, hsym, ← hright]

/-- The source overlap coefficient is symmetric in the two placement
degrees, including the impossible-union case. -/
theorem overlapCoefficient_symmetric (N p q s : ℕ)
    (hp : p ≤ N) (hq : q ≤ N) (hsp : s ≤ p) (hsq : s ≤ q) :
    overlapCoefficient N p q s = overlapCoefficient N q p s := by
  by_cases hu : unionSize p q s ≤ N
  · have hqUnion : unionSize q p s ≤ N := by
      have hsize : unionSize q p s = unionSize p q s := by
        dsimp [unionSize]
        omega
      omega
    have hsize : unionSize q p s = unionSize p q s := by
      dsimp [unionSize]
      omega
    rw [overlapCoefficient_eq_unionConfigurationNormalization hsp hsq hu,
      overlapCoefficient_eq_unionConfigurationNormalization hsq hsp hqUnion]
    rw [hsize]
    have hcount := overlapConfigurationCount_symm p q s hsp hsq
    have hcountR : (Nat.choose (unionSize p q s) p : ℝ) *
        (Nat.choose p s : ℝ) =
        (Nat.choose (unionSize p q s) q : ℝ) * (Nat.choose q s : ℝ) := by
      exact_mod_cast hcount
    have hdenEq : (Nat.choose N q : ℝ) * (Nat.choose N p : ℝ) =
        (Nat.choose N p : ℝ) * (Nat.choose N q : ℝ) := by ring
    rw [hdenEq]
    congr 1
    calc
      (Nat.choose N (unionSize p q s) : ℝ) *
          (Nat.choose (unionSize p q s) p : ℝ) *
          (Nat.choose p s : ℝ) =
        (Nat.choose N (unionSize p q s) : ℝ) *
          ((Nat.choose (unionSize p q s) p : ℝ) * (Nat.choose p s : ℝ)) := by ring
      _ = (Nat.choose N (unionSize p q s) : ℝ) *
          ((Nat.choose (unionSize p q s) q : ℝ) * (Nat.choose q s : ℝ)) := by
            rw [hcountR]
      _ = (Nat.choose N (unionSize p q s) : ℝ) *
          (Nat.choose (unionSize p q s) q : ℝ) * (Nat.choose q s : ℝ) := by ring
  · have hzero₁ := PlacementGrouping.overlapCoefficient_eq_zero_of_unionSize_gt
      hp hsq (by omega)
    have hzero₂ := PlacementGrouping.overlapCoefficient_eq_zero_of_unionSize_gt
      hq hsp (by
        have hsize : unionSize q p s = unionSize p q s := by
          dsimp [unionSize]
          omega
        rw [hsize]
        omega)
    rw [hzero₁, hzero₂]

/-- All source overlap probabilities are symmetric under exchanging the two
placement degrees. -/
theorem overlapCoefficientSymmetry_proved : OverlapCoefficientSymmetry := by
  intro N p q s hp hq hsp hsq
  exact overlapCoefficient_symmetric N p q s hp hq hsp hsq

/-- The candidate list represents `i N [represented(A), represented(B)]`.
This exact statement is retained until the zero-overlap kernel identity and
the finite reindexing of the two product expansions are proved. -/
def CandidateRepresentsScaledCommutator (N : ℕ)
    (A B : KernelList (H := H) N) : Prop :=
  represented (positiveOverlapCommutatorList N A B) =
    ((Complex.I : ℂ) * (N : ℂ)) •
      ((represented A).comp (represented B) -
        (represented B).comp (represented A))

/-- The desired radius estimate for the degreewise candidate after grouping.
The link from the ungrouped coefficient sum to this grouped radius bound is
one of the exact remaining obligations. -/
def CandidateRadiusBound (N : ℕ) (r R : ℝ)
    (A B : KernelList (H := H) N) : Prop :=
  1 ≤ r → r < R →
  radiusBound r (positiveOverlapCommutatorList N A B) ≤
    (2 / (R - r)) *
      (∑ p : Fin (N + 1), (p.1 : ℝ) * r ^ p.1 * ‖A p‖) *
      radiusBound R B

/-- The exact raw-term identity requested by the LOCAL-011 checkpoint,
re-exported from the frozen prefix aligned-transport proof. -/
theorem globallyCompressedRawPairTerm_eq_averagedOverlapKernelPlacement
    {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (b : PairPlacementBase N p q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q)
    (C : OverlapConfiguration p q
      (overlapSizeOfBase (canonicalPrefixPairBase b))
      (overlapLeftBound (canonicalPrefixPairBase b))
      (overlapRightBound (canonicalPrefixPairBase b))) :
    globallyCompressedRawPairTerm N p q hp hq
        (canonicalToAmbientPair hp hq (canonicalPrefixPairBase b) C) A Bop =
      averagedOverlapKernelPlacement N p q (canonicalPrefixPairBase b) A Bop := by
  exact globallyCompressedCanonicalPrefixRawPairTerm_eq_averagedPlacement
    hp hq b A Bop C

/-- The already-closed LOCAL-011 clauses, bundled in source order: the
finite-degree N-independent product identity, its operator radius bound,
and the fixed-degree commutator cancellation/radius estimate. -/
theorem local011_product_and_fixedDegree_clauses :
    (∀ (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
      (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q),
      (genericU_N_r N p hp A).comp (genericU_N_r N q hq Bop) =
        ∑ s : FeasibleOverlapIndex N p q,
          (((overlapCoefficient N p q s.1.1 : ℝ) : ℂ) •
            genericU_N_r N (unionSize p q s.1.1) s.2
              (averagedOverlapKernel
                (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_left _ _))
                (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_right _ _)) A Bop))) ∧
    (∀ {N p q : ℕ} {R : ℝ} (hp : p ≤ N) (hq : q ≤ N) (_hR : 1 ≤ R)
      (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q),
      ‖(genericU_N_r N p hp A).comp (genericU_N_r N q hq Bop)‖ ≤
        (R ^ p * ‖A‖) * (R ^ q * ‖Bop‖)) ∧
    (∀ (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
      (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q),
      (N : ℝ) *
          ‖(genericU_N_r N p hp A).comp (genericU_N_r N q hq Bop) -
            (genericU_N_r N q hq Bop).comp (genericU_N_r N p hp A)‖ ≤
        2 * (p * q : ℝ) * ‖A‖ * ‖Bop‖) := by
  exact ⟨by
      intro N p q hp hq A Bop
      exact genericU_product_eq_overlapKernelExpansion hp hq A Bop,
    by
      intro N p q R hp hq hR A Bop
      exact norm_genericU_product_le_radius hp hq hR A Bop,
    by
      intro N p q hp hq A Bop
      exact local011_fixedDegreeCommutator_radius N p q hp hq A Bop⟩

/-- A declaration of the still-open commutator assembly obligation; no
compatibility premise or unproved theorem is introduced. -/
def RemainingCommutatorAssembly (N : ℕ)
    (A B : KernelList (H := H) N) : Prop :=
  ZeroOverlapKernelIdentity (H := H) ∧
  CandidateRepresentsScaledCommutator (H := H) N A B ∧
  ∀ {r R : ℝ}, CandidateRadiusBound (H := H) N r R A B

#print axioms kernelSpike
#print axioms positiveOverlapCommutatorList
#print axioms overlapCoefficient_symmetric
#print axioms overlapCoefficientSymmetry_proved
#print axioms globallyCompressedRawPairTerm_eq_averagedOverlapKernelPlacement
#print axioms local011_product_and_fixedDegree_clauses

end QuantumNLS.PlacementFiberPrefixCommutatorAssembly

end
