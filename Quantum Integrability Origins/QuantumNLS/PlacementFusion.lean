/-
QuantumNLS.PlacementFusion — concrete overlap kernels for products of
normalized subset placements (LOCAL-011, first product clause).

This module builds a kernel from the actual ordered product of two frozen
subset placements on their union and records the source overlap coefficient
and radius majorant. It does not assert the unresolved arbitrary-N grouping
identity with one universal kernel C_{p,q,s}.
-/
import QuantumNLS.LocalPlacement
import Mathlib.Data.Nat.Choose.Vandermonde

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.KernelDefinition

noncomputable section

namespace QuantumNLS.PlacementFusion

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Reindex a completed tensor-power operator along an equality of particle
counts. -/
def castTensorOperator {m n : ℕ} (h : m = n)
    (T : HilbertTensorPower ℂ H m →L[ℂ] HilbertTensorPower ℂ H m) :
    HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n := by
  cases h
  exact T

omit [CompleteSpace H] in
/-- Reindexing tensor slots preserves the operator norm. -/
theorem norm_castTensorOperator {m n : ℕ} (h : m = n)
    (T : HilbertTensorPower ℂ H m →L[ℂ] HilbertTensorPower ℂ H m) :
    ‖castTensorOperator h T‖ = ‖T‖ := by
  cases h
  rfl

/-- The canonical reindexing from the q-placement presentation of the union
to the p-placement presentation. -/
def overlapSlotEquiv {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q) :
    Fin (q + (p - s)) ≃ Fin (p + (q - s)) :=
  Equiv.cast (congrArg Fin (by omega))

/-- The exact overlap configurations on the union of a p-subset and a
q-subset. The ambient tensor power has `p + (q-s)` slots, and the two subsets
cover it with intersection size `s`. -/
structure OverlapConfiguration (p q s : ℕ) (hsp : s ≤ p) (hsq : s ≤ q) where
  left : PlacementSubset p (q - s)
  right : PlacementSubset q (p - s)
  overlap_card :
    (left.1 ∩ (right.1.map (overlapSlotEquiv hsp hsq).toEmbedding)).card = s
  covers_union :
    left.1 ∪ (right.1.map (overlapSlotEquiv hsp hsq).toEmbedding) = Finset.univ

/-- The q-kernel placement transported to the common union tensor power. -/
def rightPlacement {p q s : ℕ} {hsp : s ≤ p} {hsq : s ≤ q}
    (C : OverlapConfiguration p q s hsp hsq)
    (B : BoundedSymmetricKernel H q) :
    HilbertTensorPower ℂ H (p + (q - s)) →L[ℂ] HilbertTensorPower ℂ H (p + (q - s)) :=
  castTensorOperator (by omega) (subsetPlacement C.right B)

/-- A local fusion kernel is the symmetric-sector compression of the actual
ordered product of the two placements on a specified overlap configuration.
The order agrees with `Q_{N,p}(A) Q_{N,q}(B)`. -/
def overlapFusionKernel {p q s : ℕ} {hsp : s ≤ p} {hsq : s ≤ q}
    (C : OverlapConfiguration p q s hsp hsq)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    BoundedSymmetricKernel H (p + (q - s)) :=
  (symProjToSector (p + (q - s))).comp
    (((subsetPlacement C.left A).comp (rightPlacement C B)).comp
      (SymSector ℂ H (p + (q - s))).subtypeL)

omit [CompleteSpace H] in
/-- The symmetric projection is contractive as a map into the symmetric
sector. -/
theorem norm_symProjToSector_le (n : ℕ) :
    ‖symProjToSector (H := H) n‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) ?_
  intro x
  change ‖symProj ℂ H n x‖ ≤ 1 * ‖x‖
  rw [symProj_eq_starProjection]
  simpa using (SymSector ℂ H n).norm_starProjection_apply_le x

/-- Every concrete overlap fusion kernel obeys the source product norm bound.
No hypothesis about an abstract fusion identity is used. -/
theorem norm_overlapFusionKernel_le {p q s : ℕ}
    {hsp : s ≤ p} {hsq : s ≤ q}
    (C : OverlapConfiguration p q s hsp hsq)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    ‖overlapFusionKernel C A B‖ ≤ ‖A‖ * ‖B‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (norm_nonneg A) (norm_nonneg B)) ?_
  intro x
  let X := subsetPlacement C.left A
  let Y := rightPlacement C B
  have hX : ‖X‖ ≤ ‖A‖ := by
    dsimp [X, subsetPlacement]
    exact norm_permutedPlacement_le _ A
  have hY : ‖Y‖ ≤ ‖B‖ := by
    dsimp [Y, rightPlacement, subsetPlacement]
    rw [norm_castTensorOperator]
    exact norm_permutedPlacement_le _ B
  have hP : ‖symProjToSector (H := H) (p + (q - s))‖ ≤ 1 :=
    norm_symProjToSector_le (H := H) _
  change ‖symProjToSector (p + (q - s)) (X (Y x.1))‖ ≤
    (‖A‖ * ‖B‖) * ‖x‖
  calc
    _ ≤ ‖X (Y x.1)‖ := by
      calc
        _ ≤ ‖symProjToSector (H := H) (p + (q - s))‖ * ‖X (Y x.1)‖ :=
          (symProjToSector (H := H) (p + (q - s))).le_opNorm _
        _ ≤ 1 * ‖X (Y x.1)‖ :=
          mul_le_mul_of_nonneg_right hP (norm_nonneg _)
        _ = _ := by simp
    _ ≤ ‖X‖ * ‖Y x.1‖ := X.le_opNorm _
    _ ≤ ‖A‖ * (‖Y‖ * ‖x.1‖) := by
      calc
        ‖X‖ * ‖Y x.1‖ ≤ ‖A‖ * ‖Y x.1‖ :=
          mul_le_mul_of_nonneg_right hX (norm_nonneg _)
        _ ≤ ‖A‖ * (‖Y‖ * ‖x.1‖) :=
          mul_le_mul_of_nonneg_left (Y.le_opNorm _) (norm_nonneg A)
    _ ≤ ‖A‖ * (‖B‖ * ‖x‖) := by
      have hy : ‖Y‖ * ‖x.1‖ ≤ ‖B‖ * ‖x‖ := by
        calc
          ‖Y‖ * ‖x.1‖ ≤ ‖B‖ * ‖x.1‖ :=
            mul_le_mul_of_nonneg_right hY (norm_nonneg _)
          _ = ‖B‖ * ‖x‖ := by rfl
      exact mul_le_mul_of_nonneg_left hy (norm_nonneg A)
    _ = (‖A‖ * ‖B‖) * ‖x‖ := by ring

/-- The local kernel retains the actual ordered pair-placement product on the
union, with only the symmetric projection applied at its output. -/
theorem overlapFusionKernel_apply {p q s : ℕ}
    {hsp : s ≤ p} {hsq : s ≤ q}
    (C : OverlapConfiguration p q s hsp hsq)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q)
    (x : SymSector ℂ H (p + (q - s))) :
    overlapFusionKernel C A B x =
      symProjToSector (p + (q - s))
        (subsetPlacement C.left A (rightPlacement C B x.1)) := rfl

/-- The hypergeometric coefficient for overlap size `s`, with impossible
choices represented by the usual zero binomial coefficients. This is the
source coefficient `c_{N,p,q,s}`. -/
def overlapCoefficient (N p q s : ℕ) : ℝ :=
  if s ≤ q then
    (Nat.choose p s : ℝ) * (Nat.choose (N - p) (q - s) : ℝ) /
      (Nat.choose N q : ℝ)
  else 0

/-- The source overlap coefficients sum to one, with the q-subset size
running from zero through `N`. -/
theorem sum_overlapCoefficient_eq_one {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N) :
    (∑ s ∈ Finset.range (q + 1), overlapCoefficient N p q s) = 1 := by
  have hchoose :
      (∑ s ∈ Finset.range (q + 1),
        Nat.choose p s * Nat.choose (N - p) (q - s)) = Nat.choose N q := by
    rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
      (fun ij : ℕ × ℕ => Nat.choose p ij.1 * Nat.choose (N - p) ij.2) q]
    rw [← Nat.add_choose_eq p (N - p) q]
    rw [Nat.add_sub_of_le hp]
  have hdenNat : Nat.choose N q ≠ 0 := Nat.choose_ne_zero hq
  have hden : (Nat.choose N q : ℝ) ≠ 0 := by exact_mod_cast hdenNat
  have hchooseR :
      (∑ s ∈ Finset.range (q + 1),
        (Nat.choose p s : ℝ) * (Nat.choose (N - p) (q - s) : ℝ)) =
        (Nat.choose N q : ℝ) := by
    norm_cast
  calc
    (∑ s ∈ Finset.range (q + 1), overlapCoefficient N p q s) =
        ∑ s ∈ Finset.range (q + 1),
          ((Nat.choose p s : ℝ) *
            (Nat.choose (N - p) (q - s) : ℝ)) / (Nat.choose N q : ℝ) := by
          apply Finset.sum_congr rfl
          intro s hs
          have hsle : s ≤ q := by
            have hlt := Finset.mem_range.mp hs
            omega
          simp [overlapCoefficient, hsle]
    _ = ((∑ s ∈ Finset.range (q + 1),
          (Nat.choose p s : ℝ) *
            (Nat.choose (N - p) (q - s) : ℝ)) / (Nat.choose N q : ℝ)) := by
          rw [Finset.sum_div]
    _ = 1 := by rw [hchooseR, div_self hden]

/-- The overlap coefficient is nonnegative, including impossible overlaps. -/
theorem overlapCoefficient_nonneg (N p q s : ℕ) :
    0 ≤ overlapCoefficient N p q s := by
  by_cases hs : s ≤ q
  · simp [overlapCoefficient, hs]
    positivity
  · simp [overlapCoefficient, hs]

/-- Since the coefficients sum to one, each source overlap probability is at
most one. -/
theorem overlapCoefficient_le_one {N p q s : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (hs : s ≤ q) : overlapCoefficient N p q s ≤ 1 := by
  have hsRange : s ∈ Finset.range (q + 1) := by
    simp [Finset.mem_range]
    omega
  calc
    overlapCoefficient N p q s ≤
        ∑ t ∈ Finset.range (q + 1), overlapCoefficient N p q t :=
      Finset.single_le_sum (fun t ht => overlapCoefficient_nonneg N p q t) hsRange
    _ = 1 := sum_overlapCoefficient_eq_one hp hq

/-- Every radius-weighted local fusion contribution is bounded by the
product of the two source degree weights. The exponent is the actual union
size `p+q-s`, rather than `p+q`. -/
theorem overlap_radius_majorant {p q s : ℕ} {R : ℝ}
    (hR : 1 ≤ R) {hsp : s ≤ p} {hsq : s ≤ q}
    (C : OverlapConfiguration p q s hsp hsq)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    R ^ (p + q - s) * ‖overlapFusionKernel C A B‖ ≤
      (R ^ p * ‖A‖) * (R ^ q * ‖B‖) := by
  have hK := norm_overlapFusionKernel_le C A B
  have hpow : R ^ (p + q - s) ≤ R ^ (p + q) :=
    pow_le_pow_right₀ hR (Nat.sub_le _ _)
  have hR0 : 0 ≤ R := le_trans (by norm_num : (0 : ℝ) ≤ 1) hR
  calc
    R ^ (p + q - s) * ‖overlapFusionKernel C A B‖ ≤
        R ^ (p + q - s) * (‖A‖ * ‖B‖) :=
      mul_le_mul_of_nonneg_left hK (pow_nonneg hR0 _)
    _ ≤ R ^ (p + q) * (‖A‖ * ‖B‖) :=
      mul_le_mul_of_nonneg_right hpow (mul_nonneg (norm_nonneg A) (norm_nonneg B))
    _ = (R ^ p * ‖A‖) * (R ^ q * ‖B‖) := by rw [pow_add]; ring

/-- The source probability-weighted contribution of a concrete overlap
kernel obeys the same product majorant. -/
theorem weighted_overlap_radius_majorant {N p q s : ℕ} {R : ℝ}
    (hR : 1 ≤ R)
    {hsp : s ≤ p} {hsq : s ≤ q}
    (C : OverlapConfiguration p q s hsp hsq)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    overlapCoefficient N p q s *
        (R ^ (p + q - s) * ‖overlapFusionKernel C A B‖) ≤
      overlapCoefficient N p q s * ((R ^ p * ‖A‖) * (R ^ q * ‖B‖)) :=
  mul_le_mul_of_nonneg_left (overlap_radius_majorant hR C A B)
    (overlapCoefficient_nonneg N p q s)

end QuantumNLS.PlacementFusion

#print axioms QuantumNLS.PlacementFusion.norm_overlapFusionKernel_le
#print axioms QuantumNLS.PlacementFusion.overlapFusionKernel_apply
#print axioms QuantumNLS.PlacementFusion.sum_overlapCoefficient_eq_one
#print axioms QuantumNLS.PlacementFusion.overlapCoefficient_nonneg
#print axioms QuantumNLS.PlacementFusion.overlapCoefficient_le_one
#print axioms QuantumNLS.PlacementFusion.overlap_radius_majorant
#print axioms QuantumNLS.PlacementFusion.weighted_overlap_radius_majorant
