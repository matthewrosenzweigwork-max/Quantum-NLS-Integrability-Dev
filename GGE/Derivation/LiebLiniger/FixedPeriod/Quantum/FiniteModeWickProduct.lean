import LiebLiniger.FixedPeriod.Quantum.OneModeWickNormalOrder
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Ring.List
import LiebLiniger.FixedPeriod.Quantum.WickDerivativeContraction
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Embedding
import Mathlib.Data.Fintype.CardEmbedding
import LiebLiniger.FixedPeriod.Quantum.WickTransferContractionBound
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import LiebLiniger.FixedPeriod.Quantum.SymmetricSubspacePureSpan
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import LiebLiniger.FixedPeriod.Quantum.WickPhysicalModeCommutation
import LiebLiniger.FixedPeriod.Quantum.WickWeightedMatching
import LiebLiniger.FixedPeriod.Quantum.WickDerivativeOrderedPairing
import LiebLiniger.FixedPeriod.Quantum.FiniteModeMixedKernelSpan
import LiebLiniger.FixedPeriod.Quantum.WickPureRankNormalOrderSector
import LiebLiniger.FixedPeriod.Quantum.WickGuardedDerivativePairing
import LiebLiniger.FixedPeriod.Quantum.WickMatchingDerivativeKernel
import LiebLiniger.FixedPeriod.Quantum.WickMixedOuterFactors
import LiebLiniger.FixedPeriod.Quantum.WickGuardedMixedOuterPairing
/-! Existing WHOLE finite-mode Wick product proof, source-preserving coalescence.
The first five historical providers are supplied by checked OneModeWickNormalOrder.
No new proof or target hypothesis is introduced; all new runtime gates are pending. -/




/- Source0 private lemmas are reproduced byte-for-byte locally; imported private
names are not visible to the downstream whole-proof sections. -/
section Q2024AssemblyPrivateHelpers
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

private theorem q2024_sector_inner_smul_left (n : ℕ) (a : ℂ)
    (x y : SymmetricSector μ n) :
    inner ℂ (a • x) y = (starRingEnd ℂ) a * inner ℂ x y := by
  change inner ℂ (a • (x : ProductL2 μ (Fin n))) (y : ProductL2 μ (Fin n)) = _
  exact inner_smul_left (𝕜 := ℂ) _ _ _

private theorem q2024_sector_inner_smul_right (n : ℕ) (a : ℂ)
    (x y : SymmetricSector μ n) :
    inner ℂ x (a • y) = a * inner ℂ x y := by
  change inner ℂ (x : ProductL2 μ (Fin n)) (a • (y : ProductL2 μ (Fin n))) = _
  exact inner_smul_right (𝕜 := ℂ) _ _ _

end LiebLiniger.FixedPeriod.Quantum
end
end Q2024AssemblyPrivateHelpers

/- Source-frozen leaf LiebLiniger.FixedPeriod.Quantum.WickSourceRankOneNormalOrder; 37e6fb8897fbc72f824e86eefe8f5ec1d7e2a1c02c2f047cd21b8378ce9a5592 -/
section Q2024Source1

/-! Direct source-Wick pure-rank-one normal ordering on complete sectors.
The scalar falling-factorial calculation reuses the written mathematical proof
in frozen WickGeometricPowers303ba, but the operators here are LITERALLY repeated
sourceWickAnnihilation, and their adjoints LITERALLY repeated sourceWickCreation.
No geometric-mode transport chain or operator-product formula is imported.
All p/q/k=0 cases are retained. SOURCE ONLY / UNCOMPILED. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum

variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- Every actual repeated creation on finite particles is the SAME bounded
complete-sector power, included in the genuine output sector. -/
theorem sourceFiniteParticleCreation_pow_lof (epsilon : ℝ) (h : Lp ℂ 2 μ)
    (k q : ℕ) (v : SymmetricSector μ k) :
    (sourceFiniteParticleCreation μ epsilon h ^ q)
        (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) k v) =
      DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) (k + q)
        (sourceWickCreationPower μ epsilon h k q v) := by
  induction q with
  | zero => simp only [pow_zero, Module.End.one_apply, Nat.add_zero,
      sourceWickCreationPower_zero, ContinuousLinearMap.id_apply]
  | succ q ih =>
    rw [pow_succ', Module.End.mul_apply, ih, sourceFiniteParticleCreation_lof,
      sourceWickCreationPower_succ, ContinuousLinearMap.comp_apply]
    rfl

/-- Actual repeated annihilation on each available input sector is the SAME
bounded source power; no occupation-basis transport is a premise. -/
theorem sourceFiniteParticleAnnihilation_pow_lof (epsilon : ℝ) (g : Lp ℂ 2 μ)
    (k p : ℕ) (v : SymmetricSector μ (k + p)) :
    (sourceFiniteParticleAnnihilation μ epsilon g ^ p)
        (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) (k + p) v) =
      DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) k
        (sourceWickAnnihilationPower μ epsilon g k p v) := by
  induction p with
  | zero => simp only [pow_zero, Module.End.one_apply, Nat.add_zero,
      sourceWickAnnihilationPower, ContinuousLinearMap.id_apply]
  | succ p ih =>
    rw [pow_succ, Module.End.mul_apply]
    calc
      _ = (sourceFiniteParticleAnnihilation μ epsilon g ^ p)
          (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) (k + p)
            (sourceWickAnnihilation μ epsilon g (k + p) v)) :=
        congrArg (fun w : SourceFiniteParticleSpace μ =>
          (sourceFiniteParticleAnnihilation μ epsilon g ^ p) w)
          (sourceFiniteParticleAnnihilation_lof_succ μ epsilon g (k + p) v)
      _ = _ := by
        rw [ih, sourceWickAnnihilationPower, ContinuousLinearMap.comp_apply]

/-- When p exceeds the ACTUAL input particle number, repeated source
annihilation is really zero, including the genuine vacuum branch. -/
theorem sourceFiniteParticleAnnihilation_pow_lof_of_lt (epsilon : ℝ)
    (g : Lp ℂ 2 μ) (p n : ℕ) (hn : n < p) (v : SymmetricSector μ n) :
    (sourceFiniteParticleAnnihilation μ epsilon g ^ p)
      (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n v) = 0 := by
  induction p generalizing n with
  | zero => omega
  | succ p ih =>
    rw [pow_succ, Module.End.mul_apply]
    cases n with
    | zero => rw [sourceFiniteParticleAnnihilation_lof_zero, map_zero]
    | succ n =>
      rw [sourceFiniteParticleAnnihilation_lof_succ]
      exact ih n (by omega) _

/-- Literal all-input-sector actual normal order, retaining the source
unavailable-input zero branch and equality-only source index casts. -/
def sourceWickPureRankNormalOrderOnSector (epsilon : ℝ) (h g : Lp ℂ 2 μ)
    (p q n : ℕ) : SymmetricSector μ n →L[ℂ] SymmetricSector μ (n + q - p) :=
  if hn : p ≤ n then
    (symmetricSectorCast μ (show q + (n - p) = n + q - p by omega)).toLinearIsometry.toContinuousLinearMap ∘L
      sourceWickPureRankNormalOrder μ epsilon h g p q (n - p) ∘L
      (symmetricSectorCast μ (show n = p + (n - p) by omega)).toLinearIsometry.toContinuousLinearMap
  else 0

/-- Whole all-sector pure-rank-one source-Wick identification with actual
normal order. This is an OPERATOR equality on complete sectors, with all
vacuum/unavailable branches. No product/CCR/normal-order premise is supplied. -/
theorem wickSectorMap_pure_rankOne_eq_source_normal_order (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (h g : Lp ℂ 2 μ) (p q n : ℕ) :
    wickSectorMap μ epsilon
        (InnerProductSpace.rankOne ℂ (pureSymmetricTensor μ q h)
          (pureSymmetricTensor μ p g)) n =
      sourceWickPureRankNormalOrderOnSector μ epsilon h g p q n := by
  unfold wickSectorMap sourceWickPureRankNormalOrderOnSector
  split_ifs with hn
  · rw [wickSectorAdded_pure_rankOne_eq_source_normal_order μ epsilon hepsilon]
  · rfl
end LiebLiniger.FixedPeriod.Quantum
end
end Q2024Source1


/- Source-frozen leaf LiebLiniger.FixedPeriod.Quantum.WickGlobalRankOneNormalOrder; 3c4f5d24a6884040de4f265e4e352d5b2439eaf0e085e4cdbfd5e6fd8d7c8e98 -/
section Q2024Source2

/-! Literal finite-particle source-Wick realization of pure-rank-one normal
ordering. Every summand is the SAME source wickSectorMap, including unavailable
input sectors. The right side is actual composition of the already realized
physical creation/annihilation endomorphisms. This closes the specific actual
rank-one monomial identification; it is not the general Wick product theorem.
SOURCE ONLY / UNCOMPILED. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped DirectSum
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- Actual source Wick on its full physical finite-particle domain: each input
sector is mapped by the literal independently constructed wickSectorMap. -/
def sourceFiniteParticleWick (epsilon : ℝ) {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) :
    Module.End ℂ (SourceFiniteParticleSpace μ) :=
  DirectSum.toModule ℂ ℕ _ (fun n =>
    (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) (n + q - p)).comp
      (wickSectorMap μ epsilon A n).toLinearMap)

@[simp] theorem sourceFiniteParticleWick_lof (epsilon : ℝ) {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (n : ℕ) (v : SymmetricSector μ n) :
    sourceFiniteParticleWick μ epsilon A
        (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n v) =
      DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) (n + q - p)
        (wickSectorMap μ epsilon A n v) := by
  rw [sourceFiniteParticleWick, DirectSum.toModule_lof]
  rfl

/-- Only equality transport: an index cast and its physical inclusion cancel. -/
private theorem source_lof_cast {m n : ℕ} (heq : m = n)
    (v : SymmetricSector μ m) :
    DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n (symmetricSectorCast μ heq v) =
      DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) m v := by
  subst n
  rfl

/-- In an available sector the literal source wickSectorMap is precisely its
source Added block, included at the exact output degree; no phase/factor added. -/
theorem sourceFiniteParticleWick_available_lof (epsilon : ℝ) {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (k : ℕ) (v : SymmetricSector μ (p + k)) :
    sourceFiniteParticleWick μ epsilon A
        (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) (p + k) v) =
      DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) (q + k)
        (wickSectorAdded μ epsilon A k v) := by
  rw [sourceFiniteParticleWick_lof, wickSectorMap,
    dif_pos (show p ≤ p + k by omega)]
  change DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) (p + k + q - p)
    (symmetricSectorCast μ (show q + (p + k - p) = p + k + q - p by omega)
      (wickSectorAdded μ epsilon A (p + k - p)
        (symmetricSectorCast μ (show p + k = p + (p + k - p) by omega) v))) = _
  rw [source_lof_cast]
  have htransport (m : ℕ) (hm : m = k) (hv : p + k = p + m) :
      DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) (q + m)
        (wickSectorAdded μ epsilon A m (symmetricSectorCast μ hv v)) =
      DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) (q + k)
        (wickSectorAdded μ epsilon A k v) := by
    subst m
    cases Subsingleton.elim hv rfl
    rfl
  exact htransport (p + k - p) (by omega) (by omega)

/-- Whole genuine physical rank-one monomial binding, on the SAME full
finite-particle domain: source Wick(|h^q><g^p|) = C_h^q A_g^p.
This includes unavailable input sectors, vacuum, p=0/q=0 and arbitrary L2
fields. No normal-ordering, product, CCR or intertwining premise is supplied. -/
theorem sourceFiniteParticleWick_pure_rankOne (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (h g : Lp ℂ 2 μ) (p q : ℕ) :
    sourceFiniteParticleWick μ epsilon
        (InnerProductSpace.rankOne ℂ (pureSymmetricTensor μ q h)
          (pureSymmetricTensor μ p g)) =
      sourceFiniteParticleCreation μ epsilon h ^ q *
        sourceFiniteParticleAnnihilation μ epsilon g ^ p := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro v
  change sourceFiniteParticleWick μ epsilon
      (InnerProductSpace.rankOne ℂ (pureSymmetricTensor μ q h)
        (pureSymmetricTensor μ p g))
      (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n v) =
    (sourceFiniteParticleCreation μ epsilon h ^ q)
      ((sourceFiniteParticleAnnihilation μ epsilon g ^ p)
        (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n v))
  by_cases hn : p ≤ n
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [sourceFiniteParticleWick_available_lof,
      wickSectorAdded_pure_rankOne_eq_source_normal_order μ epsilon hepsilon]
    change DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) (q + k)
      (symmetricSectorCast μ (Nat.add_comm k q)
        (sourceWickCreationPower μ epsilon h k q
          (sourceWickAnnihilationPower μ epsilon g k p
            (symmetricSectorCast μ (Nat.add_comm p k) v)))) = _
    rw [source_lof_cast]
    have hin := source_lof_cast μ (Nat.add_comm p k) v
    rw [← hin, sourceFiniteParticleAnnihilation_pow_lof,
      sourceFiniteParticleCreation_pow_lof]
  · have hnp : n < p := Nat.lt_of_not_ge hn
    rw [sourceFiniteParticleWick_lof, wickSectorMap_of_lt μ epsilon _ hnp,
      ContinuousLinearMap.zero_apply, map_zero,
      sourceFiniteParticleAnnihilation_pow_lof_of_lt μ epsilon g p n hnp,
      map_zero]

/-- The literal same operator identity evaluated on arbitrary physical finite
particles, ready to consume the actual normal-order/commutation formula. -/
theorem sourceFiniteParticleWick_pure_rankOne_apply (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (h g : Lp ℂ 2 μ) (p q : ℕ)
    (v : SourceFiniteParticleSpace μ) :
    sourceFiniteParticleWick μ epsilon
        (InnerProductSpace.rankOne ℂ (pureSymmetricTensor μ q h)
          (pureSymmetricTensor μ p g)) v =
      (sourceFiniteParticleCreation μ epsilon h ^ q)
        ((sourceFiniteParticleAnnihilation μ epsilon g ^ p) v) := by
  rw [sourceFiniteParticleWick_pure_rankOne μ epsilon hepsilon, Module.End.mul_apply]
end LiebLiniger.FixedPeriod.Quantum
end
end Q2024Source2


/- Source-frozen leaf LiebLiniger.FixedPeriod.Quantum.WickMixedRankOneNormalOrder; 83b1d5c4365eaf0b37248d8965c0b382ab3cfbbc3b2c7ecbfa5d370ccc0e824b -/
section Q2024Source3

/-! Actual arbitrary mixed-mode normal-ordered monomials on complete physical
sectors. Every field in the p input and q output slots is independent. The
kernel is the independently constructed rank-one operator of actual symmetrized
mixed tensors. Actual source annihilation words and their creation adjoints
are proved equal to source Wick, with every zero degree/spectator retained.
This is the physical monomial realization needed by Q2-024, not a supplied
polynomial intertwiner. SOURCE ONLY / UNCOMPILED. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- Actual successive source annihilations, one independently chosen physical
field per slot. Slot zero acts FIRST; the remaining tail then acts on the lower
sector. No polynomial/occupation-basis representation is used. -/
def sourceWickAnnihilationWord (epsilon : ℝ) (k : ℕ) :
    (p : ℕ) → (Fin p → Lp ℂ 2 μ) →
      SymmetricSector μ (k + p) →L[ℂ] SymmetricSector μ k
  | 0, _ => ContinuousLinearMap.id ℂ _
  | p + 1, gs => (sourceWickAnnihilationWord epsilon k p (fun i => gs i.succ)).comp
      (sourceWickAnnihilation μ epsilon (gs 0) (k + p))

/-- Actual source creation word, as the adjoint of the actual annihilation
word. Its recursion below exhibits EACH literal source creation factor. -/
def sourceWickCreationWord (epsilon : ℝ) (k p : ℕ) (hs : Fin p → Lp ℂ 2 μ) :
    SymmetricSector μ k →L[ℂ] SymmetricSector μ (k + p) :=
  (sourceWickAnnihilationWord μ epsilon k p hs).adjoint

@[simp] theorem sourceWickCreationWord_zero (epsilon : ℝ) (k : ℕ)
    (hs : Fin 0 → Lp ℂ 2 μ) :
    sourceWickCreationWord μ epsilon k 0 hs = ContinuousLinearMap.id ℂ _ := by
  simp only [sourceWickCreationWord, sourceWickAnnihilationWord,
    ContinuousLinearMap.adjoint_id]
  rfl

/-- Literal independent-field creation factors on the complete physical sector. -/
theorem sourceWickCreationWord_succ (epsilon : ℝ) (k p : ℕ)
    (hs : Fin (p + 1) → Lp ℂ 2 μ) :
    sourceWickCreationWord μ epsilon k (p + 1) hs =
      (sourceWickCreation μ epsilon (hs 0) (k + p)).comp
        (sourceWickCreationWord μ epsilon k p (fun i => hs i.succ)) := by
  simp only [sourceWickCreationWord, sourceWickAnnihilationWord,
    ContinuousLinearMap.adjoint_comp]
  rw [← sourceWickCreation_eq_adjoint_annihilation μ epsilon (hs 0) (k + p)]

/-- Exact all-sector pure action of the actual independent-field annihilation
word. The source factorial coefficient depends on p/k, while the fields enter
through their actual individual Hilbert inner products. -/
theorem sourceWickAnnihilationWord_pure (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (k p : ℕ) (gs : Fin p → Lp ℂ 2 μ) (u : Lp ℂ 2 μ) :
    sourceWickAnnihilationWord μ epsilon k p gs (pureSymmetricTensor μ (k + p) u) =
      ((sourceWickPowerCoefficient epsilon k p : ℂ) *
        ∏ i : Fin p, inner ℂ (gs i) u) • pureSymmetricTensor μ k u := by
  induction p with
  | zero => simp [sourceWickAnnihilationWord]
  | succ p ih =>
    rw [sourceWickAnnihilationWord, ContinuousLinearMap.comp_apply]
    calc
      _ = sourceWickAnnihilationWord μ epsilon k p (fun i => gs i.succ)
          (((sourceWickElementaryCoefficient epsilon (k + p) : ℂ) *
            inner ℂ (gs 0) u) • pureSymmetricTensor μ (k + p) u) :=
        congrArg (fun x : SymmetricSector μ (k + p) =>
          sourceWickAnnihilationWord μ epsilon k p (fun i => gs i.succ) x)
          (sourceWickAnnihilation_pure μ epsilon (gs 0) u (k + p))
      _ = _ := by
        rw [map_smul, ih, smul_smul, sourceWickPowerCoefficient_succ epsilon hepsilon,
          Complex.ofReal_mul, sourceWickElementaryCoefficient, Complex.ofReal_mul,
          Fin.prod_univ_succ]
        apply congrArg (fun c : ℂ => c • pureSymmetricTensor μ k u)
        ring

private theorem mixedRank_cast_pure {m n : ℕ} (heq : m = n) (u : Lp ℂ 2 μ) :
    symmetricSectorCast μ heq (pureSymmetricTensor μ m u) = pureSymmetricTensor μ n u := by
  subst n
  rfl

/-- Actual p independent-field annihilations, followed by actual q independent-
field creations, with the SAME source spectator and index ordering. -/
def sourceWickMixedRankNormalOrder (epsilon : ℝ) (p q k : ℕ)
    (hs : Fin q → Lp ℂ 2 μ) (gs : Fin p → Lp ℂ 2 μ) :
    SymmetricSector μ (p + k) →L[ℂ] SymmetricSector μ (q + k) :=
  (symmetricSectorCast μ (Nat.add_comm k q)).toLinearIsometry.toContinuousLinearMap ∘L
    sourceWickCreationWord μ epsilon k q hs ∘L
    sourceWickAnnihilationWord μ epsilon k p gs ∘L
    (symmetricSectorCast μ (Nat.add_comm p k)).toLinearIsometry.toContinuousLinearMap

/-- Earned polarized matrix element of the actual mixed normal-ordered product. -/
theorem sourceWickMixedRankNormalOrder_pairing (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (p q k : ℕ) (hs : Fin q → Lp ℂ 2 μ) (gs : Fin p → Lp ℂ 2 μ)
    (v u : Lp ℂ 2 μ) :
    inner ℂ (pureSymmetricTensor μ (q + k) v)
      (sourceWickMixedRankNormalOrder μ epsilon p q k hs gs
        (pureSymmetricTensor μ (p + k) u)) =
      (LLFPSectorCandidate.wickCoefficient epsilon p q (p + k) : ℂ) *
        (((∏ i : Fin q, inner ℂ v (hs i)) *
          (∏ i : Fin p, inner ℂ (gs i) u)) * inner ℂ v u ^ k) := by
  change inner ℂ (pureSymmetricTensor μ (q + k) v)
    (symmetricSectorCast μ (Nat.add_comm k q)
      ((sourceWickAnnihilationWord μ epsilon k q hs).adjoint
        (sourceWickAnnihilationWord μ epsilon k p gs
          (symmetricSectorCast μ (Nat.add_comm p k)
            (pureSymmetricTensor μ (p + k) u))))) = _
  rw [mixedRank_cast_pure]
  have hv := mixedRank_cast_pure μ (Nat.add_comm k q) v
  rw [← hv, (symmetricSectorCast μ (Nat.add_comm k q)).inner_map_map,
    ContinuousLinearMap.adjoint_inner_right,
    sourceWickAnnihilationWord_pure μ epsilon hepsilon,
    sourceWickAnnihilationWord_pure μ epsilon hepsilon,
    q2024_sector_inner_smul_left μ k, q2024_sector_inner_smul_right μ k]
  simp only [map_mul, map_prod, Complex.conj_ofReal, inner_conj_symm,
    inner_pureSymmetricTensor, smul_eq_mul]
  have hc : (sourceWickPowerCoefficient epsilon k p : ℂ) *
      (sourceWickPowerCoefficient epsilon k q : ℂ) =
        (LLFPSectorCandidate.wickCoefficient epsilon p q (p + k) : ℂ) := by
    exact_mod_cast sourceWickPowerCoefficient_mul epsilon hepsilon k p q
  rw [← hc]
  ring

/-- Actual source Wick of an arbitrary MIXED physical rank-one monomial is
exactly actual normal-ordered creation/annihilation words, complete sectors.
All fields/zero degrees/spectators are unrestricted; no transport/product or
commutation relation is assumed. -/
theorem wickSectorAdded_mixed_rankOne_eq_source_normal_order (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (p q k : ℕ)
    (hs : Fin q → Lp ℂ 2 μ) (gs : Fin p → Lp ℂ 2 μ) :
    wickSectorAdded μ epsilon
        (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ q hs)
          (symmetricTensorContinuousMultilinear μ p gs)) k =
      sourceWickMixedRankNormalOrder μ epsilon p q k hs gs := by
  apply wickSymmetricSector_operator_eq_of_pure_pairings μ
  intro u v
  change inner ℂ (pureSymmetricTensor μ (q + k) v)
    ((LLFPSectorCandidate.wickCoefficient epsilon p q (p + k) : ℂ) •
      unscaledWickAdded μ
        (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ q hs)
          (symmetricTensorContinuousMultilinear μ p gs)) k
        (pureSymmetricTensor μ (p + k) u)) = _
  rw [q2024_sector_inner_smul_right μ (q + k),
    unscaledWickAdded_pairing, sourceWickMixedRankNormalOrder_pairing μ epsilon hepsilon]
  simp only [wickKernelPolarized, InnerProductSpace.rankOne_apply,
    q2024_sector_inner_smul_right μ, inner_pure_symmetricMixedTensor,
    inner_symmetricMixedTensor_pure, smul_eq_mul]
  ring
end LiebLiniger.FixedPeriod.Quantum
end
end Q2024Source3


/- Source-frozen leaf LiebLiniger.FixedPeriod.Quantum.WickGlobalMixedRankOneNormalOrder; fbfd75d25515aeb90bdc473e86691e098535b1894640330f26d943cd3cb5ffba -/
section Q2024Source4

/-! Genuine finite-particle mixed-mode source monomial realization. Every
source Wick factor is independently defined on COMPLETE physical sectors; each
word factor is an actual source creation/annihilation. The proof includes both
available and unavailable particle sectors and arbitrary independent fields.
No occupation-polynomial or assumed intertwiner is used. SOURCE ONLY / UNCOMPILED. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped DirectSum
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- Actual global creation word, with precisely the bounded-sector adjoint
word's order: the head creation acts after all tail creations. -/
def sourceFiniteParticleCreationWord (epsilon : ℝ) :
    (q : ℕ) → (Fin q → Lp ℂ 2 μ) → Module.End ℂ (SourceFiniteParticleSpace μ)
  | 0, _ => 1
  | q + 1, hs => sourceFiniteParticleCreation μ epsilon (hs 0) *
      sourceFiniteParticleCreationWord epsilon q (fun i => hs i.succ)

/-- Actual global annihilation word: the head annihilator acts first. -/
def sourceFiniteParticleAnnihilationWord (epsilon : ℝ) :
    (p : ℕ) → (Fin p → Lp ℂ 2 μ) → Module.End ℂ (SourceFiniteParticleSpace μ)
  | 0, _ => 1
  | p + 1, gs => sourceFiniteParticleAnnihilationWord epsilon p (fun i => gs i.succ) *
      sourceFiniteParticleAnnihilation μ epsilon (gs 0)

/-- Actual global mixed-field creation word on each genuine source sector. -/
theorem sourceFiniteParticleCreationWord_lof (epsilon : ℝ) (k q : ℕ)
    (hs : Fin q → Lp ℂ 2 μ) (v : SymmetricSector μ k) :
    sourceFiniteParticleCreationWord μ epsilon q hs
        (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) k v) =
      DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) (k + q)
        (sourceWickCreationWord μ epsilon k q hs v) := by
  induction q with
  | zero => simp only [sourceFiniteParticleCreationWord, Module.End.one_apply,
      Nat.add_zero, sourceWickCreationWord_zero, ContinuousLinearMap.id_apply]
  | succ q ih =>
    rw [sourceFiniteParticleCreationWord, Module.End.mul_apply, ih,
      sourceFiniteParticleCreation_lof, sourceWickCreationWord_succ,
      ContinuousLinearMap.comp_apply]
    rfl

/-- Actual global mixed-field annihilation word on every available source sector. -/
theorem sourceFiniteParticleAnnihilationWord_lof (epsilon : ℝ) (k p : ℕ)
    (gs : Fin p → Lp ℂ 2 μ) (v : SymmetricSector μ (k + p)) :
    sourceFiniteParticleAnnihilationWord μ epsilon p gs
        (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) (k + p) v) =
      DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) k
        (sourceWickAnnihilationWord μ epsilon k p gs v) := by
  induction p with
  | zero => simp only [sourceFiniteParticleAnnihilationWord, Module.End.one_apply,
      Nat.add_zero, sourceWickAnnihilationWord, ContinuousLinearMap.id_apply]
  | succ p ih =>
    rw [sourceFiniteParticleAnnihilationWord, Module.End.mul_apply]
    calc
      _ = sourceFiniteParticleAnnihilationWord μ epsilon p (fun i => gs i.succ)
          (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) (k + p)
            (sourceWickAnnihilation μ epsilon (gs 0) (k + p) v)) :=
        congrArg (fun w : SourceFiniteParticleSpace μ =>
          sourceFiniteParticleAnnihilationWord μ epsilon p (fun i => gs i.succ) w)
          (sourceFiniteParticleAnnihilation_lof_succ μ epsilon (gs 0) (k + p) v)
      _ = _ := by
        rw [ih, sourceWickAnnihilationWord, ContinuousLinearMap.comp_apply]

/-- All unavailable source sectors are genuinely killed by the actual mixed
annihilation word, including its literal vacuum branch. -/
theorem sourceFiniteParticleAnnihilationWord_lof_of_lt (epsilon : ℝ)
    (p n : ℕ) (gs : Fin p → Lp ℂ 2 μ) (hn : n < p) (v : SymmetricSector μ n) :
    sourceFiniteParticleAnnihilationWord μ epsilon p gs
      (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n v) = 0 := by
  induction p generalizing n with
  | zero => omega
  | succ p ih =>
    rw [sourceFiniteParticleAnnihilationWord, Module.End.mul_apply]
    cases n with
    | zero => rw [sourceFiniteParticleAnnihilation_lof_zero, map_zero]
    | succ n =>
      rw [sourceFiniteParticleAnnihilation_lof_succ]
      exact ih n (fun i => gs i.succ) (by omega) _

private theorem globalMixed_lof_cast {m n : ℕ} (heq : m = n)
    (v : SymmetricSector μ m) :
    DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n (symmetricSectorCast μ heq v) =
      DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) m v := by
  subst n
  rfl

/-- WHOLE physical finite-particle monomial realization for ARBITRARY mixed
fields. The left side is the independent actual source Wick of the rank-one
operator between actual symmetric mixed tensors. The right side is literal
composition of actual physical source words. All epsilon>0, zero bidegrees,
independent fields, vacuum and unavailable input sectors are retained. -/
theorem sourceFiniteParticleWick_mixed_rankOne (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (p q : ℕ) (hs : Fin q → Lp ℂ 2 μ) (gs : Fin p → Lp ℂ 2 μ) :
    sourceFiniteParticleWick μ epsilon
        (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ q hs)
          (symmetricTensorContinuousMultilinear μ p gs)) =
      sourceFiniteParticleCreationWord μ epsilon q hs *
        sourceFiniteParticleAnnihilationWord μ epsilon p gs := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro v
  change sourceFiniteParticleWick μ epsilon
      (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ q hs)
        (symmetricTensorContinuousMultilinear μ p gs))
      (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n v) =
    sourceFiniteParticleCreationWord μ epsilon q hs
      (sourceFiniteParticleAnnihilationWord μ epsilon p gs
        (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n v))
  by_cases hn : p ≤ n
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [sourceFiniteParticleWick_available_lof,
      wickSectorAdded_mixed_rankOne_eq_source_normal_order μ epsilon hepsilon]
    change DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) (q + k)
      (symmetricSectorCast μ (Nat.add_comm k q)
        (sourceWickCreationWord μ epsilon k q hs
          (sourceWickAnnihilationWord μ epsilon k p gs
            (symmetricSectorCast μ (Nat.add_comm p k) v)))) = _
    rw [globalMixed_lof_cast]
    have hin := globalMixed_lof_cast μ (Nat.add_comm p k) v
    rw [← hin, sourceFiniteParticleAnnihilationWord_lof,
      sourceFiniteParticleCreationWord_lof]
  · have hnp : n < p := Nat.lt_of_not_ge hn
    rw [sourceFiniteParticleWick_lof, wickSectorMap_of_lt μ epsilon _ hnp,
      ContinuousLinearMap.zero_apply, map_zero,
      sourceFiniteParticleAnnihilationWord_lof_of_lt μ epsilon p n gs hnp,
      map_zero]
end LiebLiniger.FixedPeriod.Quantum
end
end Q2024Source4


/- Source-frozen leaf LiebLiniger.FixedPeriod.Quantum.WickMixedWordFirstCommutation; a0ab5aab9316407628d8634e5519b9379986b09757d249aa93dd5030cd9d8c1e -/
section Q2024Source5

/-! Genuine physical one-annihilator/many-independent-creators contraction.
Every field and operator is actual; the finite sum removes exactly ONE source
creation slot. This is the direct mixed-mode Leibniz step for the Q2-024 word
expansion, with arbitrary fields and the true epsilon inner(g,h_i) coefficient.
SOURCE ONLY / UNCOMPILED. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- Literal creation-word deletion at a non-head slot, with all other physical
fields preserved in their original order. -/
private theorem creationWord_remove_succ (epsilon : ℝ) (q : ℕ)
    (hs : Fin (q + 2) → Lp ℂ 2 μ) (i : Fin (q + 1)) :
    sourceFiniteParticleCreationWord μ epsilon (q + 1) (i.succ.removeNth hs) =
      sourceFiniteParticleCreation μ epsilon (hs 0) *
        sourceFiniteParticleCreationWord μ epsilon q (i.removeNth (Fin.tail hs)) := by
  have hr : i.succ.removeNth hs = Fin.cons (hs 0) (i.removeNth (Fin.tail hs)) := by
    change hs ∘ i.succ.succAbove = _
    calc
      _ = (Fin.cons (hs 0) (Fin.tail hs)) ∘ i.succ.succAbove := by
        rw [Fin.cons_self_tail]
      _ = _ := Fin.cons_comp_succ_succAbove (hs 0) (Fin.tail hs) i
  rw [hr, sourceFiniteParticleCreationWord]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- ACTUAL physical mixed-mode first commutation on every finite-particle
vector: each of the q+1 independently chosen creation slots contributes its
own epsilon*inner(g,h_i), with that exact slot removed. No word/product identity
or commutation relation is supplied as a premise. Vacuum and q=0 retained. -/
theorem sourceFiniteParticle_annihilation_creationWord (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (g : Lp ℂ 2 μ) (q : ℕ)
    (hs : Fin (q + 1) → Lp ℂ 2 μ) :
    sourceFiniteParticleAnnihilation μ epsilon g *
        sourceFiniteParticleCreationWord μ epsilon (q + 1) hs =
      sourceFiniteParticleCreationWord μ epsilon (q + 1) hs *
          sourceFiniteParticleAnnihilation μ epsilon g +
        ∑ i : Fin (q + 1), ((epsilon : ℂ) * inner ℂ g (hs i)) •
          sourceFiniteParticleCreationWord μ epsilon q (i.removeNth hs) := by
  induction q with
  | zero =>
    simpa only [sourceFiniteParticleCreationWord, mul_one, Fin.sum_univ_succ,
      Fin.sum_univ_zero, add_zero] using
      sourceFiniteParticle_CCR μ epsilon hepsilon g (hs 0)
  | succ q ih =>
    let A := sourceFiniteParticleAnnihilation μ epsilon g
    let C := sourceFiniteParticleCreation μ epsilon (hs 0)
    let T := sourceFiniteParticleCreationWord μ epsilon (q + 1) (Fin.tail hs)
    let S : Module.End ℂ (SourceFiniteParticleSpace μ) :=
      ∑ i : Fin (q + 1), ((epsilon : ℂ) * inner ℂ g ((Fin.tail hs) i)) •
        sourceFiniteParticleCreationWord μ epsilon q (i.removeNth (Fin.tail hs))
    let c : ℂ := (epsilon : ℂ) * inner ℂ g (hs 0)
    have hccr : A * C = C * A + c • (1 : Module.End ℂ (SourceFiniteParticleSpace μ)) :=
      sourceFiniteParticle_CCR μ epsilon hepsilon g (hs 0)
    have hih : A * T = T * A + S := ih (Fin.tail hs)
    have hsum : (∑ i : Fin (q + 2), ((epsilon : ℂ) * inner ℂ g (hs i)) •
        sourceFiniteParticleCreationWord μ epsilon (q + 1) (i.removeNth hs)) =
        c • T + C * S := by
      rw [Fin.sum_univ_succ (fun i : Fin (q + 2) =>
        ((epsilon : ℂ) * inner ℂ g (hs i)) •
          sourceFiniteParticleCreationWord μ epsilon (q + 1) (i.removeNth hs))]
      rw [Fin.removeNth_zero]
      change c • T + _ = c • T + C * S
      congr 1
      dsimp only [S]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [creationWord_remove_succ, mul_smul_comm]
      rfl
    change A * (C * T) = (C * T) * A + _
    rw [hsum]
    calc
      A * (C * T) = (A * C) * T := by rw [mul_assoc]
      _ = (C * A + c • (1 : Module.End ℂ (SourceFiniteParticleSpace μ))) * T := by
        rw [hccr]
      _ = (C * T) * A + (c • T + C * S) := by
        rw [add_mul, smul_mul_assoc, one_mul, mul_assoc, hih, mul_add]
        simp only [← mul_assoc]
        abel
end LiebLiniger.FixedPeriod.Quantum
end
end Q2024Source5


/- Source-frozen leaf LiebLiniger.FixedPeriod.Quantum.WickMixedWordMatchingExpansion; 61a1c42451446afd2f4414e1b31ee08ec984b74a5f8188f5c016ace091657f31 -/
section Q2024Source6

/-! Actual mixed-word contraction expansion before grouping by j.
The finite data below contain ONLY remaining physical fields, a complex product
of actual field inner products, and the number of contracted pairs. There are
NO proposition fields or product/CCR assumptions. The list retains every
matching as a separate term, including coincident-field multiplicities.
The theorem identifies the ACTUAL physical operator composition with the sum
of literal source Wick kernels, with epsilon^j explicit before grouping.
SOURCE ONLY / UNCOMPILED. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- Independent actual source Wick quantization of a matching's mixed rank-one
kernel. The recorded contraction count earns the exact explicit epsilon^j. -/
def sourceWickMatchingQuantize (epsilon : ℝ) (t : SourceWickMatchingTerm μ) :
    Module.End ℂ (SourceFiniteParticleSpace μ) :=
  ((epsilon : ℂ) ^ t.contractions * t.coefficient) •
    sourceFiniteParticleWick μ epsilon
      (InnerProductSpace.rankOne ℂ
        (symmetricTensorContinuousMultilinear μ t.outputDegree t.outputFields)
        (symmetricTensorContinuousMultilinear μ t.inputDegree t.inputFields))

/-- Finite sum, with all matching multiplicities retained. -/
def sourceWickMatchingSum (epsilon : ℝ) : List (SourceWickMatchingTerm μ) →
    Module.End ℂ (SourceFiniteParticleSpace μ)
  | [] => 0
  | t :: ts => sourceWickMatchingQuantize μ epsilon t + sourceWickMatchingSum epsilon ts

private theorem matchingQuantize_keep (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (g : Lp ℂ 2 μ) (t : SourceWickMatchingTerm μ) :
    sourceWickMatchingQuantize μ epsilon (sourceMatchingKeep μ g t) =
      sourceWickMatchingQuantize μ epsilon t * sourceFiniteParticleAnnihilation μ epsilon g := by
  unfold sourceWickMatchingQuantize sourceMatchingKeep
  dsimp only
  rw [sourceFiniteParticleWick_mixed_rankOne μ epsilon hepsilon,
    sourceFiniteParticleWick_mixed_rankOne μ epsilon hepsilon,
    sourceFiniteParticleAnnihilationWord]
  simp only [Fin.cons_zero, Fin.cons_succ, smul_mul_assoc, mul_assoc]

private theorem matchingQuantize_contract (epsilon : ℝ) (c : ℂ)
    (t : SourceWickMatchingTerm μ) :
    sourceWickMatchingQuantize μ epsilon (sourceMatchingContract μ c t) =
      ((epsilon : ℂ) * c) • sourceWickMatchingQuantize μ epsilon t := by
  let W : Module.End ℂ (SourceFiniteParticleSpace μ) :=
    sourceFiniteParticleWick μ epsilon
      (InnerProductSpace.rankOne ℂ
        (symmetricTensorContinuousMultilinear μ t.outputDegree t.outputFields)
        (symmetricTensorContinuousMultilinear μ t.inputDegree t.inputFields))
  change ((epsilon : ℂ) ^ (t.contractions + 1) * (c * t.coefficient)) • W =
    ((epsilon : ℂ) * c) • (((epsilon : ℂ) ^ t.contractions * t.coefficient) • W)
  rw [smul_smul]
  congr 1
  rw [pow_succ]
  ring

private theorem matchingSum_append (epsilon : ℝ)
    (as bs : List (SourceWickMatchingTerm μ)) :
    sourceWickMatchingSum μ epsilon (as ++ bs) =
      sourceWickMatchingSum μ epsilon as + sourceWickMatchingSum μ epsilon bs := by
  induction as with
  | nil => simp only [List.nil_append, sourceWickMatchingSum, zero_add]
  | cons a as ih =>
    simp only [List.cons_append, sourceWickMatchingSum, ih, add_assoc]

private theorem matchingSum_keep (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (g : Lp ℂ 2 μ) (ts : List (SourceWickMatchingTerm μ)) :
    sourceWickMatchingSum μ epsilon (ts.map (sourceMatchingKeep μ g)) =
      sourceWickMatchingSum μ epsilon ts * sourceFiniteParticleAnnihilation μ epsilon g := by
  induction ts with
  | nil => simp only [List.map_nil, sourceWickMatchingSum, zero_mul]
  | cons t ts ih =>
    simp only [List.map_cons, sourceWickMatchingSum, matchingQuantize_keep μ epsilon hepsilon,
      ih, add_mul]

private theorem matchingSum_contract (epsilon : ℝ) (c : ℂ)
    (ts : List (SourceWickMatchingTerm μ)) :
    sourceWickMatchingSum μ epsilon (ts.map (sourceMatchingContract μ c)) =
      ((epsilon : ℂ) * c) • sourceWickMatchingSum μ epsilon ts := by
  induction ts with
  | nil => simp only [List.map_nil, sourceWickMatchingSum, smul_zero]
  | cons t ts ih =>
    simp only [List.map_cons, sourceWickMatchingSum, matchingQuantize_contract,
      ih, smul_add]

private theorem matchingSum_flatten (epsilon : ℝ)
    (tss : List (List (SourceWickMatchingTerm μ))) :
    sourceWickMatchingSum μ epsilon tss.flatten =
      (tss.map (sourceWickMatchingSum μ epsilon)).sum := by
  induction tss with
  | nil => simp only [List.flatten_nil, sourceWickMatchingSum, List.map_nil, List.sum_nil]
  | cons ts tss ih =>
    simp only [List.flatten_cons, matchingSum_append, List.map_cons, List.sum_cons, ih]

private theorem matchingSum_flatten_ofFn (epsilon : ℝ) (n : ℕ)
    (ts : Fin n → List (SourceWickMatchingTerm μ)) :
    sourceWickMatchingSum μ epsilon (List.ofFn ts).flatten =
      ∑ i : Fin n, sourceWickMatchingSum μ epsilon (ts i) := by
  rw [matchingSum_flatten, List.map_ofFn, List.sum_ofFn]
  rfl

/-- Genuine complete physical mixed-word contraction expansion BEFORE grouping
by j. Every term is an independent actual source Wick mixed-rank-one kernel,
weighted by the actual matching inner products and EXACT epsilon^j. There is
no product, CCR, derivative-kernel or polynomial-intertwiner premise. -/
theorem sourceFiniteParticle_mixedWord_matching_expansion (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (p q : ℕ) (gs : Fin p → Lp ℂ 2 μ)
    (hs : Fin q → Lp ℂ 2 μ) :
    sourceFiniteParticleAnnihilationWord μ epsilon p gs *
        sourceFiniteParticleCreationWord μ epsilon q hs =
      sourceWickMatchingSum μ epsilon (sourceWickMatchingTerms μ p gs q hs) := by
  induction p generalizing q hs with
  | zero =>
    simp only [sourceFiniteParticleAnnihilationWord, one_mul,
      sourceWickMatchingTerms, sourceWickMatchingSum, add_zero,
      sourceWickMatchingQuantize, pow_zero, one_mul, one_smul,
      sourceFiniteParticleWick_mixed_rankOne μ epsilon hepsilon, mul_one]
  | succ p ih =>
    cases q with
    | zero =>
      rw [sourceWickMatchingTerms, matchingSum_keep μ epsilon hepsilon]
      have hh := ih 0 (Fin.tail gs) hs
      simp only [sourceFiniteParticleCreationWord, mul_one] at hh
      rw [← hh, sourceFiniteParticleAnnihilationWord, sourceFiniteParticleCreationWord, mul_one]
      rfl
    | succ q =>
      rw [sourceWickMatchingTerms, matchingSum_append,
        matchingSum_keep μ epsilon hepsilon, matchingSum_flatten_ofFn]
      simp_rw [matchingSum_contract]
      rw [← ih (q + 1) (Fin.tail gs) hs]
      have hrem (i : Fin (q + 1)) :
          sourceWickMatchingSum μ epsilon
              (sourceWickMatchingTerms μ p (Fin.tail gs) q (i.removeNth hs)) =
            sourceFiniteParticleAnnihilationWord μ epsilon p (Fin.tail gs) *
              sourceFiniteParticleCreationWord μ epsilon q (i.removeNth hs) :=
        (ih q (Fin.tail gs) (i.removeNth hs)).symm
      simp_rw [hrem]
      rw [sourceFiniteParticleAnnihilationWord, mul_assoc,
        sourceFiniteParticle_annihilation_creationWord μ epsilon hepsilon,
        mul_add, Finset.mul_sum]
      simp only [mul_assoc, mul_smul_comm]
      rfl
end LiebLiniger.FixedPeriod.Quantum
end
end Q2024Source6








/- Source-frozen leaf LiebLiniger.FixedPeriod.Quantum.WickKernelLinearity; 5db2ade206a6adcf3d1402aa85508fc8dc0cf4cb29a9dd3bfaf56be2b0af2e30 -/
section Q2024Source9

/-! Genuine source-Wick linearity in its independent actual kernel, needed for
finite matching-kernel assembly. The already reviewed scalar proofs e6ea are
retained verbatim; additivity is earned by physical pure pairings and complete
sector totality. No product or source-kernel identity is an input premise.
SOURCE ONLY / UNCOMPILED. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped DirectSum
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- Source Wick is genuinely linear in scalar multiplication of its kernel,
including every unavailable-input branch of the actual sector map. -/
theorem wickSectorMap_smul_sourceKernel (epsilon : ℝ) {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (c : ℂ) (n : ℕ) :
    wickSectorMap μ epsilon (c • A) n = c • wickSectorMap μ epsilon A n := by
  apply wickSymmetricSector_operator_eq_of_pure_pairings μ
  intro u v
  rw [ContinuousLinearMap.smul_apply, q2024_sector_inner_smul_right μ (n + q - p)]
  by_cases hn : p ≤ n
  · rw [wickSectorMap_available_pairing μ epsilon (c • A) hn,
      wickSectorMap_available_pairing μ epsilon A hn]
    simp only [wickKernelPolarized, ContinuousLinearMap.smul_apply,
      q2024_sector_inner_smul_right μ q]
    ring
  · rw [wickSectorMap_of_lt μ epsilon (c • A) (Nat.lt_of_not_ge hn),
      wickSectorMap_of_lt μ epsilon A (Nat.lt_of_not_ge hn)]
    simp only [ContinuousLinearMap.zero_apply, inner_zero_right, mul_zero]

/-- The SAME full physical finite-particle source Wick map is scalar-linear
in its actual bounded kernel. No Hilbert-Fock operator norm is being asserted. -/
theorem sourceFiniteParticleWick_smul_kernel (epsilon : ℝ) {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (c : ℂ) :
    sourceFiniteParticleWick μ epsilon (c • A) = c • sourceFiniteParticleWick μ epsilon A := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro v
  change sourceFiniteParticleWick μ epsilon (c • A)
    (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n v) =
      c • sourceFiniteParticleWick μ epsilon A
        (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n v)
  rw [sourceFiniteParticleWick_lof, sourceFiniteParticleWick_lof,
    wickSectorMap_smul_sourceKernel, ContinuousLinearMap.smul_apply, map_smul]

/-- Literal source sector Wick is additive in its actual bounded kernel,
including the prescribed unavailable-input zero branches. -/
theorem wickSectorMap_add_sourceKernel (epsilon : ℝ) {p q : ℕ}
    (A B : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (n : ℕ) :
    wickSectorMap μ epsilon (A + B) n =
      wickSectorMap μ epsilon A n + wickSectorMap μ epsilon B n := by
  apply wickSymmetricSector_operator_eq_of_pure_pairings μ
  intro u v
  rw [ContinuousLinearMap.add_apply, inner_add_right]
  by_cases hn : p ≤ n
  · rw [wickSectorMap_available_pairing μ epsilon (A + B) hn,
      wickSectorMap_available_pairing μ epsilon A hn,
      wickSectorMap_available_pairing μ epsilon B hn]
    simp only [wickKernelPolarized, ContinuousLinearMap.add_apply, inner_add_right]
    ring
  · rw [wickSectorMap_of_lt μ epsilon (A + B) (Nat.lt_of_not_ge hn),
      wickSectorMap_of_lt μ epsilon A (Nat.lt_of_not_ge hn),
      wickSectorMap_of_lt μ epsilon B (Nat.lt_of_not_ge hn)]
    simp only [ContinuousLinearMap.zero_apply, inner_zero_right, add_zero]

/-- The SAME actual finite-particle Wick map is additive in the source kernel. -/
theorem sourceFiniteParticleWick_add_kernel (epsilon : ℝ) {p q : ℕ}
    (A B : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) :
    sourceFiniteParticleWick μ epsilon (A + B) =
      sourceFiniteParticleWick μ epsilon A + sourceFiniteParticleWick μ epsilon B := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro v
  change sourceFiniteParticleWick μ epsilon (A + B)
    (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n v) =
      sourceFiniteParticleWick μ epsilon A (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n v) +
        sourceFiniteParticleWick μ epsilon B (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n v)
  rw [sourceFiniteParticleWick_lof, sourceFiniteParticleWick_lof,
    sourceFiniteParticleWick_lof, wickSectorMap_add_sourceKernel,
    ContinuousLinearMap.add_apply, map_add]

/-- Actual zero kernel quantizes to actual zero, all sectors retained. -/
@[simp] theorem sourceFiniteParticleWick_zero_kernel (epsilon : ℝ) (p q : ℕ) :
    sourceFiniteParticleWick μ epsilon
      (0 : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) = 0 := by
  have hz : (0 : ℂ) • (0 : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply, smul_zero]
  calc
    sourceFiniteParticleWick μ epsilon (0 : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) =
        sourceFiniteParticleWick μ epsilon
          ((0 : ℂ) • (0 : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)) :=
      (congrArg (sourceFiniteParticleWick μ epsilon) hz).symm
    _ = (0 : ℂ) • sourceFiniteParticleWick μ epsilon
        (0 : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) :=
      sourceFiniteParticleWick_smul_kernel μ epsilon _ _
    _ = 0 := zero_smul ℂ _

/-- A genuine linear map on ACTUAL bounded homogeneous source kernels, with
values in actual finite-particle physical operators. No global Fock norm bound. -/
def sourceFiniteParticleWickKernelLinearMap (epsilon : ℝ) (p q : ℕ) :
    (SymmetricSector μ p →L[ℂ] SymmetricSector μ q) →ₗ[ℂ]
      Module.End ℂ (SourceFiniteParticleSpace μ) where
  toFun := sourceFiniteParticleWick μ epsilon
  map_add' := sourceFiniteParticleWick_add_kernel μ epsilon
  map_smul' := fun c A => sourceFiniteParticleWick_smul_kernel μ epsilon A c

/-- Source index transport is equality only and preserves the physical global
finite-particle operator. This is not a change of measure or mode basis. -/
theorem sourceFiniteParticleWick_indexCast (epsilon : ℝ) {a b c d : ℕ}
    (hin : a = b) (hout : c = d)
    (T : SymmetricSector μ b →L[ℂ] SymmetricSector μ c) :
    sourceFiniteParticleWick μ epsilon
        ((symmetricSectorCast μ hout).toLinearIsometry.toContinuousLinearMap ∘L T ∘L
          (symmetricSectorCast μ hin).toLinearIsometry.toContinuousLinearMap) =
      sourceFiniteParticleWick μ epsilon T := by
  subst b
  subst d
  congr 1
end LiebLiniger.FixedPeriod.Quantum
end
end Q2024Source9


/- Source-frozen leaf LiebLiniger.FixedPeriod.Quantum.WickMatchingKernel; 7f11eaf755c444ef8ebab5271d0b291569e48e7c82ea1dd0cba08f2626d23f8d -/
section Q2024Source10

/-! Actual fixed-degree kernel of the count-j matching terms. Each term is the
literal physical mixed rank-one kernel, with equality-only index transports
proved from the actual recursive matching degree invariant. Every list
multiplicity is retained. The exact filtered physical operator sum is its
actual source Wick quantization with epsilon^j. This construction does not
assume the weighted embedding/matching identity or any Wick product formula.
SOURCE ONLY / UNCOMPILED. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- The actual source quantization of a single transported count-j kernel.
This equality is proved from actual source kernel scalar-linearity and index
transport, not from a target-bearing matching quantization assumption. -/
theorem sourceWickMatchingTermKernel_quantize (epsilon : ℝ) (p q j : ℕ)
    (gs : Fin p → Lp ℂ 2 μ) (hs : Fin q → Lp ℂ 2 μ)
    (t : {t // t ∈ sourceWickMatchingCountTerms μ p q j gs hs}) :
    sourceWickMatchingQuantize μ epsilon t.val =
      (epsilon : ℂ) ^ j •
        sourceFiniteParticleWick μ epsilon (sourceWickMatchingTermKernel μ p q j gs hs t) := by
  have hj : t.val.contractions = j := by
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp t.property).2
  unfold sourceWickMatchingTermKernel
  rw [sourceFiniteParticleWick_smul_kernel, sourceFiniteParticleWick_indexCast,
    smul_smul]
  simp only [sourceWickMatchingQuantize, hj]

private theorem matching_wick_list_sum (epsilon : ℝ) {p q : ℕ}
    (ts : List (SymmetricSector μ p →L[ℂ] SymmetricSector μ q)) :
    sourceFiniteParticleWick μ epsilon ts.sum =
      (ts.map (sourceFiniteParticleWick μ epsilon)).sum := by
  induction ts with
  | nil => simp only [List.sum_nil, List.map_nil, sourceFiniteParticleWick_zero_kernel]
  | cons T ts ih =>
    simp only [List.sum_cons, List.map_cons, sourceFiniteParticleWick_add_kernel, ih]

private theorem matching_list_smul_sum {A M : Type*} [AddCommMonoid M] [Module ℂ M]
    (c : ℂ) (ts : List A) (f : A → M) :
    (ts.map (fun x => c • f x)).sum = c • (ts.map f).sum := by
  induction ts with
  | nil => simp only [List.map_nil, List.sum_nil, smul_zero]
  | cons x ts ih => simp only [List.map_cons, List.sum_cons, ih, smul_add]

/-- Whole actual count-j operator grouping: the filtered physical matching
operators are epsilon^j times source Wick of the independent actual bounded
matching kernel. No embedding/matching identity or general product premise. -/
theorem sourceWickMatchingKernel_quantize (epsilon : ℝ) (p q j : ℕ)
    (gs : Fin p → Lp ℂ 2 μ) (hs : Fin q → Lp ℂ 2 μ) :
    ((sourceWickMatchingCountTerms μ p q j gs hs).map
      (sourceWickMatchingQuantize μ epsilon)).sum =
      (epsilon : ℂ) ^ j •
        sourceFiniteParticleWick μ epsilon (sourceWickMatchingKernel μ p q j gs hs) := by
  rw [← List.attach_map_val]
  have hm := List.map_congr_left
    (l := (sourceWickMatchingCountTerms μ p q j gs hs).attach)
    (fun t _ => sourceWickMatchingTermKernel_quantize μ epsilon p q j gs hs t)
  rw [hm, matching_list_smul_sum]
  unfold sourceWickMatchingKernel
  rw [matching_wick_list_sum, List.map_map]
  rfl

private theorem matchingSum_eq_map_sum (epsilon : ℝ)
    (ts : List (SourceWickMatchingTerm μ)) :
    sourceWickMatchingSum μ epsilon ts =
      (ts.map (sourceWickMatchingQuantize μ epsilon)).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [sourceWickMatchingSum, List.map_cons, List.sum_cons, ih]

private theorem matching_sum_group_count (epsilon : ℝ) (M : ℕ)
    (ts : List (SourceWickMatchingTerm μ))
    (hbound : ∀ t ∈ ts, t.contractions ≤ M) :
    (ts.map (sourceWickMatchingQuantize μ epsilon)).sum =
      ∑ j ∈ Finset.range (M + 1),
        ((ts.filter (fun t => decide (t.contractions = j))).map
          (sourceWickMatchingQuantize μ epsilon)).sum := by
  classical
  induction ts with
  | nil => simp only [List.map_nil, List.sum_nil, List.filter_nil, Finset.sum_const_zero]
  | cons t ts ih =>
    have ht : t.contractions ∈ Finset.range (M + 1) :=
      Finset.mem_range.mpr (by have hh := hbound t (by simp); omega)
    have htail : ∀ a ∈ ts, a.contractions ≤ M :=
      fun a ha => hbound a (List.mem_cons_of_mem t ha)
    have hsingle : (∑ j ∈ Finset.range (M + 1),
        if t.contractions = j then sourceWickMatchingQuantize μ epsilon t else 0) =
        sourceWickMatchingQuantize μ epsilon t := by
      rw [Finset.sum_eq_single t.contractions]
      · rw [if_pos rfl]
      · intro j hj hne
        exact if_neg (Ne.symm hne)
      · intro hnot
        exact False.elim (hnot ht)
    calc
      _ = sourceWickMatchingQuantize μ epsilon t +
          (ts.map (sourceWickMatchingQuantize μ epsilon)).sum := rfl
      _ = (∑ j ∈ Finset.range (M + 1),
          if t.contractions = j then sourceWickMatchingQuantize μ epsilon t else 0) +
          ∑ j ∈ Finset.range (M + 1),
            ((ts.filter (fun t => decide (t.contractions = j))).map
              (sourceWickMatchingQuantize μ epsilon)).sum := by rw [hsingle, ih htail]
      _ = _ := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases heq : t.contractions = j
        · simp [List.filter_cons, heq]
        · simp [List.filter_cons, heq]

/-- Actual physical annihilation-word/creation-word product grouped into its
independent bounded matching kernels, with the exact source epsilon power and
all count multiplicities. The remaining conversion to the specified derivative
kernels requires the separate weighted embedding/matching bijection. -/
theorem sourceFiniteParticle_mixedWord_matchingKernel_product (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (p q : ℕ) (gs : Fin p → Lp ℂ 2 μ)
    (hs : Fin q → Lp ℂ 2 μ) :
    sourceFiniteParticleAnnihilationWord μ epsilon p gs *
        sourceFiniteParticleCreationWord μ epsilon q hs =
      ∑ j ∈ Finset.range (min p q + 1), (epsilon : ℂ) ^ j •
        sourceFiniteParticleWick μ epsilon (sourceWickMatchingKernel μ p q j gs hs) := by
  rw [sourceFiniteParticle_mixedWord_matching_expansion μ epsilon hepsilon,
    matchingSum_eq_map_sum]
  have hb : ∀ t ∈ sourceWickMatchingTerms μ p gs q hs, t.contractions ≤ min p q := by
    intro t ht
    have hd := sourceWickMatchingTerms_degrees μ p q gs hs t ht
    omega
  rw [matching_sum_group_count μ epsilon (min p q) _ hb]
  apply Finset.sum_congr rfl
  intro j hj
  exact sourceWickMatchingKernel_quantize μ epsilon p q j gs hs
end LiebLiniger.FixedPeriod.Quantum
end
end Q2024Source10





/- Source-frozen leaf LiebLiniger.FixedPeriod.Quantum.WickMatchingDerivativeKernel; 939d74a80db859f667b3e130fb13043b7421650b59c1ed9ba94c3d84a7daa568 -/
section Q2024Source12

/-! Actual source derivative kernel equals j! times the independent matching
kernel. The analytic ordered-embedding producer and the separate weighted
matching bijection are consumed on the SAME arbitrary physical fields. The
final theorem is actual operator composition in the SPECIFIED source derivative
kernels for pure annihilation against pure creation, all original degrees.
The weighted matching module is the separately authored exact7f1139 source
prerequisite; no assumed identity or unregistered placeholder appears.
SOURCE ONLY / UNCOMPILED. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- Genuine physical annihilation-word/creation-word product in the SPECIFIED
source derivative contraction kernels with EXACT epsilon^j/j!. This includes
all independent field slots, repeated fields, unavailable source branches,
empty words and the physical vacuum. It is the direct pure-annihilation /
pure-creation product prerequisite of the general mixed Wick product. -/
theorem sourceFiniteParticle_mixedWord_sourceDerivative_product (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (p q : ℕ) (gs : Fin p → Lp ℂ 2 μ)
    (hs : Fin q → Lp ℂ 2 μ) :
    sourceFiniteParticleAnnihilationWord μ epsilon p gs *
        sourceFiniteParticleCreationWord μ epsilon q hs =
      ∑ j ∈ Finset.range (min p q + 1),
        ((epsilon : ℂ) ^ j / (j.factorial : ℂ)) •
          sourceFiniteParticleWick μ epsilon (sourceDerivativeContractionKernel μ
            (InnerProductSpace.rankOne ℂ (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))
              (symmetricTensorContinuousMultilinear μ p gs))
            (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ q hs)
              (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))) j) := by
  calc
    _ = ∑ j ∈ Finset.range (min p q + 1), (epsilon : ℂ) ^ j •
        sourceFiniteParticleWick μ epsilon (sourceWickMatchingKernel μ p q j gs hs) :=
      sourceFiniteParticle_mixedWord_matchingKernel_product μ epsilon hepsilon p q gs hs
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [sourceDerivativeContractionKernel_mixed_annihilation_creation μ p q j gs hs,
        sourceFiniteParticleWick_smul_kernel, smul_smul]
      have hfac : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
      rw [div_mul_cancel₀ _ hfac]
end LiebLiniger.FixedPeriod.Quantum
end
end Q2024Source12





/- Source-frozen leaf LiebLiniger.FixedPeriod.Quantum.WickMixedRankOneProduct; 80ba841c7bfee4e5c07a8c6096b3351bdbda03cf7247c9917c0c9cdcfced6e59 -/
section Q2024Source14

/-! Actual general mixed rank-one Wick product, using the SAME derivative
kernels. All four source field families are independent. Actual finite-particle
word concatenation is first earned from literal list products; the extended
matching kernel then retains both outer word families in its actual symmetric
tensors. Full derivative-kernel equality is proved by pure matrix elements,
not supplied as an assumption. General finite/compact kernels remain separate.
SOURCE ONLY / UNCOMPILED. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

private theorem creationWord_eq_list_prod (epsilon : ℝ) (p : ℕ)
    (gs : Fin p → Lp ℂ 2 μ) :
    sourceFiniteParticleCreationWord μ epsilon p gs =
      ((List.ofFn gs).map (sourceFiniteParticleCreation μ epsilon)).prod := by
  induction p with
  | zero => simp only [sourceFiniteParticleCreationWord, List.ofFn_zero,
      List.map_nil, List.prod_nil]
  | succ p ih =>
    rw [sourceFiniteParticleCreationWord, List.ofFn_succ, List.map_cons,
      List.prod_cons, ih]

private theorem annihilationWord_eq_reverse_list_prod (epsilon : ℝ) (p : ℕ)
    (gs : Fin p → Lp ℂ 2 μ) :
    sourceFiniteParticleAnnihilationWord μ epsilon p gs =
      ((List.ofFn gs).map (sourceFiniteParticleAnnihilation μ epsilon)).reverse.prod := by
  induction p with
  | zero => simp only [sourceFiniteParticleAnnihilationWord, List.ofFn_zero,
      List.map_nil, List.reverse_nil, List.prod_nil]
  | succ p ih =>
    rw [sourceFiniteParticleAnnihilationWord, List.ofFn_succ, List.map_cons,
      List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil, mul_one, ih]

/-- Literal actual creator words concatenate in their source operator order. -/
theorem sourceFiniteParticleCreationWord_append (epsilon : ℝ) (p q : ℕ)
    (gs : Fin p → Lp ℂ 2 μ) (hs : Fin q → Lp ℂ 2 μ) :
    sourceFiniteParticleCreationWord μ epsilon (p + q) (Fin.append gs hs) =
      sourceFiniteParticleCreationWord μ epsilon p gs *
        sourceFiniteParticleCreationWord μ epsilon q hs := by
  rw [creationWord_eq_list_prod, List.ofFn_fin_append, List.map_append,
    List.prod_append, creationWord_eq_list_prod, creationWord_eq_list_prod]

/-- Literal annihilator words concatenate with the first source family acting
first. This order is earned; no implicit commutation/permutation is needed. -/
theorem sourceFiniteParticleAnnihilationWord_append (epsilon : ℝ) (p q : ℕ)
    (gs : Fin p → Lp ℂ 2 μ) (hs : Fin q → Lp ℂ 2 μ) :
    sourceFiniteParticleAnnihilationWord μ epsilon (p + q) (Fin.append gs hs) =
      sourceFiniteParticleAnnihilationWord μ epsilon q hs *
        sourceFiniteParticleAnnihilationWord μ epsilon p gs := by
  rw [annihilationWord_eq_reverse_list_prod, List.ofFn_fin_append, List.map_append,
    List.reverse_append, List.prod_append, annihilationWord_eq_reverse_list_prod,
    annihilationWord_eq_reverse_list_prod]

/-- Actual bounded kernel of one matching with BOTH outer field families.
Outer annihilators ks act first, so the input word is ks followed by the
remaining gs. The symmetric source kernel equality below earns its equivalence
to the source tensor-contraction ordering by actual pure pairings. -/
def sourceWickMixedMatchingTermKernel (p q r s j : ℕ)
    (gs : Fin p → Lp ℂ 2 μ) (as : Fin q → Lp ℂ 2 μ)
    (hs : Fin s → Lp ℂ 2 μ) (ks : Fin r → Lp ℂ 2 μ)
    (t : {t // t ∈ sourceWickMatchingCountTerms μ p s j gs hs}) :
    SymmetricSector μ (p + r - j) →L[ℂ] SymmetricSector μ (q + s - j) := by
  have hm := (List.mem_filter.mp t.property).1
  have hc : t.val.contractions = j := by
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp t.property).2
  have hd := sourceWickMatchingTerms_degrees μ p s gs hs t.val hm
  have hin : p + r - j = r + t.val.inputDegree := by omega
  have hout : q + t.val.outputDegree = q + s - j := by omega
  exact t.val.coefficient •
    ((symmetricSectorCast μ hout).toLinearIsometry.toContinuousLinearMap ∘L
      InnerProductSpace.rankOne ℂ
        (symmetricTensorContinuousMultilinear μ (q + t.val.outputDegree)
          (Fin.append as t.val.outputFields))
        (symmetricTensorContinuousMultilinear μ (r + t.val.inputDegree)
          (Fin.append ks t.val.inputFields)) ∘L
      (symmetricSectorCast μ hin).toLinearIsometry.toContinuousLinearMap)

/-- Actual mixed matching kernel with all source outer fields and multiplicities. -/
def sourceWickMixedMatchingKernel (p q r s j : ℕ)
    (gs : Fin p → Lp ℂ 2 μ) (as : Fin q → Lp ℂ 2 μ)
    (hs : Fin s → Lp ℂ 2 μ) (ks : Fin r → Lp ℂ 2 μ) :
    SymmetricSector μ (p + r - j) →L[ℂ] SymmetricSector μ (q + s - j) :=
  ((sourceWickMatchingCountTerms μ p s j gs hs).attach.map
    (sourceWickMixedMatchingTermKernel μ p q r s j gs as hs ks)).sum

private theorem outer_cast_polarized {a b c d : ℕ}
    (hin : a = b) (hout : c = d)
    (T : SymmetricSector μ b →L[ℂ] SymmetricSector μ c) (v u : Lp ℂ 2 μ) :
    wickKernelPolarized μ
      ((symmetricSectorCast μ hout).toLinearIsometry.toContinuousLinearMap ∘L T ∘L
        (symmetricSectorCast μ hin).toLinearIsometry.toContinuousLinearMap) v u =
      wickKernelPolarized μ T v u := by
  subst b
  subst d
  rfl

private theorem outer_polarized_smul {p q : ℕ}
    (c : ℂ) (T : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (v u : Lp ℂ 2 μ) :
    wickKernelPolarized μ (c • T) v u = c * wickKernelPolarized μ T v u := by
  simp only [wickKernelPolarized, ContinuousLinearMap.smul_apply,
    q2024_sector_inner_smul_right μ q]

private theorem outer_polarized_list_sum {p q : ℕ}
    (ts : List (SymmetricSector μ p →L[ℂ] SymmetricSector μ q)) (v u : Lp ℂ 2 μ) :
    wickKernelPolarized μ ts.sum v u =
      (ts.map (fun T => wickKernelPolarized μ T v u)).sum := by
  induction ts with
  | nil => simp only [List.sum_nil, List.map_nil, wickKernelPolarized,
      ContinuousLinearMap.zero_apply, inner_zero_right]
  | cons T ts ih =>
    simp only [List.sum_cons, List.map_cons, wickKernelPolarized,
      ContinuousLinearMap.add_apply, inner_add_right] at ih ⊢
    rw [ih]

private theorem mixedMatchingTerm_polarized (p q r s j : ℕ)
    (gs : Fin p → Lp ℂ 2 μ) (as : Fin q → Lp ℂ 2 μ)
    (hs : Fin s → Lp ℂ 2 μ) (ks : Fin r → Lp ℂ 2 μ)
    (t : {t // t ∈ sourceWickMatchingCountTerms μ p s j gs hs}) (v u : Lp ℂ 2 μ) :
    wickKernelPolarized μ (sourceWickMixedMatchingTermKernel μ p q r s j gs as hs ks t) v u =
      ((∏ i : Fin q, inner ℂ v (as i)) * (∏ k : Fin r, inner ℂ (ks k) u)) *
        sourceWickMatchingPureWeight μ t.val v u := by
  unfold sourceWickMixedMatchingTermKernel
  rw [outer_polarized_smul, outer_cast_polarized]
  simp only [wickKernelPolarized, InnerProductSpace.rankOne_apply, inner_smul_right,
    inner_pure_symmetricMixedTensor, inner_symmetricMixedTensor_pure,
    Fin.prod_univ_add, Fin.append_left, Fin.append_right, sourceWickMatchingPureWeight]
  ring

/-- Every outer physical field appears in the actual complete kernel pairing. -/
theorem sourceWickMixedMatchingKernel_polarized (p q r s j : ℕ)
    (gs : Fin p → Lp ℂ 2 μ) (as : Fin q → Lp ℂ 2 μ)
    (hs : Fin s → Lp ℂ 2 μ) (ks : Fin r → Lp ℂ 2 μ) (v u : Lp ℂ 2 μ) :
    wickKernelPolarized μ (sourceWickMixedMatchingKernel μ p q r s j gs as hs ks) v u =
      ((∏ i : Fin q, inner ℂ v (as i)) * (∏ k : Fin r, inner ℂ (ks k) u)) *
        sourceWickMatchingPureSum μ p s j gs hs v u := by
  unfold sourceWickMixedMatchingKernel
  rw [outer_polarized_list_sum, List.map_map]
  simp only [Function.comp_def]
  have hm := List.map_congr_left
    (l := (sourceWickMatchingCountTerms μ p s j gs hs).attach)
    (fun t _ => mixedMatchingTerm_polarized μ p q r s j gs as hs ks t v u)
  rw [hm, List.sum_map_mul_left]
  have hAttach := List.attach_map_val (l := sourceWickMatchingCountTerms μ p s j gs hs)
    (f := fun t => sourceWickMatchingPureWeight μ t v u)
  have hSum := congrArg (fun xs : List ℂ => xs.sum) hAttach
  change ((∏ i : Fin q, inner ℂ v (as i)) * (∏ k : Fin r, inner ℂ (ks k) u)) *
      ((sourceWickMatchingCountTerms μ p s j gs hs).attach.map
        (fun t => sourceWickMatchingPureWeight μ t.val v u)).sum =
    ((∏ i : Fin q, inner ℂ v (as i)) * (∏ k : Fin r, inner ℂ (ks k) u)) *
      ((sourceWickMatchingCountTerms μ p s j gs hs).map
        (fun t => sourceWickMatchingPureWeight μ t v u)).sum
  exact congrArg (fun z : ℂ =>
    ((∏ i : Fin q, inner ℂ v (as i)) * (∏ k : Fin r, inner ℂ (ks k) u)) * z) hSum

/-- General mixed-rank-one source kernel is j! times the SAME actual bounded
mixed matching kernel. The actual all-j outer derivative factorization and the
separate weighted identity are consumed; no kernel equality is assumed. -/
theorem sourceDerivativeContractionKernel_mixed_rankOne (p q r s j : ℕ)
    (gs : Fin p → Lp ℂ 2 μ) (as : Fin q → Lp ℂ 2 μ)
    (hs : Fin s → Lp ℂ 2 μ) (ks : Fin r → Lp ℂ 2 μ) :
    sourceDerivativeContractionKernel μ
        (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ q as)
          (symmetricTensorContinuousMultilinear μ p gs))
        (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ s hs)
          (symmetricTensorContinuousMultilinear μ r ks)) j =
      (j.factorial : ℂ) • sourceWickMixedMatchingKernel μ p q r s j gs as hs ks := by
  apply wickSymmetricSector_operator_eq_of_pure_pairings μ
  intro u v
  change wickKernelPolarized μ (sourceDerivativeContractionKernel μ _ _ j) v u = _
  rw [sourceDerivativeContractionKernel_mixed_outer_pairing,
    sourceDerivativeContractionKernel_mixed_annihilation_creation,
    outer_polarized_smul, sourceWickMatchingKernel_polarized]
  change _ = wickKernelPolarized μ
    ((j.factorial : ℂ) • sourceWickMixedMatchingKernel μ p q r s j gs as hs ks) v u
  rw [outer_polarized_smul, sourceWickMixedMatchingKernel_polarized]
  change _ = (j.factorial : ℂ) *
    (((∏ i : Fin q, inner ℂ v (as i)) * (∏ k : Fin r, inner ℂ (ks k) u)) *
      sourceWickMatchingPureSum μ p s j gs hs v u)
  change ((∏ i : Fin q, inner ℂ v (as i)) * (∏ k : Fin r, inner ℂ (ks k) u)) *
    ((j.factorial : ℂ) * sourceWickMatchingPureSum μ p s j gs hs v u) = _
  ring

private theorem mixedMatchingTerm_quantize (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (p q r s j : ℕ) (gs : Fin p → Lp ℂ 2 μ) (as : Fin q → Lp ℂ 2 μ)
    (hs : Fin s → Lp ℂ 2 μ) (ks : Fin r → Lp ℂ 2 μ)
    (t : {t // t ∈ sourceWickMatchingCountTerms μ p s j gs hs}) :
    sourceFiniteParticleCreationWord μ epsilon q as *
        sourceWickMatchingQuantize μ epsilon t.val *
        sourceFiniteParticleAnnihilationWord μ epsilon r ks =
      (epsilon : ℂ) ^ j • sourceFiniteParticleWick μ epsilon
        (sourceWickMixedMatchingTermKernel μ p q r s j gs as hs ks t) := by
  have hc : t.val.contractions = j := by
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp t.property).2
  unfold sourceWickMixedMatchingTermKernel
  rw [sourceFiniteParticleWick_smul_kernel, sourceFiniteParticleWick_indexCast]
  unfold sourceWickMatchingQuantize
  have hbase := sourceFiniteParticleWick_mixed_rankOne μ epsilon hepsilon
    t.val.inputDegree t.val.outputDegree t.val.outputFields t.val.inputFields
  have houter := sourceFiniteParticleWick_mixed_rankOne μ epsilon hepsilon
    (r + t.val.inputDegree) (q + t.val.outputDegree)
      (Fin.append as t.val.outputFields) (Fin.append ks t.val.inputFields)
  conv_lhs => rw [hbase]
  conv_rhs => rw [houter]
  rw [sourceFiniteParticleCreationWord_append μ epsilon q t.val.outputDegree as t.val.outputFields,
    sourceFiniteParticleAnnihilationWord_append μ epsilon r t.val.inputDegree ks t.val.inputFields]
  simp only [hc, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]

private theorem outer_sum_smul {A M : Type*} [AddCommMonoid M] [Module ℂ M]
    (c : ℂ) (ts : List A) (f : A → M) :
    (ts.map (fun x => c • f x)).sum = c • (ts.map f).sum := by
  induction ts with
  | nil => simp only [List.map_nil, List.sum_nil, smul_zero]
  | cons x ts ih => simp only [List.map_cons, List.sum_cons, ih, smul_add]

/-- Genuine physical outer-word application to the count-j matching kernel.
This binds actual operator multiplication to the independent complete kernel. -/
theorem sourceWickMixedMatchingKernel_quantize (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (p q r s j : ℕ) (gs : Fin p → Lp ℂ 2 μ) (as : Fin q → Lp ℂ 2 μ)
    (hs : Fin s → Lp ℂ 2 μ) (ks : Fin r → Lp ℂ 2 μ) :
    sourceFiniteParticleCreationWord μ epsilon q as *
        ((epsilon : ℂ) ^ j • sourceFiniteParticleWick μ epsilon
          (sourceWickMatchingKernel μ p s j gs hs)) *
        sourceFiniteParticleAnnihilationWord μ epsilon r ks =
      (epsilon : ℂ) ^ j • sourceFiniteParticleWick μ epsilon
        (sourceWickMixedMatchingKernel μ p q r s j gs as hs ks) := by
  rw [← sourceWickMatchingKernel_quantize μ epsilon p s j gs hs]
  rw [← List.attach_map_val]
  rw [← List.sum_map_mul_left, ← List.sum_map_mul_right]
  have hm := List.map_congr_left
    (l := (sourceWickMatchingCountTerms μ p s j gs hs).attach)
    (fun t _ => mixedMatchingTerm_quantize μ epsilon hepsilon p q r s j gs as hs ks t)
  rw [hm, outer_sum_smul]
  unfold sourceWickMixedMatchingKernel
  have hmap := map_list_sum (sourceFiniteParticleWickKernelLinearMap μ epsilon
    (p + r - j) (q + s - j))
    ((sourceWickMatchingCountTerms μ p s j gs hs).attach.map
      (sourceWickMixedMatchingTermKernel μ p q r s j gs as hs ks))
  change _ = (epsilon : ℂ) ^ j •
    (sourceFiniteParticleWickKernelLinearMap μ epsilon (p + r - j) (q + s - j)) _
  rw [hmap, List.map_map]
  rfl

private theorem actual_outer_word_matching_product (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (p q r s : ℕ) (gs : Fin p → Lp ℂ 2 μ) (as : Fin q → Lp ℂ 2 μ)
    (hs : Fin s → Lp ℂ 2 μ) (ks : Fin r → Lp ℂ 2 μ) :
    (sourceFiniteParticleCreationWord μ epsilon q as *
      sourceFiniteParticleAnnihilationWord μ epsilon p gs) *
      (sourceFiniteParticleCreationWord μ epsilon s hs *
        sourceFiniteParticleAnnihilationWord μ epsilon r ks) =
      ∑ j ∈ Finset.range (min p s + 1),
        (sourceFiniteParticleCreationWord μ epsilon q as *
          ((epsilon : ℂ) ^ j • sourceFiniteParticleWick μ epsilon
            (sourceWickMatchingKernel μ p s j gs hs))) *
          sourceFiniteParticleAnnihilationWord μ epsilon r ks := by
  let C : Module.End ℂ (SourceFiniteParticleSpace μ) :=
    sourceFiniteParticleCreationWord μ epsilon q as
  let A : Module.End ℂ (SourceFiniteParticleSpace μ) :=
    sourceFiniteParticleAnnihilationWord μ epsilon p gs
  let D : Module.End ℂ (SourceFiniteParticleSpace μ) :=
    sourceFiniteParticleCreationWord μ epsilon s hs
  let B : Module.End ℂ (SourceFiniteParticleSpace μ) :=
    sourceFiniteParticleAnnihilationWord μ epsilon r ks
  have hassoc (x y z w : Module.End ℂ (SourceFiniteParticleSpace μ)) :
      (x*y)*(z*w) = (x*(y*z))*w := by
    simp only [mul_assoc]
  have hdist {R : Type} [Semiring R] (S : Finset ℕ) (f : ℕ → R) (x y : R) :
      (x * ∑ j ∈ S, f j) * y = ∑ j ∈ S, (x * f j) * y := by
    rw [Finset.mul_sum, Finset.sum_mul]
  change (C*A)*(D*B) = _
  calc
    _ = (C*(A*D))*B := hassoc C A D B
    _ = (C * (∑ j ∈ Finset.range (min p s + 1), (epsilon : ℂ) ^ j •
        sourceFiniteParticleWick μ epsilon (sourceWickMatchingKernel μ p s j gs hs))) * B :=
      congrArg (fun T : Module.End ℂ (SourceFiniteParticleSpace μ) => C*T*B)
        (sourceFiniteParticle_mixedWord_matchingKernel_product μ epsilon hepsilon p s gs hs)
    _ = ∑ j ∈ Finset.range (min p s + 1),
        (C * ((epsilon : ℂ) ^ j •
          sourceFiniteParticleWick μ epsilon (sourceWickMatchingKernel μ p s j gs hs))) * B :=
      hdist (R := Module.End ℂ (SourceFiniteParticleSpace μ))
        (Finset.range (min p s + 1))
        (fun j => (epsilon : ℂ) ^ j •
          sourceFiniteParticleWick μ epsilon (sourceWickMatchingKernel μ p s j gs hs)) C B

private theorem actual_outer_matching_summand (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (p q r s j : ℕ) (gs : Fin p → Lp ℂ 2 μ) (as : Fin q → Lp ℂ 2 μ)
    (hs : Fin s → Lp ℂ 2 μ) (ks : Fin r → Lp ℂ 2 μ) :
    (sourceFiniteParticleCreationWord μ epsilon q as *
      ((epsilon : ℂ) ^ j • sourceFiniteParticleWick μ epsilon
        (sourceWickMatchingKernel μ p s j gs hs))) *
        sourceFiniteParticleAnnihilationWord μ epsilon r ks =
      ((epsilon : ℂ) ^ j / (j.factorial : ℂ)) •
        sourceFiniteParticleWick μ epsilon (sourceDerivativeContractionKernel μ
          (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ q as)
            (symmetricTensorContinuousMultilinear μ p gs))
          (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ s hs)
            (symmetricTensorContinuousMultilinear μ r ks)) j) := by
  rw [sourceWickMixedMatchingKernel_quantize μ epsilon hepsilon,
    sourceDerivativeContractionKernel_mixed_rankOne,
    sourceFiniteParticleWick_smul_kernel, smul_smul]
  have hfac : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  rw [div_mul_cancel₀ _ hfac]

/-- WHOLE actual physical product for arbitrary independent mixed rank-one
source kernels in the SPECIFIED all-order derivative kernels. All four degree
families, arbitrary fields/repetitions, epsilon>0, empty words and vacuum are
retained. General finite-mode/compact kernels still require their own passage. -/
theorem sourceFiniteParticleWick_mixed_rankOne_source_product (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (p q r s : ℕ)
    (gs : Fin p → Lp ℂ 2 μ) (as : Fin q → Lp ℂ 2 μ)
    (hs : Fin s → Lp ℂ 2 μ) (ks : Fin r → Lp ℂ 2 μ) :
    sourceFiniteParticleWick μ epsilon
        (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ q as)
          (symmetricTensorContinuousMultilinear μ p gs)) *
        sourceFiniteParticleWick μ epsilon
          (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ s hs)
            (symmetricTensorContinuousMultilinear μ r ks)) =
      ∑ j ∈ Finset.range (min p s + 1),
        ((epsilon : ℂ) ^ j / (j.factorial : ℂ)) •
          sourceFiniteParticleWick μ epsilon (sourceDerivativeContractionKernel μ
            (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ q as)
              (symmetricTensorContinuousMultilinear μ p gs))
            (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ s hs)
              (symmetricTensorContinuousMultilinear μ r ks)) j) := by
  conv_lhs =>
    rw [sourceFiniteParticleWick_mixed_rankOne μ epsilon hepsilon p q as gs,
      sourceFiniteParticleWick_mixed_rankOne μ epsilon hepsilon r s hs ks]
  calc
    _ = ∑ j ∈ Finset.range (min p s + 1),
        (sourceFiniteParticleCreationWord μ epsilon q as *
          ((epsilon : ℂ) ^ j • sourceFiniteParticleWick μ epsilon
            (sourceWickMatchingKernel μ p s j gs hs))) *
          sourceFiniteParticleAnnihilationWord μ epsilon r ks :=
      actual_outer_word_matching_product μ epsilon hepsilon p q r s gs as hs ks
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact actual_outer_matching_summand μ epsilon hepsilon p q r s j gs as hs ks

end LiebLiniger.FixedPeriod.Quantum
end
end Q2024Source14


/- Source-frozen leaf LiebLiniger.FixedPeriod.Quantum.WickSourceContractionLinearity; 60587f47a7531526db1f5844687d17b7b9db50e84db7f0de4ee020039b2054e5 -/
section Q2024Source15

/-! Bilinearity of the ACTUAL source derivative contraction. It is earned from
the independently defined full free functional/Riesz vector and pure totality,
then transported through the literal source guard/casts. No product theorem or
kernel-linearity premise. Needed to expand the finite-mode source polynomial
in its actual mixed rank-one kernel span. SOURCE ONLY / UNCOMPILED. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

private theorem inputDerivative_add {r j q : ℕ}
    (A B : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ q) (v u : Lp ℂ 2 μ) :
    wickInputDerivativeFunctional (j := j) μ (A + B) v u =
      wickInputDerivativeFunctional (j := j) μ A v u +
        wickInputDerivativeFunctional (j := j) μ B v u := by
  ext w
  simp only [wickInputDerivativeFunctional, wickInputSlotFunctional,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, inner_add_right,
    smul_eq_mul, mul_add]

private theorem inputDerivative_smul {r j q : ℕ} (c : ℂ)
    (A : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ q) (v u : Lp ℂ 2 μ) :
    wickInputDerivativeFunctional (j := j) μ (c • A) v u =
      c • wickInputDerivativeFunctional (j := j) μ A v u := by
  ext w
  simp only [wickInputDerivativeFunctional, wickInputSlotFunctional,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul]
  rw [map_smul]
  ring

private theorem outputDerivative_add {p j s : ℕ}
    (A B : SymmetricSector μ p →L[ℂ] SymmetricSector μ (j + s)) (v u : Lp ℂ 2 μ) :
    wickOutputDerivativeVector (j := j) μ (A + B) v u =
      wickOutputDerivativeVector (j := j) μ A v u +
        wickOutputDerivativeVector (j := j) μ B v u := by
  simp only [wickOutputDerivativeVector, wickOutputSlotVector,
    ContinuousLinearMap.add_apply, map_add, smul_add]

private theorem outputDerivative_smul {p j s : ℕ} (c : ℂ)
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ (j + s)) (v u : Lp ℂ 2 μ) :
    wickOutputDerivativeVector (j := j) μ (c • A) v u =
      c • wickOutputDerivativeVector (j := j) μ A v u := by
  simp only [wickOutputDerivativeVector, wickOutputSlotVector,
    ContinuousLinearMap.smul_apply, map_smul]
  exact smul_comm _ _ _

/-- Actual source tensor contraction is additive in its first bounded kernel. -/
theorem tensorDerivativeContraction_add_left {r j s q p : ℕ}
    (A B : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ q)
    (C : SymmetricSector μ p →L[ℂ] SymmetricSector μ (j + s)) :
    tensorDerivativeContraction (j := j) μ (A + B) C =
      tensorDerivativeContraction (j := j) μ A C +
        tensorDerivativeContraction (j := j) μ B C := by
  apply wickSymmetricSector_operator_eq_of_pure_pairings μ
  intro u v
  rw [ContinuousLinearMap.add_apply, inner_add_right]
  change wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ (A + B) C) v u =
    wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ A C) v u +
      wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ B C) v u
  simp only [← wickDerivativeDot_eq_tensorKernel, wickDerivativeDot,
    inputDerivative_add, ContinuousLinearMap.add_apply]

/-- Actual source tensor contraction is complex-linear in its first kernel. -/
theorem tensorDerivativeContraction_smul_left {r j s q p : ℕ} (c : ℂ)
    (A : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ q)
    (B : SymmetricSector μ p →L[ℂ] SymmetricSector μ (j + s)) :
    tensorDerivativeContraction (j := j) μ (c • A) B =
      c • tensorDerivativeContraction (j := j) μ A B := by
  apply wickSymmetricSector_operator_eq_of_pure_pairings μ
  intro u v
  rw [ContinuousLinearMap.smul_apply, inner_smul_right]
  change wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ (c • A) B) v u =
    c * wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ A B) v u
  simp only [← wickDerivativeDot_eq_tensorKernel, wickDerivativeDot,
    inputDerivative_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- Actual source tensor contraction is additive in its second bounded kernel. -/
theorem tensorDerivativeContraction_add_right {r j s q p : ℕ}
    (A : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ q)
    (B C : SymmetricSector μ p →L[ℂ] SymmetricSector μ (j + s)) :
    tensorDerivativeContraction (j := j) μ A (B + C) =
      tensorDerivativeContraction (j := j) μ A B +
        tensorDerivativeContraction (j := j) μ A C := by
  apply wickSymmetricSector_operator_eq_of_pure_pairings μ
  intro u v
  rw [ContinuousLinearMap.add_apply, inner_add_right]
  change wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ A (B + C)) v u =
    wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ A B) v u +
      wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ A C) v u
  simp only [← wickDerivativeDot_eq_tensorKernel, wickDerivativeDot,
    outputDerivative_add, map_add]

/-- Actual source tensor contraction is complex-linear in its second kernel;
the conjugate-first Riesz representation does not make this kernel antilinear. -/
theorem tensorDerivativeContraction_smul_right {r j s q p : ℕ} (c : ℂ)
    (A : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ q)
    (B : SymmetricSector μ p →L[ℂ] SymmetricSector μ (j + s)) :
    tensorDerivativeContraction (j := j) μ A (c • B) =
      c • tensorDerivativeContraction (j := j) μ A B := by
  apply wickSymmetricSector_operator_eq_of_pure_pairings μ
  intro u v
  rw [ContinuousLinearMap.smul_apply, inner_smul_right]
  change wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ A (c • B)) v u =
    c * wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ A B) v u
  simp only [← wickDerivativeDot_eq_tensorKernel, wickDerivativeDot,
    outputDerivative_smul, map_smul, smul_eq_mul]

/-- Original-degree guarded source contraction is additive in its first kernel. -/
theorem sourceDerivativeContractionKernel_add_left {p q r s : ℕ}
    (A B : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (C : SymmetricSector μ r →L[ℂ] SymmetricSector μ s) (j : ℕ) :
    sourceDerivativeContractionKernel μ (A + B) C j =
      sourceDerivativeContractionKernel μ A C j + sourceDerivativeContractionKernel μ B C j := by
  by_cases hj : j ≤ min p s
  · simp only [sourceDerivativeContractionKernel, dif_pos hj]
    simp only [ContinuousLinearMap.add_comp, tensorDerivativeContraction_add_left,
      ContinuousLinearMap.comp_add]
  · simp only [sourceDerivativeContractionKernel, dif_neg hj]
    apply ContinuousLinearMap.ext
    intro x
    simp

/-- Original-degree guarded source contraction is scalar-linear in its first kernel. -/
theorem sourceDerivativeContractionKernel_smul_left {p q r s : ℕ} (c : ℂ)
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (B : SymmetricSector μ r →L[ℂ] SymmetricSector μ s) (j : ℕ) :
    sourceDerivativeContractionKernel μ (c • A) B j =
      c • sourceDerivativeContractionKernel μ A B j := by
  by_cases hj : j ≤ min p s
  · simp only [sourceDerivativeContractionKernel, dif_pos hj]
    simp only [ContinuousLinearMap.smul_comp, tensorDerivativeContraction_smul_left,
      ContinuousLinearMap.comp_smul]
  · simp only [sourceDerivativeContractionKernel, dif_neg hj]
    apply ContinuousLinearMap.ext
    intro x
    simp

/-- Original-degree guarded source contraction is additive in its second kernel. -/
theorem sourceDerivativeContractionKernel_add_right {p q r s : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (B C : SymmetricSector μ r →L[ℂ] SymmetricSector μ s) (j : ℕ) :
    sourceDerivativeContractionKernel μ A (B + C) j =
      sourceDerivativeContractionKernel μ A B j + sourceDerivativeContractionKernel μ A C j := by
  by_cases hj : j ≤ min p s
  · simp only [sourceDerivativeContractionKernel, dif_pos hj]
    simp only [ContinuousLinearMap.comp_add, tensorDerivativeContraction_add_right,
      ContinuousLinearMap.add_comp]
  · simp only [sourceDerivativeContractionKernel, dif_neg hj]
    apply ContinuousLinearMap.ext
    intro x
    simp

/-- Original-degree guarded source contraction is scalar-linear in its second kernel. -/
theorem sourceDerivativeContractionKernel_smul_right {p q r s : ℕ} (c : ℂ)
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (B : SymmetricSector μ r →L[ℂ] SymmetricSector μ s) (j : ℕ) :
    sourceDerivativeContractionKernel μ A (c • B) j =
      c • sourceDerivativeContractionKernel μ A B j := by
  by_cases hj : j ≤ min p s
  · simp only [sourceDerivativeContractionKernel, dif_pos hj]
    simp only [ContinuousLinearMap.comp_smul, tensorDerivativeContraction_smul_right,
      ContinuousLinearMap.smul_comp]
  · simp only [sourceDerivativeContractionKernel, dif_neg hj]
    apply ContinuousLinearMap.ext
    intro x
    simp

/-- Genuine zero-kernel branches, proved by complex linearity at scalar zero. -/
@[simp] theorem sourceDerivativeContractionKernel_zero_left {p q r s : ℕ}
    (B : SymmetricSector μ r →L[ℂ] SymmetricSector μ s) (j : ℕ) :
    sourceDerivativeContractionKernel μ (0 : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) B j = 0 := by
  have hzero : (0 : ℂ) • (0 : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) = 0 := by
    ext x
    simp
  calc
    sourceDerivativeContractionKernel μ (0 : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) B j =
        sourceDerivativeContractionKernel μ ((0 : ℂ) • (0 : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)) B j := by
      rw [hzero]
    _ = (0 : ℂ) • sourceDerivativeContractionKernel μ (0 : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) B j :=
      sourceDerivativeContractionKernel_smul_left μ 0 0 B j
    _ = 0 := by
      ext x
      simp

@[simp] theorem sourceDerivativeContractionKernel_zero_right {p q r s : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (j : ℕ) :
    sourceDerivativeContractionKernel μ A (0 : SymmetricSector μ r →L[ℂ] SymmetricSector μ s) j = 0 := by
  have hzero : (0 : ℂ) • (0 : SymmetricSector μ r →L[ℂ] SymmetricSector μ s) = 0 := by
    ext x
    simp
  calc
    sourceDerivativeContractionKernel μ A (0 : SymmetricSector μ r →L[ℂ] SymmetricSector μ s) j =
        sourceDerivativeContractionKernel μ A ((0 : ℂ) • (0 : SymmetricSector μ r →L[ℂ] SymmetricSector μ s)) j := by
      rw [hzero]
    _ = (0 : ℂ) • sourceDerivativeContractionKernel μ A (0 : SymmetricSector μ r →L[ℂ] SymmetricSector μ s) j :=
      sourceDerivativeContractionKernel_smul_right μ 0 A 0 j
    _ = 0 := by
      ext x
      simp
end LiebLiniger.FixedPeriod.Quantum
end
end Q2024Source15





/- Source-frozen leaf LiebLiniger.FixedPeriod.Quantum.WickFiniteModeProduct; b5e9b1a1c7ecb6df248013e11844d5f0187e5e6f45ab428269874582081bdecb -/
section Q2024Source17

/-! Source finite-mode Wick product with its actual derivative kernels. Expand
both independent actual compressed kernels in the earned mixed rank-one span,
then consume actual product/derivative bilinearity. No finite polynomial model,
transport identity, product/CCR premise or compact-limit assumption is used.
SOURCE ONLY / UNCOMPILED. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- Literal finite source derivative-product sum in the ACTUAL kernel maps,
including their original-degree guards and equality-only sector transports. -/
def sourceWickDerivativeProduct (epsilon : ℝ) {p q r s : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (B : SymmetricSector μ r →L[ℂ] SymmetricSector μ s) :
    Module.End ℂ (SourceFiniteParticleSpace μ) :=
  ∑ j ∈ Finset.range (min p s + 1), ((epsilon : ℂ) ^ j / (j.factorial : ℂ)) •
    sourceFiniteParticleWick μ epsilon (sourceDerivativeContractionKernel μ A B j)

private theorem derivativeProduct_add_left (epsilon : ℝ) {p q r s : ℕ}
    (A B : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (C : SymmetricSector μ r →L[ℂ] SymmetricSector μ s) :
    sourceWickDerivativeProduct μ epsilon (A + B) C =
      sourceWickDerivativeProduct μ epsilon A C + sourceWickDerivativeProduct μ epsilon B C := by
  simp only [sourceWickDerivativeProduct, sourceDerivativeContractionKernel_add_left,
    sourceFiniteParticleWick_add_kernel, smul_add, Finset.sum_add_distrib]

private theorem derivativeProduct_add_right (epsilon : ℝ) {p q r s : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (B C : SymmetricSector μ r →L[ℂ] SymmetricSector μ s) :
    sourceWickDerivativeProduct μ epsilon A (B + C) =
      sourceWickDerivativeProduct μ epsilon A B + sourceWickDerivativeProduct μ epsilon A C := by
  simp only [sourceWickDerivativeProduct, sourceDerivativeContractionKernel_add_right,
    sourceFiniteParticleWick_add_kernel, smul_add, Finset.sum_add_distrib]

private theorem derivativeProduct_smul_left (epsilon : ℝ) {p q r s : ℕ} (c : ℂ)
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (B : SymmetricSector μ r →L[ℂ] SymmetricSector μ s) :
    sourceWickDerivativeProduct μ epsilon (c • A) B =
      c • sourceWickDerivativeProduct μ epsilon A B := by
  unfold sourceWickDerivativeProduct
  simp only [sourceDerivativeContractionKernel_smul_left,
    sourceFiniteParticleWick_smul_kernel, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact smul_comm _ _ _

private theorem derivativeProduct_smul_right (epsilon : ℝ) {p q r s : ℕ} (c : ℂ)
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (B : SymmetricSector μ r →L[ℂ] SymmetricSector μ s) :
    sourceWickDerivativeProduct μ epsilon A (c • B) =
      c • sourceWickDerivativeProduct μ epsilon A B := by
  unfold sourceWickDerivativeProduct
  simp only [sourceDerivativeContractionKernel_smul_right,
    sourceFiniteParticleWick_smul_kernel, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact smul_comm _ _ _

private theorem derivativeProduct_zero_left (epsilon : ℝ) {p q r s : ℕ}
    (B : SymmetricSector μ r →L[ℂ] SymmetricSector μ s) :
    sourceWickDerivativeProduct μ epsilon (0 : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) B = 0 := by
  simp only [sourceWickDerivativeProduct, sourceDerivativeContractionKernel_zero_left,
    sourceFiniteParticleWick_zero_kernel, smul_zero, Finset.sum_const_zero]

private theorem derivativeProduct_zero_right (epsilon : ℝ) {p q r s : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) :
    sourceWickDerivativeProduct μ epsilon A (0 : SymmetricSector μ r →L[ℂ] SymmetricSector μ s) = 0 := by
  simp only [sourceWickDerivativeProduct, sourceDerivativeContractionKernel_zero_right,
    sourceFiniteParticleWick_zero_kernel, smul_zero, Finset.sum_const_zero]

/-- Actual finite-mode polynomial expansion step. Both kernel memberships are
ordinary finite linear span facts of genuine spatial symmetric-tensor rank-one
maps; the theorem proves their product identity, rather than assuming it. -/
theorem sourceFiniteParticleWick_product_of_finite_mixed_spans (epsilon : ℝ)
    (hepsilon : 0 < epsilon) {d : ℕ} (e : Fin d → Lp ℂ 2 μ) (p q r s : ℕ)
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (B : SymmetricSector μ r →L[ℂ] SymmetricSector μ s)
    (hA : A ∈ Submodule.span ℂ (Set.range (fun fg : (Fin q → Fin d) × (Fin p → Fin d) =>
      InnerProductSpace.rankOne ℂ
        (symmetricTensorContinuousMultilinear μ q (fun i => e (fg.1 i)))
        (symmetricTensorContinuousMultilinear μ p (fun i => e (fg.2 i))))))
    (hB : B ∈ Submodule.span ℂ (Set.range (fun fg : (Fin s → Fin d) × (Fin r → Fin d) =>
      InnerProductSpace.rankOne ℂ
        (symmetricTensorContinuousMultilinear μ s (fun i => e (fg.1 i)))
        (symmetricTensorContinuousMultilinear μ r (fun i => e (fg.2 i)))))) :
    sourceFiniteParticleWick μ epsilon A * sourceFiniteParticleWick μ epsilon B =
      sourceWickDerivativeProduct μ epsilon A B := by
  classical
  refine Submodule.span_induction₂
    (p := fun A B _hA _hB =>
      sourceFiniteParticleWick μ epsilon A * sourceFiniteParticleWick μ epsilon B =
        sourceWickDerivativeProduct μ epsilon A B)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hA hB
  · intro A B hA hB
    obtain ⟨fg, rfl⟩ := hA
    obtain ⟨hk, rfl⟩ := hB
    exact sourceFiniteParticleWick_mixed_rankOne_source_product μ epsilon hepsilon p q r s
      (fun i => e (fg.2 i)) (fun i => e (fg.1 i))
      (fun i => e (hk.1 i)) (fun i => e (hk.2 i))
  · intro B hB
    rw [sourceFiniteParticleWick_zero_kernel, zero_mul, derivativeProduct_zero_left]
  · intro A hA
    rw [sourceFiniteParticleWick_zero_kernel, mul_zero, derivativeProduct_zero_right]
  · intro A B C hA hB hC hAC hBC
    rw [sourceFiniteParticleWick_add_kernel, add_mul, hAC, hBC, derivativeProduct_add_left]
  · intro A B C hA hB hC hAB hAC
    rw [sourceFiniteParticleWick_add_kernel, mul_add, hAB, hAC, derivativeProduct_add_right]
  · intro c A B hA hB hAB
    rw [sourceFiniteParticleWick_smul_kernel, smul_mul_assoc, hAB,
      derivativeProduct_smul_left]
  · intro c A B hA hB hAB
    rw [sourceFiniteParticleWick_smul_kernel, mul_smul_comm, hAB,
      derivativeProduct_smul_right]

/-- WHOLE finite-mode Wick product for the actual source kernels compressed to
an arbitrary finite physical orthonormal coordinate family. Their finite mixed
spans are earned by the independent actual occupation-basis provider; no support
or product property is assumed. All d/p/q/r/s zero cases and the vacuum remain.
This equality on the full physical finite-particle core implies each actual
available-sector equality by evaluation on its literal direct-sum inclusion. -/
theorem sourceFiniteParticleWick_finiteMode_product (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {d : ℕ} (e : Fin d → Lp ℂ 2 μ) (he : Orthonormal ℂ e) (p q r s : ℕ)
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (B : SymmetricSector μ r →L[ℂ] SymmetricSector μ s) :
    let Ad := ((finiteModeSymmetricSpace μ e q).starProjection.comp A).comp
      (finiteModeSymmetricSpace μ e p).starProjection
    let Bd := ((finiteModeSymmetricSpace μ e s).starProjection.comp B).comp
      (finiteModeSymmetricSpace μ e r).starProjection
    sourceFiniteParticleWick μ epsilon Ad * sourceFiniteParticleWick μ epsilon Bd =
      ∑ j ∈ Finset.range (min p s + 1), ((epsilon : ℂ) ^ j / (j.factorial : ℂ)) •
        sourceFiniteParticleWick μ epsilon (sourceDerivativeContractionKernel μ Ad Bd j) := by
  dsimp only
  exact sourceFiniteParticleWick_product_of_finite_mixed_spans μ epsilon hepsilon e p q r s _ _
    (finiteModeKernelCompression_mem_mixedRankOne_span μ e he p q A)
    (finiteModeKernelCompression_mem_mixedRankOne_span μ e he r s B)

/-- Literal available-sector consumer of the whole actual finite-mode formula.
It is evaluated on the ACTUAL complete sector inclusion, not a finite-mode
vector model, and retains all source zero/guard conventions. -/
theorem sourceFiniteParticleWick_finiteMode_product_lof (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {d : ℕ} (e : Fin d → Lp ℂ 2 μ) (he : Orthonormal ℂ e) (p q r s n : ℕ)
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (B : SymmetricSector μ r →L[ℂ] SymmetricSector μ s) (v : SymmetricSector μ n) :
    let Ad := ((finiteModeSymmetricSpace μ e q).starProjection.comp A).comp
      (finiteModeSymmetricSpace μ e p).starProjection
    let Bd := ((finiteModeSymmetricSpace μ e s).starProjection.comp B).comp
      (finiteModeSymmetricSpace μ e r).starProjection
    sourceFiniteParticleWick μ epsilon Ad
        (sourceFiniteParticleWick μ epsilon Bd (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n v)) =
      (∑ j ∈ Finset.range (min p s + 1), ((epsilon : ℂ) ^ j / (j.factorial : ℂ)) •
        sourceFiniteParticleWick μ epsilon (sourceDerivativeContractionKernel μ Ad Bd j))
          (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n v) := by
  have h := sourceFiniteParticleWick_finiteMode_product μ epsilon hepsilon e he p q r s A B
  exact congrArg (fun T : Module.End ℂ (SourceFiniteParticleSpace μ) =>
    T (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n v)) h
end LiebLiniger.FixedPeriod.Quantum
end
end Q2024Source17
