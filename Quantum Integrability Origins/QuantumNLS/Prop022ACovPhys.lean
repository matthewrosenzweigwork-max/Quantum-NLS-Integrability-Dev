import Mathlib
import QuantumNLS.Prop022ACovTensor
import QuantumNLS.Prop022GClassical
import QuantumNLS.Prop022StrongOperatorR125
import QuantumNLS.Prop022FactorialCoefficientsR115
import QuantumNLS.PhysicalPlacements

/-! PROP-022 route A, stage A5b: covariance of the physical objects under `Γ(R)`, `R` any unitary of
`L²(𝕋_L)`.

* `symMap_contraction`, `symMap_annihilation`: the two-particle annihilation block;
* `physicalQ_cov`, `numberBlock_cov`: the number block (placement average);
* `symMap_insertion`, `symMap_insertion_adjoint`, `mixedTerm_cov`, `pairTerm_cov`,
  `numberCoefficient_cov`, `pairCoefficient_cov`: the factorial coefficient data;
* `numberCoordinates_cov`, `lower_cov`, `strongCoordinates_cov`, `rootLift_cov`: the strong
  quadratic generator `dΓ(a) + ½(a*(b) + a(b))` on second-moment coordinates. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace
open ContinuousLinearMap

namespace QuantumNLS.Prop022ACovPhys
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022GTensor Prop022GClassical Prop022ACovTensor Ext005PairSector IntrinsicContact
open Prop022TensorCompressionR115 Prop022FactorialCoefficientsR115 Prop022StrongOperatorR125
open Ext005QuadraticEnergyR108 Ext005PhysicalNumberFormR114

variable {L : ℝ} [Fact (0 < L)] (R : L2T L ≃ₗᵢ[ℂ] L2T L)

/-- `Γ(R)` on the physical Fock space. -/
abbrev GR : Fock L ≃ₗᵢ[ℂ] Fock L := fockMap R

lemma GR_apply (z : Fock L) (n : ℕ) : GR R z n = symMap R n (z n) := rfl

lemma conjSym_rel (p : ℕ) (A : HN L p →L[ℂ] HN L p) (y : HN L p) :
    symMap R p (A y) = conjSym R p A (symMap R p y) := by
  rw [conjSym_apply, LinearIsometryEquiv.symm_apply_apply]

/-! ### Annihilation -/

lemma symMap_contraction (b : HN L 2) (n : ℕ) (x : HN L (2 + n)) :
    symMap R n (contraction b n x) = contraction (symMap R 2 b) n (symMap R (2 + n) x) := by
  have h := tensorMap_contractL R 2 n (b : HilbertTensorPower ℂ (L2T L) 2)
    (x : HilbertTensorPower ℂ (L2T L) (2 + n))
  change symMap R n ((physSector L n).orthogonalProjectionOnto
      (contractL (F := HilbertTensorPower ℂ (L2T L) n) (b : HilbertTensorPower ℂ (L2T L) 2)
        (splitIsometry (𝕜 := ℂ) (E := L2T L) 2 n (x : HilbertTensorPower ℂ (L2T L) (2 + n))))) =
    (physSector L n).orthogonalProjectionOnto
      (contractL (F := HilbertTensorPower ℂ (L2T L) n)
        ((symMap R 2 b : HN L 2) : HilbertTensorPower ℂ (L2T L) 2)
        (splitIsometry (𝕜 := ℂ) (E := L2T L) 2 n
          ((symMap R (2 + n) x : HN L (2 + n)) : HilbertTensorPower ℂ (L2T L) (2 + n))))
  rw [symMap_orthProj, h]
  rfl

lemma symMap_annihilation (b : HN L 2) (n : ℕ) (x : HN L (2 + n)) :
    symMap R n (annihilation b n x) = annihilation (symMap R 2 b) n (symMap R (2 + n) x) := by
  simp only [annihilation, smul_apply, map_smul, symMap_contraction]

/-! ### The number block -/

lemma cast_cov {m n : ℕ} (h : m = n) (X X' : HN L m →L[ℂ] HN L m)
    (hX : ∀ y, symMap R m (X y) = X' (symMap R m y)) (y : HN L n) :
    symMap R n (PhysicalPlacements.castSymSectorOperator L h X y) =
      PhysicalPlacements.castSymSectorOperator L h X' (symMap R n y) := by
  subst h
  exact hX y

lemma physicalQ_cov (N p : ℕ) (hp : p ≤ N) (A : HN L p →L[ℂ] HN L p) (y : HN L N) :
    symMap R N (PhysicalPlacements.physicalQ_N_p L N p hp A y) =
      PhysicalPlacements.physicalQ_N_p L N p hp (conjSym R p A) (symMap R N y) := by
  unfold PhysicalPlacements.physicalQ_N_p
  exact cast_cov R _ _ _ (fun y' => symMap_Q_N_p R A (conjSym R p A) (conjSym_rel R p A) y') y

lemma numberBlock_cov (a : HN L 1 →L[ℂ] HN L 1) (n : ℕ) (y : HN L n) :
    symMap R n (numberBlock a n y) = numberBlock (conjSym R 1 a) n (symMap R n y) := by
  unfold numberBlock
  split_ifs with hn
  · simp only [smul_apply, map_smul, physicalQ_cov]
  · simp

lemma normalizedBlock_cov (a : HN L 1 →L[ℂ] HN L 1) (n : ℕ) (y : HN L n) :
    symMap R n (normalizedBlock a n y) = normalizedBlock (conjSym R 1 a) n (symMap R n y) := by
  simp only [normalizedBlock, smul_apply, map_smul, numberBlock_cov]

lemma numberCoordinates_cov (a : HN L 1 →L[ℂ] HN L 1) (z : Fock L) :
    GR R (numberCoordinates a z) = numberCoordinates (conjSym R 1 a) (GR R z) := by
  apply lp.ext
  funext n
  exact normalizedBlock_cov R a n (z n)

/-! ### Lowering blocks and their adjoints -/

lemma lower_cov (j : ℕ) (hj : 1 ≤ j) (b : HN L 2) (z : Fock L) :
    GR R (lower j hj b z) = lower j hj (symMap R 2 b) (GR R z) := by
  apply lp.ext
  funext n
  change symMap R n (lowerBlock j b n (z (2 + n))) =
    lowerBlock j (symMap R 2 b) n (symMap R (2 + n) (z (2 + n)))
  simp only [lowerBlock, smul_apply, map_smul, symMap_annihilation]

lemma adjoint_cov (T T' : Fock L →L[ℂ] Fock L) (h : ∀ z, GR R (T z) = T' (GR R z)) (z : Fock L) :
    GR R (T.adjoint z) = T'.adjoint (GR R z) := by
  apply ext_inner_left ℂ
  intro w
  obtain ⟨w₀, rfl⟩ := (GR R).surjective w
  rw [adjoint_inner_right, ← h, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map,
    adjoint_inner_right]

lemma rootLift_cov (j : ℕ) (z : Fock L) :
    Ext005FormCutoffR109.rootLift j (GR R z) = GR R (Ext005FormCutoffR109.rootLift j z) := by
  by_cases hz : z ∈ Ext005Moments.momentDomain (L := L) j
  · have hz' : GR R z ∈ Ext005Moments.momentDomain (L := L) j := by
      rw [Ext005Moments.momentDomain_iff] at hz ⊢
      simpa only [GR_apply, LinearIsometryEquiv.norm_map] using hz
    rw [Ext005FormCutoffR109.rootLift_eq j _ hz', Ext005FormCutoffR109.rootLift_eq j _ hz]
    apply lp.ext
    funext n
    have h1 : (Ext005Moments.momentRoot (L := L) j ⟨GR R z, hz'⟩ : Fock L) n =
        ((Real.sqrt (Ext005Moments.momentWeight j n) : ℝ) : ℂ) • symMap R n (z n) := rfl
    have h2 : (Ext005Moments.momentRoot (L := L) j ⟨z, hz⟩ : Fock L) n =
        ((Real.sqrt (Ext005Moments.momentWeight j n) : ℝ) : ℂ) • z n := rfl
    refine h1.trans ?_
    change _ = symMap R n ((Ext005Moments.momentRoot (L := L) j ⟨z, hz⟩ : Fock L) n)
    rw [h2, map_smul]
  · have hz' : GR R z ∉ Ext005Moments.momentDomain (L := L) j := by
      intro h
      apply hz
      rw [Ext005Moments.momentDomain_iff] at h ⊢
      simpa only [GR_apply, LinearIsometryEquiv.norm_map] using h
    simp [Ext005FormCutoffR109.rootLift, hz, hz']

/-- **Covariance of the strong quadratic generator.** -/
theorem strongCoordinates_cov (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (z : Fock L) :
    GR R (strongCoordinates a b z) =
      strongCoordinates (conjSym R 1 a) (symMap R 2 b) (GR R z) := by
  have h3 : ∀ z, GR R (lower 3 (by omega) b z) = lower 3 (by omega) (symMap R 2 b) (GR R z) :=
    fun z => lower_cov R 3 _ b z
  have h1 : ∀ z, GR R (lower 1 (by omega) b z) = lower 1 (by omega) (symMap R 2 b) (GR R z) :=
    fun z => lower_cov R 1 _ b z
  have h1a := adjoint_cov R _ _ h1 z
  unfold strongCoordinates
  simp only [add_apply, smul_apply, map_add, map_smul, numberCoordinates_cov, h3, h1a]

end QuantumNLS.Prop022ACovPhys

#print axioms QuantumNLS.Prop022ACovPhys.symMap_annihilation
#print axioms QuantumNLS.Prop022ACovPhys.numberBlock_cov
#print axioms QuantumNLS.Prop022ACovPhys.rootLift_cov
#print axioms QuantumNLS.Prop022ACovPhys.strongCoordinates_cov
