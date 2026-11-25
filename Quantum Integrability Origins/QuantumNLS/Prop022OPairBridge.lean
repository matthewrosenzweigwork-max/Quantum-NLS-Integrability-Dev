import QuantumNLS.Ext006FiniteExponentialR39a
import QuantumNLS.Ext006PhysicalContinuityR38a
import QuantumNLS.Ext006PhysicalApproximationR38a
import QuantumNLS.Prop022ONumberBridge

/-! PROP-022 takeover, stage O3. Matrix elements of the actual physical pair
creation block between Fourier occupation kets. For any symmetric
two-particle vector b and any finite mode set S containing the support of
the outgoing ket,
  <k| creation b N |m> = sum_{i,j in S} <e_i (x) e_j, b> <k| Cre i Cre j |m>.
The completed tensor is expanded in the product Hilbert basis; continuity
and linearity of the actual creation block in b justify the expansion. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
namespace QuantumNLS.Prop022OPairBridge
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Occupation Ext006PhysicalCoreR39a Ext006KernelHilbertSchmidt Ext006PhysFockCoord
open Ext006PhysicalNormBridge.PairTensor Ext006PhysicalApproximationR38a TraceClass
variable {L : ℝ} [Fact (0 < L)]

/-- The pair coefficient of b in the ordered product basis. -/
def pairCoeff (b : HN L 2) (i j : ℤ) : ℂ :=
  ⟪htmul (physicalBasis L i) (physicalBasis L j),
    twoIso (E := L2T L) (b : HilbertTensorPower ℂ (L2T L) 2)⟫_ℂ

lemma creation_add (y y' : HN L 2) (N : ℕ) (x : HN L N) :
    Ext005PairSector.creation (y + y') N x =
      Ext005PairSector.creation y N x + Ext005PairSector.creation y' N x := by
  apply Subtype.ext
  simp only [Ext006PhysicalNormBridge.CreationFormula.creation_eq_projection,
    Submodule.coe_smul, Submodule.coe_add]
  change (Real.sqrt (((N : ℝ)+1)*((N : ℝ)+2)) : ℂ) •
    (physSector L (2+N)).starProjection
      (Ext006PairPowerWick.concat ((y : HilbertTensorPower ℂ (L2T L) 2) + y') x) = _
  rw [Ext006PairPowerWick.concat_add_left, map_add, smul_add]
  rfl

lemma creation_norm_le (y : HN L 2) (N : ℕ) (x : HN L N) :
    ‖Ext005PairSector.creation y N x‖ ≤ (Real.sqrt (((N : ℝ)+1)*((N : ℝ)+2)) * ‖x‖) * ‖y‖ := by
  have ha : ‖Ext005PairSector.annihilation y N‖ ≤ ‖y‖ * Real.sqrt (((N : ℝ)+1)*((N : ℝ)+2)) :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      (fun z => Ext005PairSector.annihilation_bound y N z)
  calc ‖Ext005PairSector.creation y N x‖
      ≤ ‖Ext005PairSector.creation y N‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖Ext005PairSector.annihilation y N‖ * ‖x‖ := by
      rw [Ext005PairSector.creation, ContinuousLinearMap.adjoint.norm_map]
    _ ≤ (‖y‖ * Real.sqrt (((N : ℝ)+1)*((N : ℝ)+2))) * ‖x‖ :=
      mul_le_mul_of_nonneg_right ha (norm_nonneg x)
    _ = _ := by ring

/-- Creation at a fixed datum, as a continuous linear map of the pair vector. -/
def creationCLM (N : ℕ) (x : HN L N) : HN L 2 →L[ℂ] HN L (2+N) :=
  LinearMap.mkContinuous
    { toFun := fun y => Ext005PairSector.creation y N x
      map_add' := fun y y' => creation_add y y' N x
      map_smul' := fun c y => Ext006FiniteExponentialR39a.creation_smul c y N x }
    (Real.sqrt (((N : ℝ)+1)*((N : ℝ)+2)) * ‖x‖) (fun y => creation_norm_le y N x)

lemma creationCLM_apply (N : ℕ) (x : HN L N) (y : HN L 2) :
    creationCLM N x y = Ext005PairSector.creation y N x := rfl

/-- Expansion of every physical pair vector in the symmetrized product basis. -/
theorem hasSum_basisPair (b : HN L 2) :
    HasSum (fun p : ℤ × ℤ => pairCoeff b p.1 p.2 • basisPair (physicalBasis L) p.1 p.2) b := by
  have h := (pairProjection (L := L)).hasSum
    ((htmulBasis (physicalBasis L) (physicalBasis L)).hasSum_repr
      (twoIso (E := L2T L) (b : HilbertTensorPower ℂ (L2T L) 2)))
  have hb : pairProjection (L := L) (twoIso (E := L2T L) (b : HilbertTensorPower ℂ (L2T L) 2)) = b := by
    change (physSector L 2).orthogonalProjectionOnto
      ((twoIso (E := L2T L)).symm (twoIso (E := L2T L) (b : HilbertTensorPower ℂ (L2T L) 2))) = b
    rw [LinearIsometryEquiv.symm_apply_apply]
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self b
  have hf : (fun p : ℤ × ℤ => pairProjection (L := L)
      ((htmulBasis (physicalBasis L) (physicalBasis L)).repr
        (twoIso (E := L2T L) (b : HilbertTensorPower ℂ (L2T L) 2)) p •
        htmulBasis (physicalBasis L) (physicalBasis L) p)) =
      fun p => pairCoeff b p.1 p.2 • basisPair (physicalBasis L) p.1 p.2 := by
    funext p
    rw [HilbertBasis.repr_apply_apply, htmulBasis_apply, map_smul]
    rfl
  rw [hb, hf] at h
  exact h

lemma coreEmbedding_apply (v : FS) (k : Occ) : Ext006PhysicalVacuum.coreEmbedding v k = v k := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add u w hu hw => rw [map_add, lp.coeFn_add, Pi.add_apply, hu, hw, Finsupp.add_apply]
  | single m c =>
    rw [Ext006PhysicalVacuum.coreEmbedding, Finsupp.linearCombination_single, lp.coeFn_smul,
      Pi.smul_apply, lp.single_apply, Finsupp.single_apply, Pi.single_apply]
    by_cases h : k = m
    · subst h
      rw [if_pos rfl, if_pos rfl, smul_eq_mul, mul_one]
    · rw [if_neg h, if_neg (Ne.symm h), smul_zero]

lemma inner_physCore_core (k : Occ) (v : FS) :
    ⟪physCore (L := L) (ket k), physCore v⟫_ℂ = ip (ket k) v := by
  rw [inner_physCore_ket, ip_ket_left]
  change (Phi (L := L) ((Phi (L := L)).symm (Ext006PhysicalVacuum.coreEmbedding v))) k = v k
  rw [LinearIsometryEquiv.apply_symm_apply, coreEmbedding_apply]

lemma cre_cre_ket (i j : ℤ) (m : Occ) :
    Cre i (Cre j (ket m)) =
      ((Real.sqrt ((m j : ℝ)+1) : ℂ) * (Real.sqrt (((m + e j) i : ℝ)+1) : ℂ)) •
        ket (m + e j + e i) := by
  rw [Cre_ket, map_smul, Cre_ket, smul_smul, mul_comm]

lemma ip_cre_cre (k m : Occ) (i j : ℤ) :
    ip (ket k) (Cre i (Cre j (ket m))) =
      ((Real.sqrt ((m j : ℝ)+1) : ℂ) * (Real.sqrt (((m + e j) i : ℝ)+1) : ℂ)) *
        (if m + e j + e i = k then 1 else 0) := by
  rw [cre_cre_ket, ip_ket_left, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]

lemma support_of_cre_cre {k m : Occ} {i j : ℤ} (h : ip (ket k) (Cre i (Cre j (ket m))) ≠ 0) :
    i ∈ k.support ∧ j ∈ k.support := by
  rw [ip_cre_cre] at h
  have hk : m + e j + e i = k := by
    by_contra hne
    rw [if_neg hne, mul_zero] at h
    exact h rfl
  subst hk
  constructor
  · rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same]
    omega
  · rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_eq_same]
    omega

/-- **Pair bridge.** Physical pair creation between occupation kets. -/
theorem creation_ket (N : ℕ) (b : HN L 2) (k : Arr (2+N)) (m : Arr N) (S : Finset ℤ)
    (hk : k.1.support ⊆ S) :
    ⟪sectorKet (L := L) k, Ext005PairSector.creation b N (sectorKet m)⟫_ℂ =
      ∑ i ∈ S, ∑ j ∈ S, pairCoeff b i j * ip (ket k.1) (Cre i (Cre j (ket m.1))) := by
  have hcre : HasSum (fun p : ℤ × ℤ => pairCoeff b p.1 p.2 •
      Ext005PairSector.creation (basisPair (physicalBasis L) p.1 p.2) N (sectorKet (L := L) m))
      (Ext005PairSector.creation b N (sectorKet (L := L) m)) := by
    have h := (creationCLM (L := L) N (sectorKet m)).hasSum (hasSum_basisPair b)
    simp only [creationCLM_apply, map_smul] at h
    exact h
  have hs := (innerSL ℂ (sectorKet (L := L) k)).hasSum hcre
  have hterm (p : ℤ × ℤ) :
      innerSL ℂ (sectorKet (L := L) k) (pairCoeff b p.1 p.2 •
        Ext005PairSector.creation (basisPair (physicalBasis L) p.1 p.2) N (sectorKet (L := L) m)) =
        pairCoeff b p.1 p.2 * ip (ket k.1) (Cre p.1 (Cre p.2 (ket m.1))) := by
    rw [map_smul, smul_eq_mul, innerSL_apply_apply]
    congr 1
    rw [← (inclusion L (2+N)).inner_map_map, ← physCore_ket_sector, physical_pair_core_ket,
      inner_physCore_core]
  simp only [hterm] at hs
  have hz : ∀ p ∉ S ×ˢ S, pairCoeff b p.1 p.2 * ip (ket k.1) (Cre p.1 (Cre p.2 (ket m.1))) = 0 := by
    intro p hp
    by_contra hne
    have h2 := support_of_cre_cre (right_ne_zero_of_mul hne)
    exact hp (Finset.mem_product.mpr ⟨hk h2.1, hk h2.2⟩)
  have hf : HasSum (fun p : ℤ × ℤ => pairCoeff b p.1 p.2 * ip (ket k.1) (Cre p.1 (Cre p.2 (ket m.1))))
      (∑ p ∈ S ×ˢ S, pairCoeff b p.1 p.2 * ip (ket k.1) (Cre p.1 (Cre p.2 (ket m.1)))) :=
    hasSum_sum_of_ne_finset_zero hz
  rw [innerSL_apply_apply] at hs
  change HasSum _ ⟪sectorKet (L := L) k, Ext005PairSector.creation b N (sectorKet m)⟫_ℂ at hs
  rw [hs.unique hf, Finset.sum_product]

end QuantumNLS.Prop022OPairBridge

#print axioms QuantumNLS.Prop022OPairBridge.creation_ket
