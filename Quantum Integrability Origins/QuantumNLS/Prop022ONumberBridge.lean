import QuantumNLS.GaugeTransport
import QuantumNLS.Ext006PhysicalCoreR39a
import QuantumNLS.Prop022TensorCompressionR115
import QuantumNLS.Ext005QuadraticEnergyR108

/-! PROP-022 takeover, stage O2. Matrix elements of the actual physical
number-preserving block `numberBlock a N` (the sector restriction of dGamma)
between Fourier occupation kets are the finite-mode creation/annihilation
sums of the literal CCR core: for every finite mode set S containing both
supports,
  <k| numberBlock a N |m> = sum_{i,j in S} <e_i, a e_j> <k| Cre i Ann j |m>.
The proof uses the actual subset-average placement, its symmetrization on
symmetric vectors, the realized DEF-026 collective operators and a
projection-locality argument. No matrix-element formula is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
namespace QuantumNLS.Prop022ONumberBridge
open TensorCarrier TensorFourier TensorPlacements PhysicalTensor BetheCoefficientTransform
open Occupation OccupationUnitary OccupationConjugacy GaugeTransport
open Ext006PhysicalCoreR39a Ext006KernelHilbertSchmidt Prop022TensorCompressionR115
variable {L : ℝ} [Fact (0 < L)]

local notation "T1" => HilbertTensorPower ℂ (L2T L) 1

/-! ### The first-slot placement as an algebra map -/

lemma blockPlacement_comp (q : ℕ) (Y Z : T1 →L[ℂ] T1) :
    blockPlacement 1 q (Y ∘L Z) = blockPlacement 1 q Y ∘L blockPlacement 1 q Z := by
  apply ContinuousLinearMap.ext
  intro x
  apply (splitIsometry (𝕜 := ℂ) (E := L2T L) 1 q).injective
  rw [comp_apply, split_blockPlacement, split_blockPlacement, split_blockPlacement,
    ← comp_apply (htmap Y _), ← htmap_comp, ContinuousLinearMap.id_comp]

lemma blockPlacement_add (q : ℕ) (Y Z : T1 →L[ℂ] T1) :
    blockPlacement 1 q (Y + Z) = blockPlacement 1 q Y + blockPlacement 1 q Z := by
  apply ContinuousLinearMap.ext
  intro x
  apply (splitIsometry (𝕜 := ℂ) (E := L2T L) 1 q).injective
  rw [add_apply, map_add, split_blockPlacement, split_blockPlacement, split_blockPlacement,
    htmap_add_left, add_apply]

lemma blockPlacement_smul (q : ℕ) (c : ℂ) (Y : T1 →L[ℂ] T1) :
    blockPlacement 1 q (c • Y) = c • blockPlacement 1 q Y := by
  apply ContinuousLinearMap.ext
  intro x
  apply (splitIsometry (𝕜 := ℂ) (E := L2T L) 1 q).injective
  rw [smul_apply, map_smul, split_blockPlacement, split_blockPlacement,
    htmap_smul_left, smul_apply]

/-- The placement as a linear map in its one-particle operator. -/
def placementLinear (q : ℕ) :
    (T1 →L[ℂ] T1) →ₗ[ℂ] (HilbertTensorPower ℂ (L2T L) (1+q) →L[ℂ]
      HilbertTensorPower ℂ (L2T L) (1+q)) where
  toFun Y := blockPlacement 1 q Y
  map_add' := blockPlacement_add q
  map_smul' := blockPlacement_smul q

lemma blockPlacement_inner (q : ℕ) (Y : T1 →L[ℂ] T1)
    (x y : HilbertTensorPower ℂ (L2T L) (1+q)) :
    ⟪blockPlacement 1 q Y x, y⟫_ℂ = ⟪x, blockPlacement 1 q Y.adjoint y⟫_ℂ := by
  let e := splitIsometry (𝕜 := ℂ) (E := L2T L) 1 q
  have h1 : ⟪blockPlacement 1 q Y x, y⟫_ℂ = ⟪e (blockPlacement 1 q Y x), e y⟫_ℂ :=
    (e.inner_map_map _ _).symm
  have h2 : ⟪x, blockPlacement 1 q Y.adjoint y⟫_ℂ =
      ⟪e x, e (blockPlacement 1 q Y.adjoint y)⟫_ℂ := (e.inner_map_map _ _).symm
  rw [h1, h2, split_blockPlacement, split_blockPlacement, ← adjoint_inner_right,
    adjoint_htmap, adjoint_id]

/-! ### Symmetric vectors -/

lemma perm_fixed {N : ℕ} (σ : Equiv.Perm (Fin N)) (x : physSector L N) :
    permHilbertIsometry σ (x : HilbertTensorPower ℂ (L2T L) N) = x :=
  (mem_fixedSubmodule.mp x.property) σ

lemma perm_symm_fixed {N : ℕ} (σ : Equiv.Perm (Fin N)) (x : physSector L N) :
    (permHilbertIsometry σ).symm (x : HilbertTensorPower ℂ (L2T L) N) = x := by
  conv_lhs => rw [← perm_fixed σ x]
  exact LinearIsometryEquiv.symm_apply_apply _ _

lemma inner_perm_sym {N : ℕ} (σ : Equiv.Perm (Fin N)) (φ : physSector L N)
    (y : HilbertTensorPower ℂ (L2T L) N) :
    ⟪(φ : HilbertTensorPower ℂ (L2T L) N), permHilbertIsometry σ y⟫_ℂ =
      ⟪(φ : HilbertTensorPower ℂ (L2T L) N), y⟫_ℂ := by
  rw [← LinearIsometryEquiv.inner_map_map (permHilbertIsometry σ).symm,
    LinearIsometryEquiv.symm_apply_apply, perm_symm_fixed]

/-- Every literal slot has the matrix elements of slot zero between symmetric vectors. -/
lemma slot_inner (n : ℕ) (i : Fin (1+n)) (a b : ℤ) (φ ψ : physSector L (1+n)) :
    ⟪(φ : HilbertTensorPower ℂ (L2T L) (1+n)), physicalSlot L n i a b ψ⟫_ℂ =
      ⟪(φ : HilbertTensorPower ℂ (L2T L) (1+n)),
        oneBodyPlacement n (physicalMatrixUnit L a b) ψ⟫_ℂ := by
  simp only [physicalSlot, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  rw [inner_perm_sym, perm_symm_fixed]

/-- The collective is slot zero in symmetric matrix elements. -/
lemma collective_inner (n : ℕ) (a b : ℤ) (φ ψ : physSector L (1+n)) :
    ⟪(φ : HilbertTensorPower ℂ (L2T L) (1+n)), physicalCollective L n a b ψ⟫_ℂ =
      ⟪(φ : HilbertTensorPower ℂ (L2T L) (1+n)),
        oneBodyPlacement n (physicalMatrixUnit L a b) ψ⟫_ℂ := by
  change ⟪(φ : HilbertTensorPower ℂ (L2T L) (1+n)),
    (((1 + n : ℕ) : ℂ)⁻¹) • physicalTotal L n a b ψ⟫_ℂ = _
  rw [inner_smul_right, physicalTotal, sum_apply, inner_sum]
  simp only [slot_inner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : ((1 + n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 1 + n ≠ 0 by omega)
  rw [← mul_assoc, show ((1 + n : ℕ) : ℂ) = (((1 + n : ℕ) : ℕ) : ℂ) from rfl,
    inv_mul_cancel₀ hn, one_mul]

/-! ### Occupation kets -/

lemma ip_cre_ann (k m : Occ) (a b : ℤ) :
    ip (ket k) (Cre b (Ann a (ket m))) = (w a b m : ℂ) * (if shift a b m = k then 1 else 0) := by
  rw [← Module.End.mul_apply, ← Top_eq_Cre_Ann, Top_ket, ip_ket_left, Finsupp.smul_apply,
    smul_eq_mul, Finsupp.single_apply]

/-- The DEF-026 occupation formula, now as an exact physical matrix element. -/
lemma slot_ket (n : ℕ) (a b : ℤ) (k m : Arr (1+n)) :
    ⟪((sectorKet (L := L) k : HN L (1+n)) : HilbertTensorPower ℂ (L2T L) (1+n)),
      oneBodyPlacement n (physicalMatrixUnit L a b) (sectorKet (L := L) m)⟫_ℂ =
      (((1 + n : ℕ) : ℂ))⁻¹ * ip (ket k.1) (Cre b (Ann a (ket m.1))) := by
  rw [← collective_inner, ← Submodule.coe_inner,
    ← (physicalOccupation L (1+n)).inner_map_map, physicalOccupation_collective]
  simp only [sectorKet, LinearIsometryEquiv.apply_symm_apply, OccupationHilbert.E_single,
    ip_cre_ann]
  split_ifs with hd hs hs
  · have hk : k = shiftArr a b m hd := Subtype.ext hs.symm
    rw [lp.inner_single_left, lp.single_apply, hk, Pi.single_eq_same, coef_eq_w]
    simp only [RCLike.inner_apply, map_one, mul_one]
    push_cast
    ring
  · have hk : k ≠ shiftArr a b m hd := fun h => hs (congrArg Subtype.val h).symm
    rw [lp.inner_single_left, lp.single_apply, Pi.single_eq_of_ne hk]
    simp
  all_goals
    simp only [inner_zero_right]
    have hz : m.1 a = 0 := by
      have : ¬ 1 ≤ m.1 a := hd
      omega
    rw [w_empty hz]
    simp

/-! ### Matrix units and the finite projection -/

/-- The one-particle Fourier basis vectors in the first tensor power. -/
def hv (i : ℤ) : T1 := htpow 1 (physicalBasis L i)

/-- The first-power matrix unit |h_i><h_j|. -/
def unitY (i j : ℤ) : T1 →L[ℂ] T1 := InnerProductSpace.rankOne ℂ (hv (L := L) i) (hv j)

lemma physicalBasis_eq (i : ℤ) : (Fourier.fourierL2 L).symm (oneBasis i) = physicalBasis L i := by
  rw [← fourier_physicalBasis (L := L) i, LinearIsometryEquiv.symm_apply_apply]

lemma firstPowerIso_symm_apply (u : L2T L) :
    (firstPowerIso (𝕜 := ℂ) (E := L2T L)).symm u = htpow 1 u := by
  apply (firstPowerIso (𝕜 := ℂ) (E := L2T L)).injective
  rw [LinearIsometryEquiv.apply_symm_apply, firstPowerIso_htpow]

lemma hv_inner (i j : ℤ) : ⟪hv (L := L) i, hv j⟫_ℂ = if i = j then 1 else 0 := by
  simp only [hv, ← firstPowerIso_symm_apply]
  exact ((firstPowerIso (𝕜 := ℂ) (E := L2T L)).symm.inner_map_map _ _).trans
    (orthonormal_iff_ite.mp (physicalBasis L).orthonormal i j)

lemma oneBody_eq (n : ℕ) (a b : ℤ) :
    oneBodyPlacement n (physicalMatrixUnit L a b) = blockPlacement 1 n (unitY (L := L) b a) := by
  unfold oneBodyPlacement
  congr 1
  apply ContinuousLinearMap.ext
  intro z
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.symm_symm,
    physicalMatrixUnit_rankOne, physicalBasis_eq, physicalBasis_eq]
  simp only [unitY, InnerProductSpace.rankOne_apply, map_smul, firstPowerIso_symm_apply]
  congr 1
  rw [hv, ← firstPowerIso_symm_apply, LinearIsometryEquiv.inner_map_eq_flip,
    LinearIsometryEquiv.symm_symm]

lemma rankOne_self_adjoint (x : T1) :
    (InnerProductSpace.rankOne ℂ x x).adjoint = InnerProductSpace.rankOne ℂ x x := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  simp only [InnerProductSpace.rankOne_apply, inner_smul_left, inner_smul_right,
    inner_conj_symm]
  ring

/-- The finite Fourier projection onto the modes in S. -/
def proj (S : Finset ℤ) : T1 →L[ℂ] T1 := ∑ i ∈ S, unitY (L := L) i i

lemma proj_adjoint (S : Finset ℤ) : (proj (L := L) S).adjoint = proj S := by
  unfold proj
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => rankOne_self_adjoint _)

lemma sandwich (S : Finset ℤ) (Y : T1 →L[ℂ] T1) :
    proj (L := L) S ∘L Y ∘L proj S =
      ∑ i ∈ S, ∑ j ∈ S, ⟪hv (L := L) i, Y (hv j)⟫_ℂ • unitY i j := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [proj, comp_apply, sum_apply, unitY, InnerProductSpace.rankOne_apply, map_sum,
    map_smul, smul_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact mul_comm _ _

lemma proj_comp (S : Finset ℤ) : proj (L := L) S ∘L proj S = proj S := by
  have h := sandwich (L := L) S (ContinuousLinearMap.id ℂ T1)
  rw [ContinuousLinearMap.id_comp] at h
  rw [h]
  unfold proj
  apply Finset.sum_congr rfl
  intro i hi
  simp only [id_apply, hv_inner, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq S i (fun j => unitY (L := L) i j), if_pos hi]

lemma ip_number (m : Occ) (i : ℤ) : ip (ket m) (Cre i (Ann i (ket m))) = (m i : ℂ) := by
  rw [ip_cre_ann]
  by_cases h : 1 ≤ m i
  · rw [show shift i i m = m from shift_self h, if_pos rfl]
    simp [w]
  · have hz : m i = 0 := by omega
    rw [w_empty hz, hz]
    simp

lemma sum_occupation (m : Occ) (S : Finset ℤ) (hm : m.support ⊆ S) :
    ∑ i ∈ S, (m i : ℂ) = (total m : ℂ) := by
  rw [total, Finsupp.degree_apply, Nat.cast_sum]
  symm
  apply Finset.sum_subset hm
  intro i _ hi
  simp [Finsupp.notMem_support_iff.mp hi]

lemma sectorKet_norm {N : ℕ} (m : Arr N) : ‖sectorKet (L := L) m‖ = 1 := by
  rw [sectorKet, LinearIsometryEquiv.norm_map, lp.norm_single (by norm_num), norm_one]

/-- The finite projection fixes every occupation ket supported in S. -/
lemma proj_fixes (n : ℕ) (S : Finset ℤ) (m : Arr (1+n)) (hm : m.1.support ⊆ S) :
    blockPlacement 1 n (proj (L := L) S)
      ((sectorKet (L := L) m : HN L (1+n)) : HilbertTensorPower ℂ (L2T L) (1+n)) =
      ((sectorKet (L := L) m : HN L (1+n)) : HilbertTensorPower ℂ (L2T L) (1+n)) := by
  set ψ : HilbertTensorPower ℂ (L2T L) (1+n) :=
    ((sectorKet (L := L) m : HN L (1+n)) : HilbertTensorPower ℂ (L2T L) (1+n))
  set T := blockPlacement 1 n (proj (L := L) S)
  have hdiag : ⟪ψ, T ψ⟫_ℂ = 1 := by
    have he : T = ∑ i ∈ S, blockPlacement 1 n (unitY (L := L) i i) := by
      change placementLinear n (proj S) = _
      rw [proj, map_sum]
      rfl
    rw [he, sum_apply, inner_sum]
    simp only [ψ, ← oneBody_eq, slot_ket, ip_number, ← Finset.mul_sum]
    rw [sum_occupation m.1 S hm, show total m.1 = 1 + n from m.2]
    have hn : ((1 + n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 1 + n ≠ 0 by omega)
    exact inv_mul_cancel₀ hn
  have hself (y : HilbertTensorPower ℂ (L2T L) (1+n)) : ⟪T ψ, y⟫_ℂ = ⟪ψ, T y⟫_ℂ := by
    rw [blockPlacement_inner, proj_adjoint]
  have hTT : ⟪T ψ, T ψ⟫_ℂ = 1 := by
    rw [hself, ← comp_apply, ← blockPlacement_comp, proj_comp]
    exact hdiag
  have hψ : ⟪ψ, ψ⟫_ℂ = 1 := by
    have hn : ‖((sectorKet (L := L) m : HN L (1+n)) : HilbertTensorPower ℂ (L2T L) (1+n))‖ = 1 :=
      sectorKet_norm m
    rw [inner_self_eq_norm_sq_to_K, hn]
    simp
  have hz : ⟪T ψ - ψ, T ψ - ψ⟫_ℂ = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, hTT, hself, hdiag, hψ]
    ring
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

/-- Locality: slot-zero matrix elements between occupation kets see only the
finitely many matrix entries on the supports. -/
theorem placement_ket (n : ℕ) (Y : T1 →L[ℂ] T1) (k m : Arr (1+n)) (S : Finset ℤ)
    (hk : k.1.support ⊆ S) (hm : m.1.support ⊆ S) :
    ⟪((sectorKet (L := L) k : HN L (1+n)) : HilbertTensorPower ℂ (L2T L) (1+n)),
      blockPlacement 1 n Y (sectorKet (L := L) m)⟫_ℂ =
      ∑ i ∈ S, ∑ j ∈ S, ⟪hv (L := L) i, Y (hv j)⟫_ℂ *
        ((((1 + n : ℕ) : ℂ))⁻¹ * ip (ket k.1) (Cre i (Ann j (ket m.1)))) := by
  set φ : HilbertTensorPower ℂ (L2T L) (1+n) :=
    ((sectorKet (L := L) k : HN L (1+n)) : HilbertTensorPower ℂ (L2T L) (1+n))
  set ψ : HilbertTensorPower ℂ (L2T L) (1+n) :=
    ((sectorKet (L := L) m : HN L (1+n)) : HilbertTensorPower ℂ (L2T L) (1+n))
  have hφ := proj_fixes (L := L) n S k hk
  have hψ := proj_fixes (L := L) n S m hm
  calc
    ⟪φ, blockPlacement 1 n Y ψ⟫_ℂ =
        ⟪blockPlacement 1 n (proj S) φ, blockPlacement 1 n Y (blockPlacement 1 n (proj S) ψ)⟫_ℂ := by
      rw [hφ, hψ]
    _ = ⟪φ, blockPlacement 1 n (proj S ∘L Y ∘L proj S) ψ⟫_ℂ := by
      rw [blockPlacement_inner, proj_adjoint, blockPlacement_comp, blockPlacement_comp]
      rfl
    _ = ∑ i ∈ S, ∑ j ∈ S, ⟪hv (L := L) i, Y (hv j)⟫_ℂ * ⟪φ, blockPlacement 1 n (unitY i j) ψ⟫_ℂ := by
      rw [sandwich]
      change ⟪φ, placementLinear n (∑ i ∈ S, ∑ j ∈ S, _) ψ⟫_ℂ = _
      simp only [map_sum, map_smul, sum_apply, smul_apply, inner_sum, inner_smul_right]
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [← oneBody_eq, slot_ket]

/-! ### The subset-average placement and the number block -/

lemma firstPlacement_eq (q : ℕ) (a : SymSector ℂ (L2T L) 1 →L[ℂ] SymSector ℂ (L2T L) 1) :
    firstPlacement (q := q) a = blockPlacement 1 q (extendSymKernel a) := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

lemma Q_inner (q : ℕ) (a : SymSector ℂ (L2T L) 1 →L[ℂ] SymSector ℂ (L2T L) 1)
    (φ ψ : physSector L (1+q)) :
    ⟪(φ : HilbertTensorPower ℂ (L2T L) (1+q)), (Q_N_p (q := q) a ψ : SymSector ℂ (L2T L) (1+q))⟫_ℂ =
      ⟪(φ : HilbertTensorPower ℂ (L2T L) (1+q)),
        blockPlacement 1 q (extendSymKernel a) ψ⟫_ℂ := by
  change ⟪(φ : HilbertTensorPower ℂ (L2T L) (1+q)), symmetrizedPlacement a ψ⟫_ℂ = _
  rw [symmetrizedPlacement, smul_apply, sum_apply, inner_smul_right, inner_sum]
  have hterm (σ : Equiv.Perm (Fin (1+q))) :
      ⟪(φ : HilbertTensorPower ℂ (L2T L) (1+q)), permutedPlacement σ a ψ⟫_ℂ =
        ⟪(φ : HilbertTensorPower ℂ (L2T L) (1+q)), blockPlacement 1 q (extendSymKernel a) ψ⟫_ℂ := by
    change ⟪(φ : HilbertTensorPower ℂ (L2T L) (1+q)),
      permHilbertIsometry σ (firstPlacement a (permHilbertIsometry σ⁻¹ ψ))⟫_ℂ = _
    rw [inner_perm_sym, perm_fixed, firstPlacement_eq]
  simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card (Equiv.Perm (Fin (1+q))) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := Equiv.Perm (Fin (1+q)))).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

lemma symProjToSector_power (u : L2T L) :
    symProjToSector (H := L2T L) 1 (htpow 1 u) = power 1 u := by
  apply Subtype.ext
  change symProj ℂ (L2T L) 1 (htpow 1 u) = htpow 1 u
  rw [symProj_eq_starProjection]
  exact Submodule.starProjection_eq_self_iff.mpr (htpow_mem_symSector 1 u)

lemma extend_entry (a : SymSector ℂ (L2T L) 1 →L[ℂ] SymSector ℂ (L2T L) 1) (i j : ℤ) :
    ⟪hv (L := L) i, extendSymKernel a (hv j)⟫_ℂ =
      ⟪power 1 (physicalBasis L i), a (power 1 (physicalBasis L j))⟫_ℂ := by
  change ⟪hv (L := L) i, ((a (symProjToSector 1 (hv j)) : SymSector ℂ (L2T L) 1) :
    HilbertTensorPower ℂ (L2T L) 1)⟫_ℂ = _
  simp only [hv]
  rw [symProjToSector_power, Submodule.coe_inner]
  rfl

lemma Q_ket (q : ℕ) (a : SymSector ℂ (L2T L) 1 →L[ℂ] SymSector ℂ (L2T L) 1)
    (k m : Arr (1+q)) (S : Finset ℤ) (hk : k.1.support ⊆ S) (hm : m.1.support ⊆ S) :
    ⟪sectorKet (L := L) k, Q_N_p (q := q) a (sectorKet m)⟫_ℂ =
      (((1 + q : ℕ) : ℂ))⁻¹ * ∑ i ∈ S, ∑ j ∈ S,
        ⟪power 1 (physicalBasis L i), a (power 1 (physicalBasis L j))⟫_ℂ *
          ip (ket k.1) (Cre i (Ann j (ket m.1))) := by
  rw [Submodule.coe_inner, Q_inner, placement_ket q _ k m S hk hm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [extend_entry]
  ring

lemma cast_ket (q N : ℕ) (h : 1 + q = N)
    (a : SymSector ℂ (L2T L) 1 →L[ℂ] SymSector ℂ (L2T L) 1)
    (k m : Arr N) (S : Finset ℤ) (hk : k.1.support ⊆ S) (hm : m.1.support ⊆ S) :
    ⟪sectorKet (L := L) k, PhysicalPlacements.castSymSectorOperator L h
      (Q_N_p (q := q) a) (sectorKet m)⟫_ℂ =
      ((N : ℂ))⁻¹ * ∑ i ∈ S, ∑ j ∈ S,
        ⟪power 1 (physicalBasis L i), a (power 1 (physicalBasis L j))⟫_ℂ *
          ip (ket k.1) (Cre i (Ann j (ket m.1))) := by
  subst h
  exact Q_ket q a k m S hk hm

/-- **Number bridge.** The actual physical number block between occupation
kets equals the finite CCR-core sum with the literal one-particle entries. -/
theorem numberBlock_ket (N : ℕ) (a : HN L 1 →L[ℂ] HN L 1) (k m : Arr N) (S : Finset ℤ)
    (hk : k.1.support ⊆ S) (hm : m.1.support ⊆ S) :
    ⟪sectorKet (L := L) k, Ext005QuadraticEnergyR108.numberBlock a N (sectorKet m)⟫_ℂ =
      ∑ i ∈ S, ∑ j ∈ S,
        ⟪power 1 (physicalBasis L i), a (power 1 (physicalBasis L j))⟫_ℂ *
          ip (ket k.1) (Cre i (Ann j (ket m.1))) := by
  by_cases hN : 1 ≤ N
  · rw [Ext005QuadraticEnergyR108.numberBlock, dif_pos hN, smul_apply, inner_smul_right]
    change (N : ℂ) * ⟪sectorKet (L := L) k, PhysicalPlacements.castSymSectorOperator L
      (Nat.add_sub_of_le hN) (Q_N_p (q := N - 1) a) (sectorKet m)⟫_ℂ = _
    rw [cast_ket (N - 1) N (Nat.add_sub_of_le hN) a k m S hk hm, ← mul_assoc]
    have hn : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [mul_inv_cancel₀ hn, one_mul]
  · have hN0 : N = 0 := by omega
    rw [Ext005QuadraticEnergyR108.numberBlock, dif_neg hN, zero_apply, inner_zero_right]
    have hm0 : m.1 = 0 := by
      have ht : total m.1 = 0 := m.2.trans hN0
      exact (Finsupp.degree_eq_zero_iff m.1).mp ht
    symm
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    rw [hm0, Ann_ket]
    simp [ip_zero_right]

end QuantumNLS.Prop022ONumberBridge

#print axioms QuantumNLS.Prop022ONumberBridge.numberBlock_ket
