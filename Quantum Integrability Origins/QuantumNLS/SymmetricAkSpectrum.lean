/-
QuantumNLS.SymmetricAkSpectrum — DEF-031 `A_k = 1 − Σ_{j≤k} ∂²_{x_j}` realized as a self-adjoint
operator on the actual DEF-004 tensor sector `H_k = Sym^k L²(𝕋_L)`, via a generic unitary transport
of unbounded operators; compact inverse (owner: opus_tensor).

Source: DEF-004 (definitions.tex:25) `H_N = Sym^N L²(𝕋_L)` inside the completed tensor power;
DEF-031 (:187) `A_k = 1 − Σ_{j≤k} ∂²_{x_j}`.

Reused frozen results (no duplicate carrier/basis/compactness proof): SymmetricAk SA1 1921938b
(`symL2`, `symSectorUnitary`, `physAkSym`, `physAkSym_isSelfAdjoint`, `physAkInv`, `physAkInvSym`),
ProductPermutation PP1 b2f62828, ProductSecondDerivatives PSD1 fca540b6, PhysicalEnergy 01370715,
PhysicalTensor e774c776 (`physSector`, `physUnitary`), EnergyMultiplier 7394da58 (`AkInv`,
`AhalfInv`, `invCLM_apply`, `kinSqrt_sq`), ContactOperator c847ea9b (Terra-accepted R25;
imported read-only only for `isCompactOperator_AhalfInv`, and to relate its `SymL2` to `symL2`).
No contact/Bethe/collision edits; no S2 decision; no dynamics claimed.

Results (all proved, standard axioms only):
* §1 generic: `transportPMap U T = U⁻¹ T U` for a unitary `U : E ≃ₗᵢ E'` between Hilbert spaces;
  **`transportPMap_isSelfAdjoint`** (full adjoint-domain argument, any self-adjoint `T`).
* §2 DEF-031 on DEF-004: `physAkH L k : physSector L k →ₗ.[ℂ] physSector L k`;
  **`physAkH_isSelfAdjoint`**; `mem_physAkH_domain_iff` (weak `∂ⱼ²` of the wave function in `L²`);
  `physUnitary_physAkH` (`A_k` acts on the wave function); `physUnitary_physAkH_eq_sub_sum`
  (`= ψ − Σⱼ ∂ⱼ²ψ`); `momUnitary_physUnitary_physAkH` (Fourier multiplier `1 + Σⱼ(2πwⱼ/L)²`).
* §3 compact inverse: `AkInv_eq_comp`, `isCompactOperator_physAkInv`,
  `isCompactOperator_physAkInvSym`, `physAkInv_physAk`; on `H_k`: `physAkHInv`,
  `isCompactOperator_physAkHInv`, `physAkH_physAkHInv`, `physAkHInv_physAkH`.
* `symL2_eq_SymL2`: SA1's `symL2` coincides with ContactOperator's `SymL2`.
-/
import QuantumNLS.SymmetricAk
import QuantumNLS.ContactOperator

open scoped InnerProductSpace ENNReal ComplexConjugate LinearPMap
open MeasureTheory QuantumNLS.TensorCarrier QuantumNLS.Fourier QuantumNLS.PhysicalTensor
  QuantumNLS.PhysicalEnergy QuantumNLS.Energy QuantumNLS.ProductWeakDerivatives
  QuantumNLS.ProductSecondDerivatives QuantumNLS.ProductPermutation QuantumNLS.SymmetricAk

noncomputable section

namespace QuantumNLS.SymmetricAkSpectrum

/-! ## §1 Generic unitary transport of unbounded operators -/

section Transport

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']

/-- `U⁻¹ T U` for a unitary `U : E ≃ₗᵢ E'` and an operator `T` on `E'`; domain `U⁻¹ D(T)`. -/
def transportPMap (U : E ≃ₗᵢ[ℂ] E') (T : E' →ₗ.[ℂ] E') : E →ₗ.[ℂ] E where
  domain := T.domain.comap U.toLinearEquiv.toLinearMap
  toFun :=
    { toFun := fun x => U.symm (T ⟨U x, x.2⟩)
      map_add' := fun x y => by
        have : (⟨U ((x : E) + y), (x + y).2⟩ : T.domain) = ⟨U x, x.2⟩ + ⟨U y, y.2⟩ :=
          Subtype.ext (map_add U _ _)
        show U.symm (T ⟨U ((x : E) + y), (x + y).2⟩) = _
        rw [this, T.map_add, map_add]
      map_smul' := fun c x => by
        have : (⟨U (c • (x : E)), (c • x).2⟩ : T.domain) = c • ⟨U x, x.2⟩ :=
          Subtype.ext (map_smul U _ _)
        show U.symm (T ⟨U (c • (x : E)), (c • x).2⟩) = _
        rw [this, T.map_smul, map_smul]
        rfl }

omit [CompleteSpace E] [CompleteSpace E'] in
theorem mem_transportPMap_domain (U : E ≃ₗᵢ[ℂ] E') (T : E' →ₗ.[ℂ] E') (x : E) :
    x ∈ (transportPMap U T).domain ↔ U x ∈ T.domain := Iff.rfl

omit [CompleteSpace E] [CompleteSpace E'] in
theorem transportPMap_apply (U : E ≃ₗᵢ[ℂ] E') (T : E' →ₗ.[ℂ] E')
    (x : (transportPMap U T).domain) :
    (transportPMap U T x : E) = U.symm (T ⟨U x, x.2⟩) := rfl

/-- **Self-adjointness transports along a unitary** (general unbounded `T`). -/
theorem transportPMap_isSelfAdjoint (U : E ≃ₗᵢ[ℂ] E') {T : E' →ₗ.[ℂ] E'}
    (hT : IsSelfAdjoint T) : IsSelfAdjoint (transportPMap U T) := by
  set S := transportPMap U T with hSdef
  have hT' : T† = T := LinearPMap.isSelfAdjoint_def.1 hT
  have hdT : Dense (T.domain : Set E') := hT.dense_domain
  have hsymT : T.IsFormalAdjoint T := by
    have h := LinearPMap.adjoint_isFormalAdjoint hdT
    rw [hT'] at h
    exact h
  have hdS : Dense (S.domain : Set E) := by
    show Dense (U ⁻¹' (T.domain : Set E'))
    exact hdT.preimage U.toHomeomorph.isOpenMap
  have hsymS : S.IsFormalAdjoint S := by
    intro x y
    show ⟪U.symm (T ⟨U x, x.2⟩), (y : E)⟫_ℂ = ⟪(x : E), U.symm (T ⟨U y, y.2⟩)⟫_ℂ
    rw [← U.inner_map_map, ← U.inner_map_map (x : E), U.apply_symm_apply, U.apply_symm_apply]
    exact hsymT ⟨U x, x.2⟩ ⟨U y, y.2⟩
  have hle : S ≤ S† := LinearPMap.IsFormalAdjoint.le_adjoint hdS hsymS
  have hdom : S†.domain ≤ S.domain := by
    intro y hy
    show U y ∈ T.domain
    have hmem : U y ∈ T†.domain := by
      refine LinearPMap.mem_adjoint_domain_of_exists (U y) ⟨U (S† ⟨y, hy⟩), fun x => ?_⟩
      have mem : U.symm (x : E') ∈ S.domain := by
        show U (U.symm (x : E')) ∈ T.domain
        rw [U.apply_symm_apply]; exact x.2
      have h2 := LinearPMap.adjoint_isFormalAdjoint hdS ⟨y, hy⟩ ⟨U.symm (x : E'), mem⟩
      have e : (⟨U (U.symm (x : E')), mem⟩ : T.domain) = x := Subtype.ext (U.apply_symm_apply _)
      change ⟪S† ⟨y, hy⟩, U.symm (x : E')⟫_ℂ = ⟪y, U.symm (T ⟨U (U.symm (x : E')), mem⟩)⟫_ℂ at h2
      rw [e] at h2
      rw [← U.symm.inner_map_map, U.symm_apply_apply]
      conv_rhs => rw [← U.symm.inner_map_map, U.symm_apply_apply]
      exact h2
    rwa [hT'] at hmem
  exact LinearPMap.isSelfAdjoint_def.2
    (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 hdom)).symm

end Transport

variable {L : ℝ} [Fact (0 < L)] {k : ℕ}

/-! ## §2 DEF-031 `A_k` on the DEF-004 tensor sector `H_k` -/

/-- **`A_k` on `H_k = Sym^k L²(𝕋_L)`** (DEF-004 tensor sector): the symmetric restriction of the
position-space `A_k` transported through `symSectorUnitary : H_k ≃ₗᵢ symL2`. -/
def physAkH (L : ℝ) [Fact (0 < L)] (k : ℕ) : physSector L k →ₗ.[ℂ] physSector L k :=
  transportPMap symSectorUnitary (physAkSym L k)

/-- **`A_k` is self-adjoint on `H_k`.** -/
theorem physAkH_isSelfAdjoint : IsSelfAdjoint (physAkH L k) :=
  transportPMap_isSelfAdjoint symSectorUnitary physAkSym_isSelfAdjoint

/-- **Domain of `A_k` on `H_k`:** `ψ ∈ D(A_k)` iff every weak second partial `∂ⱼ²` of the wave
function `physUnitary ψ` lies in `L²(𝕋_L^k)`. -/
theorem mem_physAkH_domain_iff (ψ : physSector L k) :
    ψ ∈ (physAkH L k).domain ↔
      ∀ j, ∃ H, HasWeakSecondPartial j j (physUnitary (ψ : HilbertTensorPower ℂ (L2T L) k)) H :=
  mem_physAk_domain_iff_second _

theorem physUnitary_mem_physAk_domain (ψ : (physAkH L k).domain) :
    physUnitary ((ψ : physSector L k) : HilbertTensorPower ℂ (L2T L) k) ∈ (physAk L k).domain :=
  ψ.2

theorem physAkH_apply (ψ : (physAkH L k).domain) :
    (physAkH L k ψ : physSector L k) =
      symSectorUnitary.symm (physAkSym L k ⟨symSectorUnitary (ψ : physSector L k), ψ.2⟩) := rfl

/-- `A_k` on `H_k` acts as the position-space `A_k` on the wave function. -/
theorem physUnitary_physAkH (ψ : (physAkH L k).domain) :
    physUnitary ((physAkH L k ψ : physSector L k) : HilbertTensorPower ℂ (L2T L) k) =
      physAk L k ⟨physUnitary ((ψ : physSector L k) : HilbertTensorPower ℂ (L2T L) k),
        physUnitary_mem_physAk_domain ψ⟩ := by
  show ((symSectorUnitary (symSectorUnitary.symm
    (physAkSym L k ⟨symSectorUnitary (ψ : physSector L k), ψ.2⟩)) : symL2 L k) : L2TN L k) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact physAkSym_apply _

/-- **DEF-031 action on `H_k`:** the wave function of `A_kψ` is `ψ − Σⱼ ∂ⱼ²ψ` (weak). -/
theorem physUnitary_physAkH_eq_sub_sum (ψ : (physAkH L k).domain) (H : Fin k → L2TN L k)
    (hH : ∀ j, HasWeakSecondPartial j j
      (physUnitary ((ψ : physSector L k) : HilbertTensorPower ℂ (L2T L) k)) (H j)) :
    physUnitary ((physAkH L k ψ : physSector L k) : HilbertTensorPower ℂ (L2T L) k) =
      physUnitary ((ψ : physSector L k) : HilbertTensorPower ℂ (L2T L) k) - ∑ j, H j := by
  rw [physUnitary_physAkH]
  exact physAk_eq_sub_sum ⟨_, physUnitary_mem_physAk_domain ψ⟩ H hH

/-- **DEF-031 Fourier form on `H_k`:** `\widehat{A_kψ}(w) = (1 + Σⱼ(2πwⱼ/L)²) ψ̂(w)`. -/
theorem momUnitary_physUnitary_physAkH (ψ : (physAkH L k).domain) (w : Mom k) :
    (momUnitary L k (physUnitary ((physAkH L k ψ : physSector L k) :
        HilbertTensorPower ℂ (L2T L) k)) : Mom k → ℂ) w =
      (kinWeight L k w : ℂ) *
        (momUnitary L k (physUnitary ((ψ : physSector L k) :
          HilbertTensorPower ℂ (L2T L) k)) : Mom k → ℂ) w := by
  rw [physUnitary_physAkH, momUnitary_physAk]

/-! ## §3 Compact inverse -/

omit [Fact (0 < L)] in
theorem AkInv_eq_comp : AkInv L k = AhalfInv L k ∘L AhalfInv L k := by
  refine ContinuousLinearMap.ext fun x => ?_
  apply Subtype.ext; funext w
  show ((invCLM (kinWeight L k) (one_le_kinWeight L k) x : L2 (Mom k)) : Mom k → ℂ) w =
    ((invCLM (kinSqrt L k) (one_le_kinSqrt L k)
      (invCLM (kinSqrt L k) (one_le_kinSqrt L k) x) : L2 (Mom k)) : Mom k → ℂ) w
  rw [invCLM_apply, invCLM_apply, invCLM_apply, ← kinSqrt_sq]
  push_cast
  ring

/-- `A_k⁻¹` on `L²(𝕋_L^k)` is compact (`= (A_k^{-1/2})²`, frozen ContactOperator compactness). -/
theorem isCompactOperator_physAkInv : IsCompactOperator (physAkInv L k) := by
  have hA : IsCompactOperator (AkInv L k) := by
    rw [AkInv_eq_comp]
    exact (QuantumNLS.ContactOperator.isCompactOperator_AhalfInv (L := L) (N := k)).comp_clm
      (AhalfInv L k)
  exact (hA.comp_clm (momUnitary L k).toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
    (momUnitary L k).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- `A_k^{sym}⁻¹` on the symmetric sector is compact. -/
theorem isCompactOperator_physAkInvSym : IsCompactOperator (physAkInvSym L k) :=
  (isCompactOperator_physAkInv.comp_clm (symL2 L k).subtypeL).codRestrict _ isClosed_symL2

theorem physAkInv_physAk (F : (physAk L k).domain) : physAkInv L k (physAk L k F) = F := by
  apply (momUnitary L k).injective
  ext w
  rw [momUnitary_physAkInv, momUnitary_physAk]
  have h := m_ne_zero (one_le_kinWeight L k) w
  push_cast
  field_simp

/-- `A_k⁻¹` on `H_k`. -/
def physAkHInv (L : ℝ) [Fact (0 < L)] (k : ℕ) : physSector L k →L[ℂ] physSector L k :=
  (symSectorUnitary (L := L) (k := k)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    physAkInvSym L k ∘L (symSectorUnitary (L := L) (k := k)).toContinuousLinearEquiv.toContinuousLinearMap

/-- **`A_k⁻¹` is compact on `H_k`** (so `A_k` on `H_k` has compact resolvent at `0`). -/
theorem isCompactOperator_physAkHInv : IsCompactOperator (physAkHInv L k) :=
  (isCompactOperator_physAkInvSym.comp_clm
    (symSectorUnitary (L := L) (k := k)).toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
    (symSectorUnitary (L := L) (k := k)).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem physAkHInv_mem_domain (ψ : physSector L k) : physAkHInv L k ψ ∈ (physAkH L k).domain := by
  show symSectorUnitary (physAkHInv L k ψ) ∈ (physAkSym L k).domain
  show symSectorUnitary (symSectorUnitary.symm (physAkInvSym L k (symSectorUnitary ψ))) ∈ _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact physAkInv_mem_domain _

/-- `A_k (A_k⁻¹ ψ) = ψ` on `H_k`. -/
theorem physAkH_physAkHInv (ψ : physSector L k) :
    physAkH L k ⟨physAkHInv L k ψ, physAkHInv_mem_domain ψ⟩ = ψ := by
  apply symSectorUnitary.injective
  rw [physAkH_apply, LinearIsometryEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [physAkSym_apply]
  have e : ((symSectorUnitary (physAkHInv L k ψ) : symL2 L k) : L2TN L k) =
      physAkInv L k ((symSectorUnitary ψ : symL2 L k) : L2TN L k) := by
    show ((symSectorUnitary (symSectorUnitary.symm (physAkInvSym L k (symSectorUnitary ψ))) :
      symL2 L k) : L2TN L k) = _
    rw [LinearIsometryEquiv.apply_symm_apply]
    rfl
  have h := physAk_physAkInv ((symSectorUnitary ψ : symL2 L k) : L2TN L k)
  rw [← h]
  congr 1
  exact Subtype.ext e

/-- `A_k⁻¹ (A_k ψ) = ψ` on `D(A_k) ⊆ H_k`. -/
theorem physAkHInv_physAkH (ψ : (physAkH L k).domain) :
    physAkHInv L k (physAkH L k ψ) = ψ := by
  apply symSectorUnitary.injective
  apply Subtype.ext
  show ((symSectorUnitary (symSectorUnitary.symm (physAkInvSym L k
    (symSectorUnitary (physAkH L k ψ))))) : L2TN L k) = _
  rw [LinearIsometryEquiv.apply_symm_apply, coe_physAkInvSym, physAkH_apply,
    LinearIsometryEquiv.apply_symm_apply, physAkSym_apply, physAkInv_physAk]

/-- SA1's `symL2` is ContactOperator's `SymL2` (same permutation-invariant subspace). -/
theorem symL2_eq_SymL2 : symL2 L k = QuantumNLS.ContactOperator.SymL2 L k := by
  ext F
  rw [QuantumNLS.ContactOperator.mem_SymL2_iff]
  exact Iff.rfl

end QuantumNLS.SymmetricAkSpectrum

#print axioms QuantumNLS.SymmetricAkSpectrum.transportPMap_isSelfAdjoint
#print axioms QuantumNLS.SymmetricAkSpectrum.physAkH_isSelfAdjoint
#print axioms QuantumNLS.SymmetricAkSpectrum.mem_physAkH_domain_iff
#print axioms QuantumNLS.SymmetricAkSpectrum.physUnitary_physAkH
#print axioms QuantumNLS.SymmetricAkSpectrum.physUnitary_physAkH_eq_sub_sum
#print axioms QuantumNLS.SymmetricAkSpectrum.momUnitary_physUnitary_physAkH
#print axioms QuantumNLS.SymmetricAkSpectrum.isCompactOperator_physAkInvSym
#print axioms QuantumNLS.SymmetricAkSpectrum.isCompactOperator_physAkHInv
#print axioms QuantumNLS.SymmetricAkSpectrum.physAkH_physAkHInv
#print axioms QuantumNLS.SymmetricAkSpectrum.physAkHInv_physAkH
#print axioms QuantumNLS.SymmetricAkSpectrum.symL2_eq_SymL2
