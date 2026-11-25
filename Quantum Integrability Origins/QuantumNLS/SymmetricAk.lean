/-
QuantumNLS.SymmetricAk — the orthogonal symmetrizer on `L²(𝕋_L^k)`, closedness of the symmetric
sector, its identification with the DEF-004 physical symmetric sector, the reducing property of the
symmetrizer for `A_k`, and self-adjointness of `A_k` restricted to the symmetric sector
(owner: opus_tensor).

Source: DEF-004 (definitions.tex:25) `H_N = Sym^N L²(𝕋_L)`, `P_N = (N!)⁻¹ Σ_σ U_σ` orthogonal
projection; DEF-031 (:187) `A_k = 1 − Σ_{j≤k} ∂²_{x_j}`.

Reused frozen results (no duplicate carrier or projection): TensorCarrier 1b210cb0 (`symProj`,
`SymSector`, `symProj_eq_starProjection`), PhysicalTensor e774c776 (`physSector`, `physSymProj_eq`,
`physUnitary`, `physPerm`, `physEmbed_permRep`, `mem_physSector_iff`), PhysicalEnergy 01370715
(`physAk`, `isSelfAdjoint_of_inverse`, `momUnitary_physPerm`, `momUnitary_physAk`, `kinWeight_comp`,
`isSymm_iff_coeff`, `AkInv`), ProductPermutation PP1 b2f62828 (`symL2`, `physAkSym`,
`inner_physAkSym_comm`). No contact/Bethe/collision edits; no S2 decision; no dynamics claimed.

Results (all proved, standard axioms only):
* `symL2_eq_map`, `physUnitary_mem_symL2_iff`, `symSectorUnitary : physSector L k ≃ₗᵢ symL2 L k`
  — the position symmetric sector is exactly the `physUnitary` image of DEF-004's `H_k`.
* `isClosed_symL2` (hence complete, with orthogonal projection).
* `symProjL2 = (k!)⁻¹ Σ_σ V_σ`; `symProjL2_eq_conj` (`= physUnitary ∘ P_k ∘ physUnitary⁻¹`);
  **`symProjL2_eq_starProjection`** (it is the orthogonal projection onto `symL2`).
* Reducing projection: `symProjL2_mem_domain`, **`physAk_symProjL2`** (`P D(A_k) ⊆ D(A_k)`,
  `A_k P = P A_k` on `D(A_k)`).
* **`physAkSym_isSelfAdjoint`**: `A_k` restricted to the symmetric sector is self-adjoint;
  `physAkSym_surjective`, `norm_sq_le_re_inner_physAkSym` (`A_k^{sym} ≥ 1`).
-/
import QuantumNLS.ProductPermutation

open scoped InnerProductSpace ENNReal ComplexConjugate LinearPMap
open MeasureTheory QuantumNLS.TensorCarrier QuantumNLS.Fourier QuantumNLS.PhysicalTensor QuantumNLS.PhysicalEnergy
  QuantumNLS.Energy QuantumNLS.ProductWeakDerivatives QuantumNLS.ProductSecondDerivatives
  QuantumNLS.ProductPermutation

noncomputable section

namespace QuantumNLS.SymmetricAk

variable {L : ℝ} [Fact (0 < L)] {k : ℕ}

/-! ## The symmetric sector: identification and closedness -/

/-- `physUnitary ψ` is permutation invariant iff `ψ ∈ H_k = Sym^k L²(𝕋_L)` (DEF-004). -/
theorem physUnitary_mem_symL2_iff (ψ : HilbertTensorPower ℂ (L2T L) k) :
    physUnitary ψ ∈ symL2 L k ↔ ψ ∈ physSector L k :=
  (mem_physSector_iff ψ).symm

/-- **The position symmetric sector is the image of DEF-004's `H_k`.** -/
theorem symL2_eq_map :
    symL2 L k = (physSector L k).map
      ((physUnitary (L := L) (N := k)).toLinearEquiv : HilbertTensorPower ℂ (L2T L) k →ₗ[ℂ] L2TN L k) := by
  ext F
  constructor
  · intro hF
    refine ⟨physUnitary.symm F, ?_, physUnitary.apply_symm_apply F⟩
    exact (physUnitary_mem_symL2_iff _).1 (by rw [physUnitary.apply_symm_apply]; exact hF)
  · rintro ⟨ψ, hψ, rfl⟩
    exact (physUnitary_mem_symL2_iff ψ).2 hψ

/-- The symmetric sector is closed. -/
theorem isClosed_symL2 : IsClosed (symL2 L k : Set (L2TN L k)) := by
  have e : (symL2 L k : Set (L2TN L k)) =
      ⋂ σ : Equiv.Perm (Fin k), {F | physPerm σ F = F} := by
    ext F; simp only [Set.mem_iInter, Set.mem_ofPred_eq]; exact Iff.rfl
  rw [e]
  exact isClosed_iInter fun σ => isClosed_eq (physPerm σ).continuous continuous_id

instance : CompleteSpace (symL2 L k) := isClosed_symL2.completeSpace_coe

/-- **Unitary `H_k ≃ symL2`** (restriction of `physUnitary`). -/
def symSectorUnitary : physSector L k ≃ₗᵢ[ℂ] symL2 L k :=
  (physUnitary.submoduleMap (physSector L k)).trans
    (LinearIsometryEquiv.ofEq _ _ symL2_eq_map.symm)

theorem coe_symSectorUnitary (ψ : physSector L k) :
    ((symSectorUnitary ψ : symL2 L k) : L2TN L k) = physUnitary (ψ : HilbertTensorPower ℂ (L2T L) k) :=
  rfl

/-! ## The symmetrizer -/

/-- `P = (k!)⁻¹ Σ_σ V_σ` on `L²(𝕋_L^k)`. -/
def symProjL2 (L : ℝ) [Fact (0 < L)] (k : ℕ) : L2TN L k →L[ℂ] L2TN L k :=
  ((k.factorial : ℂ)⁻¹) • ∑ σ : Equiv.Perm (Fin k), (physPerm (L := L) σ).toContinuousLinearMap

theorem symProjL2_apply (F : L2TN L k) :
    symProjL2 L k F = ((k.factorial : ℂ)⁻¹) • ∑ σ : Equiv.Perm (Fin k), physPerm σ F := by
  simp [symProjL2]

/-- `P = physUnitary ∘ P_k ∘ physUnitary⁻¹` with the frozen tensor-side symmetrizer `P_k`. -/
theorem symProjL2_eq_conj (F : L2TN L k) :
    symProjL2 L k F = physUnitary (symProj ℂ (L2T L) k (physUnitary.symm F)) := by
  rw [(physSymProj_eq L k).2, symProjL2_apply]
  simp only [FunLike.coe_smul, Pi.smul_apply, FunLike.coe_sum, Finset.sum_apply, map_smul,
    map_sum]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  show physPerm σ F = physEmbed ((permRep ℂ (L2T L) k σ :
    HilbertTensorPower ℂ (L2T L) k →L[ℂ] HilbertTensorPower ℂ (L2T L) k) (physUnitary.symm F))
  rw [physEmbed_permRep]
  congr 1
  exact (physUnitary.apply_symm_apply F).symm

/-- **`P` is the orthogonal projection onto `symL2`.** -/
theorem symProjL2_eq_starProjection :
    symProjL2 L k = (Submodule.starProjection (symL2 L k) : L2TN L k →L[ℂ] L2TN L k) := by
  refine ContinuousLinearMap.ext fun F => ?_
  rw [symProjL2_eq_conj]
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := symL2 L k) ?_ fun w hw => ?_
  · rw [physUnitary_mem_symL2_iff, symProj_eq_starProjection]
    exact Submodule.starProjection_apply_mem _ _
  · rw [symL2_eq_map] at hw
    obtain ⟨ψ, hψ, rfl⟩ := hw
    have e : F = physUnitary (physUnitary.symm F) := (physUnitary.apply_symm_apply F).symm
    rw [e, ← map_sub]
    change ⟪physUnitary _, physUnitary ψ⟫_ℂ = 0
    rw [physUnitary.inner_map_map, physUnitary.symm_apply_apply, symProj_eq_starProjection]
    exact Submodule.starProjection_inner_eq_zero _ _ hψ

theorem symProjL2_mem (F : L2TN L k) : symProjL2 L k F ∈ symL2 L k := by
  rw [symProjL2_eq_starProjection]
  exact Submodule.starProjection_apply_mem _ _

theorem symProjL2_of_mem {F : L2TN L k} (hF : F ∈ symL2 L k) : symProjL2 L k F = F := by
  rw [symProjL2_eq_starProjection]
  exact Submodule.starProjection_eq_self_iff.2 hF

/-- Fourier side of the symmetrizer: `\widehat{PF}(w) = (k!)⁻¹ Σ_σ F̂(w∘σ)`. -/
theorem momUnitary_symProjL2 (F : L2TN L k) (w : Mom k) :
    (momUnitary L k (symProjL2 L k F) : Mom k → ℂ) w =
      ((k.factorial : ℂ)⁻¹) * ∑ σ : Equiv.Perm (Fin k), (momUnitary L k F : Mom k → ℂ) (w ∘ σ) := by
  rw [symProjL2_apply, map_smul, map_sum, lp.coeFn_smul, Pi.smul_apply, lp.coeFn_sum,
    Finset.sum_apply, smul_eq_mul]
  simp_rw [momUnitary_physPerm]

/-! ## Reducing property -/

/-- `P` maps `D(A_k)` into `D(A_k)`. -/
theorem symProjL2_mem_domain (F : (physAk L k).domain) :
    symProjL2 L k F ∈ (physAk L k).domain := by
  rw [symProjL2_apply]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun σ _ =>
    (physPerm_mem_physAk_domain_iff σ _).2 F.2)

/-- **`P` reduces `A_k`:** `A_k (P F) = P (A_k F)` for `F ∈ D(A_k)`. -/
theorem physAk_symProjL2 (F : (physAk L k).domain) :
    physAk L k ⟨symProjL2 L k F, symProjL2_mem_domain F⟩ = symProjL2 L k (physAk L k F) := by
  apply (momUnitary L k).injective
  ext w
  rw [momUnitary_physAk, momUnitary_symProjL2, momUnitary_symProjL2]
  simp_rw [momUnitary_physAk, kinWeight_comp]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

/-! ## Bounded inverse on the symmetric sector -/

/-- `A_k⁻¹` on `L²(𝕋_L^k)`, transported from the frozen momentum-side `AkInv`. -/
def physAkInv (L : ℝ) [Fact (0 < L)] (k : ℕ) : L2TN L k →L[ℂ] L2TN L k :=
  (momUnitary L k).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L AkInv L k ∘L
    (momUnitary L k).toContinuousLinearEquiv.toContinuousLinearMap

theorem physAkInv_apply (y : L2TN L k) :
    physAkInv L k y = (momUnitary L k).symm (AkInv L k (momUnitary L k y)) := rfl

theorem momUnitary_physAkInv (y : L2TN L k) (w : Mom k) :
    (momUnitary L k (physAkInv L k y) : Mom k → ℂ) w =
      ((kinWeight L k w)⁻¹ : ℝ) * (momUnitary L k y : Mom k → ℂ) w := by
  rw [physAkInv_apply, LinearIsometryEquiv.apply_symm_apply]
  exact invCLM_apply (one_le_kinWeight L k) _ w

theorem physAkInv_mem_domain (y : L2TN L k) : physAkInv L k y ∈ (physAk L k).domain := by
  show momUnitary L k (physAkInv L k y) ∈ (Ak L k).domain
  rw [physAkInv_apply, LinearIsometryEquiv.apply_symm_apply]
  exact invCLM_mem (one_le_kinWeight L k) _

theorem physAk_physAkInv (y : L2TN L k) :
    physAk L k ⟨physAkInv L k y, physAkInv_mem_domain y⟩ = y := by
  apply (momUnitary L k).injective
  ext w
  rw [momUnitary_physAk, momUnitary_physAkInv]
  have h := (m_ne_zero (one_le_kinWeight L k) w)
  push_cast
  field_simp

theorem inner_physAkInv (x y : L2TN L k) :
    ⟪physAkInv L k x, y⟫_ℂ = ⟪x, physAkInv L k y⟫_ℂ := by
  rw [← (momUnitary L k).inner_map_map, ← (momUnitary L k).inner_map_map x, physAkInv_apply,
    physAkInv_apply, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  exact inner_invCLM (one_le_kinWeight L k) _ _

theorem physAkInv_mem_symL2 {y : L2TN L k} (hy : y ∈ symL2 L k) : physAkInv L k y ∈ symL2 L k := by
  rw [mem_symL2_iff, isSymm_iff_coeff]
  intro σ w
  rw [momUnitary_physAkInv, momUnitary_physAkInv, kinWeight_comp,
    ((isSymm_iff_coeff y).1 hy) σ w]

/-- `A_k⁻¹` restricted to the symmetric sector. -/
def physAkInvSym (L : ℝ) [Fact (0 < L)] (k : ℕ) : symL2 L k →L[ℂ] symL2 L k :=
  ((physAkInv L k).comp (symL2 L k).subtypeL).codRestrict (symL2 L k)
    fun y => physAkInv_mem_symL2 y.2

theorem coe_physAkInvSym (y : symL2 L k) :
    ((physAkInvSym L k y : symL2 L k) : L2TN L k) = physAkInv L k (y : L2TN L k) := rfl

/-! ## Self-adjointness on the symmetric sector -/

/-- **`A_k` restricted to the symmetric sector is self-adjoint.** -/
theorem physAkSym_isSelfAdjoint : IsSelfAdjoint (physAkSym L k) := by
  refine isSelfAdjoint_of_inverse (physAkSym L k) (physAkInvSym L k) ?_ ?_ ?_ ?_
  · intro x y
    rw [Submodule.coe_inner, Submodule.coe_inner, coe_physAkInvSym, coe_physAkInvSym]
    exact inner_physAkInv _ _
  · intro y
    exact physAkInv_mem_domain (y : L2TN L k)
  · intro y
    apply Subtype.ext
    rw [physAkSym_apply]
    exact physAk_physAkInv (y : L2TN L k)
  · exact inner_physAkSym_comm

/-- `A_k^{sym}` is onto the symmetric sector. -/
theorem physAkSym_surjective (y : symL2 L k) :
    ∃ x : (physAkSym L k).domain, physAkSym L k x = y :=
  ⟨⟨physAkInvSym L k y, physAkInv_mem_domain (y : L2TN L k)⟩,
    Subtype.ext (physAk_physAkInv (y : L2TN L k))⟩

/-- `A_k^{sym} ≥ 1`: `‖F‖² ≤ Re⟪F, A_k^{sym}F⟫`. -/
theorem norm_sq_le_re_inner_physAkSym (x : (physAkSym L k).domain) :
    ‖(x : symL2 L k)‖ ^ 2 ≤ RCLike.re ⟪(x : symL2 L k), physAkSym L k x⟫_ℂ := by
  set F : (physAk L k).domain := ⟨((x : symL2 L k) : L2TN L k), x.2⟩
  show ‖(F : L2TN L k)‖ ^ 2 ≤ RCLike.re ⟪(F : L2TN L k), physAk L k F⟫_ℂ
  rw [inner_physAk_self, RCLike.re_to_complex, Complex.ofReal_re]
  exact norm_sq_le_physAk F

end QuantumNLS.SymmetricAk

#print axioms QuantumNLS.SymmetricAk.symL2_eq_map
#print axioms QuantumNLS.SymmetricAk.isClosed_symL2
#print axioms QuantumNLS.SymmetricAk.symSectorUnitary
#print axioms QuantumNLS.SymmetricAk.symProjL2_eq_conj
#print axioms QuantumNLS.SymmetricAk.symProjL2_eq_starProjection
#print axioms QuantumNLS.SymmetricAk.physAk_symProjL2
#print axioms QuantumNLS.SymmetricAk.physAkSym_isSelfAdjoint
#print axioms QuantumNLS.SymmetricAk.physAkSym_surjective
#print axioms QuantumNLS.SymmetricAk.norm_sq_le_re_inner_physAkSym
