import Mathlib
import QuantumNLS.RootOverlapCommutator

/-!
# R-F9AB39A7 `QG:lem:haar-offgrid-bessel`: square-sum bounds survive placements

(`QUANTUM_GAUGE_COMPONENTS.tex:664-669`: "If operators `C_n` satisfy `∑ C_n^*C_n ≤ b²·1`, then any common convex average of
their placements has the same vector square-sum bound".)  Generic complex Hilbert space `H`; finite families.

* `htmap_sqsum`: if `∑_m ‖T_m x‖² ≤ B²‖x‖²` on `E` then `∑_m ‖(T_m ⊗̂ 1) y‖² ≤ B²‖y‖²` on `E ⊗̂ G`
  (the operator `B² - ∑ T_m^*T_m` is positive, hence `R^*R` (C*-algebra), and `T ↦ T ⊗̂ 1` is a *-homomorphism);
* `rawSubsetPlacement_sqsum`: the same for every actual placement `rawSubsetPlacement N p hp S (A_m)` on the
  `N`-fold tensor power (permutation and slot-cast conjugates are isometries).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open scoped InnerProductSpace ComplexConjugate BigOperators TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements QuantumNLS.KernelDefinition
  QuantumNLS.PlacementFusion QuantumNLS.PlacementGrouping QuantumNLS.RootOverlapCommutator

namespace QuantumNLS.PlacementSquareSum

section Htmap

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem htmap_id_eq : htmap (ContinuousLinearMap.id ℂ E) (ContinuousLinearMap.id ℂ G) =
    ContinuousLinearMap.id ℂ (HilbertTensor ℂ E G) := by
  ext z
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq
        (htmap (ContinuousLinearMap.id ℂ E) (ContinuousLinearMap.id ℂ G)).continuous
        (ContinuousLinearMap.id ℂ _).continuous
  | ih a =>
      simp [htmap, TensorProduct.mapL_id_id]

/-- Ampliation `T ↦ T ⊗̂ 1_G`. -/
abbrev amp (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (T : E →L[ℂ] E) : HilbertTensor ℂ E G →L[ℂ] HilbertTensor ℂ E G :=
  htmap T (ContinuousLinearMap.id ℂ G)

theorem amp_comp (S T : E →L[ℂ] E) : amp G (S ∘L T) = amp G S ∘L amp G T := by
  have := htmap_comp S T (ContinuousLinearMap.id ℂ G) (ContinuousLinearMap.id ℂ G)
  rw [ContinuousLinearMap.id_comp] at this
  exact this

theorem amp_adjoint (T : E →L[ℂ] E) :
    ContinuousLinearMap.adjoint (amp G T) = amp G (ContinuousLinearMap.adjoint T) := by
  unfold amp
  rw [adjoint_htmap, ContinuousLinearMap.adjoint_id]

theorem amp_id : amp G (ContinuousLinearMap.id ℂ E) = ContinuousLinearMap.id ℂ _ := htmap_id_eq

theorem amp_sum {ι' : Type*} (F : Finset ι') (T : ι' → E →L[ℂ] E) :
    amp G (∑ m ∈ F, T m) = ∑ m ∈ F, amp G (T m) :=
  map_sum (ampliate ℂ E G) T F

theorem amp_smul (c : ℂ) (T : E →L[ℂ] E) : amp G (c • T) = c • amp G T :=
  htmap_smul_left c T _

theorem amp_sub (S T : E →L[ℂ] E) : amp G (S - T) = amp G S - amp G T :=
  map_sub (ampliate ℂ E G) S T

/-- **Square-sum bounds survive tensoring with the identity.** -/
theorem htmap_sqsum {ι' : Type*} (F : Finset ι') (T : ι' → E →L[ℂ] E) {B : ℝ}
    (hB : ∀ x : E, ∑ m ∈ F, ‖T m x‖ ^ 2 ≤ B ^ 2 * ‖x‖ ^ 2) (y : HilbertTensor ℂ E G) :
    ∑ m ∈ F, ‖amp G (T m) y‖ ^ 2 ≤ B ^ 2 * ‖y‖ ^ 2 := by
  set M : E →L[ℂ] E := ((B ^ 2 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ E -
    ∑ m ∈ F, (ContinuousLinearMap.adjoint (T m)) ∘L (T m) with hM
  have hMx : ∀ x : E, ⟪M x, x⟫_ℂ = ((B ^ 2 * ‖x‖ ^ 2 - ∑ m ∈ F, ‖T m x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    have e1 : M x = ((B ^ 2 : ℝ) : ℂ) • x - ∑ m ∈ F, ContinuousLinearMap.adjoint (T m) (T m x) := by
      rw [hM]
      simp [ContinuousLinearMap.sum_apply]
    have e2 : ∀ m, ⟪ContinuousLinearMap.adjoint (T m) (T m x), x⟫_ℂ = ((‖T m x‖ ^ 2 : ℝ) : ℂ) := by
      intro m
      rw [ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K]
      push_cast <;> rfl
    rw [e1, inner_sub_left, inner_smul_left, sum_inner, inner_self_eq_norm_sq_to_K]
    simp only [e2, Complex.conj_ofReal]
    push_cast <;> rfl
  have hMpos : 0 ≤ M := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
    intro x
    have h1 := hMx x
    have h2 : 0 ≤ B ^ 2 * ‖x‖ ^ 2 - ∑ m ∈ F, ‖T m x‖ ^ 2 := by linarith [hB x]
    generalize hr : B ^ 2 * ‖x‖ ^ 2 - ∑ m ∈ F, ‖T m x‖ ^ 2 = r at h1 h2
    rw [h1]
    exact ⟨by simp, by simpa using h2⟩
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hMpos
  have hR' : M = ContinuousLinearMap.adjoint R ∘L R := hR
  have e1 : amp G M = ((B ^ 2 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ _ -
      ∑ m ∈ F, ContinuousLinearMap.adjoint (amp G (T m)) ∘L amp G (T m) := by
    rw [hM, amp_sub, amp_smul, amp_id, amp_sum]
    congr 1
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [amp_comp, amp_adjoint]
  have e2 : amp G M = ContinuousLinearMap.adjoint (amp G R) ∘L amp G R := by
    rw [hR', amp_comp, amp_adjoint]
  have e3 : ⟪y, amp G M y⟫_ℂ = ((B ^ 2 * ‖y‖ ^ 2 - ∑ m ∈ F, ‖amp G (T m) y‖ ^ 2 : ℝ) : ℂ) := by
    rw [e1]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
      inner_sub_right, inner_smul_right, inner_sum, ← ContinuousLinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K]
    push_cast
    simp [ContinuousLinearMap.adjoint_inner_right]
  have e4 : ⟪y, amp G M y⟫_ℂ = ((‖amp G R y‖ ^ 2 : ℝ) : ℂ) := by
    rw [e2]
    simp only [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    push_cast <;> rfl
  have := e3.symm.trans e4
  have h5 : B ^ 2 * ‖y‖ ^ 2 - ∑ m ∈ F, ‖amp G (T m) y‖ ^ 2 = ‖amp G R y‖ ^ 2 := by
    exact_mod_cast this
  nlinarith [sq_nonneg ‖amp G R y‖]

end Htmap

section Placement

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem extend_sqsum {p : ℕ} {ι' : Type*} (F : Finset ι')
    (A : ι' → SymSector ℂ H p →L[ℂ] SymSector ℂ H p) {B : ℝ}
    (hB : ∀ x : SymSector ℂ H p, ∑ m ∈ F, ‖A m x‖ ^ 2 ≤ B ^ 2 * ‖x‖ ^ 2)
    (z : HilbertTensorPower ℂ H p) :
    ∑ m ∈ F, ‖extendSymKernel (A m) z‖ ^ 2 ≤ B ^ 2 * ‖z‖ ^ 2 := by
  have hproj : ‖symProjToSector (H := H) p z‖ ≤ ‖z‖ := by
    change ‖symProj ℂ H p z‖ ≤ ‖z‖
    rw [symProj_eq_starProjection]
    exact (SymSector ℂ H p).norm_starProjection_apply_le z
  have h1 := hB (symProjToSector p z)
  have h2 : B ^ 2 * ‖symProjToSector (H := H) p z‖ ^ 2 ≤ B ^ 2 * ‖z‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hproj 2) (by positivity)
  refine le_trans (le_of_eq ?_) (h1.trans h2)
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rfl

theorem firstPlacement_sqsum {p q : ℕ} {ι' : Type*} (F : Finset ι')
    (A : ι' → SymSector ℂ H p →L[ℂ] SymSector ℂ H p) {B : ℝ}
    (hB : ∀ x : SymSector ℂ H p, ∑ m ∈ F, ‖A m x‖ ^ 2 ≤ B ^ 2 * ‖x‖ ^ 2)
    (x : HilbertTensorPower ℂ H (p + q)) :
    ∑ m ∈ F, ‖firstPlacement (q := q) (A m) x‖ ^ 2 ≤ B ^ 2 * ‖x‖ ^ 2 := by
  let e : HilbertTensorPower ℂ H (p + q) ≃ₗᵢ[ℂ]
      HilbertTensor ℂ (HilbertTensorPower ℂ H p) (HilbertTensorPower ℂ H q) := splitIsometry p q
  have hterm : ∀ m, ‖firstPlacement (q := q) (A m) x‖ =
      ‖amp (HilbertTensorPower ℂ H q) (extendSymKernel (A m)) (e x)‖ := by
    intro m
    show ‖e.symm (htmap (𝕜 := ℂ) (extendSymKernel (A m)) (ContinuousLinearMap.id ℂ
      (HilbertTensorPower ℂ H q)) (e x))‖ = _
    exact e.symm.norm_map _
  simp only [hterm]
  have := htmap_sqsum (G := HilbertTensorPower ℂ H q) F (fun m => extendSymKernel (A m))
    (fun z => extend_sqsum F A hB z) (e x)
  rw [e.norm_map] at this
  exact this

theorem permutedPlacement_sqsum {p q : ℕ} {ι' : Type*} (F : Finset ι') (σ : Equiv.Perm (Fin (p + q)))
    (A : ι' → SymSector ℂ H p →L[ℂ] SymSector ℂ H p) {B : ℝ}
    (hB : ∀ x : SymSector ℂ H p, ∑ m ∈ F, ‖A m x‖ ^ 2 ≤ B ^ 2 * ‖x‖ ^ 2)
    (x : HilbertTensorPower ℂ H (p + q)) :
    ∑ m ∈ F, ‖permutedPlacement σ (A m) x‖ ^ 2 ≤ B ^ 2 * ‖x‖ ^ 2 := by
  let u := permHilbertIsometry (𝕜 := ℂ) (E := H) σ
  let ui := permHilbertIsometry (𝕜 := ℂ) (E := H) σ⁻¹
  have hterm : ∀ m, ‖permutedPlacement σ (A m) x‖ = ‖firstPlacement (q := q) (A m) (ui x)‖ := by
    intro m
    show ‖(permRep ℂ H (p + q) σ : HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q))
        (firstPlacement (q := q) (A m) ((permRep ℂ H (p + q) σ⁻¹ :
        HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q)) x))‖ = _
    rw [permRep_apply, permRep_apply]
    exact u.norm_map _
  simp only [hterm]
  have := firstPlacement_sqsum (q := q) F A hB (ui x)
  rw [ui.norm_map] at this
  exact this

theorem rawSubsetPlacement_sqsum (N p : ℕ) (hp : p ≤ N) (S : PlacementSubset p (N - p))
    {ι' : Type*} (F : Finset ι') (A : ι' → BoundedSymmetricKernel H p) {B : ℝ}
    (hB : ∀ x : SymSector ℂ H p, ∑ m ∈ F, ‖A m x‖ ^ 2 ≤ B ^ 2 * ‖x‖ ^ 2)
    (φ : HilbertTensorPower ℂ H N) :
    ∑ m ∈ F, ‖rawSubsetPlacement N p hp S (A m) φ‖ ^ 2 ≤ B ^ 2 * ‖φ‖ ^ 2 := by
  have hterm : ∀ m, ‖rawSubsetPlacement N p hp S (A m) φ‖ =
      ‖subsetPlacement S (A m) ((cIso (Nat.add_sub_of_le hp)).symm φ)‖ := by
    intro m
    unfold rawSubsetPlacement
    rw [castTensorOperator_eq_conj]
    exact (cIso (Nat.add_sub_of_le hp)).norm_map _
  simp only [hterm]
  have := permutedPlacement_sqsum (q := N - p) F (subsetRepresentative S) A hB
    ((cIso (Nat.add_sub_of_le hp)).symm φ)
  rw [(cIso (Nat.add_sub_of_le hp)).symm.norm_map] at this
  exact this

end Placement

#print axioms rawSubsetPlacement_sqsum

end QuantumNLS.PlacementSquareSum
