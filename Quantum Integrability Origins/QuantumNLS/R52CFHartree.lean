import QuantumNLS.Prop001RfourteenIdentification
import QuantumNLS.BethePhysicalTransfer
import QuantumNLS.Ext025A8SourceHartree
import QuantumNLS.SymplecticBracket

/-!
# R-52CF5DA1 stage 3: the Hartree field of bounded interaction kernels is the Hamiltonian field of their coherent energy

`prop:audit-finite-count-propagation` (GAUGE_RETARGETING.tex:101), proof paragraph "The limiting Hamiltonian is the
corresponding linear functional of the classical transfer with denominator frozen at `v`": the classical flow
produced by the accepted bounded-interaction propagation theorem (PROP-001, `Ext025A8.sourceHartreeField`) is the
Hamiltonian flow (DEF-015 convention `X_F = -i∇F`, `dF(u)[h] = 2 Re⟨∇F(u), h⟩`) of the coherent energy
`E_A(u) = Σ_n Re ⟨u^{⊗(n+1)}, A_n u^{⊗(n+1)}⟩` of the kernels.

Generic complex Hilbert space `H`.  For self-adjoint bounded symmetric kernels `A_n` on `Sym^{n+1} H` with
`Σ (n+1) ‖A_n‖ S^{2n+1} < ∞` and `‖u‖ < S`:
* `cohTerm_hasFDerivAt`: `d Re⟨u^{⊗r}, A u^{⊗r}⟩ [h] = 2 Re⟨r J(u)^*A u^{⊗r}, h⟩` (all slots of the symmetric vector
  `A u^{⊗r}` contribute equally);
* **`hamField_coh_eq`**: `E_A` is Fréchet differentiable at `u` and `X_{E_A}(u) = sourceHartreeField A u`.
No hypothesis beyond the stated kernel data is used; all inherited modules are read-only.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable section
open Set Filter Topology Metric
open scoped BigOperators InnerProductSpace

attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.R52CFHartree

open TensorCarrier TensorPlacements Ext025A8 KernelDefinition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem symProj_htpow (r : ℕ) (u : H) :
    symProjToSector r (htpow r u : HilbertTensorPower ℂ H r) = ⟨htpow r u, htpow_mem_symSector r u⟩ := by
  apply Subtype.ext
  change symProj ℂ H r (htpow r u : HilbertTensorPower ℂ H r) = htpow r u
  rw [symProj_eq_starProjection]
  exact (Submodule.starProjection_eq_self_iff (K := SymSector ℂ H r)).mpr (htpow_mem_symSector r u)

theorem kernelProductSymbol_eq {r : ℕ} (A : BoundedSymmetricKernel H r) (u : H) :
    kernelProductSymbol A u =
      ⟪(htpow r u : HilbertTensorPower ℂ H r), extendSymKernel A (htpow r u)⟫_ℂ := by
  unfold kernelProductSymbol extendSymKernel
  simp only [ContinuousLinearMap.comp_apply, symProj_htpow]
  rfl

/-- The real derivative of the coherent tensor `u ↦ u^{⊗r}`. -/
theorem htpow_hasFDerivAt (r : ℕ) (u : H) :
    HasFDerivAt (fun v : H => (htpow r v : HilbertTensorPower ℂ H r))
      ((Prop001RfourteenIdentification.velocityMap r u).restrictScalars ℝ) u := by
  have h1 := ((tensorMultilinear (H := H) r).hasFDerivAt (fun _ => u)).comp u
    (ContinuousLinearMap.pi (fun _ : Fin r => ContinuousLinearMap.id ℂ H)).hasFDerivAt
  exact h1.restrictScalars ℝ

/-- A symmetric vector pairs equally with every slot of a one-slot variation. -/
theorem inner_sym_slot (n : ℕ) (y : HilbertTensorPower ℂ H (n + 1)) (hy : y ∈ SymSector ℂ H (n + 1))
    (u h : H) (j : Fin (n + 1)) :
    ⟪y, tensorMultilinear (n + 1) (Function.update (fun _ => u) j h)⟫_ℂ =
      ⟪y, insertFirst n u h⟫_ℂ := by
  have hperm : tensorMultilinear (n + 1) (Function.update (fun _ => u) j h) =
      (permRep ℂ H (n + 1) (Equiv.swap 0 j) : HilbertTensorPower ℂ H (n + 1) →L[ℂ] _)
        (tensorMultilinear (n + 1) (Fin.cons h (fun _ : Fin n => u))) := by
    change RootOverlapCommutator.ptC (Function.update (fun _ => u) j h) =
      (permRep ℂ H (n + 1) (Equiv.swap 0 j) : HilbertTensorPower ℂ H (n + 1) →L[ℂ] _)
        (RootOverlapCommutator.ptC (Fin.cons h (fun _ : Fin n => u)))
    rw [RootOverlapCommutator.permRep_ptC]
    congr 1
    funext i
    rw [Equiv.symm_swap]
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self, Equiv.swap_apply_right]
      rfl
    · rw [Function.update_of_ne hij]
      by_cases hi0 : i = 0
      · subst hi0
        rw [Equiv.swap_apply_left]
        obtain ⟨k, hk⟩ := Fin.exists_succ_eq.mpr (Ne.symm hij)
        rw [← hk]
        rfl
      · rw [Equiv.swap_apply_of_ne_of_ne hi0 hij]
        obtain ⟨k, hk⟩ := Fin.exists_succ_eq.mpr hi0
        rw [← hk]
        rfl
  rw [hperm, Prop001RfourteenContraction.inner_perm]
  have hfix := hy (Equiv.swap 0 j)⁻¹
  change (permRep ℂ H (n + 1) (Equiv.swap 0 j)⁻¹ : HilbertTensorPower ℂ H (n + 1) →L[ℂ] _) y = y at hfix
  rw [hfix]
  rfl

/-- The coherent value of one kernel. -/
def cohTerm {n : ℕ} (A : BoundedSymmetricKernel H (n + 1)) (u : H) : ℝ := (kernelProductSymbol A u).re

/-- Its derivative functional `h ↦ 2 Re⟨r J(u)^* A u^{⊗r}, h⟩`. -/
def cohD {n : ℕ} (A : BoundedSymmetricKernel H (n + 1)) (u : H) : H →L[ℝ] ℝ :=
  (2 : ℝ) • innerSL ℝ (((n + 1 : ℕ) : ℂ) • hartreeContraction (extendSymKernel A) u u)

theorem cohTerm_hasFDerivAt {n : ℕ} (A : BoundedSymmetricKernel H (n + 1)) (hA : IsSelfAdjoint A) (u : H) :
    HasFDerivAt (cohTerm A) (cohD A u) u := by
  set B := extendSymKernel A with hB
  have hBsa : B.adjoint = B := by
    rw [hB, BethePhysicalTransfer.extendSymKernel_adjoint, show A.adjoint = A from hA]
  have hx := htpow_hasFDerivAt (H := H) (n + 1) u
  have hBx := (B.restrictScalars ℝ).hasFDerivAt.comp u hx
  have hin := hx.inner ℂ hBx
  have hre := Complex.reCLM.hasFDerivAt.comp u hin
  refine (hre.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)).congr_fderiv ?_
  · simp only [Function.comp_apply, cohTerm, kernelProductSymbol_eq, Complex.reCLM_apply,
      ContinuousLinearMap.coe_restrictScalars']
    rfl
  ext h
  change ((⟪(htpow (n + 1) u : HilbertTensorPower ℂ H (n + 1)),
      B (Prop001RfourteenIdentification.velocityMap (n + 1) u h)⟫_ℂ +
    ⟪Prop001RfourteenIdentification.velocityMap (n + 1) u h,
      B (htpow (n + 1) u : HilbertTensorPower ℂ H (n + 1))⟫_ℂ).re) = cohD A u h
  set x : HilbertTensorPower ℂ H (n + 1) := htpow (n + 1) u with hxdef
  set V := Prop001RfourteenIdentification.velocityMap (n + 1) u h with hVdef
  have h1 : ⟪x, B V⟫_ℂ = ⟪B x, V⟫_ℂ := by
    have e := ContinuousLinearMap.adjoint_inner_left B V x
    rw [hBsa] at e
    exact e.symm
  have hsym : B x ∈ SymSector ℂ H (n + 1) := by
    rw [hB]
    exact (A (symProjToSector (n + 1) x)).2
  have h2 : ⟪B x, V⟫_ℂ = ((n + 1 : ℕ) : ℂ) * ⟪B x, insertFirst n u h⟫_ℂ := by
    have e1 : V = ∑ j : Fin (n + 1), tensorMultilinear (n + 1) (Function.update (fun _ => u) j h) :=
      Prop001.tensorVelocity_eq_sum (n + 1) u h
    have e2 := inner_sum (𝕜 := ℂ) Finset.univ
      (fun j : Fin (n + 1) => tensorMultilinear (n + 1) (Function.update (fun _ => u) j h)) (B x)
    calc ⟪B x, V⟫_ℂ
        = ⟪B x, ∑ j : Fin (n + 1), tensorMultilinear (n + 1) (Function.update (fun _ => u) j h)⟫_ℂ := by
          rw [e1]
      _ = ∑ j : Fin (n + 1), ⟪B x, tensorMultilinear (n + 1) (Function.update (fun _ => u) j h)⟫_ℂ := e2
      _ = ∑ _j : Fin (n + 1), ⟪B x, insertFirst n u h⟫_ℂ :=
          Finset.sum_congr rfl (fun j _ => inner_sym_slot n (B x) hsym u h j)
      _ = ((n + 1 : ℕ) : ℂ) * ⟪B x, insertFirst n u h⟫_ℂ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h3 : ⟪B x, insertFirst n u h⟫_ℂ = ⟪hartreeContraction B u u, h⟫_ℂ := by
    have e := ContinuousLinearMap.adjoint_inner_left (insertFirst n u) h (B (insertFirst n u u))
    have hx : x = insertFirst n u u := (insertFirst_self n u).symm
    rw [hx]
    exact e.symm
  have h4 : (⟪V, B x⟫_ℂ).re = (⟪B x, V⟫_ℂ).re :=
    (Complex.conj_re _).symm.trans (congrArg Complex.re (inner_conj_symm (𝕜 := ℂ) (B x) V))
  have key : (⟪x, B V⟫_ℂ + ⟪V, B x⟫_ℂ).re =
      2 * (((n + 1 : ℕ) : ℝ) * (⟪hartreeContraction B u u, h⟫_ℂ).re) := by
    rw [Complex.add_re, h1, h4, h2, h3]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    ring
  rw [key]
  unfold cohD
  rw [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul,
    ← SymplecticBracket.re_inner_coord, inner_smul_left]
  simp only [Complex.conj_natCast, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul,
    sub_zero]
  rfl

theorem cohD_norm_le {n : ℕ} (A : BoundedSymmetricKernel H (n + 1)) (u : H) :
    ‖cohD A u‖ ≤ 2 * ((n + 1 : ℕ) * ‖A‖ * ‖u‖ ^ (2 * n + 1)) := by
  unfold cohD
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), innerSL_apply_norm]
  gcongr
  calc ‖(((n + 1 : ℕ) : ℂ) • hartreeContraction (extendSymKernel A) u u)‖
      = (n + 1 : ℕ) * ‖hartreeContraction (extendSymKernel A) u u‖ := by
        rw [norm_smul, Complex.norm_natCast]
    _ ≤ (n + 1 : ℕ) * (‖extendSymKernel A‖ * ‖u‖ ^ (2 * n) * ‖u‖) := by
        gcongr
        exact ((hartreeContraction (extendSymKernel A) u).le_opNorm u).trans
          (mul_le_mul_of_nonneg_right (hartreeContraction_norm _ u) (norm_nonneg _))
    _ = (n + 1 : ℕ) * (‖extendSymKernel A‖ * (‖u‖ ^ (2 * n) * ‖u‖)) := by ring
    _ ≤ (n + 1 : ℕ) * (‖A‖ * (‖u‖ ^ (2 * n) * ‖u‖)) := by
        gcongr
        exact norm_extendSymKernel_le A
    _ = (n + 1 : ℕ) * ‖A‖ * ‖u‖ ^ (2 * n + 1) := by rw [pow_succ]; ring

theorem cohTerm_abs_le {n : ℕ} (A : BoundedSymmetricKernel H (n + 1)) (u : H) :
    |cohTerm A u| ≤ ‖A‖ * ‖u‖ ^ (2 * (n + 1)) := by
  unfold cohTerm
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [kernelProductSymbol_eq]
  refine (norm_inner_le_norm _ _).trans ?_
  rw [norm_htpow]
  have h1 := (extendSymKernel A).le_opNorm (htpow (n + 1) u : HilbertTensorPower ℂ H (n + 1))
  rw [norm_htpow] at h1
  have h2 := norm_extendSymKernel_le A
  calc ‖u‖ ^ (n + 1) * ‖extendSymKernel A (htpow (n + 1) u)‖
      ≤ ‖u‖ ^ (n + 1) * (‖extendSymKernel A‖ * ‖u‖ ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ ‖u‖ ^ (n + 1) * (‖A‖ * ‖u‖ ^ (n + 1)) := by gcongr
    _ = ‖A‖ * ‖u‖ ^ (2 * (n + 1)) := by ring

/-- The coherent energy `E_A(u) = Σ_n Re⟨u^{⊗(n+1)}, A_n u^{⊗(n+1)}⟩`. -/
def coh (A : ∀ n : ℕ, BoundedSymmetricKernel H (n + 1)) (u : H) : ℝ := ∑' n, cohTerm (A n) u

/-- **Stage 3 headline.**  On the ball `‖u‖ < S`, with `Σ (n+1)‖A_n‖ S^{2n+1} < ∞`, the coherent energy is
differentiable and its Hamiltonian vector field is the PROP-001 source Hartree field. -/
theorem hamField_coh_eq (A : ∀ n : ℕ, BoundedSymmetricKernel H (n + 1)) (hA : ∀ n, IsSelfAdjoint (A n))
    {S : ℝ} (hS : 0 < S) (hsum : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ‖A n‖ * S ^ (2 * n + 1)))
    (u : H) (hu : ‖u‖ < S) :
    HasFDerivAt (coh A) (∑' n, cohD (A n) u) u ∧
      SymplecticBracket.hamField (coh A) u = sourceHartreeField A u := by
  have hball : u ∈ ball (0 : H) S := mem_ball_zero_iff.mpr hu
  have hsum2 : Summable (fun n : ℕ => 2 * (((n + 1 : ℕ) : ℝ) * ‖A n‖ * S ^ (2 * n + 1))) := hsum.mul_left 2
  have hbound : ∀ n x, x ∈ ball (0 : H) S → ‖cohD (A n) x‖ ≤ 2 * (((n + 1 : ℕ) : ℝ) * ‖A n‖ * S ^ (2 * n + 1)) := by
    intro n x hx
    refine (cohD_norm_le (A n) x).trans ?_
    have hx' := (mem_ball_zero_iff.mp hx).le
    gcongr
  have hz : ∀ n, cohTerm (A n) (0 : H) = 0 := by
    intro n
    have h := cohTerm_abs_le (A n) (0 : H)
    rw [norm_zero, zero_pow (by omega), mul_zero] at h
    exact abs_nonpos_iff.mp h
  have h0 : Summable (fun n => cohTerm (A n) (0 : H)) := by
    simp only [hz]
    exact summable_zero
  have hD : HasFDerivAt (coh A) (∑' n, cohD (A n) u) u :=
    hasFDerivAt_tsum_of_isPreconnected hsum2 isOpen_ball (convex_ball (0 : H) S).isPreconnected
      (fun n x _ => cohTerm_hasFDerivAt (A n) (hA n) x) hbound (mem_ball_self hS) h0 hball
  refine ⟨hD, ?_⟩
  -- the summed Hartree vector
  have hTs : Summable (fun n => hartreeTerm (fun m => extendSymKernel (A m)) n u) := by
    apply Summable.of_norm_bounded hsum
    intro n
    refine (hartreeTerm_norm _ n u).trans ?_
    have hx := hu.le
    gcongr
    exact norm_extendSymKernel_le _
  have hDs : Summable (fun n => cohD (A n) u) :=
    Summable.of_norm_bounded hsum2 (fun n => hbound n u hball)
  have hval : ∀ h : H, (∑' n, cohD (A n) u) h =
      2 * inner ℝ (∑' n, hartreeTerm (fun m => extendSymKernel (A m)) n u) h := by
    intro h
    have hap := (ContinuousLinearMap.apply ℝ ℝ h).map_tsum hDs
    simp only [ContinuousLinearMap.apply_apply] at hap
    rw [hap]
    have he : ∀ n, cohD (A n) u h = 2 * inner ℝ (hartreeTerm (fun m => extendSymKernel (A m)) n u) h := by
      intro n
      unfold cohD hartreeTerm
      rw [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
    simp_rw [he]
    rw [tsum_mul_left]
    congr 1
    have hm := (innerSL ℝ h).map_tsum hTs
    simp only [innerSL_apply_apply] at hm
    rw [real_inner_comm, hm]
    exact tsum_congr fun n => real_inner_comm _ _
  have hgrad : SymplecticBracket.gradient (coh A) u = ∑' n, hartreeTerm (fun m => extendSymKernel (A m)) n u := by
    unfold SymplecticBracket.gradient
    rw [hD.fderiv]
    have hdual : (∑' n, cohD (A n) u) =
        InnerProductSpace.toDual ℝ H ((2 : ℝ) • ∑' n, hartreeTerm (fun m => extendSymKernel (A m)) n u) := by
      ext h
      rw [hval, InnerProductSpace.toDual_apply_apply, real_inner_smul_left]
    rw [hdual, LinearIsometryEquiv.symm_apply_apply, smul_smul]
    norm_num
  unfold SymplecticBracket.hamField sourceHartreeField hartreeField
  rw [hgrad]

end QuantumNLS.R52CFHartree

#print axioms QuantumNLS.R52CFHartree.hamField_coh_eq
#print axioms QuantumNLS.R52CFHartree.cohTerm_hasFDerivAt
