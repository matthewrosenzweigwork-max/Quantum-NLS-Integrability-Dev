/-
QuantumNLS.TensorFourier — U3, the completed tensor functor and Fourier transport.
Owner: review record. Report pin 3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f.
Source: fable-reconciled-plan.md §2 U1–U3; source/chapters/definitions.tex:7,25.
Frozen imports: Fourier f0c07d6f, PhysicalTensor e774c776, TensorCarrier 1b210cb0.
The Hilbert tensor norm is the inner-product norm of TensorCarrier, not the
projective norm on PiTensorProduct. All equivalences below are constructed.
-/
import QuantumNLS.Fourier
import QuantumNLS.PhysicalTensor

open scoped InnerProductSpace
open QuantumNLS.TensorCarrier

noncomputable section
namespace QuantumNLS.TensorFourier

section Functor
variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-- The algebraic tensor power of a unitary. -/
def algPower (e : E ≃ₗᵢ[𝕜] F) (n : ℕ) :
    AlgTensorPower 𝕜 E n ≃ₗ[𝕜] AlgTensorPower 𝕜 F n :=
  PiTensorProduct.congr (fun _ => e.toLinearEquiv)

@[simp] theorem algPower_ptprod (e : E ≃ₗᵢ[𝕜] F) {n : ℕ} (f : Fin n → E) :
    algPower e n (ptprod f) = ptprod (fun i => e (f i)) :=
  PiTensorProduct.congr_tprod _ _

theorem inner_algPower (e : E ≃ₗᵢ[𝕜] F) (n : ℕ) (x y : AlgTensorPower 𝕜 E n) :
    ⟪algPower e n x, algPower e n y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  induction x using AlgTensorPower.induction_on with
  | smul_ptprod r f =>
    induction y using AlgTensorPower.induction_on with
    | smul_ptprod s g =>
      simp only [map_smul, inner_smul_left, inner_smul_right, algPower_ptprod,
        inner_ptprod, e.inner_map_map]
    | add y z hy hz => simp only [map_add, inner_add_right, hy, hz]
  | add x z hx hz => simp only [map_add, inner_add_left, hx, hz]

/-- Isometry for the Hilbert inner product, before completion. -/
def algPowerIsometry (e : E ≃ₗᵢ[𝕜] F) (n : ℕ) :
    AlgTensorPower 𝕜 E n ≃ₗᵢ[𝕜] AlgTensorPower 𝕜 F n :=
  (algPower e n).isometryOfInner (inner_algPower e n)

/-- The n-fold completed tensor functor. No completeness assumption on E or F is needed. -/
def tensorPower (e : E ≃ₗᵢ[𝕜] F) (n : ℕ) :
    HilbertTensorPower 𝕜 E n ≃ₗᵢ[𝕜] HilbertTensorPower 𝕜 F n :=
  lieCompletion (algPowerIsometry e n)

@[simp] theorem tensorPower_coe (e : E ≃ₗᵢ[𝕜] F) (n : ℕ) (x : AlgTensorPower 𝕜 E n) :
    tensorPower e n (x : HilbertTensorPower 𝕜 E n) =
      (algPower e n x : HilbertTensorPower 𝕜 F n) := by
  exact lieCompletion_coe _ x

@[simp] theorem tensorPower_ptprod (e : E ≃ₗᵢ[𝕜] F) {n : ℕ} (f : Fin n → E) :
    tensorPower e n ((ptprod f : AlgTensorPower 𝕜 E n) : HilbertTensorPower 𝕜 E n) =
      ((ptprod (fun i => e (f i)) : AlgTensorPower 𝕜 F n) : HilbertTensorPower 𝕜 F n) := by
  rw [tensorPower_coe, algPower_ptprod]

@[simp] theorem tensorPower_htpow (e : E ≃ₗᵢ[𝕜] F) (n : ℕ) (u : E) :
    tensorPower e n (htpow n u) = htpow n (e u) := tensorPower_ptprod e _

theorem tensorPower_refl (n : ℕ) (x : HilbertTensorPower 𝕜 E n) :
    tensorPower (LinearIsometryEquiv.refl 𝕜 E) n x = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (tensorPower _ n).continuous continuous_id
  | ih a =>
    induction a using AlgTensorPower.induction_on with
    | smul_ptprod r f => simp only [UniformSpace.Completion.coe_smul, map_smul, tensorPower_ptprod]; rfl
    | add a b ha hb => simp only [map_add, ha, hb, UniformSpace.Completion.coe_add]

theorem tensorPower_trans (e : E ≃ₗᵢ[𝕜] F) (d : F ≃ₗᵢ[𝕜] G) (n : ℕ)
    (x : HilbertTensorPower 𝕜 E n) :
    tensorPower (e.trans d) n x = tensorPower d n (tensorPower e n x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (tensorPower (e.trans d) n).continuous
      ((tensorPower d n).continuous.comp (tensorPower e n).continuous)
  | ih a =>
    induction a using AlgTensorPower.induction_on with
    | smul_ptprod r f =>
      simp only [UniformSpace.Completion.coe_smul, map_smul, tensorPower_ptprod,
        LinearIsometryEquiv.trans_apply]
    | add a b ha hb => simp only [UniformSpace.Completion.coe_add, map_add, ha, hb]

theorem algPower_perm (e : E ≃ₗᵢ[𝕜] F) {n : ℕ} (σ : Equiv.Perm (Fin n))
    (a : AlgTensorPower 𝕜 E n) :
    algPower e n (permLinearEquiv σ a) = permLinearEquiv σ (algPower e n a) := by
  induction a using AlgTensorPower.induction_on with
  | smul_ptprod r f => simp only [map_smul, algPower_ptprod, permLinearEquiv_ptprod]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- Tensoring the same unitary in every slot intertwines permutations. -/
theorem tensorPower_permRep (e : E ≃ₗᵢ[𝕜] F) {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : HilbertTensorPower 𝕜 E n) :
    tensorPower e n ((permRep 𝕜 E n σ : HilbertTensorPower 𝕜 E n →L[𝕜] _) x) =
      (permRep 𝕜 F n σ : HilbertTensorPower 𝕜 F n →L[𝕜] _) (tensorPower e n x) := by
  simp only [permRep_apply]
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((tensorPower e n).continuous.comp (permHilbertIsometry σ).continuous)
      ((permHilbertIsometry σ).continuous.comp (tensorPower e n).continuous)
  | ih a => rw [permHilbertIsometry_coe, tensorPower_coe, tensorPower_coe,
      permHilbertIsometry_coe, algPower_perm]

/-- Symmetry is preserved and reflected, including n=0. -/
theorem tensorPower_mem_symSector_iff (e : E ≃ₗᵢ[𝕜] F) {n : ℕ}
    (x : HilbertTensorPower 𝕜 E n) :
    tensorPower e n x ∈ SymSector 𝕜 F n ↔ x ∈ SymSector 𝕜 E n := by
  constructor
  · intro h σ
    apply (tensorPower e n).injective
    rw [tensorPower_permRep]
    exact h σ
  · intro h σ
    rw [← tensorPower_permRep, h σ]

/-- Restriction of the tensor functor to the actual closed symmetric subspaces. -/
def symTensorPower (e : E ≃ₗᵢ[𝕜] F) (n : ℕ) :
    SymSector 𝕜 E n ≃ₗᵢ[𝕜] SymSector 𝕜 F n :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap :=
        { toFun := fun x => ⟨tensorPower e n x, (tensorPower_mem_symSector_iff e (n := n) (x : HilbertTensorPower 𝕜 E n)).2 x.property⟩
          map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
          map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }
      norm_map' := fun x => (tensorPower e n).norm_map x }
    (fun y => by
      refine ⟨⟨(tensorPower e n).symm y, ?_⟩, ?_⟩
      · apply (tensorPower_mem_symSector_iff e _).1
        simp only [LinearIsometryEquiv.apply_symm_apply]; exact y.property
      · exact Subtype.ext ((tensorPower e n).apply_symm_apply y))

@[simp] theorem symTensorPower_apply (e : E ≃ₗᵢ[𝕜] F) (n : ℕ) (x : SymSector 𝕜 E n) :
    (symTensorPower e n x : HilbertTensorPower 𝕜 F n) = tensorPower e n x := rfl

/-- The orthogonal symmetrizers commute with unitary tensor transport. -/
theorem tensorPower_symProj (e : E ≃ₗᵢ[𝕜] F) (n : ℕ) (x : HilbertTensorPower 𝕜 E n) :
    tensorPower e n (symProj 𝕜 E n x) = symProj 𝕜 F n (tensorPower e n x) := by
  simp only [symProj, groupAverage, smul_apply,
    sum_apply, map_smul, map_sum]
  congr 1
  exact Finset.sum_congr rfl (fun σ _ => tensorPower_permRep e σ x)

end Functor

/-! ## Split compatibility and bounded tensor placements -/
section Placements
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Tensor transport respects the chosen first k / last m split. -/
theorem tensorPower_split (e : E ≃ₗᵢ[𝕜] F) (k m : ℕ)
    (x : HilbertTensorPower 𝕜 E (k + m)) :
    splitIsometry k m (tensorPower e (k + m) x) =
      htmap (tensorPower e k).toContinuousLinearEquiv.toContinuousLinearMap
        (tensorPower e m).toContinuousLinearEquiv.toContinuousLinearMap (splitIsometry k m x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq ((splitIsometry k m).continuous.comp (tensorPower e (k + m)).continuous)
      ((htmap _ _).continuous.comp (splitIsometry k m).continuous)
  | ih a =>
    induction a using AlgTensorPower.induction_on with
    | smul_ptprod r f =>
      let a : Fin k → E := fun i => f (Fin.castAdd m i)
      let b : Fin m → E := fun i => f (Fin.natAdd k i)
      have hf : f = Fin.append a b := Fin.append_castAdd_natAdd.symm
      have he : (fun i => e (Fin.append a b i)) =
          Fin.append (fun i => e (a i)) (fun i => e (b i)) := by
        funext i
        exact Fin.addCases (fun j => by simp) (fun j => by simp) i
      simp only [UniformSpace.Completion.coe_smul, map_smul, tensorPower_ptprod]
      rw [hf, he, splitIsometry_ptprod_append, splitIsometry_ptprod_append, htmap_htmul]
      rw [show (tensorPower e k).toContinuousLinearEquiv.toContinuousLinearMap
        ((ptprod a : AlgTensorPower 𝕜 E k) : HilbertTensorPower 𝕜 E k) =
          tensorPower e k ((ptprod a : AlgTensorPower 𝕜 E k) : HilbertTensorPower 𝕜 E k) from rfl,
        tensorPower_ptprod]
      rw [show (tensorPower e m).toContinuousLinearEquiv.toContinuousLinearMap
        ((ptprod b : AlgTensorPower 𝕜 E m) : HilbertTensorPower 𝕜 E m) =
          tensorPower e m ((ptprod b : AlgTensorPower 𝕜 E m) : HilbertTensorPower 𝕜 E m) from rfl,
        tensorPower_ptprod]
    | add a b ha hb => simp only [UniformSpace.Completion.coe_add, map_add, ha, hb]

/-- Place a bounded k-factor operator in the first k tensor coordinates. -/
def blockPlacement (k m : ℕ) (A : HilbertTensorPower 𝕜 E k →L[𝕜] HilbertTensorPower 𝕜 E k) :
    HilbertTensorPower 𝕜 E (k + m) →L[𝕜] HilbertTensorPower 𝕜 E (k + m) :=
  (splitIsometry k m).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    htmap A (ContinuousLinearMap.id 𝕜 _) ∘L
      (splitIsometry k m).toContinuousLinearEquiv.toContinuousLinearMap

theorem split_blockPlacement (k m : ℕ)
    (A : HilbertTensorPower 𝕜 E k →L[𝕜] HilbertTensorPower 𝕜 E k)
    (x : HilbertTensorPower 𝕜 E (k + m)) :
    splitIsometry k m (blockPlacement k m A x) =
      htmap A (ContinuousLinearMap.id 𝕜 _) (splitIsometry k m x) := by
  exact (splitIsometry k m).apply_symm_apply _

/-- Intertwining of completed binary tensor maps, from bounded-operator intertwining. -/
theorem htmap_intertwine
    {X Y Z W : Type*} [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    [NormedAddCommGroup Z] [InnerProductSpace 𝕜 Z]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    (U : X →L[𝕜] Y) (V : Z →L[𝕜] W) (A : X →L[𝕜] X) (B : Y →L[𝕜] Y)
    (h : ∀ x, U (A x) = B (U x)) (x : HilbertTensor 𝕜 X Z) :
    htmap U V (htmap A (ContinuousLinearMap.id 𝕜 Z) x) =
      htmap B (ContinuousLinearMap.id 𝕜 W) (htmap U V x) := by
  have hAB : U ∘L A = B ∘L U := ContinuousLinearMap.ext h
  have hV : V ∘L ContinuousLinearMap.id 𝕜 Z = ContinuousLinearMap.id 𝕜 W ∘L V := by ext; rfl
  rw [← ContinuousLinearMap.comp_apply, ← htmap_comp, hAB, hV, htmap_comp]
  rfl

/-- U3 carries bounded tensor placements, with the transported operator U A U⁻¹. -/
theorem tensorPower_blockPlacement (e : E ≃ₗᵢ[𝕜] F) (k m : ℕ)
    (A : HilbertTensorPower 𝕜 E k →L[𝕜] HilbertTensorPower 𝕜 E k)
    (x : HilbertTensorPower 𝕜 E (k + m)) :
    tensorPower e (k + m) (blockPlacement k m A x) =
      blockPlacement k m ((tensorPower e k).conjStarAlgEquiv A) (tensorPower e (k + m) x) := by
  apply (splitIsometry (𝕜 := 𝕜) (E := F) k m).injective
  rw [tensorPower_split, split_blockPlacement, split_blockPlacement, tensorPower_split]
  exact htmap_intertwine _ _ A _ (fun z => by simp) _

end Placements


/-! ## The one-particle identification and literal one-body placements -/
section OneBody
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- A single algebraic tensor factor is the original space. -/
def firstAlgEquiv : AlgTensorPower 𝕜 E 1 ≃ₗ[𝕜] E :=
  PiTensorProduct.subsingletonEquiv (R := 𝕜) (s := fun _ : Fin 1 => E) 0

@[simp] theorem firstAlgEquiv_ptprod (f : Fin 1 → E) :
    firstAlgEquiv (ptprod f : AlgTensorPower 𝕜 E 1) = f 0 :=
  PiTensorProduct.subsingletonEquiv_apply_tprod _ _

theorem inner_firstAlgEquiv (x y : AlgTensorPower 𝕜 E 1) :
    ⟪firstAlgEquiv x, firstAlgEquiv y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  refine inner_map_map_of_span firstAlgEquiv.toLinearMap (span_range_ptprod 1) ?_ x y
  rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩
  change ⟪firstAlgEquiv (ptprod f), firstAlgEquiv (ptprod g)⟫_𝕜 = _
  rw [firstAlgEquiv_ptprod, firstAlgEquiv_ptprod, inner_ptprod]
  simp

def firstAlgIsometry : AlgTensorPower 𝕜 E 1 ≃ₗᵢ[𝕜] E :=
  firstAlgEquiv.isometryOfInner inner_firstAlgEquiv

variable [CompleteSpace E] [CompleteSpace F]

/-- The completed first tensor power is the given Hilbert space. -/
def firstPowerIso : HilbertTensorPower 𝕜 E 1 ≃ₗᵢ[𝕜] E :=
  (lieCompletion firstAlgIsometry).trans (QuantumNLS.PhysicalTensor.completionSelf E)

@[simp] theorem firstPowerIso_ptprod (f : Fin 1 → E) :
    firstPowerIso ((ptprod f : AlgTensorPower 𝕜 E 1) : HilbertTensorPower 𝕜 E 1) = f 0 := by
  rw [firstPowerIso, LinearIsometryEquiv.trans_apply, lieCompletion_coe]
  change (LinearIsometry.id : E →ₗᵢ[𝕜] E).fromCompletion _ = _
  rw [LinearIsometry.fromCompletion_apply_coe]
  exact firstAlgEquiv_ptprod f

@[simp] theorem firstPowerIso_htpow (u : E) :
    firstPowerIso (htpow 1 u : HilbertTensorPower 𝕜 E 1) = u := firstPowerIso_ptprod _

/-- Tensor functor at n=1 agrees with its original one-body unitary. -/
theorem firstPowerIso_tensorPower (e : E ≃ₗᵢ[𝕜] F) (x : HilbertTensorPower 𝕜 E 1) :
    firstPowerIso (tensorPower e 1 x) = e (firstPowerIso x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (firstPowerIso.continuous.comp (tensorPower e 1).continuous)
      (e.continuous.comp firstPowerIso.continuous)
  | ih a =>
    induction a using AlgTensorPower.induction_on with
    | smul_ptprod r f =>
      simp only [UniformSpace.Completion.coe_smul, map_smul, tensorPower_ptprod,
        firstPowerIso_ptprod]
    | add a b ha hb => simp only [UniformSpace.Completion.coe_add, map_add, ha, hb]

/-- Place an actual bounded one-body operator in the first factor, followed by m identities. -/
def oneBodyPlacement (m : ℕ) (A : E →L[𝕜] E) :
    HilbertTensorPower 𝕜 E (1 + m) →L[𝕜] HilbertTensorPower 𝕜 E (1 + m) :=
  blockPlacement 1 m (firstPowerIso.symm.conjStarAlgEquiv A)

theorem firstPowerIso_conjugation (e : E ≃ₗᵢ[𝕜] F) (A : E →L[𝕜] E) :
    (tensorPower e 1).conjStarAlgEquiv (firstPowerIso.symm.conjStarAlgEquiv A) =
      (firstPowerIso (𝕜 := 𝕜) (E := F)).symm.conjStarAlgEquiv (e.conjStarAlgEquiv A) := by
  ext z
  apply (firstPowerIso (𝕜 := 𝕜) (E := F)).injective
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, firstPowerIso_tensorPower,
    LinearIsometryEquiv.apply_symm_apply]
  congr 2
  apply e.injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  have h := firstPowerIso_tensorPower e ((tensorPower e 1).symm z)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

/-- Literal one-body placement is carried to placement of e A e⁻¹. -/
theorem tensorPower_oneBodyPlacement (e : E ≃ₗᵢ[𝕜] F) (m : ℕ) (A : E →L[𝕜] E)
    (x : HilbertTensorPower 𝕜 E (1 + m)) :
    tensorPower e (1 + m) (oneBodyPlacement m A x) =
      oneBodyPlacement m (e.conjStarAlgEquiv A) (tensorPower e (1 + m) x) := by
  rw [oneBodyPlacement, tensorPower_blockPlacement, firstPowerIso_conjugation]
  rfl

end OneBody


section Supplement
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The functor preserves inverse unitaries. -/
theorem tensorPower_symm (e : E ≃ₗᵢ[𝕜] F) (n : ℕ) :
    tensorPower e.symm n = (tensorPower e n).symm := by
  ext z
  apply (tensorPower e n).injective
  rw [LinearIsometryEquiv.apply_symm_apply, ← tensorPower_trans]
  have h : e.symm.trans e = LinearIsometryEquiv.refl 𝕜 F := by ext; simp
  rw [h, tensorPower_refl]

/-- Zero-factor transport fixes the scalar vacuum under the canonical identifications. -/
theorem zeroSectorIso_tensorPower (e : E ≃ₗᵢ[𝕜] F) (x : HilbertTensorPower 𝕜 E 0) :
    QuantumNLS.PhysicalTensor.zeroSectorIso (tensorPower e 0 x) =
      QuantumNLS.PhysicalTensor.zeroSectorIso x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq
      (QuantumNLS.PhysicalTensor.zeroSectorIso.continuous.comp (tensorPower e 0).continuous)
      QuantumNLS.PhysicalTensor.zeroSectorIso.continuous
  | ih a =>
    induction a using AlgTensorPower.induction_on with
    | smul_ptprod r f =>
      have hf : f = fun _ : Fin 0 => (0 : E) := Subsingleton.elim _ _
      simp only [UniformSpace.Completion.coe_smul, map_smul]
      rw [hf]
      change r • QuantumNLS.PhysicalTensor.zeroSectorIso (tensorPower e 0 (htpow 0 (0 : E))) =
        r • QuantumNLS.PhysicalTensor.zeroSectorIso (htpow 0 (0 : E))
      rw [tensorPower_htpow, QuantumNLS.PhysicalTensor.zeroSectorIso_htpow,
        QuantumNLS.PhysicalTensor.zeroSectorIso_htpow]
    | add a b ha hb => simp only [UniformSpace.Completion.coe_add, map_add, ha, hb]

/-- Bounded placement has the original operator-norm bound, without nontriviality assumptions. -/
theorem norm_blockPlacement_le (k m : ℕ)
    (A : HilbertTensorPower 𝕜 E k →L[𝕜] HilbertTensorPower 𝕜 E k) :
    ‖blockPlacement k m A‖ ≤ ‖A‖ := by
  have hnorm : ‖htmap A (ContinuousLinearMap.id 𝕜 (HilbertTensorPower 𝕜 E m))‖ ≤ ‖A‖ :=
    (norm_htmap_le _ _).trans (by
      calc ‖A‖ * ‖ContinuousLinearMap.id 𝕜 (HilbertTensorPower 𝕜 E m)‖ ≤ ‖A‖ * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
        _ = ‖A‖ := mul_one _)
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  change ‖(splitIsometry k m).symm (htmap A (ContinuousLinearMap.id 𝕜 _) (splitIsometry k m x))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  calc ‖htmap A (ContinuousLinearMap.id 𝕜 _) (splitIsometry k m x)‖ ≤
        ‖htmap A (ContinuousLinearMap.id 𝕜 _)‖ * ‖splitIsometry k m x‖ :=
          ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖A‖ * ‖splitIsometry k m x‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ = ‖A‖ * ‖x‖ := by rw [LinearIsometryEquiv.norm_map]

theorem tensorPower_permHilbert (e : E ≃ₗᵢ[𝕜] F) {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : HilbertTensorPower 𝕜 E n) :
    tensorPower e n (permHilbertIsometry σ x) = permHilbertIsometry σ (tensorPower e n x) :=
  tensorPower_permRep e σ x

theorem tensorPower_permHilbert_symm (e : E ≃ₗᵢ[𝕜] F) {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : HilbertTensorPower 𝕜 E n) :
    tensorPower e n ((permHilbertIsometry σ).symm x) =
      (permHilbertIsometry σ).symm (tensorPower e n x) := by
  apply (permHilbertIsometry (𝕜 := 𝕜) (E := F) σ).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  have h := tensorPower_permHilbert e σ ((permHilbertIsometry σ).symm x)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

/-- A block placement relocated by a specified factor permutation.
No subset averaging or multiplicity assertion is made here. -/
def permutedBlockPlacement (k m : ℕ) (σ : Equiv.Perm (Fin (k + m)))
    (A : HilbertTensorPower 𝕜 E k →L[𝕜] HilbertTensorPower 𝕜 E k) :
    HilbertTensorPower 𝕜 E (k + m) →L[𝕜] HilbertTensorPower 𝕜 E (k + m) :=
  (permHilbertIsometry σ).conjStarAlgEquiv (blockPlacement k m A)

/-- U3 transports a bounded placement in any permuted set of tensor coordinates. -/
theorem tensorPower_permutedBlockPlacement (e : E ≃ₗᵢ[𝕜] F) (k m : ℕ)
    (σ : Equiv.Perm (Fin (k + m)))
    (A : HilbertTensorPower 𝕜 E k →L[𝕜] HilbertTensorPower 𝕜 E k)
    (x : HilbertTensorPower 𝕜 E (k + m)) :
    tensorPower e (k + m) (permutedBlockPlacement k m σ A x) =
      permutedBlockPlacement k m σ ((tensorPower e k).conjStarAlgEquiv A)
        (tensorPower e (k + m) x) := by
  simp only [permutedBlockPlacement, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  rw [tensorPower_permHilbert, tensorPower_blockPlacement, tensorPower_permHilbert_symm]

end Supplement

/-! ## U3 at the mass-L physical Fourier unitary -/
section Fourier
open MeasureTheory QuantumNLS.PhysicalTensor
variable (L : ℝ) [Fact (0 < L)]

/-- The target one-particle Hilbert space is the unweighted square-summable space. -/
abbrev FourierFiber := lp (fun _ : ℤ => ℂ) 2

/-- Full tensor Fourier unitary U1^{⊗N}. -/
abbrev fourierTensor (N : ℕ) :
    HilbertTensorPower ℂ (L2T L) N ≃ₗᵢ[ℂ] HilbertTensorPower ℂ FourierFiber N :=
  tensorPower (QuantumNLS.Fourier.fourierL2 L) N

/-- U3 = Sym^N(U1), an equivalence of completed bosonic sectors. -/
def U3 (N : ℕ) : physSector L N ≃ₗᵢ[ℂ] SymSector ℂ FourierFiber N :=
  symTensorPower (QuantumNLS.Fourier.fourierL2 L) N

@[simp] theorem U3_apply (N : ℕ) (ψ : physSector L N) :
    (U3 L N ψ : HilbertTensorPower ℂ FourierFiber N) = fourierTensor L N ψ := rfl

theorem fourierTensor_ptprod {N : ℕ} (f : Fin N → L2T L) :
    fourierTensor L N ((ptprod f : AlgTensorPower ℂ (L2T L) N) : HilbertTensorPower ℂ (L2T L) N) =
      ((ptprod (fun i => QuantumNLS.Fourier.fourierL2 L (f i)) :
        AlgTensorPower ℂ FourierFiber N) : HilbertTensorPower ℂ FourierFiber N) :=
  tensorPower_ptprod _ _

theorem fourierTensor_htpow (N : ℕ) (u : L2T L) :
    fourierTensor L N (htpow N u) = htpow N (QuantumNLS.Fourier.fourierL2 L u) :=
  tensorPower_htpow _ _ _

/-- The elementary product carries exactly the mass-L report Fourier coefficients. -/
theorem fourierTensor_coeff (u : L2T L) (n : ℤ) :
    QuantumNLS.Fourier.fourierL2 L u n = QuantumNLS.Fourier.coeff L (u : AddCircle L → ℂ) n :=
  QuantumNLS.Fourier.fourierL2_apply L u n

theorem fourierTensor_permRep {N : ℕ} (σ : Equiv.Perm (Fin N))
    (ψ : HilbertTensorPower ℂ (L2T L) N) :
    fourierTensor L N ((permRep ℂ (L2T L) N σ : HilbertTensorPower ℂ (L2T L) N →L[ℂ] _) ψ) =
      (permRep ℂ FourierFiber N σ : HilbertTensorPower ℂ FourierFiber N →L[ℂ] _)
        (fourierTensor L N ψ) := tensorPower_permRep _ _ _

theorem fourierTensor_symProj (N : ℕ) (ψ : HilbertTensorPower ℂ (L2T L) N) :
    fourierTensor L N (symProj ℂ (L2T L) N ψ) =
      symProj ℂ FourierFiber N (fourierTensor L N ψ) := tensorPower_symProj _ _ _

/-- U3 expressed on actual position-space L²(T_L^N), using the proved U2 unitary. -/
def positionFourier (N : ℕ) : L2TN L N ≃ₗᵢ[ℂ] HilbertTensorPower ℂ FourierFiber N :=
  physUnitary.symm.trans (fourierTensor L N)

theorem positionFourier_prodLp {N : ℕ} (f : Fin N → L2T L) :
    positionFourier L N (prodLp f) =
      ((ptprod (fun i => QuantumNLS.Fourier.fourierL2 L (f i)) :
        AlgTensorPower ℂ FourierFiber N) : HilbertTensorPower ℂ FourierFiber N) := by
  have h := physUnitary_ptprod f
  rw [positionFourier, LinearIsometryEquiv.trans_apply, ← h,
    LinearIsometryEquiv.symm_apply_apply, fourierTensor_ptprod]

theorem positionFourier_perm {N : ℕ} (σ : Equiv.Perm (Fin N)) (ψ : L2TN L N) :
    positionFourier L N (physPerm σ ψ) =
      (permRep ℂ FourierFiber N σ : HilbertTensorPower ℂ FourierFiber N →L[ℂ] _)
        (positionFourier L N ψ) := by
  obtain ⟨x, rfl⟩ := physUnitary.surjective ψ
  have h := physEmbed_permRep σ x
  change physUnitary ((permRep ℂ (L2T L) N σ : HilbertTensorPower ℂ (L2T L) N →L[ℂ] _) x) =
    physPerm σ (physUnitary x) at h
  change fourierTensor L N (physUnitary.symm (physPerm σ (physUnitary x))) = _
  rw [← h, LinearIsometryEquiv.symm_apply_apply, fourierTensor_permRep]
  simp only [positionFourier, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply]

theorem positionFourier_mem_symSector_iff (N : ℕ) (ψ : L2TN L N) :
    positionFourier L N ψ ∈ SymSector ℂ FourierFiber N ↔
      ∀ σ : Equiv.Perm (Fin N), physPerm σ ψ = ψ := by
  constructor
  · intro h σ
    apply (positionFourier L N).injective
    rw [positionFourier_perm]
    exact h σ
  · intro h σ
    rw [← positionFourier_perm, h σ]

/-- Bounded block placements in Fourier coordinates, including k=1.
A proof-valued specialization: infer the exact generic equality to avoid costly
re-elaboration through the concrete Fourier unitary's operator-algebra instances. -/
def fourierTensor_blockPlacement (k m : ℕ)
    (A : HilbertTensorPower ℂ (L2T L) k →L[ℂ] HilbertTensorPower ℂ (L2T L) k)
    (ψ : HilbertTensorPower ℂ (L2T L) (k + m)) :=
  tensorPower_blockPlacement (𝕜 := ℂ) (E := L2T L) (F := FourierFiber)
    (QuantumNLS.Fourier.fourierL2 L) k m A ψ

end Fourier


section FourierConsequences
open QuantumNLS.PhysicalTensor
variable (L : ℝ) [Fact (0 < L)]

/-- U3 carries physical pure products to their Fourier pure products. -/
theorem U3_htpow (N : ℕ) (u : L2T L) :
    U3 L N ⟨htpow N u, htpow_mem_symSector N u⟩ =
      ⟨htpow N (QuantumNLS.Fourier.fourierL2 L u), htpow_mem_symSector N _⟩ :=
  Subtype.ext (fourierTensor_htpow L N u)

/-- In the zero sector, U3 is the identity on scalars under the canonical identifications. -/
theorem fourierTensor_zero (ψ : HilbertTensorPower ℂ (L2T L) 0) :
    zeroSectorIso (fourierTensor L 0 ψ) = zeroSectorIso ψ :=
  zeroSectorIso_tensorPower (QuantumNLS.Fourier.fourierL2 L) ψ

/-- The actual physical one-body operator is Fourier conjugated before tensor placement. -/
def fourierTensor_oneBodyPlacement (m : ℕ) (A : L2T L →L[ℂ] L2T L)
    (ψ : HilbertTensorPower ℂ (L2T L) (1 + m)) :=
  tensorPower_oneBodyPlacement (𝕜 := ℂ) (E := L2T L) (F := FourierFiber)
    (QuantumNLS.Fourier.fourierL2 L) m A ψ

/-- Fourier transport of a bounded k-body placement in permuted coordinates. -/
def fourierTensor_permutedBlockPlacement (k m : ℕ) (σ : Equiv.Perm (Fin (k + m)))
    (A : HilbertTensorPower ℂ (L2T L) k →L[ℂ] HilbertTensorPower ℂ (L2T L) k)
    (ψ : HilbertTensorPower ℂ (L2T L) (k + m)) :=
  tensorPower_permutedBlockPlacement (𝕜 := ℂ) (E := L2T L) (F := FourierFiber)
    (QuantumNLS.Fourier.fourierL2 L) k m σ A ψ

end FourierConsequences

end QuantumNLS.TensorFourier

#print axioms QuantumNLS.TensorFourier.algPower
#print axioms QuantumNLS.TensorFourier.algPower_ptprod
#print axioms QuantumNLS.TensorFourier.inner_algPower
#print axioms QuantumNLS.TensorFourier.algPowerIsometry
#print axioms QuantumNLS.TensorFourier.tensorPower
#print axioms QuantumNLS.TensorFourier.tensorPower_coe
#print axioms QuantumNLS.TensorFourier.tensorPower_ptprod
#print axioms QuantumNLS.TensorFourier.tensorPower_htpow
#print axioms QuantumNLS.TensorFourier.tensorPower_refl
#print axioms QuantumNLS.TensorFourier.tensorPower_trans
#print axioms QuantumNLS.TensorFourier.algPower_perm
#print axioms QuantumNLS.TensorFourier.tensorPower_permRep
#print axioms QuantumNLS.TensorFourier.tensorPower_mem_symSector_iff
#print axioms QuantumNLS.TensorFourier.symTensorPower
#print axioms QuantumNLS.TensorFourier.symTensorPower_apply
#print axioms QuantumNLS.TensorFourier.tensorPower_symProj
#print axioms QuantumNLS.TensorFourier.tensorPower_split
#print axioms QuantumNLS.TensorFourier.blockPlacement
#print axioms QuantumNLS.TensorFourier.split_blockPlacement
#print axioms QuantumNLS.TensorFourier.htmap_intertwine
#print axioms QuantumNLS.TensorFourier.tensorPower_blockPlacement
#print axioms QuantumNLS.TensorFourier.firstAlgEquiv
#print axioms QuantumNLS.TensorFourier.firstAlgEquiv_ptprod
#print axioms QuantumNLS.TensorFourier.inner_firstAlgEquiv
#print axioms QuantumNLS.TensorFourier.firstAlgIsometry
#print axioms QuantumNLS.TensorFourier.firstPowerIso
#print axioms QuantumNLS.TensorFourier.firstPowerIso_ptprod
#print axioms QuantumNLS.TensorFourier.firstPowerIso_htpow
#print axioms QuantumNLS.TensorFourier.firstPowerIso_tensorPower
#print axioms QuantumNLS.TensorFourier.oneBodyPlacement
#print axioms QuantumNLS.TensorFourier.firstPowerIso_conjugation
#print axioms QuantumNLS.TensorFourier.tensorPower_oneBodyPlacement
#print axioms QuantumNLS.TensorFourier.tensorPower_symm
#print axioms QuantumNLS.TensorFourier.zeroSectorIso_tensorPower
#print axioms QuantumNLS.TensorFourier.norm_blockPlacement_le
#print axioms QuantumNLS.TensorFourier.tensorPower_permHilbert
#print axioms QuantumNLS.TensorFourier.tensorPower_permHilbert_symm
#print axioms QuantumNLS.TensorFourier.permutedBlockPlacement
#print axioms QuantumNLS.TensorFourier.tensorPower_permutedBlockPlacement
#print axioms QuantumNLS.TensorFourier.FourierFiber
#print axioms QuantumNLS.TensorFourier.fourierTensor
#print axioms QuantumNLS.TensorFourier.U3
#print axioms QuantumNLS.TensorFourier.U3_apply
#print axioms QuantumNLS.TensorFourier.fourierTensor_ptprod
#print axioms QuantumNLS.TensorFourier.fourierTensor_htpow
#print axioms QuantumNLS.TensorFourier.fourierTensor_coeff
#print axioms QuantumNLS.TensorFourier.fourierTensor_permRep
#print axioms QuantumNLS.TensorFourier.fourierTensor_symProj
#print axioms QuantumNLS.TensorFourier.positionFourier
#print axioms QuantumNLS.TensorFourier.positionFourier_prodLp
#print axioms QuantumNLS.TensorFourier.positionFourier_perm
#print axioms QuantumNLS.TensorFourier.positionFourier_mem_symSector_iff
#print axioms QuantumNLS.TensorFourier.fourierTensor_blockPlacement
#print axioms QuantumNLS.TensorFourier.U3_htpow
#print axioms QuantumNLS.TensorFourier.fourierTensor_zero
#print axioms QuantumNLS.TensorFourier.fourierTensor_oneBodyPlacement
#print axioms QuantumNLS.TensorFourier.fourierTensor_permutedBlockPlacement

#check QuantumNLS.TensorFourier.fourierTensor_blockPlacement
#check QuantumNLS.TensorFourier.fourierTensor_oneBodyPlacement
#check QuantumNLS.TensorFourier.fourierTensor_permutedBlockPlacement
