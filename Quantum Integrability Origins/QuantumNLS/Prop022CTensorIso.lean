import Mathlib
import QuantumNLS.Prop022AIsoTensor
import QuantumNLS.Prop022BIso
import QuantumNLS.IntrinsicContact
import QuantumNLS.TensorPlacements

/-! PROP-022 route A, round 4, stage C1: generic tensor-level covariance under an ISOMETRY.

For a linear isometry `J : E →ₗᵢ[ℂ] F` of complex Hilbert spaces (no surjectivity) this module proves
the tensor-level facts needed to show that canonical operators defined from `E` alone (creation,
annihilation, second quantization) intertwine with `Γ(J)`:

* `split_tensorMapI`: `split ∘ J^{⊗(k+m)} = (J^{⊗k} ⊗̂ J^{⊗m}) ∘ split`;
* `tensorMapI_symProj`: the symmetrizing projection commutes with `J^{⊗n}`;
* first-slot and last-slot insertion maps `insFirst`, `insLast` with
  `J^{⊗} ∘ ins = ins ∘ J^{⊗}` and the adjoint form `(J^{⊗})† ∘ ins (J b) = ins b ∘ (J^{⊗})†`;
* covariance of the DEF-041 placements (`tensorMapI_symmetrizedPlacement`, `symMapI_Q_N_p`).

These are generic in `E`, `F`; the torus `L2T L` plays no role here. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable section
open scoped InnerProductSpace

namespace QuantumNLS.Prop022CTensorIso
open QuantumNLS.TensorCarrier QuantumNLS.Prop022GTensor QuantumNLS.Prop022AIsoTensor
open QuantumNLS.Prop022BIso QuantumNLS.IntrinsicContact

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- `J^{⊗n}` as a continuous linear map. -/
def tcI (J : E →ₗᵢ[ℂ] F) (n : ℕ) : HilbertTensorPower ℂ E n →L[ℂ] HilbertTensorPower ℂ F n :=
  (tensorMapI J n).toContinuousLinearMap

@[simp] lemma tcI_apply (J : E →ₗᵢ[ℂ] F) (n : ℕ) (z : HilbertTensorPower ℂ E n) :
    tcI J n z = tensorMapI J n z := rfl

lemma tensorMapI_ptprod_coe (J : E →ₗᵢ[ℂ] F) {n : ℕ} (f : Fin n → E) :
    tensorMapI J n ((ptprod f : AlgTensorPower ℂ E n) : HilbertTensorPower ℂ E n) =
      ((ptprod (fun i => J (f i)) : AlgTensorPower ℂ F n) : HilbertTensorPower ℂ F n) := by
  rw [tensorMapI_coe, algMapI_ptprod]

lemma tcI_adj_tcI (J : E →ₗᵢ[ℂ] F) (n : ℕ) (z : HilbertTensorPower ℂ E n) :
    ContinuousLinearMap.adjoint (tcI J n) (tcI J n z) = z := by
  apply ext_inner_right ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (tensorMapI J n).inner_map_map z v

/-- **Splitting commutes with `J^{⊗}`.** -/
theorem split_tensorMapI (J : E →ₗᵢ[ℂ] F) (k m : ℕ) (z : HilbertTensorPower ℂ E (k + m)) :
    splitIsometry k m (tensorMapI J (k + m) z) =
      htmap (tcI J k) (tcI J m) (splitIsometry k m z) := by
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq ((splitIsometry k m).continuous.comp (tensorMapI J (k + m)).continuous)
      ((htmap (tcI J k) (tcI J m)).continuous.comp (splitIsometry k m).continuous)
  | ih a =>
    induction a using AlgTensorPower.induction_on with
    | smul_ptprod r f =>
      have key : ∀ g : Fin (k + m) → E,
          splitIsometry k m (tensorMapI J (k + m) ((ptprod g : AlgTensorPower ℂ E (k + m)) :
            HilbertTensorPower ℂ E (k + m))) =
          htmap (tcI J k) (tcI J m) (splitIsometry k m ((ptprod g : AlgTensorPower ℂ E (k + m)) :
            HilbertTensorPower ℂ E (k + m))) := by
        intro g
        have hg : g = Fin.append (fun i => g (Fin.castAdd m i)) (fun i => g (Fin.natAdd k i)) :=
          (Fin.append_castAdd_natAdd (f := g)).symm
        set a : Fin k → E := fun i => g (Fin.castAdd m i)
        set b : Fin m → E := fun i => g (Fin.natAdd k i)
        rw [hg, tensorMapI_ptprod_coe]
        have h2 : (fun i => J (Fin.append a b i)) =
            Fin.append (fun i => J (a i)) (fun i => J (b i)) := by
          funext i
          refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
        rw [h2, splitIsometry_ptprod_append, splitIsometry_ptprod_append, htmap_htmul,
          tcI_apply, tcI_apply, tensorMapI_ptprod_coe, tensorMapI_ptprod_coe]
      rw [UniformSpace.Completion.coe_smul]
      simp only [map_smul]
      rw [key f]
    | add x y hx hy =>
      rw [UniformSpace.Completion.coe_add]
      simp only [map_add]
      rw [hx, hy]

theorem tensorMapI_split_symm (J : E →ₗᵢ[ℂ] F) (k m : ℕ) (x : HilbertTensorPower ℂ E k)
    (y : HilbertTensorPower ℂ E m) :
    tensorMapI J (k + m) ((splitIsometry k m).symm (htmul x y)) =
      (splitIsometry k m).symm (htmul (tensorMapI J k x) (tensorMapI J m y)) := by
  apply (splitIsometry k m).injective
  rw [split_tensorMapI, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply,
    htmap_htmul]
  rfl

/-- The symmetrizing projection commutes with `J^{⊗n}`. -/
theorem tensorMapI_symProj (J : E →ₗᵢ[ℂ] F) (n : ℕ) (z : HilbertTensorPower ℂ E n) :
    tensorMapI J n (symProj ℂ E n z) = symProj ℂ F n (tensorMapI J n z) := by
  rw [symProj_eq_factorial_average, symProj_eq_factorial_average]
  simp only [smul_apply, sum_apply, map_smul, map_sum,
    permRep_apply]
  congr 1
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  exact (tensorMapI_perm J σ z).symm

theorem symMapI_orthProj (J : E →ₗᵢ[ℂ] F) (n : ℕ) (z : HilbertTensorPower ℂ E n) :
    symMapI J n ((SymSector ℂ E n).orthogonalProjectionOnto z) =
      (SymSector ℂ F n).orthogonalProjectionOnto (tensorMapI J n z) := by
  apply Subtype.ext
  rw [symMapI_coe]
  have h1 : ((SymSector ℂ E n).orthogonalProjectionOnto z : HilbertTensorPower ℂ E n) =
      symProj ℂ E n z := by
    rw [symProj_eq_starProjection]; rfl
  have h2 : ((SymSector ℂ F n).orthogonalProjectionOnto (tensorMapI J n z) :
      HilbertTensorPower ℂ F n) = symProj ℂ F n (tensorMapI J n z) := by
    rw [symProj_eq_starProjection]; rfl
  rw [h1, h2, tensorMapI_symProj]

/-! ### Insertion maps -/

/-- `y ↦ x ⊗ y` is `htmulR`; its mirror `x ↦ x ⊗ y`. -/
def htmulL {A F' : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F'] (y : F') :
    A →L[ℂ] HilbertTensor ℂ A F' :=
  LinearMap.mkContinuous
    { toFun := fun x => htmul x y
      map_add' := fun x x' => htmul_add_left x x' y
      map_smul' := fun c x => htmul_smul_left c x y } ‖y‖ (by
    intro x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, norm_htmul]
    rw [mul_comm])

theorem htmulL_apply {A F' : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [CompleteSpace A] [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    (y : F') (x : A) : htmulL (A := A) y x = htmul x y := rfl

/-- First-slot insertion `x ↦ b ⊗ x` into `E^{⊗̂(k+n)}`, `b ∈ E^{⊗̂k}`. -/
def insFirst (k n : ℕ) (b : HilbertTensorPower ℂ E k) :
    HilbertTensorPower ℂ E n →L[ℂ] HilbertTensorPower ℂ E (k + n) :=
  (splitIsometry k n).symm.toLinearIsometry.toContinuousLinearMap ∘L
    htmulR (F := HilbertTensorPower ℂ E n) b

theorem insFirst_apply (k n : ℕ) (b : HilbertTensorPower ℂ E k) (x : HilbertTensorPower ℂ E n) :
    insFirst k n b x = (splitIsometry k n).symm (htmul b x) := rfl

/-- Last-slot insertion `x ↦ x ⊗ y` into `E^{⊗̂(n+k)}`, `y ∈ E^{⊗̂k}`. -/
def insLast (n k : ℕ) (b : HilbertTensorPower ℂ E k) :
    HilbertTensorPower ℂ E n →L[ℂ] HilbertTensorPower ℂ E (n + k) :=
  (splitIsometry n k).symm.toLinearIsometry.toContinuousLinearMap ∘L
    htmulL (A := HilbertTensorPower ℂ E n) b

theorem insLast_apply (n k : ℕ) (b : HilbertTensorPower ℂ E k) (x : HilbertTensorPower ℂ E n) :
    insLast n k b x = (splitIsometry n k).symm (htmul x b) := rfl

/-- `J^{⊗}` commutes with first-slot insertion. -/
theorem tensorMapI_insFirst (J : E →ₗᵢ[ℂ] F) (k n : ℕ) (b : HilbertTensorPower ℂ E k)
    (x : HilbertTensorPower ℂ E n) :
    tensorMapI J (k + n) (insFirst k n b x) =
      insFirst k n (tensorMapI J k b) (tensorMapI J n x) := by
  rw [insFirst_apply, insFirst_apply, tensorMapI_split_symm]

theorem tensorMapI_insLast (J : E →ₗᵢ[ℂ] F) (n k : ℕ) (b : HilbertTensorPower ℂ E k)
    (x : HilbertTensorPower ℂ E n) :
    tensorMapI J (n + k) (insLast n k b x) =
      insLast n k (tensorMapI J k b) (tensorMapI J n x) := by
  rw [insLast_apply, insLast_apply, tensorMapI_split_symm]

lemma inner_symm_left {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] (e : X ≃ₗᵢ[ℂ] Y) (u : Y) (v : X) :
    ⟪e.symm u, v⟫_ℂ = ⟪u, e v⟫_ℂ := by
  rw [LinearIsometryEquiv.inner_map_eq_flip, LinearIsometryEquiv.symm_symm]

/-- Adjoint form: `(J^{⊗})† ∘ ins (J b) = ins b ∘ (J^{⊗})†`. -/
theorem tcI_adj_insFirst (J : E →ₗᵢ[ℂ] F) (k n : ℕ) (b : HilbertTensorPower ℂ E k)
    (w : HilbertTensorPower ℂ F n) :
    ContinuousLinearMap.adjoint (tcI J (k + n)) (insFirst k n (tensorMapI J k b) w) =
      insFirst k n b (ContinuousLinearMap.adjoint (tcI J n) w) := by
  apply ext_inner_right ℂ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_left, insFirst_apply, insFirst_apply, inner_symm_left,
    inner_symm_left, tcI_apply, split_tensorMapI, ← ContinuousLinearMap.adjoint_inner_left,
    adjoint_htmap, htmap_htmul]
  have hb : (ContinuousLinearMap.adjoint (tcI J k)) (tensorMapI J k b) = b := tcI_adj_tcI J k b
  rw [hb]

theorem tcI_adj_insLast (J : E →ₗᵢ[ℂ] F) (n k : ℕ) (b : HilbertTensorPower ℂ E k)
    (w : HilbertTensorPower ℂ F n) :
    ContinuousLinearMap.adjoint (tcI J (n + k)) (insLast n k (tensorMapI J k b) w) =
      insLast n k b (ContinuousLinearMap.adjoint (tcI J n) w) := by
  apply ext_inner_right ℂ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_left, insLast_apply, insLast_apply, inner_symm_left,
    inner_symm_left, tcI_apply, split_tensorMapI, ← ContinuousLinearMap.adjoint_inner_left,
    adjoint_htmap, htmap_htmul]
  have hb : (ContinuousLinearMap.adjoint (tcI J k)) (tensorMapI J k b) = b := tcI_adj_tcI J k b
  rw [hb]

/-! ### Placements (port of `Prop022ACovTensor` to isometries) -/

theorem tensorMapI_extendSymKernel (J : E →ₗᵢ[ℂ] F) {p : ℕ}
    (A : SymSector ℂ E p →L[ℂ] SymSector ℂ E p)
    (A' : SymSector ℂ F p →L[ℂ] SymSector ℂ F p)
    (hA : ∀ y, symMapI J p (A y) = A' (symMapI J p y)) (z : HilbertTensorPower ℂ E p) :
    tensorMapI J p (TensorPlacements.extendSymKernel A z) =
      TensorPlacements.extendSymKernel A' (tensorMapI J p z) := by
  have h : symMapI J p (TensorPlacements.symProjToSector p z) =
      TensorPlacements.symProjToSector p (tensorMapI J p z) := by
    apply Subtype.ext
    exact tensorMapI_symProj J p z
  change ((symMapI J p (A (TensorPlacements.symProjToSector p z)) : SymSector ℂ F p) :
      HilbertTensorPower ℂ F p) = ((A' (TensorPlacements.symProjToSector p (tensorMapI J p z)) :
      SymSector ℂ F p) : HilbertTensorPower ℂ F p)
  rw [hA, h]

theorem tensorMapI_firstPlacement (J : E →ₗᵢ[ℂ] F) {p q : ℕ}
    (A : SymSector ℂ E p →L[ℂ] SymSector ℂ E p)
    (A' : SymSector ℂ F p →L[ℂ] SymSector ℂ F p)
    (hA : ∀ y, symMapI J p (A y) = A' (symMapI J p y)) (z : HilbertTensorPower ℂ E (p + q)) :
    tensorMapI J (p + q) (TensorPlacements.firstPlacement (q := q) A z) =
      TensorPlacements.firstPlacement (q := q) A' (tensorMapI J (p + q) z) := by
  apply (splitIsometry p q).injective
  change splitIsometry p q (tensorMapI J (p + q)
      ((splitIsometry p q).symm (htmap (TensorPlacements.extendSymKernel A)
        (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E q)) (splitIsometry p q z)))) =
    splitIsometry p q ((splitIsometry p q).symm (htmap (TensorPlacements.extendSymKernel A')
        (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ F q))
        (splitIsometry p q (tensorMapI J (p + q) z))))
  rw [split_tensorMapI, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply,
    split_tensorMapI]
  have hcomp : ∀ Φ : HilbertTensor ℂ (HilbertTensorPower ℂ E p) (HilbertTensorPower ℂ E q),
      htmap (tcI J p) (tcI J q) (htmap (TensorPlacements.extendSymKernel A)
        (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E q)) Φ) =
      htmap (TensorPlacements.extendSymKernel A') (ContinuousLinearMap.id ℂ _)
        (htmap (tcI J p) (tcI J q) Φ) := by
    intro Φ
    have e1 := htmap_comp (tcI J p) (TensorPlacements.extendSymKernel A) (tcI J q)
      (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E q))
    have e2 := htmap_comp (TensorPlacements.extendSymKernel A') (tcI J p)
      (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ F q)) (tcI J q)
    have e3 : (tcI J p).comp (TensorPlacements.extendSymKernel A) =
        (TensorPlacements.extendSymKernel A').comp (tcI J p) := by
      ext w
      exact tensorMapI_extendSymKernel J A A' hA w
    have e4 : (tcI J q).comp (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E q)) =
        (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ F q)).comp (tcI J q) := by
      ext w; rfl
    rw [e3, e4] at e1
    have := congrArg (fun T => T Φ) (e1.symm.trans e2)
    simpa using this
  exact hcomp _

theorem tensorMapI_permutedPlacement (J : E →ₗᵢ[ℂ] F) {p q : ℕ} (σ : Equiv.Perm (Fin (p + q)))
    (A : SymSector ℂ E p →L[ℂ] SymSector ℂ E p)
    (A' : SymSector ℂ F p →L[ℂ] SymSector ℂ F p)
    (hA : ∀ y, symMapI J p (A y) = A' (symMapI J p y)) (z : HilbertTensorPower ℂ E (p + q)) :
    tensorMapI J (p + q) (TensorPlacements.permutedPlacement σ A z) =
      TensorPlacements.permutedPlacement σ A' (tensorMapI J (p + q) z) := by
  unfold TensorPlacements.permutedPlacement
  simp only [ContinuousLinearMap.comp_apply, permRep_apply]
  rw [← tensorMapI_perm J σ, tensorMapI_firstPlacement J A A' hA, ← tensorMapI_perm J σ⁻¹]

theorem tensorMapI_symmetrizedPlacement (J : E →ₗᵢ[ℂ] F) {p q : ℕ}
    (A : SymSector ℂ E p →L[ℂ] SymSector ℂ E p)
    (A' : SymSector ℂ F p →L[ℂ] SymSector ℂ F p)
    (hA : ∀ y, symMapI J p (A y) = A' (symMapI J p y)) (z : HilbertTensorPower ℂ E (p + q)) :
    tensorMapI J (p + q) (TensorPlacements.symmetrizedPlacement (q := q) A z) =
      TensorPlacements.symmetrizedPlacement (q := q) A' (tensorMapI J (p + q) z) := by
  unfold TensorPlacements.symmetrizedPlacement
  simp only [smul_apply, sum_apply, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  exact tensorMapI_permutedPlacement J σ A A' hA z

theorem symMapI_Q_N_p (J : E →ₗᵢ[ℂ] F) {p q : ℕ}
    (A : SymSector ℂ E p →L[ℂ] SymSector ℂ E p)
    (A' : SymSector ℂ F p →L[ℂ] SymSector ℂ F p)
    (hA : ∀ y, symMapI J p (A y) = A' (symMapI J p y)) (y : SymSector ℂ E (p + q)) :
    symMapI J (p + q) (TensorPlacements.Q_N_p (q := q) A y) =
      TensorPlacements.Q_N_p (q := q) A' (symMapI J (p + q) y) := by
  apply Subtype.ext
  rw [symMapI_coe]
  exact tensorMapI_symmetrizedPlacement J A A' hA y.1

end QuantumNLS.Prop022CTensorIso

#print axioms QuantumNLS.Prop022CTensorIso.split_tensorMapI
#print axioms QuantumNLS.Prop022CTensorIso.tcI_adj_insFirst
#print axioms QuantumNLS.Prop022CTensorIso.tcI_adj_insLast
#print axioms QuantumNLS.Prop022CTensorIso.symMapI_Q_N_p
