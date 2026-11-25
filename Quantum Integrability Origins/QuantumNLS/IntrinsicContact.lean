import Mathlib
import QuantumNLS.TensorCarrier

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped TensorProduct InnerProductSpace ComplexConjugate
open QuantumNLS.TensorCarrier

namespace QuantumNLS.IntrinsicContact

section Carrier
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem ptprod_one_add (u v : E) :
    (ptprod (fun _ : Fin 1 => u + v) : AlgTensorPower ℂ E 1) =
      ptprod (fun _ : Fin 1 => u) + ptprod (fun _ : Fin 1 => v) := by
  have h : (fun _ : Fin 1 => u + v) = Function.update (fun _ : Fin 1 => u) 0 (u + v) := by
    ext i; fin_cases i; simp
  have h1 := (PiTensorProduct.tprod ℂ (s := fun _ : Fin 1 => E)).map_update_add
    (fun _ : Fin 1 => u) 0 u v
  have e1 : Function.update (fun _ : Fin 1 => u) 0 u = fun _ => u := by
    ext i; fin_cases i; simp
  have e2 : Function.update (fun _ : Fin 1 => u) 0 v = fun _ => v := by
    ext i; fin_cases i; simp
  rw [e1, e2, ← h] at h1
  exact h1

theorem ptprod_one_smul (c : ℂ) (u : E) :
    (ptprod (fun _ : Fin 1 => c • u) : AlgTensorPower ℂ E 1) =
      c • ptprod (fun _ : Fin 1 => u) := by
  have h : (fun _ : Fin 1 => c • u) = Function.update (fun _ : Fin 1 => u) 0 (c • u) := by
    ext i; fin_cases i; simp
  have h1 := (PiTensorProduct.tprod ℂ (s := fun _ : Fin 1 => E)).map_update_smul
    (fun _ : Fin 1 => u) 0 c u
  have e1 : Function.update (fun _ : Fin 1 => u) 0 u = fun _ => u := by
    ext i; fin_cases i; simp
  rw [e1, ← h] at h1
  exact h1

/-- `E → E^{⊗̂ 1}`, `u ↦ u^{⊗ 1}`, as a linear isometry. -/
def powOne : E →ₗᵢ[ℂ] HilbertTensorPower ℂ E 1 where
  toFun u := htpow 1 u
  map_add' u v := by
    show ((ptprod (fun _ : Fin 1 => u + v) : AlgTensorPower ℂ E 1) :
      HilbertTensorPower ℂ E 1) = _
    rw [ptprod_one_add, UniformSpace.Completion.coe_add]; rfl
  map_smul' c u := by
    show ((ptprod (fun _ : Fin 1 => c • u) : AlgTensorPower ℂ E 1) :
      HilbertTensorPower ℂ E 1) = _
    rw [ptprod_one_smul, UniformSpace.Completion.coe_smul]; rfl
  norm_map' u := by simp [norm_htpow]

theorem powOne_apply (u : E) : powOne u = (htpow 1 u : HilbertTensorPower ℂ E 1) := rfl

theorem powOne_surjective : Function.Surjective (powOne (E := E)) := by
  have hclosed : IsClosed (Set.range (powOne (E := E))) :=
    powOne.isometry.isClosedEmbedding.isClosed_range
  have hmem : ∀ a : AlgTensorPower ℂ E 1,
      (a : HilbertTensorPower ℂ E 1) ∈ Set.range (powOne (E := E)) := by
    intro a
    induction a using AlgTensorPower.induction_on with
    | smul_ptprod r f =>
      refine ⟨r • f 0, ?_⟩
      rw [map_smul, powOne_apply]
      have : f = fun _ => f 0 := by ext i; fin_cases i; rfl
      rw [UniformSpace.Completion.coe_smul]
      congr 1
      rw [this]
      rfl
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb, UniformSpace.Completion.coe_add]⟩
  intro z
  have hd : DenseRange ((↑) : AlgTensorPower ℂ E 1 → HilbertTensorPower ℂ E 1) :=
    UniformSpace.Completion.denseRange_coe
  have : z ∈ closure (Set.range ((↑) : AlgTensorPower ℂ E 1 → HilbertTensorPower ℂ E 1)) := by
    rw [hd.closure_range]; exact Set.mem_univ z
  have hsub : Set.range ((↑) : AlgTensorPower ℂ E 1 → HilbertTensorPower ℂ E 1) ⊆
      Set.range (powOne (E := E)) := by
    rintro _ ⟨a, rfl⟩; exact hmem a
  exact (hclosed.closure_subset_iff.mpr hsub) this

/-- `E ≃ E^{⊗̂ 1}`. -/
def oneEquiv : E ≃ₗᵢ[ℂ] HilbertTensorPower ℂ E 1 :=
  LinearIsometryEquiv.ofSurjective powOne powOne_surjective

theorem oneEquiv_apply (u : E) : oneEquiv u = (htpow 1 u : HilbertTensorPower ℂ E 1) := rfl

theorem oneEquiv_symm_htpow (u : E) : (oneEquiv (E := E)).symm (htpow 1 u) = u := by
  rw [LinearIsometryEquiv.symm_apply_eq]; rfl

end Carrier

section Tensor
variable {A B F : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem htmap_id_id : htmap (ContinuousLinearMap.id ℂ A) (ContinuousLinearMap.id ℂ F) =
    ContinuousLinearMap.id ℂ (HilbertTensor ℂ A F) := by
  ext z
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (htmap _ _).continuous continuous_id
  | ih a =>
    have key : ∀ a : A ⊗[ℂ] F,
        TensorProduct.mapL (ContinuousLinearMap.id ℂ A) (ContinuousLinearMap.id ℂ F) a = a := by
      intro a
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [TensorProduct.mapL_tmul]
      | add a b ha hb => simp only [map_add, ha, hb]
    simp only [htmap, ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.id_apply]
    rw [key]

theorem adjoint_comp_self_iso (e : A ≃ₗᵢ[ℂ] B) :
    ContinuousLinearMap.adjoint (e.toLinearIsometry.toContinuousLinearMap) ∘L
      e.toLinearIsometry.toContinuousLinearMap = ContinuousLinearMap.id ℂ A := by
  ext a
  apply ext_inner_right ℂ
  intro b
  simp

/-- Tensoring a linear isometry equivalence with the identity preserves inner products. -/
theorem inner_htmap_iso (e : A ≃ₗᵢ[ℂ] B) (x y : HilbertTensor ℂ A F) :
    ⟪htmap e.toLinearIsometry.toContinuousLinearMap (ContinuousLinearMap.id ℂ F) x,
      htmap e.toLinearIsometry.toContinuousLinearMap (ContinuousLinearMap.id ℂ F) y⟫_ℂ =
      ⟪x, y⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_htmap]
  have h : ContinuousLinearMap.adjoint (ContinuousLinearMap.id ℂ F) ∘L
      ContinuousLinearMap.id ℂ F = ContinuousLinearMap.id ℂ F := by
    rw [ContinuousLinearMap.adjoint_id]; rfl
  have := congrArg (fun T => T y)
    (htmap_comp (ContinuousLinearMap.adjoint e.toLinearIsometry.toContinuousLinearMap)
      e.toLinearIsometry.toContinuousLinearMap
      (ContinuousLinearMap.adjoint (ContinuousLinearMap.id ℂ F)) (ContinuousLinearMap.id ℂ F))
  simp only [ContinuousLinearMap.comp_apply] at this
  rw [← this, adjoint_comp_self_iso, h, htmap_id_id]
  rfl

theorem norm_htmap_iso (e : A ≃ₗᵢ[ℂ] B) (x : HilbertTensor ℂ A F) :
    ‖htmap e.toLinearIsometry.toContinuousLinearMap (ContinuousLinearMap.id ℂ F) x‖ = ‖x‖ := by
  have h := inner_htmap_iso (F := F) e x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖htmap e.toLinearIsometry.toContinuousLinearMap (ContinuousLinearMap.id ℂ F) x‖ ^ 2 =
      ‖x‖ ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

/-- `y ↦ x ⊗ y` as a bounded operator. -/
def htmulR (x : A) : F →L[ℂ] HilbertTensor ℂ A F :=
  LinearMap.mkContinuous
    { toFun := fun y => htmul x y
      map_add' := fun y y' => htmul_add_right x y y'
      map_smul' := fun c y => htmul_smul_right c x y } ‖x‖ (by
    intro y
    simp only [LinearMap.coe_mk, AddHom.coe_mk, norm_htmul]
    exact le_refl _)

theorem htmulR_apply (x : A) (y : F) : htmulR x y = htmul x y := rfl

/-- Contraction with `⟨x|` in the first slot: the adjoint of `y ↦ x ⊗ y`. -/
def contractL (x : A) : HilbertTensor ℂ A F →L[ℂ] F :=
  ContinuousLinearMap.adjoint (htmulR (F := F) x)

theorem inner_contractL (x : A) (y : F) (Φ : HilbertTensor ℂ A F) :
    ⟪y, contractL x Φ⟫_ℂ = ⟪htmul x y, Φ⟫_ℂ := by
  rw [contractL, ContinuousLinearMap.adjoint_inner_right]; rfl

end Tensor

section Dop
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The standard identification of `E^{⊗̂(1+n)}` with `E ⊗̂ E^{⊗̂ n}` (first factor separated). -/
def Dfull (n : ℕ) : HilbertTensorPower ℂ E (1 + n) →ₗᵢ[ℂ]
    HilbertTensor ℂ E (HilbertTensorPower ℂ E n) where
  toFun x := htmap (oneEquiv (E := E)).symm.toLinearIsometry.toContinuousLinearMap
    (ContinuousLinearMap.id ℂ _) (splitIsometry 1 n x)
  map_add' x y := by simp
  map_smul' c x := by simp
  norm_map' x := by
    show ‖htmap (oneEquiv (E := E)).symm.toLinearIsometry.toContinuousLinearMap
      (ContinuousLinearMap.id ℂ _) (splitIsometry 1 n x)‖ = ‖x‖
    rw [norm_htmap_iso, LinearIsometryEquiv.norm_map]

end Dop

section Calculus
open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem htpow_smul (n : ℕ) (c : ℂ) (u : E) :
    (htpow n (c • u) : HilbertTensorPower ℂ E n) = c ^ n • htpow n u := by
  have h := (PiTensorProduct.tprod ℂ (s := fun _ : Fin n => E)).map_smul_univ
    (fun _ : Fin n => c) (fun _ : Fin n => u)
  have h' : (ptprod (fun _ : Fin n => c • u) : AlgTensorPower ℂ E n) =
      c ^ n • (ptprod (fun _ : Fin n => u) : AlgTensorPower ℂ E n) := by
    have := h
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    exact this
  simp only [htpow]
  rw [h', UniformSpace.Completion.coe_smul]

theorem inner_htpow (n : ℕ) (u v : E) :
    ⟪(htpow n u : HilbertTensorPower ℂ E n), htpow n v⟫_ℂ = ⟪u, v⟫_ℂ ^ n := by
  simp only [htpow]
  rw [UniformSpace.Completion.inner_coe, inner_ptprod]
  simp

/-- `ptprod` as a (algebraic) complex multilinear map. -/
def ptprodML (n : ℕ) : MultilinearMap ℂ (fun _ : Fin n => E) (AlgTensorPower ℂ E n) where
  toFun := fun f => ptprod f
  map_update_add' := fun m i x y =>
    (PiTensorProduct.tprod ℂ (s := fun _ : Fin n => E)).map_update_add m i x y
  map_update_smul' := fun m i c x =>
    (PiTensorProduct.tprod ℂ (s := fun _ : Fin n => E)).map_update_smul m i c x

/-- `(f_i) ↦ f_0 ⊗ ⋯ ⊗ f_{n-1}` as a continuous real multilinear map into `E^{⊗̂ n}`. -/
def htpowML (n : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => E) (HilbertTensorPower ℂ E n) :=
  ((MultilinearMap.mkContinuous
    ((UniformSpace.Completion.toComplL : AlgTensorPower ℂ E n →L[ℂ] HilbertTensorPower ℂ E n).toLinearMap.compMultilinearMap
      (ptprodML n)) 1 (by
      intro f
      simp only [LinearMap.compMultilinearMap_apply, ContinuousLinearMap.coe_coe, one_mul]
      show ‖((ptprod f : AlgTensorPower ℂ E n) : HilbertTensorPower ℂ E n)‖ ≤ _
      rw [UniformSpace.Completion.norm_coe, norm_ptprod]) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => E) (HilbertTensorPower ℂ E n))).restrictScalars ℝ

theorem htpowML_apply (n : ℕ) (f : Fin n → E) :
    htpowML n f = ((ptprod f : AlgTensorPower ℂ E n) : HilbertTensorPower ℂ E n) := by
  simp [htpowML, ptprodML]
  rfl

/-- The real diagonal embedding `v ↦ (v, …, v)`. -/
def diagL (n : ℕ) : E →L[ℝ] (Fin n → E) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ E

/-- The Fréchet derivative of `u ↦ u^{⊗ n}`. -/
def dP (n : ℕ) (u : E) : E →L[ℝ] HilbertTensorPower ℂ E n :=
  (htpowML n).linearDeriv (fun _ => u) ∘L diagL n

theorem dP_apply (n : ℕ) (u h : E) :
    dP n u h = ∑ i : Fin n, ((ptprod (Function.update (fun _ : Fin n => u) i h) :
      AlgTensorPower ℂ E n) : HilbertTensorPower ℂ E n) := by
  simp [dP, diagL, ContinuousMultilinearMap.linearDeriv_apply, htpowML_apply]

theorem hasFDerivAt_htpow (n : ℕ) (u : E) :
    HasFDerivAt (fun v : E => (htpow n v : HilbertTensorPower ℂ E n)) (dP n u) u := by
  have h1 := (htpowML n).hasFDerivAt (fun _ : Fin n => u)
  have h2 := h1.comp u (diagL n).hasFDerivAt
  have h3 : (⇑(htpowML n) ∘ ⇑(diagL n)) =
      fun v : E => (htpow n v : HilbertTensorPower ℂ E n) := by
    funext v
    simp only [Function.comp_apply, htpowML_apply]
    rfl
  rw [h3] at h2
  exact h2

theorem inner_ptprod_update_same (n : ℕ) {u : E} (hu : ‖u‖ = 1) (h : E) (i : Fin n) :
    ⟪((ptprod (Function.update (fun _ : Fin n => u) i h) : AlgTensorPower ℂ E n) :
        HilbertTensorPower ℂ E n),
      ((ptprod (Function.update (fun _ : Fin n => u) i h) : AlgTensorPower ℂ E n) :
        HilbertTensorPower ℂ E n)⟫_ℂ = ⟪h, h⟫_ℂ := by
  have hu1 : ⟪u, u⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hu]; norm_num
  rw [UniformSpace.Completion.inner_coe, inner_ptprod]
  have : (fun k => ⟪Function.update (fun _ : Fin n => u) i h k,
      Function.update (fun _ : Fin n => u) i h k⟫_ℂ) =
      fun k => if k = i then ⟪h, h⟫_ℂ else 1 := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · rw [Function.update_of_ne hk]; simp only [hk, if_false]; exact hu1
  rw [this, Finset.prod_ite_eq']
  simp

theorem inner_ptprod_update_ne (n : ℕ) {u : E} (h : E) (hperp : ⟪u, h⟫_ℂ = 0) {i j : Fin n}
    (hij : i ≠ j) :
    ⟪((ptprod (Function.update (fun _ : Fin n => u) i h) : AlgTensorPower ℂ E n) :
        HilbertTensorPower ℂ E n),
      ((ptprod (Function.update (fun _ : Fin n => u) j h) : AlgTensorPower ℂ E n) :
        HilbertTensorPower ℂ E n)⟫_ℂ = 0 := by
  rw [UniformSpace.Completion.inner_coe, inner_ptprod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [Function.update_of_ne hij, Function.update_self, ← inner_conj_symm, hperp]
  simp

theorem inner_htpow_dP (n : ℕ) {u : E} (hu : ‖u‖ = 1) (h : E) :
    ⟪(htpow n u : HilbertTensorPower ℂ E n), dP n u h⟫_ℂ = (n : ℂ) * ⟪u, h⟫_ℂ := by
  have hu1 : ⟪u, u⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hu]; norm_num
  rw [dP_apply, inner_sum]
  have : ∀ i : Fin n, ⟪(htpow n u : HilbertTensorPower ℂ E n),
      ((ptprod (Function.update (fun _ : Fin n => u) i h) : AlgTensorPower ℂ E n) :
        HilbertTensorPower ℂ E n)⟫_ℂ = ⟪u, h⟫_ℂ := by
    intro i
    simp only [htpow]
    rw [UniformSpace.Completion.inner_coe, inner_ptprod]
    have : (fun k => ⟪(fun _ : Fin n => u) k, Function.update (fun _ : Fin n => u) i h k⟫_ℂ) =
        fun k => if k = i then ⟪u, h⟫_ℂ else 1 := by
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · rw [Function.update_of_ne hk]; simp only [hk, if_false]; exact hu1
    rw [this, Finset.prod_ite_eq']
    simp
  simp [this]

theorem norm_dP_sq (n : ℕ) {u : E} (hu : ‖u‖ = 1) {h : E} (hperp : ⟪u, h⟫_ℂ = 0) :
    ‖dP n u h‖ ^ 2 = n * ‖h‖ ^ 2 := by
  have hsum : ∀ i : Fin n,
      ⟪((ptprod (Function.update (fun _ : Fin n => u) i h) : AlgTensorPower ℂ E n) :
          HilbertTensorPower ℂ E n),
        ∑ j : Fin n, ((ptprod (Function.update (fun _ : Fin n => u) j h) :
          AlgTensorPower ℂ E n) : HilbertTensorPower ℂ E n)⟫_ℂ = ⟪h, h⟫_ℂ := by
    intro i
    rw [inner_sum, Finset.sum_eq_single i]
    · exact inner_ptprod_update_same n hu h i
    · intro j _ hji
      exact inner_ptprod_update_ne n h hperp (Ne.symm hji)
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have h1 : ⟪dP n u h, dP n u h⟫_ℂ = (n : ℂ) * ⟪h, h⟫_ℂ := by
    rw [dP_apply, sum_inner]
    rw [Finset.sum_congr rfl (fun i _ => hsum i)]
    simp
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
  have h2 : ((‖dP n u h‖ ^ 2 : ℝ) : ℂ) = ((n * ‖h‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; exact h1
  exact_mod_cast h2

theorem dP_smul_self (n : ℕ) (u : E) (c : ℂ) :
    dP n u (c • u) = ((n : ℂ) * c) • (htpow n u : HilbertTensorPower ℂ E n) := by
  rw [dP_apply]
  have : ∀ i : Fin n, ((ptprod (Function.update (fun _ : Fin n => u) i (c • u)) :
      AlgTensorPower ℂ E n) : HilbertTensorPower ℂ E n) = c • (htpow n u : HilbertTensorPower ℂ E n) := by
    intro i
    have h1 := (PiTensorProduct.tprod ℂ (s := fun _ : Fin n => E)).map_update_smul
      (fun _ : Fin n => u) i c u
    rw [Function.update_eq_self] at h1
    have h2 : (ptprod (Function.update (fun _ : Fin n => u) i (c • u)) : AlgTensorPower ℂ E n) =
        c • (ptprod (fun _ : Fin n => u) : AlgTensorPower ℂ E n) := h1
    rw [h2, UniformSpace.Completion.coe_smul]; rfl
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]

end Calculus

section RealBilinear
variable {A F : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option synthInstance.maxHeartbeats 400000 in
/-- `(x, y) ↦ x ⊗ y` as a bounded real-bilinear map. -/
def htmulB : A →L[ℝ] F →L[ℝ] HilbertTensor ℂ A F :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun x y => (htmul x y : HilbertTensor ℂ A F))
      (fun x x' y => htmul_add_left x x' y)
      (fun r x y => by
        rw [← Complex.coe_smul r x, htmul_smul_left, Complex.coe_smul])
      (fun x y y' => htmul_add_right x y y')
      (fun r x y => by
        rw [← Complex.coe_smul r y, htmul_smul_right, Complex.coe_smul])) 1
    (fun x y => by
      show ‖(htmul x y : HilbertTensor ℂ A F)‖ ≤ 1 * ‖x‖ * ‖y‖
      rw [norm_htmul]; exact le_of_eq (by ring))

theorem htmulB_apply (x : A) (y : F) : htmulB x y = (htmul x y : HilbertTensor ℂ A F) := rfl

end RealBilinear

section Curves
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Differentials along the sphere: for a map `X` defined on `H`, `fderivWithin` along the unit
sphere computes the derivative along any `C¹` curve that stays on the sphere. -/
theorem hasDerivAt_comp_curve {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X : H → V} {u : H} (hX : DifferentiableWithinAt ℝ X (Metric.sphere (0 : H) 1) u)
    {c : ℝ → H} (hc : ∀ t, c t ∈ Metric.sphere (0 : H) 1) (hc0 : c 0 = u) {v : H}
    (hcd : HasDerivAt c v 0) :
    HasDerivAt (X ∘ c) (fderivWithin ℝ X (Metric.sphere (0 : H) 1) u v) 0 := by
  have h1 : HasFDerivWithinAt X (fderivWithin ℝ X (Metric.sphere (0 : H) 1) u)
      (Metric.sphere (0 : H) 1) (c 0) := by
    rw [hc0]; exact hX.hasFDerivWithinAt
  have h2 := h1.comp_hasDerivWithinAt (x := (0 : ℝ)) (f := c) (s := Set.univ) hcd.hasDerivWithinAt
    (fun t _ => hc t)
  rw [hasDerivWithinAt_univ] at h2
  exact h2

/-- A `C¹` curve on the unit sphere with prescribed tangent velocity. -/
theorem exists_sphere_curve {u h : H} (hu : ‖u‖ = 1) (hh : (⟪u, h⟫_ℂ).re = 0) :
    ∃ c : ℝ → H, (∀ t, c t ∈ Metric.sphere (0 : H) 1) ∧ c 0 = u ∧ HasDerivAt c h 0 := by
  by_cases h0 : h = 0
  · subst h0
    exact ⟨fun _ => u, fun _ => by simp [hu], rfl, hasDerivAt_const _ _⟩
  · have hs : 0 < ‖h‖ := norm_pos_iff.mpr h0
    refine ⟨fun t => Real.cos (t * ‖h‖) • u + (Real.sin (t * ‖h‖) / ‖h‖) • h, ?_, ?_, ?_⟩
    · intro t
      rw [mem_sphere_zero_iff_norm]
      have key := norm_add_sq (𝕜 := ℂ) (Real.cos (t * ‖h‖) • u)
        ((Real.sin (t * ‖h‖) / ‖h‖) • h)
      have e0 : ⟪Real.cos (t * ‖h‖) • u, (Real.sin (t * ‖h‖) / ‖h‖) • h⟫_ℂ =
          ((Real.cos (t * ‖h‖) * (Real.sin (t * ‖h‖) / ‖h‖) : ℝ) : ℂ) * ⟪u, h⟫_ℂ := by
        rw [← Complex.coe_smul, ← Complex.coe_smul, inner_smul_left, inner_smul_right]
        simp only [Complex.conj_ofReal, Complex.ofReal_mul]
        ring
      rw [e0] at key
      have h2 : ‖Real.cos (t * ‖h‖) • u + (Real.sin (t * ‖h‖) / ‖h‖) • h‖ ^ 2 = 1 := by
        rw [key, norm_smul, norm_smul, hu]
        simp only [RCLike.re_to_complex]
        have e1 : (((Real.cos (t * ‖h‖) * (Real.sin (t * ‖h‖) / ‖h‖) : ℝ) : ℂ) *
            ⟪u, h⟫_ℂ).re = 0 := by
          rw [Complex.re_ofReal_mul, hh, mul_zero]
        rw [e1]
        simp only [Real.norm_eq_abs, mul_one, mul_zero, add_zero, mul_pow, sq_abs]
        rw [div_pow]
        field_simp
        nlinarith [Real.sin_sq_add_cos_sq (t * ‖h‖)]
      have h3 : ‖Real.cos (t * ‖h‖) • u + (Real.sin (t * ‖h‖) / ‖h‖) • h‖ = 1 := by
        have := norm_nonneg (Real.cos (t * ‖h‖) • u + (Real.sin (t * ‖h‖) / ‖h‖) • h)
        nlinarith [sq_nonneg (‖Real.cos (t * ‖h‖) • u + (Real.sin (t * ‖h‖) / ‖h‖) • h‖ - 1)]
      exact h3
    · simp [hu]
    · have h1 : HasDerivAt (fun t : ℝ => Real.cos (t * ‖h‖))
          (-Real.sin (0 * ‖h‖) * (1 * ‖h‖)) 0 :=
        ((hasDerivAt_id (0 : ℝ)).mul_const ‖h‖).cos
      have h2 : HasDerivAt (fun t : ℝ => Real.sin (t * ‖h‖) / ‖h‖)
          (Real.cos (0 * ‖h‖) * (1 * ‖h‖) / ‖h‖) 0 :=
        (((hasDerivAt_id (0 : ℝ)).mul_const ‖h‖).sin).div_const ‖h‖
      have h3 := (h1.smul_const u).add (h2.smul_const h)
      convert h3 using 1
      simp [hs.ne']

theorem phase_curve_mem {u : H} (hu : ‖u‖ = 1) (t : ℝ) :
    Complex.exp (t * Complex.I) • u ∈ Metric.sphere (0 : H) 1 := by
  rw [mem_sphere_zero_iff_norm, norm_smul, hu, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem phase_curve_deriv (u : H) :
    HasDerivAt (fun t : ℝ => Complex.exp (t * Complex.I) • u) (Complex.I • u) 0 := by
  have h1 : HasDerivAt (fun w : ℂ => Complex.exp (w * Complex.I)) Complex.I ((0 : ℝ) : ℂ) := by
    have := ((hasDerivAt_id (((0 : ℝ) : ℂ))).mul_const Complex.I).cexp
    simpa using this
  have h2 := h1.comp_ofReal
  have h3 := h2.smul_const u
  simpa using h3

end Curves

section Algebra
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- The pure algebra of the contact-form identity (no analysis). -/
theorem algebra_identity (F T F' T' : W) (hF : ‖F‖ = 1) (hT : ‖T‖ = 1) (N a zz : ℝ) (c : ℂ)
    (hc : c = ((N * a : ℝ) : ℂ) * Complex.I)
    (h1 : (⟪F, F'⟫_ℂ).im = N * a) (h2 : (⟪T, T'⟫_ℂ).im = zz + (N - 1) * a) :
    a - zz = (⟪T, F' - T'⟫_ℂ + ⟪T', F - T⟫_ℂ).im +
      (⟪F - T, (F' - c • F) + (T' - c • T)⟫_ℂ).im := by
  have hFF : ⟪F, F⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hF]; norm_num
  have hTT : ⟪T, T⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hT]; norm_num
  have e1 : ⟪T', F⟫_ℂ = (starRingEnd ℂ) ⟪F, T'⟫_ℂ := (inner_conj_symm T' F).symm
  have e2 : ⟪T', T⟫_ℂ = (starRingEnd ℂ) ⟪T, T'⟫_ℂ := (inner_conj_symm T' T).symm
  have e3 : ⟪T, F⟫_ℂ = (starRingEnd ℂ) ⟪F, T⟫_ℂ := (inner_conj_symm T F).symm
  simp only [inner_sub_left, inner_sub_right, inner_add_right, inner_add_left, inner_smul_right,
    hFF, hTT, e1, e2, e3]
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    hc, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_im,
    Complex.one_re, Complex.sub_re, Complex.add_re, Complex.mul_re]
  nlinarith [h1, h2]

end Algebra

section Contact
open Filter Topology

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]

/-- The data of `contact.tex` §"The full annihilation row": fixed unitaries
`J_N : Sym^N H → Sym^N K` and a `C¹` map `z` from the unit sphere of `H` into the unit sphere of
`K` with `z(e^{iθ}u) = e^{iθ}z(u)`. -/
structure ContactSetup (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [TopologicalSpace.SeparableSpace K] where
  J : ∀ N : ℕ, SymSector ℂ H N ≃ₗᵢ[ℂ] SymSector ℂ K N
  z : H → K
  z_unit : ∀ u : H, ‖u‖ = 1 → ‖z u‖ = 1
  z_equivariant : ∀ u : H, ‖u‖ = 1 → ∀ θ : ℝ,
    z (Complex.exp (θ * Complex.I) • u) = Complex.exp (θ * Complex.I) • z u
  z_contDiffOn : ContDiffOn ℝ 1 z (Metric.sphere (0 : H) 1)

namespace ContactSetup
variable (S : ContactSetup H K)

/-- `g_N(u) = J_N u^{⊗N}`. -/
def g (N : ℕ) (u : H) : SymSector ℂ K N :=
  S.J N ⟨htpow N u, htpow_mem_symSector N u⟩

/-- Ambient extension of `J_N`: `J_N` composed with the orthogonal projection onto `Sym^N H`. -/
def Jext (N : ℕ) : HilbertTensorPower ℂ H N →L[ℂ] HilbertTensorPower ℂ K N :=
  (SymSector ℂ K N).subtypeL ∘L (S.J N).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (SymSector ℂ H N).orthogonalProjectionOnto

theorem Jext_apply (N : ℕ) (x : HilbertTensorPower ℂ H N) :
    S.Jext N x = ((S.J N ((SymSector ℂ H N).orthogonalProjectionOnto x) : SymSector ℂ K N) :
      HilbertTensorPower ℂ K N) := rfl

theorem g_eq (N : ℕ) (u : H) :
    ((S.g N u : SymSector ℂ K N) : HilbertTensorPower ℂ K N) = S.Jext N (htpow N u) := by
  rw [Jext_apply, g]
  congr 2
  exact (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
    (⟨htpow N u, htpow_mem_symSector N u⟩ : SymSector ℂ H N)).symm

theorem inner_Jext (N : ℕ) {x : HilbertTensorPower ℂ H N} (hx : x ∈ SymSector ℂ H N)
    (y : HilbertTensorPower ℂ H N) :
    ⟪S.Jext N x, S.Jext N y⟫_ℂ = ⟪x, y⟫_ℂ := by
  have h1 : (SymSector ℂ H N).orthogonalProjectionOnto x = ⟨x, hx⟩ :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨x, hx⟩ : SymSector ℂ H N)
  rw [Jext_apply, Jext_apply, h1]
  rw [← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (⟨x, hx⟩ : SymSector ℂ H N) y

theorem norm_Jext_le (N : ℕ) (y : HilbertTensorPower ℂ H N) : ‖S.Jext N y‖ ≤ ‖y‖ := by
  rw [Jext_apply, Submodule.norm_coe, LinearIsometryEquiv.norm_map]
  exact Submodule.norm_orthogonalProjectionOnto_apply_le _ y

/-- The annihilation operator `b(f)` on `Sym^N K`, `N = 1+n`: `b(f)ψ = √N (⟨f| ⊗ 1) ψ`, the first
factor of the symmetric tensor contracted with `f` (antilinear in `f`). -/
def ann (f : K) (n : ℕ) (ψ : HilbertTensorPower ℂ K (1 + n)) : HilbertTensorPower ℂ K n :=
  Real.sqrt ((1 + n : ℕ) : ℝ) • contractL f (Dfull n ψ)

/-- `D_N` on `Sym^N K`, `N = 1+n`: the first factor of a symmetric tensor separated. -/
def Dop (n : ℕ) : SymSector ℂ K (1 + n) →ₗᵢ[ℂ] HilbertTensor ℂ K (HilbertTensorPower ℂ K n) :=
  (Dfull n).comp (SymSector ℂ K (1 + n)).subtypeₗᵢ

/-- `F_N(u) = D_N g_N(u)`, `N = 1+n`. -/
def F (n : ℕ) (u : H) : HilbertTensor ℂ K (HilbertTensorPower ℂ K n) :=
  Dop n (S.g (1 + n) u)

/-- `T_N(u) = z(u) ⊗ g_{N-1}(u)`, `N = 1+n`. -/
def T (n : ℕ) (u : H) : HilbertTensor ℂ K (HilbertTensorPower ℂ K n) :=
  htmul (S.z u) ((S.g n u : SymSector ℂ K n) : HilbertTensorPower ℂ K n)

/-- `R_N = F_N - T_N`. -/
def R (n : ℕ) (u : H) : HilbertTensor ℂ K (HilbertTensorPower ℂ K n) := S.F n u - S.T n u

theorem norm_g (N : ℕ) {u : H} (hu : ‖u‖ = 1) : ‖(S.g N u : HilbertTensorPower ℂ K N)‖ = 1 := by
  have : ‖S.g N u‖ = 1 := by
    simp [g, norm_htpow, hu]
  simpa using this

theorem norm_F {n : ℕ} {u : H} (hu : ‖u‖ = 1) : ‖S.F n u‖ = 1 := by
  simp only [F, LinearIsometry.norm_map]
  simpa using S.norm_g (1 + n) hu

theorem norm_T {n : ℕ} {u : H} (hu : ‖u‖ = 1) : ‖S.T n u‖ = 1 := by
  simp only [T, norm_htmul]
  rw [S.z_unit u hu, S.norm_g n hu]; norm_num

theorem inner_T_F (n : ℕ) (u : H) :
    ⟪S.T n u, S.F n u⟫_ℂ =
      ⟪((S.g n u : SymSector ℂ K n) : HilbertTensorPower ℂ K n),
        (Real.sqrt ((1 + n : ℕ) : ℝ))⁻¹ • ann (S.z u) n
          ((S.g (1 + n) u : SymSector ℂ K (1 + n)) : HilbertTensorPower ℂ K (1 + n))⟫_ℂ := by
  have hpos : Real.sqrt ((1 + n : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < ((1 + n : ℕ) : ℝ) := by positivity
    exact (Real.sqrt_pos.mpr this).ne'
  have hF : S.F n u = Dfull n ((S.g (1 + n) u : SymSector ℂ K (1 + n)) :
      HilbertTensorPower ℂ K (1 + n)) := rfl
  rw [hF, ann, smul_smul, inv_mul_cancel₀ hpos, one_smul, inner_contractL]
  rfl

end ContactSetup

/-- **R-E5ACFD2A** (`intr:contact:eq:P1`): for a fixed unit input `u`, qualitative P1
(`b(f)/√N g_N(u) − ⟨f,z(u)⟩ g_{N-1}(u) → 0` in norm for every fixed `f ∈ K`) implies
`‖R_N(u)‖ → 0`.  Here `N = 1 + n`, `n → ∞`. -/
theorem lemma_P1 (S : ContactSetup H K) (u : H) (hu : ‖u‖ = 1)
    (hP1 : ∀ f : K, Tendsto (fun n : ℕ =>
      ‖(Real.sqrt ((1 + n : ℕ) : ℝ))⁻¹ • ContactSetup.ann f n
          ((S.g (1 + n) u : SymSector ℂ K (1 + n)) : HilbertTensorPower ℂ K (1 + n))
        - ⟪f, S.z u⟫_ℂ • ((S.g n u : SymSector ℂ K n) : HilbertTensorPower ℂ K n)‖)
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ‖S.R n u‖) atTop (𝓝 0) := by
  set X : ℕ → ℝ := fun n =>
    ‖(Real.sqrt ((1 + n : ℕ) : ℝ))⁻¹ • ContactSetup.ann (S.z u) n
          ((S.g (1 + n) u : SymSector ℂ K (1 + n)) : HilbertTensorPower ℂ K (1 + n))
        - ⟪S.z u, S.z u⟫_ℂ • ((S.g n u : SymSector ℂ K n) : HilbertTensorPower ℂ K n)‖ with hXdef
  have hX : Tendsto X atTop (𝓝 0) := hP1 (S.z u)
  have hzz : ⟪S.z u, S.z u⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, S.z_unit u hu]; norm_num
  have key : ∀ n : ℕ, ‖S.R n u‖ ^ 2 ≤ 2 * X n := by
    intro n
    set g0 : HilbertTensorPower ℂ K n := ((S.g n u : SymSector ℂ K n) : HilbertTensorPower ℂ K n)
    set c : HilbertTensorPower ℂ K n := (Real.sqrt ((1 + n : ℕ) : ℝ))⁻¹ • ContactSetup.ann (S.z u) n
          ((S.g (1 + n) u : SymSector ℂ K (1 + n)) : HilbertTensorPower ℂ K (1 + n)) with hc
    have hinner : ⟪S.T n u, S.F n u⟫_ℂ = ⟪g0, c⟫_ℂ := S.inner_T_F n u
    have hg0 : ‖g0‖ = 1 := S.norm_g n hu
    have hXn : X n = ‖c - g0‖ := by
      simp only [hXdef, hzz, one_smul]
      rfl
    have h1 : ⟪g0, g0⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hg0]; norm_num
    have h2 : ⟪g0, c⟫_ℂ - 1 = ⟪g0, c - g0⟫_ℂ := by
      rw [inner_sub_right, h1]
    have h3 : ‖⟪g0, c - g0⟫_ℂ‖ ≤ X n := by
      rw [hXn]
      calc ‖⟪g0, c - g0⟫_ℂ‖ ≤ ‖g0‖ * ‖c - g0‖ := norm_inner_le_norm _ _
        _ = ‖c - g0‖ := by rw [hg0, one_mul]
    have hR : ‖S.R n u‖ ^ 2 = 2 - 2 * (⟪S.T n u, S.F n u⟫_ℂ).re := by
      have := norm_sub_sq (𝕜 := ℂ) (S.F n u) (S.T n u)
      rw [ContactSetup.R, this, S.norm_F hu, S.norm_T hu]
      have hre : (⟪S.F n u, S.T n u⟫_ℂ).re = (⟪S.T n u, S.F n u⟫_ℂ).re := by
        have h := congrArg Complex.re (inner_conj_symm (𝕜 := ℂ) (S.T n u) (S.F n u))
        rw [Complex.conj_re] at h
        exact h
      simp only [RCLike.re_to_complex]
      rw [hre]; ring
    rw [hR, hinner]
    have h4 : -‖⟪g0, c - g0⟫_ℂ‖ ≤ (⟪g0, c - g0⟫_ℂ).re := by
      have := Complex.abs_re_le_norm ⟪g0, c - g0⟫_ℂ
      have := neg_abs_le (⟪g0, c - g0⟫_ℂ).re
      linarith
    have h8 : (⟪g0, c⟫_ℂ - 1).re = (⟪g0, c⟫_ℂ).re - 1 := by simp
    rw [h2] at h8
    linarith
  have hsqrt : Tendsto (fun n => Real.sqrt (2 * X n)) atTop (𝓝 0) := by
    have : Tendsto (fun n => 2 * X n) atTop (𝓝 0) := by simpa using hX.const_mul 2
    have h9 := (Real.continuous_sqrt.tendsto 0).comp this
    rwa [Real.sqrt_zero] at h9
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hsqrt
  exact Real.le_sqrt_of_sq_le (key n)

namespace ContactSetup
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K] [TopologicalSpace.SeparableSpace K] (S : ContactSetup H K)

/-- `Φ_n = D ∘ J_ext` so that `F_{1+n}(u) = Φ_n (u^{⊗(1+n)})`. -/
def Phi (n : ℕ) : HilbertTensorPower ℂ H (1 + n) →L[ℂ]
    HilbertTensor ℂ K (HilbertTensorPower ℂ K n) :=
  (Dfull n).toContinuousLinearMap ∘L S.Jext (1 + n)

theorem F_eq (n : ℕ) (u : H) : S.F n u = S.Phi n (htpow (1 + n) u) := by
  show Dfull n ((S.g (1 + n) u : SymSector ℂ K (1 + n)) : HilbertTensorPower ℂ K (1 + n)) = _
  rw [g_eq]; rfl

theorem hasFDerivAt_F (n : ℕ) (u : H) :
    HasFDerivAt (S.F n) ((S.Phi n).restrictScalars ℝ ∘L dP (1 + n) u) u := by
  have h := ((S.Phi n).restrictScalars ℝ).hasFDerivAt.comp u (hasFDerivAt_htpow (1 + n) u)
  have h3 : (⇑((S.Phi n).restrictScalars ℝ) ∘ fun v : H => (htpow (1 + n) v : HilbertTensorPower ℂ H (1 + n))) = S.F n := by
    funext v; exact (S.F_eq n v).symm
  rw [h3] at h
  exact h

theorem hasFDerivAt_gg (n : ℕ) (u : H) :
    HasFDerivAt (fun v : H => ((S.g n v : SymSector ℂ K n) : HilbertTensorPower ℂ K n))
      ((S.Jext n).restrictScalars ℝ ∘L dP n u) u := by
  have h := ((S.Jext n).restrictScalars ℝ).hasFDerivAt.comp u (hasFDerivAt_htpow n u)
  have h3 : (⇑((S.Jext n).restrictScalars ℝ) ∘ fun v : H => (htpow n v : HilbertTensorPower ℂ H n)) =
      fun v : H => ((S.g n v : SymSector ℂ K n) : HilbertTensorPower ℂ K n) := by
    funext v; exact (S.g_eq n v).symm
  rw [h3] at h
  exact h

theorem inner_F_dF (n : ℕ) {u : H} (hu : ‖u‖ = 1) (h : H) :
    ⟪S.F n u, S.Phi n (dP (1 + n) u h)⟫_ℂ = ((1 + n : ℕ) : ℂ) * ⟪u, h⟫_ℂ := by
  rw [S.F_eq]
  simp only [Phi, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.inner_map_map]
  rw [S.inner_Jext _ (htpow_mem_symSector (1 + n) u), inner_htpow_dP _ hu]

theorem inner_g_dg (n : ℕ) {u : H} (hu : ‖u‖ = 1) (h : H) :
    ⟪((S.g n u : SymSector ℂ K n) : HilbertTensorPower ℂ K n), S.Jext n (dP n u h)⟫_ℂ =
      (n : ℂ) * ⟪u, h⟫_ℂ := by
  rw [S.g_eq, S.inner_Jext _ (htpow_mem_symSector n u), inner_htpow_dP _ hu]

theorem norm_Phi_dP_le (n : ℕ) {u : H} (hu : ‖u‖ = 1) {h : H} (hperp : ⟪u, h⟫_ℂ = 0) :
    ‖S.Phi n (dP (1 + n) u h)‖ ≤ Real.sqrt ((1 + n : ℕ) : ℝ) * ‖h‖ := by
  have h1 := norm_dP_sq (1 + n) hu hperp
  have h2 : ‖dP (1 + n) u h‖ = Real.sqrt ((1 + n : ℕ) : ℝ) * ‖h‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (dP (1 + n) u h)), h1,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  rw [← h2]
  simp only [Phi, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.norm_map]
  exact S.norm_Jext_le _ _

theorem norm_Jext_dP_le (n : ℕ) {u : H} (hu : ‖u‖ = 1) {h : H} (hperp : ⟪u, h⟫_ℂ = 0) :
    ‖S.Jext n (dP n u h)‖ ≤ Real.sqrt (n : ℝ) * ‖h‖ := by
  have h1 := norm_dP_sq n hu hperp
  have h2 : ‖dP n u h‖ = Real.sqrt (n : ℝ) * ‖h‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (dP n u h)), h1,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  rw [← h2]
  exact S.norm_Jext_le _ _

end ContactSetup

end Contact

/-! ## Axiom audit -/
#print axioms lemma_P1
#print axioms ContactSetup.inner_T_F
#print axioms hasFDerivAt_htpow
#print axioms norm_dP_sq
#print axioms ContactSetup.inner_F_dF
#print axioms exists_sphere_curve
#print axioms algebra_identity

end QuantumNLS.IntrinsicContact
