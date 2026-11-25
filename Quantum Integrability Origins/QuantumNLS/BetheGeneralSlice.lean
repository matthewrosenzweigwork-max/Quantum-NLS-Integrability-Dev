import QuantumNLS.BetheTensorSlice

/-! The literal degree-one tensor slice with an arbitrary finite spectator
block. Source periodic_basis.tex:316–333. All maps are constructed on the
actual completed tensor and ordinary-volume L² carriers. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace ComplexConjugate
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
namespace QuantumNLS.BetheGeneralSlice
open TensorCarrier TensorPlacements PhysicalTensor TensorFourier BetheIntegralOperator
variable (L : ℝ) [Fact (0 < L)] (q : ℕ)

/-- Integrate the first slot and leave the second slot fixed. -/
def slice (k : Kernel (volume : Measure (AddCircle L)))
    (F : C(Fin (1+q) → AddCircle L, ℂ)) (x : Fin (1+q) → AddCircle L) : ℂ :=
  ∫ t, k.fn (x (Fin.castAdd q 0),t) * F (Fin.append (fun _ : Fin 1 => t) (fun i : Fin q => x (Fin.natAdd 1 i)))

theorem integrable_slice (k : Kernel (volume : Measure (AddCircle L)))
    (F : C(Fin (1+q) → AddCircle L, ℂ)) (x : Fin (1+q) → AddCircle L) :
    Integrable (fun t => k.fn (x (Fin.castAdd q 0),t) * F (Fin.append (fun _ : Fin 1 => t) (fun i : Fin q => x (Fin.natAdd 1 i)))) := by
  apply Integrable.of_bound
    ((k.measurable.comp (measurable_const.prodMk measurable_id)).mul
      (F.continuous.measurable.comp (by fun_prop))).aestronglyMeasurable (k.bound * ‖F‖)
  filter_upwards with t
  change ‖k.fn (x (Fin.castAdd q 0),t) * F (Fin.append (fun _ : Fin 1 => t) (fun i : Fin q => x (Fin.natAdd 1 i)))‖ ≤ k.bound * ‖F‖
  rw [norm_mul]
  exact mul_le_mul (k.norm_le _) (F.norm_coe_le_norm _) (norm_nonneg _) k.bound_nonneg

theorem norm_slice_le (k : Kernel (volume : Measure (AddCircle L)))
    (F : C(Fin (1+q) → AddCircle L, ℂ)) (x : Fin (1+q) → AddCircle L) :
    ‖slice L q k F x‖ ≤ (volume : Measure (AddCircle L)).real univ * k.bound * ‖F‖ := by
  calc
    _ ≤ ∫ _t : AddCircle L, k.bound * ‖F‖ := by
      apply norm_integral_le_of_norm_le (integrable_const _)
      filter_upwards with t
      rw [norm_mul]
      exact mul_le_mul (k.norm_le _) (F.norm_coe_le_norm _) (norm_nonneg _) k.bound_nonneg
    _ = _ := by rw [integral_const]; simp [smul_eq_mul, mul_assoc]

theorem memLp_slice (k : Kernel (volume : Measure (AddCircle L)))
    (F : C(Fin (1+q) → AddCircle L, ℂ)) : MemLp (slice L q k F) 2 (torusPiMeasure L (1+q)) := by
  apply MemLp.of_bound _ _ (Filter.Eventually.of_forall (norm_slice_le L q k F))
  have hm : Measurable (fun p : (Fin (1+q) → AddCircle L) × AddCircle L =>
      k.fn (p.1 (Fin.castAdd q 0),p.2) * F (Fin.append (fun _ : Fin 1 => p.2) (fun i : Fin q => p.1 (Fin.natAdd 1 i)))) := by
    apply Measurable.mul
    · exact k.measurable.comp (by fun_prop)
    · exact F.continuous.measurable.comp (by fun_prop)
  exact hm.aestronglyMeasurable.integral_prod_right'

/-- The actual integral slice as a bounded map from continuous functions to L². -/
def sliceMap (k : Kernel (volume : Measure (AddCircle L))) :
    C(Fin (1+q) → AddCircle L, ℂ) →L[ℂ] L2TN L (1+q) :=
  LinearMap.mkContinuous
    { toFun := fun F => (memLp_slice L q k F).toLp _
      map_add' := by
        intro F G
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_slice L q k (F+G)),
          Lp.coeFn_add ((memLp_slice L q k F).toLp _) ((memLp_slice L q k G).toLp _),
          MemLp.coeFn_toLp (memLp_slice L q k F), MemLp.coeFn_toLp (memLp_slice L q k G)]
          with x h hsum hf hg
        rw [h, hsum]
        simp only [Pi.add_apply, hf, hg, slice, ContinuousMap.add_apply, mul_add]
        exact integral_add (integrable_slice L q k F x) (integrable_slice L q k G x)
      map_smul' := by
        intro a F
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_slice L q k (a • F)),
          Lp.coeFn_smul a ((memLp_slice L q k F).toLp _),
          MemLp.coeFn_toLp (memLp_slice L q k F)] with x h hs hf
        change _ = (a • (memLp_slice L q k F).toLp _) x
        rw [h, hs]
        simp only [Pi.smul_apply, hf, slice, ContinuousMap.smul_apply, smul_eq_mul]
        simp_rw [mul_left_comm (k.fn _) a]
        exact integral_const_mul _ _ }
    ((measureUnivNNReal (torusPiMeasure L (1+q)) : ℝ) ^ (2 : ℝ)⁻¹ *
      ((volume : Measure (AddCircle L)).real univ * k.bound))
    (by
      intro F
      calc
        _ ≤ (measureUnivNNReal (torusPiMeasure L (1+q)) : ℝ) ^ (2 : ℝ)⁻¹ *
            ((volume : Measure (AddCircle L)).real univ * k.bound * ‖F‖) := by
          apply Lp.norm_le_of_ae_bound (mul_nonneg
            (mul_nonneg (measureReal_nonneg) k.bound_nonneg) (norm_nonneg F))
          filter_upwards [MemLp.coeFn_toLp (memLp_slice L q k F)] with x hx
          change ‖((memLp_slice L q k F).toLp (slice L q k F)) x‖ ≤ _
          rw [hx]
          exact norm_slice_le L q k F x
        _ = _ := by ring)

theorem coe_sliceMap (k : Kernel (volume : Measure (AddCircle L)))
    (F : C(Fin (1+q) → AddCircle L, ℂ)) :
    sliceMap L q k F =ᵐ[torusPiMeasure L (1+q)] slice L q k F := (memLp_slice L q k F).coeFn_toLp


/-- A one-factor operator acts on the head of an arbitrary product tensor. -/
theorem firstPlacement_product
    (A : SymSector ℂ (L2T L) 1 →L[ℂ] SymSector ℂ (L2T L) 1)
    (f : L2T L) (g : Fin q → L2T L) :
    firstPlacement (q := q) A
      ((ptprod (Fin.append (fun _ : Fin 1 => f) g) :
        AlgTensorPower ℂ (L2T L) (1+q)) : HilbertTensorPower ℂ (L2T L) (1+q)) =
      ((ptprod (Fin.append (fun _ : Fin 1 => firstPowerIso (extendSymKernel A
          ((ptprod (fun _ : Fin 1 => f) : AlgTensorPower ℂ (L2T L) 1) :
            HilbertTensorPower ℂ (L2T L) 1))) g) :
          AlgTensorPower ℂ (L2T L) (1+q)) : HilbertTensorPower ℂ (L2T L) (1+q)) := by
  apply (splitIsometry 1 q).injective
  simp only [firstPlacement, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.apply_symm_apply]
  rw [splitIsometry_ptprod_append, htmap_htmul, ContinuousLinearMap.id_apply,
    splitIsometry_ptprod_append, BetheTensorSlice.singleton_tensor]

/-- The actual placement transported to continuous position inputs. -/
def tensorMap
    (A : SymSector ℂ (L2T L) 1 →L[ℂ] SymSector ℂ (L2T L) 1) :
    C(Fin (1+q) → AddCircle L, ℂ) →L[ℂ] L2TN L (1+q) :=
  (physUnitary (L := L) (N := 1+q)).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    firstPlacement (q := q) A ∘L
    (physUnitary (L := L) (N := 1+q)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    ContinuousMap.toLp 2 (torusPiMeasure L (1+q)) ℂ

theorem toLp_prodCont (g : Fin (1+q) → C(AddCircle L, ℂ)) :
    ContinuousMap.toLp 2 (torusPiMeasure L (1+q)) ℂ (prodCont g) =
      prodLp (fun i => ContinuousMap.toLp 2 volume ℂ (g i)) := by
  apply Lp.ext
  have h : ∀ᵐ x ∂torusPiMeasure L (1+q), ∀ i,
      (ContinuousMap.toLp 2 volume ℂ (g i) : L2T L) (x i) = g i (x i) := by
    rw [ae_all_iff]
    intro i
    exact (Measure.quasiMeasurePreserving_eval
      (fun _ : Fin (1+q) => (volume : Measure (AddCircle L))) i).ae
      (ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ) volume (g i))
  filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ)
      (torusPiMeasure L (1+q)) (prodCont g),
    (memLp_prodFun (fun i => ContinuousMap.toLp 2 volume ℂ (g i))).coeFn_toLp, h]
    with x hx hy hh
  rw [hx]
  change prodLp (fun i => ContinuousMap.toLp 2 volume ℂ (g i)) x = _ at hy
  rw [hy, prodCont_apply, prodFun]
  exact Finset.prod_congr rfl (fun i _ => (hh i).symm)


/-- Explicit head/spectator decomposition, valid also for zero spectators. -/
theorem append_split {α : Type*} (g : Fin (1+q) → α) :
    g = Fin.append (fun _ : Fin 1 => g (Fin.castAdd q 0))
      (fun i : Fin q => g (Fin.natAdd 1 i)) := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left, Subsingleton.elim j 0]
  · rw [Fin.append_right]

theorem tensorMap_product
    (A : SymSector ℂ (L2T L) 1 →L[ℂ] SymSector ℂ (L2T L) 1)
    (k : Kernel (volume : Measure (AddCircle L)))
    (hk : ∀ v, firstPowerIso (extendSymKernel A v) = k.operator (firstPowerIso v))
    (g : Fin (1+q) → C(AddCircle L, ℂ)) :
    tensorMap L q A (prodCont g) =
      prodLp (Fin.append
        (fun _ : Fin 1 => k.operator (ContinuousMap.toLp 2 volume ℂ (g (Fin.castAdd q 0))))
        (fun i : Fin q => ContinuousMap.toLp 2 volume ℂ (g (Fin.natAdd 1 i)))) := by
  change physUnitary (firstPlacement (q := q) A
    ((physUnitary (L := L) (N := 1+q)).symm
      (ContinuousMap.toLp 2 (torusPiMeasure L (1+q)) ℂ (prodCont g)))) = _
  rw [toLp_prodCont L q g, ← physUnitary_ptprod, LinearIsometryEquiv.symm_apply_apply]
  rw [append_split q (fun i => ContinuousMap.toLp 2 volume ℂ (g i)),
    firstPlacement_product, hk, firstPowerIso_ptprod, physUnitary_ptprod]

theorem sliceMap_product (k : Kernel (volume : Measure (AddCircle L)))
    (g : Fin (1+q) → C(AddCircle L, ℂ)) :
    sliceMap L q k (prodCont g) =
      prodLp (Fin.append
        (fun _ : Fin 1 => k.operator (ContinuousMap.toLp 2 volume ℂ (g (Fin.castAdd q 0))))
        (fun i : Fin q => ContinuousMap.toLp 2 volume ℂ (g (Fin.natAdd 1 i)))) := by
  let f : L2T L := ContinuousMap.toLp 2 volume ℂ (g (Fin.castAdd q 0))
  let h : Fin q → L2T L := fun i => ContinuousMap.toLp 2 volume ℂ (g (Fin.natAdd 1 i))
  have hact := (Measure.quasiMeasurePreserving_eval
    (fun _ : Fin (1+q) => (volume : Measure (AddCircle L))) (Fin.castAdd q 0)).ae
      (k.operator_apply_ae f)
  have hh : ∀ᵐ x ∂torusPiMeasure L (1+q), ∀ i : Fin q,
      h i (x (Fin.natAdd 1 i)) = g (Fin.natAdd 1 i) (x (Fin.natAdd 1 i)) := by
    rw [ae_all_iff]
    intro i
    exact (Measure.quasiMeasurePreserving_eval
      (fun _ : Fin (1+q) => (volume : Measure (AddCircle L))) (Fin.natAdd 1 i)).ae
        (ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ) volume (g (Fin.natAdd 1 i)))
  apply Lp.ext
  filter_upwards [coe_sliceMap L q k (prodCont g),
    (memLp_prodFun (Fin.append (fun _ : Fin 1 => k.operator f) h)).coeFn_toLp,
    hact, hh] with x hx hp ha hb
  rw [hx]
  change prodLp (Fin.append (fun _ : Fin 1 => k.operator f) h) x = _ at hp
  rw [hp]
  simp only [prodFun, Fin.prod_univ_add, Fin.prod_univ_one,
    Fin.append_left, Fin.append_right, ha, hb]
  have hi : (∫ t, k.fn (x (Fin.castAdd q 0),t) * f t) =
      ∫ t, k.fn (x (Fin.castAdd q 0),t) * g (Fin.castAdd q 0) t := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ)
      volume (g (Fin.castAdd q 0))] with t ht
    rw [show f t = g (Fin.castAdd q 0) t from ht]
  rw [hi, ← integral_mul_const]
  unfold slice
  apply integral_congr_ae
  filter_upwards with t
  simp only [prodCont_apply, Fin.prod_univ_add, Fin.prod_univ_one,
    Fin.append_left, Fin.append_right]
  ring

/-- Density proves the completed tensor action for every continuous N-body
input, with an arbitrary finite spectator block. -/
theorem tensorMap_eq_sliceMap
    (A : SymSector ℂ (L2T L) 1 →L[ℂ] SymSector ℂ (L2T L) 1)
    (k : Kernel (volume : Measure (AddCircle L)))
    (hk : ∀ v, firstPowerIso (extendSymKernel A v) = k.operator (firstPowerIso v)) :
    tensorMap L q A = sliceMap L q k := by
  have hprod : ∀ F ∈ (prodAlgebra L (1+q) : Set C(Fin (1+q) → AddCircle L, ℂ)),
      tensorMap L q A F = sliceMap L q k F := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem F hF =>
      obtain ⟨g, rfl⟩ := hF
      rw [tensorMap_product L q A k hk, sliceMap_product]
    | zero => rw [map_zero, map_zero]
    | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
    | smul c a _ ha => rw [map_smul, map_smul, ha]
  apply ContinuousLinearMap.ext
  intro F
  have hF : F ∈ closure (prodAlgebra L (1+q) : Set C(Fin (1+q) → AddCircle L, ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe, prodAlgebra_dense]; trivial
  exact closure_minimal hprod
    (isClosed_eq (tensorMap L q A).continuous (sliceMap L q k).continuous) hF

open BethePhysicalTransfer BetheTensorSlice

/-- Actual physical degree-one placement, with no assumed action bridge. -/
theorem physical_tensorMap_eq_sliceMap (z : ℂ) :
    tensorMap L q (physicalKernel L 1 z) =
      sliceMap L q (physicalScalarKernel L z) :=
  tensorMap_eq_sliceMap L q _ _ (physicalScalarKernel_action L z)

end QuantumNLS.BetheGeneralSlice

#print axioms QuantumNLS.BetheGeneralSlice.slice
#print axioms QuantumNLS.BetheGeneralSlice.integrable_slice
#print axioms QuantumNLS.BetheGeneralSlice.norm_slice_le
#print axioms QuantumNLS.BetheGeneralSlice.memLp_slice
#print axioms QuantumNLS.BetheGeneralSlice.sliceMap
#print axioms QuantumNLS.BetheGeneralSlice.coe_sliceMap
#print axioms QuantumNLS.BetheGeneralSlice.firstPlacement_product
#print axioms QuantumNLS.BetheGeneralSlice.tensorMap
#print axioms QuantumNLS.BetheGeneralSlice.toLp_prodCont
#print axioms QuantumNLS.BetheGeneralSlice.append_split
#print axioms QuantumNLS.BetheGeneralSlice.tensorMap_product
#print axioms QuantumNLS.BetheGeneralSlice.sliceMap_product
#print axioms QuantumNLS.BetheGeneralSlice.tensorMap_eq_sliceMap
#print axioms QuantumNLS.BetheGeneralSlice.physical_tensorMap_eq_sliceMap
