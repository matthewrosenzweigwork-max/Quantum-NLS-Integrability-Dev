import QuantumNLS.BetheTwoParticlePlacement
import QuantumNLS.TensorFourier

/-! Completed tensor placement equals literal slice integration.
Ordinary torus volume is retained. The proof uses the dense algebra of
continuous product functions, not an assumed coordinate action formula. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace ComplexConjugate
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
namespace QuantumNLS.BetheTensorSlice
open TensorCarrier TensorPlacements PhysicalTensor TensorFourier BetheIntegralOperator
variable (L : ℝ) [Fact (0 < L)]

/-- Integrate the first slot and leave the second slot fixed. -/
def slice (k : Kernel (volume : Measure (AddCircle L)))
    (F : C(Fin 2 → AddCircle L, ℂ)) (x : Fin 2 → AddCircle L) : ℂ :=
  ∫ t, k.fn (x 0,t) * F ![t,x 1]

theorem integrable_slice (k : Kernel (volume : Measure (AddCircle L)))
    (F : C(Fin 2 → AddCircle L, ℂ)) (x : Fin 2 → AddCircle L) :
    Integrable (fun t => k.fn (x 0,t) * F ![t,x 1]) := by
  apply Integrable.of_bound
    ((k.measurable.comp (measurable_const.prodMk measurable_id)).mul
      (F.continuous.measurable.comp (by fun_prop))).aestronglyMeasurable (k.bound * ‖F‖)
  filter_upwards with t
  change ‖k.fn (x 0,t) * F ![t,x 1]‖ ≤ k.bound * ‖F‖
  rw [norm_mul]
  exact mul_le_mul (k.norm_le _) (F.norm_coe_le_norm _) (norm_nonneg _) k.bound_nonneg

theorem norm_slice_le (k : Kernel (volume : Measure (AddCircle L)))
    (F : C(Fin 2 → AddCircle L, ℂ)) (x : Fin 2 → AddCircle L) :
    ‖slice L k F x‖ ≤ (volume : Measure (AddCircle L)).real univ * k.bound * ‖F‖ := by
  calc
    _ ≤ ∫ _t : AddCircle L, k.bound * ‖F‖ := by
      apply norm_integral_le_of_norm_le (integrable_const _)
      filter_upwards with t
      rw [norm_mul]
      exact mul_le_mul (k.norm_le _) (F.norm_coe_le_norm _) (norm_nonneg _) k.bound_nonneg
    _ = _ := by rw [integral_const]; simp [smul_eq_mul, mul_assoc]

theorem memLp_slice (k : Kernel (volume : Measure (AddCircle L)))
    (F : C(Fin 2 → AddCircle L, ℂ)) : MemLp (slice L k F) 2 (torusPiMeasure L 2) := by
  apply MemLp.of_bound _ _ (Filter.Eventually.of_forall (norm_slice_le L k F))
  have hm : Measurable (fun p : (Fin 2 → AddCircle L) × AddCircle L =>
      k.fn (p.1 0,p.2) * F ![p.2,p.1 1]) := by
    apply Measurable.mul
    · exact k.measurable.comp (by fun_prop)
    · exact F.continuous.measurable.comp (by fun_prop)
  exact hm.aestronglyMeasurable.integral_prod_right'

/-- The actual integral slice as a bounded map from continuous functions to L². -/
def sliceMap (k : Kernel (volume : Measure (AddCircle L))) :
    C(Fin 2 → AddCircle L, ℂ) →L[ℂ] L2TN L 2 :=
  LinearMap.mkContinuous
    { toFun := fun F => (memLp_slice L k F).toLp _
      map_add' := by
        intro F G
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_slice L k (F+G)),
          Lp.coeFn_add ((memLp_slice L k F).toLp _) ((memLp_slice L k G).toLp _),
          MemLp.coeFn_toLp (memLp_slice L k F), MemLp.coeFn_toLp (memLp_slice L k G)]
          with x h hsum hf hg
        rw [h, hsum]
        simp only [Pi.add_apply, hf, hg, slice, ContinuousMap.add_apply, mul_add]
        exact integral_add (integrable_slice L k F x) (integrable_slice L k G x)
      map_smul' := by
        intro a F
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_slice L k (a • F)),
          Lp.coeFn_smul a ((memLp_slice L k F).toLp _),
          MemLp.coeFn_toLp (memLp_slice L k F)] with x h hs hf
        change _ = (a • (memLp_slice L k F).toLp _) x
        rw [h, hs]
        simp only [Pi.smul_apply, hf, slice, ContinuousMap.smul_apply, smul_eq_mul]
        simp_rw [mul_left_comm (k.fn _) a]
        exact integral_const_mul _ _ }
    ((measureUnivNNReal (torusPiMeasure L 2) : ℝ) ^ (2 : ℝ)⁻¹ *
      ((volume : Measure (AddCircle L)).real univ * k.bound))
    (by
      intro F
      calc
        _ ≤ (measureUnivNNReal (torusPiMeasure L 2) : ℝ) ^ (2 : ℝ)⁻¹ *
            ((volume : Measure (AddCircle L)).real univ * k.bound * ‖F‖) := by
          apply Lp.norm_le_of_ae_bound (mul_nonneg
            (mul_nonneg (measureReal_nonneg) k.bound_nonneg) (norm_nonneg F))
          filter_upwards [MemLp.coeFn_toLp (memLp_slice L k F)] with x hx
          change ‖((memLp_slice L k F).toLp (slice L k F)) x‖ ≤ _
          rw [hx]
          exact norm_slice_le L k F x
        _ = _ := by ring)

theorem coe_sliceMap (k : Kernel (volume : Measure (AddCircle L)))
    (F : C(Fin 2 → AddCircle L, ℂ)) :
    sliceMap L k F =ᵐ[torusPiMeasure L 2] slice L k F := (memLp_slice L k F).coeFn_toLp

/-- A singleton tensor is the given first-power vector. -/
theorem singleton_tensor (v : HilbertTensorPower ℂ (L2T L) 1) :
    ((ptprod (fun _ : Fin 1 => firstPowerIso v) : AlgTensorPower ℂ (L2T L) 1) :
      HilbertTensorPower ℂ (L2T L) 1) = v := by
  apply firstPowerIso.injective
  rw [firstPowerIso_ptprod]

/-- The first placement on a product tensor is the product of its acted-on
first factor and unchanged spectator. -/
theorem firstPlacement_product
    (A : SymSector ℂ (L2T L) 1 →L[ℂ] SymSector ℂ (L2T L) 1) (f g : L2T L) :
    firstPlacement (q := 1) A
      ((ptprod ![f,g] : AlgTensorPower ℂ (L2T L) 2) : HilbertTensorPower ℂ (L2T L) 2) =
      ((ptprod ![firstPowerIso (extendSymKernel A
          ((ptprod (fun _ : Fin 1 => f) : AlgTensorPower ℂ (L2T L) 1) :
            HilbertTensorPower ℂ (L2T L) 1)),g] : AlgTensorPower ℂ (L2T L) 2) :
          HilbertTensorPower ℂ (L2T L) 2) := by
  have happ (f g : L2T L) : (![f,g] : Fin 2 → L2T L) =
      Fin.append (fun _ : Fin 1 => f) (fun _ : Fin 1 => g) := by
    ext i; fin_cases i <;> rfl
  apply (splitIsometry 1 1).injective
  simp only [firstPlacement, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.apply_symm_apply]
  rw [happ, splitIsometry_ptprod_append, htmap_htmul, ContinuousLinearMap.id_apply,
    happ, splitIsometry_ptprod_append, singleton_tensor]

/-- Physical embedding of a one-factor completed tensor. -/
theorem physUnitary_one_ae (v : HilbertTensorPower ℂ (L2T L) 1) :
    physUnitary v =ᵐ[torusPiMeasure L 1] fun x => firstPowerIso v (x 0) := by
  conv_lhs => rw [← singleton_tensor L v, physUnitary_ptprod]
  filter_upwards [MemLp.coeFn_toLp (memLp_prodFun (fun _ : Fin 1 => firstPowerIso v))]
    with x hx
  simpa only [prodLp, prodFun, Fin.prod_univ_one] using hx

/-- The physical tensor placement, viewed as a map on continuous inputs. -/
def tensorMap
    (A : SymSector ℂ (L2T L) 1 →L[ℂ] SymSector ℂ (L2T L) 1) :
    C(Fin 2 → AddCircle L, ℂ) →L[ℂ] L2TN L 2 :=
  (physUnitary (L := L) (N := 2)).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    firstPlacement (q := 1) A ∘L
    (physUnitary (L := L) (N := 2)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    ContinuousMap.toLp 2 (torusPiMeasure L 2) ℂ

theorem toLp_prodCont (g : Fin 2 → C(AddCircle L, ℂ)) :
    ContinuousMap.toLp 2 (torusPiMeasure L 2) ℂ (prodCont g) =
      prodLp (fun i => ContinuousMap.toLp 2 volume ℂ (g i)) := by
  apply Lp.ext
  have h : ∀ᵐ x ∂torusPiMeasure L 2, ∀ i,
      (ContinuousMap.toLp 2 volume ℂ (g i) : L2T L) (x i) = g i (x i) := by
    rw [ae_all_iff]
    intro i
    exact (Measure.quasiMeasurePreserving_eval
      (fun _ : Fin 2 => (volume : Measure (AddCircle L))) i).ae
      (ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ) volume (g i))
  filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ)
      (torusPiMeasure L 2) (prodCont g),
    (memLp_prodFun (fun i => ContinuousMap.toLp 2 volume ℂ (g i))).coeFn_toLp, h]
    with x hx hy hh
  rw [hx]
  change prodLp (fun i => ContinuousMap.toLp 2 volume ℂ (g i)) x = _ at hy
  rw [hy, prodCont_apply, prodFun]
  exact Finset.prod_congr rfl (fun i _ => (hh i).symm)

theorem tensorMap_product
    (A : SymSector ℂ (L2T L) 1 →L[ℂ] SymSector ℂ (L2T L) 1)
    (k : Kernel (volume : Measure (AddCircle L)))
    (hk : ∀ v, firstPowerIso (extendSymKernel A v) = k.operator (firstPowerIso v))
    (g : Fin 2 → C(AddCircle L, ℂ)) :
    tensorMap L A (prodCont g) =
      prodLp ![k.operator (ContinuousMap.toLp 2 volume ℂ (g 0)),
        ContinuousMap.toLp 2 volume ℂ (g 1)] := by
  have hg : (fun i => ContinuousMap.toLp 2 volume ℂ (g i)) =
      (![ContinuousMap.toLp 2 volume ℂ (g 0), ContinuousMap.toLp 2 volume ℂ (g 1)] :
        Fin 2 → L2T L) := by ext i; fin_cases i <;> rfl
  change physUnitary (firstPlacement (q := 1) A
    ((physUnitary (L := L) (N := 2)).symm
      (ContinuousMap.toLp 2 (torusPiMeasure L 2) ℂ (prodCont g)))) = _
  rw [toLp_prodCont L g, hg, ← physUnitary_ptprod, LinearIsometryEquiv.symm_apply_apply,
    firstPlacement_product, hk, firstPowerIso_ptprod, physUnitary_ptprod]

theorem sliceMap_product (k : Kernel (volume : Measure (AddCircle L)))
    (g : Fin 2 → C(AddCircle L, ℂ)) :
    sliceMap L k (prodCont g) =
      prodLp ![k.operator (ContinuousMap.toLp 2 volume ℂ (g 0)),
        ContinuousMap.toLp 2 volume ℂ (g 1)] := by
  let f : L2T L := ContinuousMap.toLp 2 volume ℂ (g 0)
  let h : L2T L := ContinuousMap.toLp 2 volume ℂ (g 1)
  have hact := (Measure.quasiMeasurePreserving_eval
    (fun _ : Fin 2 => (volume : Measure (AddCircle L))) 0).ae (k.operator_apply_ae f)
  have hh := (Measure.quasiMeasurePreserving_eval
    (fun _ : Fin 2 => (volume : Measure (AddCircle L))) 1).ae
      (ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ) volume (g 1))
  apply Lp.ext
  filter_upwards [coe_sliceMap L k (prodCont g),
    (memLp_prodFun (![k.operator f,h] : Fin 2 → L2T L)).coeFn_toLp, hact, hh]
    with x hx hp ha hb
  rw [hx]
  change prodLp (![k.operator f,h] : Fin 2 → L2T L) x = _ at hp
  rw [hp]
  simp only [prodFun, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    ha, show h (x 1) = g 1 (x 1) from hb]
  have hi : (∫ t, k.fn (x 0,t) * f t) = ∫ t, k.fn (x 0,t) * g 0 t := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ)
      volume (g 0)] with t ht
    rw [show f t = g 0 t from ht]
  rw [hi, ← integral_mul_const]
  unfold slice
  apply integral_congr_ae
  filter_upwards with t
  simp only [prodCont_apply, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

/-- The completed tensor construction has the literal slice integral action.
The only compatibility input is the one-body kernel action; the tensor-to-slice
bridge is proved by density here. It is discharged for the physical kernel below. -/
theorem tensorMap_eq_sliceMap
    (A : SymSector ℂ (L2T L) 1 →L[ℂ] SymSector ℂ (L2T L) 1)
    (k : Kernel (volume : Measure (AddCircle L)))
    (hk : ∀ v, firstPowerIso (extendSymKernel A v) = k.operator (firstPowerIso v)) :
    tensorMap L A = sliceMap L k := by
  have hprod : ∀ F ∈ (prodAlgebra L 2 : Set C(Fin 2 → AddCircle L, ℂ)),
      tensorMap L A F = sliceMap L k F := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem F hF =>
      obtain ⟨g, rfl⟩ := hF
      rw [tensorMap_product L A k hk, sliceMap_product]
    | zero => rw [map_zero, map_zero]
    | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
    | smul c a _ ha => rw [map_smul, map_smul, ha]
  apply ContinuousLinearMap.ext
  intro F
  have hF : F ∈ closure (prodAlgebra L 2 : Set C(Fin 2 → AddCircle L, ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe, prodAlgebra_dense]; trivial
  exact closure_minimal hprod
    (isClosed_eq (tensorMap L A).continuous (sliceMap L k).continuous) hF

/-- Sum of literal bounded kernels, before taking its constructed operator. -/
def sumKernel {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (k j : Kernel μ) : Kernel μ where
  fn p := k.fn p + j.fn p
  measurable := k.measurable.add j.measurable
  bound := k.bound + j.bound
  bound_nonneg := add_nonneg k.bound_nonneg j.bound_nonneg
  norm_le p := (norm_add_le _ _).trans (add_le_add (k.norm_le p) (j.norm_le p))

theorem operator_sumKernel {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] (k j : Kernel μ) :
    (sumKernel k j).operator = k.operator + j.operator := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  rw [add_apply, inner_add_right, Kernel.inner_operator,
    Kernel.inner_operator, Kernel.inner_operator]
  simp only [Kernel.form]
  rw [← integral_add (k.integrable_integrand g f) (j.integrable_integrand g f)]
  apply integral_congr_ae
  filter_upwards with p
  simp only [Kernel.integrand, sumKernel]
  ring

/-- A one-coordinate kernel on the scalar torus, using its unique coordinate. -/
def scalarPull (k : Kernel (torusPiMeasure L 1)) :
    Kernel (volume : Measure (AddCircle L)) where
  fn p := k.fn ((fun _ : Fin 1 => p.1),(fun _ : Fin 1 => p.2))
  measurable := k.measurable.comp (by fun_prop)
  bound := k.bound
  bound_nonneg := k.bound_nonneg
  norm_le p := k.norm_le _

/-- Exact one-coordinate transport of every bounded kernel operator. -/
theorem scalarPull_action (k : Kernel (torusPiMeasure L 1))
    (v : HilbertTensorPower ℂ (L2T L) 1) :
    firstPowerIso ((physUnitary (L := L) (N := 1)).symm (k.operator (physUnitary v))) =
      (scalarPull L k).operator (firstPowerIso v) := by
  let w := (physUnitary (L := L) (N := 1)).symm (k.operator (physUnitary v))
  have hp := (measurePreserving_funUnique (volume : Measure (AddCircle L)) (Fin 1)).symm
  apply Lp.ext
  have hw := hp.quasiMeasurePreserving.ae_eq_comp (physUnitary_one_ae L w)
  have hk := hp.quasiMeasurePreserving.ae_eq_comp (k.operator_apply_ae (physUnitary v))
  filter_upwards [hw, hk, (scalarPull L k).operator_apply_ae (firstPowerIso v)]
    with x hx ha hb
  change firstPowerIso w x = _
  rw [hb]
  have hx' : firstPowerIso w x =
      k.operator (physUnitary v) (fun _ : Fin 1 => x) := by
    change physUnitary w (fun _ : Fin 1 => x) = firstPowerIso w x at hx
    rw [show physUnitary w = k.operator (physUnitary v) from
      LinearIsometryEquiv.apply_symm_apply _ _] at hx
    exact hx.symm
  rw [hx']
  change k.operator (physUnitary v) (fun _ : Fin 1 => x) = _ at ha
  rw [ha]
  calc
    _ = ∫ y : Fin 1 → AddCircle L, k.fn ((fun _ => x),y) * firstPowerIso v (y 0) := by
      apply integral_congr_ae
      filter_upwards [physUnitary_one_ae L v] with y hy
      rw [hy]
      rfl
    _ = ∫ y : Fin 1 → AddCircle L,
        (scalarPull L k).fn (x,y 0) * firstPowerIso v (y 0) := by
      apply integral_congr_ae
      filter_upwards with y
      have he : y = fun _ : Fin 1 => y 0 := by ext i; rw [Subsingleton.elim i 0]
      conv_lhs => rw [he]
      rfl
    _ = _ := by
      rw [volume_pi]
      convert (measurePreserving_funUnique (volume : Measure (AddCircle L)) (Fin 1)).integral_comp'
          (fun y => (scalarPull L k).fn (x,y) * firstPowerIso v y) using 1
      simp only [MeasurableEquiv.funUnique_apply, Fin.default_eq_zero]
      rfl

theorem symProj_one {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : HilbertTensorPower ℂ H 1) : symProj ℂ H 1 v = v := by
  rw [symProj_eq_factorial_average]
  simp

open BethePhysicalTransfer BetheTransferOperators

/-- P₁ is the identity; compression adds no one-body normalization. -/
theorem extend_physicalKernel_one (z : ℂ) (v : HilbertTensorPower ℂ (L2T L) 1) :
    extendSymKernel (physicalKernel L 1 z) v =
      (physUnitary (L := L) (N := 1)).symm (rawOperator L 1 z (physUnitary v)) := by
  have hU := (physUnitary (L := L) (N := 1)).adjoint_eq_symm
  simp only [extendSymKernel, physicalKernel, positionInclusion,
    ContinuousLinearMap.adjoint_comp, hU, ContinuousLinearMap.comp_apply]
  rw [Submodule.adjoint_subtypeL]
  simp only [Submodule.subtypeL_apply]
  rw [Submodule.coe_orthogonalProjectionOnto_apply, ← symProj_eq_starProjection]
  change symProj ℂ (L2T L) 1
    ((physUnitary (L := L) (N := 1)).symm
      (rawOperator L 1 z (physUnitary (symProj ℂ (L2T L) 1 v)))) = _
  rw [symProj_one, symProj_one]

/-- The literal one-body upper plus lower kernel, on ordinary torus volume. -/
def physicalScalarKernel (z : ℂ) : Kernel (volume : Measure (AddCircle L)) :=
  scalarPull L (sumKernel (plusKernel L 1 z) (minusKernel L 1 z))

theorem physicalScalarKernel_action (z : ℂ)
    (v : HilbertTensorPower ℂ (L2T L) 1) :
    firstPowerIso (extendSymKernel (physicalKernel L 1 z) v) =
      (physicalScalarKernel L z).operator (firstPowerIso v) := by
  rw [extend_physicalKernel_one]
  rw [show rawOperator L 1 z =
    (sumKernel (plusKernel L 1 z) (minusKernel L 1 z)).operator from
      (operator_sumKernel _ _).symm]
  exact scalarPull_action L _ v

/-- The actual physical first placement is the proved literal slice map.
No tensor-to-coordinate bridge or target eigenrelation is an input. -/
theorem physical_tensorMap_eq_sliceMap (z : ℂ) :
    tensorMap L (physicalKernel L 1 z) = sliceMap L (physicalScalarKernel L z) :=
  tensorMap_eq_sliceMap L _ _ (physicalScalarKernel_action L z)

end QuantumNLS.BetheTensorSlice

#print axioms QuantumNLS.BetheTensorSlice.slice
#print axioms QuantumNLS.BetheTensorSlice.integrable_slice
#print axioms QuantumNLS.BetheTensorSlice.norm_slice_le
#print axioms QuantumNLS.BetheTensorSlice.memLp_slice
#print axioms QuantumNLS.BetheTensorSlice.sliceMap
#print axioms QuantumNLS.BetheTensorSlice.coe_sliceMap
#print axioms QuantumNLS.BetheTensorSlice.singleton_tensor
#print axioms QuantumNLS.BetheTensorSlice.firstPlacement_product
#print axioms QuantumNLS.BetheTensorSlice.physUnitary_one_ae
#print axioms QuantumNLS.BetheTensorSlice.tensorMap
#print axioms QuantumNLS.BetheTensorSlice.toLp_prodCont
#print axioms QuantumNLS.BetheTensorSlice.tensorMap_product
#print axioms QuantumNLS.BetheTensorSlice.sliceMap_product
#print axioms QuantumNLS.BetheTensorSlice.tensorMap_eq_sliceMap
#print axioms QuantumNLS.BetheTensorSlice.sumKernel
#print axioms QuantumNLS.BetheTensorSlice.operator_sumKernel
#print axioms QuantumNLS.BetheTensorSlice.scalarPull
#print axioms QuantumNLS.BetheTensorSlice.scalarPull_action
#print axioms QuantumNLS.BetheTensorSlice.symProj_one
#print axioms QuantumNLS.BetheTensorSlice.extend_physicalKernel_one
#print axioms QuantumNLS.BetheTensorSlice.physicalScalarKernel
#print axioms QuantumNLS.BetheTensorSlice.physicalScalarKernel_action
#print axioms QuantumNLS.BetheTensorSlice.physical_tensorMap_eq_sliceMap
