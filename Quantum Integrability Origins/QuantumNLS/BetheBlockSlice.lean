import QuantumNLS.BetheBlockTensor

/-! Arbitrary-degree integral slices on the actual m+q completed physical tensor.
No tensor-to-slice identity is postulated. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace ComplexConjugate
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
namespace QuantumNLS.BetheBlockSlice
open TensorCarrier TensorPlacements PhysicalTensor TensorFourier BetheIntegralOperator BetheBlockTensor
variable (L : ℝ) [Fact (0 < L)] (m q : ℕ)

/-- Integrate the first block and leave the spectator block fixed. -/
def slice (k : Kernel (torusPiMeasure L m))
    (F : C(Fin (m+q) → AddCircle L, ℂ)) (x : Fin (m+q) → AddCircle L) : ℂ :=
  ∫ t, k.fn ((fun i => x (Fin.castAdd q i)),t) * F (Fin.append t (fun i : Fin q => x (Fin.natAdd m i)))

theorem integrable_slice (k : Kernel (torusPiMeasure L m))
    (F : C(Fin (m+q) → AddCircle L, ℂ)) (x : Fin (m+q) → AddCircle L) :
    Integrable (fun t => k.fn ((fun i => x (Fin.castAdd q i)),t) * F (Fin.append t (fun i : Fin q => x (Fin.natAdd m i)))) := by
  apply Integrable.of_bound
    ((k.measurable.comp (measurable_const.prodMk measurable_id)).mul
      (F.continuous.measurable.comp (by fun_prop))).aestronglyMeasurable (k.bound * ‖F‖)
  filter_upwards with t
  change ‖k.fn ((fun i => x (Fin.castAdd q i)),t) * F (Fin.append t (fun i : Fin q => x (Fin.natAdd m i)))‖ ≤ k.bound * ‖F‖
  rw [norm_mul]
  exact mul_le_mul (k.norm_le _) (F.norm_coe_le_norm _) (norm_nonneg _) k.bound_nonneg

theorem norm_slice_le (k : Kernel (torusPiMeasure L m))
    (F : C(Fin (m+q) → AddCircle L, ℂ)) (x : Fin (m+q) → AddCircle L) :
    ‖slice L m q k F x‖ ≤ (torusPiMeasure L m).real univ * k.bound * ‖F‖ := by
  calc
    _ ≤ ∫ _t : Fin m → AddCircle L, k.bound * ‖F‖ ∂torusPiMeasure L m := by
      apply norm_integral_le_of_norm_le (integrable_const _)
      filter_upwards with t
      rw [norm_mul]
      exact mul_le_mul (k.norm_le _) (F.norm_coe_le_norm _) (norm_nonneg _) k.bound_nonneg
    _ = _ := by rw [integral_const]; simp [smul_eq_mul, mul_assoc]

theorem memLp_slice (k : Kernel (torusPiMeasure L m))
    (F : C(Fin (m+q) → AddCircle L, ℂ)) : MemLp (slice L m q k F) 2 (torusPiMeasure L (m+q)) := by
  apply MemLp.of_bound _ _ (Filter.Eventually.of_forall (norm_slice_le L m q k F))
  have hm : Measurable (fun p : (Fin (m+q) → AddCircle L) × (Fin m → AddCircle L) =>
      k.fn ((fun i => p.1 (Fin.castAdd q i)),p.2) * F (Fin.append p.2 (fun i : Fin q => p.1 (Fin.natAdd m i)))) := by
    apply Measurable.mul
    · exact k.measurable.comp (by fun_prop)
    · exact F.continuous.measurable.comp (by fun_prop)
  exact hm.aestronglyMeasurable.integral_prod_right'

/-- The actual integral slice as a bounded map from continuous functions to L². -/
def sliceMap (k : Kernel (torusPiMeasure L m)) :
    C(Fin (m+q) → AddCircle L, ℂ) →L[ℂ] L2TN L (m+q) :=
  LinearMap.mkContinuous
    { toFun := fun F => (memLp_slice L m q k F).toLp _
      map_add' := by
        intro F G
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_slice L m q k (F+G)),
          Lp.coeFn_add ((memLp_slice L m q k F).toLp _) ((memLp_slice L m q k G).toLp _),
          MemLp.coeFn_toLp (memLp_slice L m q k F), MemLp.coeFn_toLp (memLp_slice L m q k G)]
          with x h hsum hf hg
        rw [h, hsum]
        simp only [Pi.add_apply, hf, hg, slice, ContinuousMap.add_apply, mul_add]
        exact integral_add (integrable_slice L m q k F x) (integrable_slice L m q k G x)
      map_smul' := by
        intro a F
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_slice L m q k (a • F)),
          Lp.coeFn_smul a ((memLp_slice L m q k F).toLp _),
          MemLp.coeFn_toLp (memLp_slice L m q k F)] with x h hs hf
        change _ = (a • (memLp_slice L m q k F).toLp _) x
        rw [h, hs]
        simp only [Pi.smul_apply, hf, slice, ContinuousMap.smul_apply, smul_eq_mul]
        simp_rw [mul_left_comm (k.fn _) a]
        exact integral_const_mul _ _ }
    ((measureUnivNNReal (torusPiMeasure L (m+q)) : ℝ) ^ (2 : ℝ)⁻¹ *
      ((torusPiMeasure L m).real univ * k.bound))
    (by
      intro F
      calc
        _ ≤ (measureUnivNNReal (torusPiMeasure L (m+q)) : ℝ) ^ (2 : ℝ)⁻¹ *
            ((torusPiMeasure L m).real univ * k.bound * ‖F‖) := by
          apply Lp.norm_le_of_ae_bound (mul_nonneg
            (mul_nonneg (measureReal_nonneg) k.bound_nonneg) (norm_nonneg F))
          filter_upwards [MemLp.coeFn_toLp (memLp_slice L m q k F)] with x hx
          change ‖((memLp_slice L m q k F).toLp (slice L m q k F)) x‖ ≤ _
          rw [hx]
          exact norm_slice_le L m q k F x
        _ = _ := by ring)

theorem coe_sliceMap (k : Kernel (torusPiMeasure L m))
    (F : C(Fin (m+q) → AddCircle L, ℂ)) :
    sliceMap L m q k F =ᵐ[torusPiMeasure L (m+q)] slice L m q k F := (memLp_slice L m q k F).coeFn_toLp

def tensorMap
    (A : SymSector ℂ (L2T L) m →L[ℂ] SymSector ℂ (L2T L) m) :
    C(Fin (m+q) → AddCircle L, ℂ) →L[ℂ] L2TN L (m+q) :=
  (physUnitary (L := L) (N := m+q)).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    firstPlacement (q := q) A ∘L
    (physUnitary (L := L) (N := m+q)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    ContinuousMap.toLp 2 (torusPiMeasure L (m+q)) ℂ

theorem toLp_prodCont (r : ℕ) (g : Fin r → C(AddCircle L, ℂ)) :
    ContinuousMap.toLp 2 (torusPiMeasure L r) ℂ (prodCont g) =
      prodLp (fun i => ContinuousMap.toLp 2 volume ℂ (g i)) := by
  apply Lp.ext
  have h : ∀ᵐ x ∂torusPiMeasure L r, ∀ i,
      (ContinuousMap.toLp 2 volume ℂ (g i) : L2T L) (x i) = g i (x i) := by
    rw [ae_all_iff]
    intro i
    exact (Measure.quasiMeasurePreserving_eval
      (fun _ : Fin r => (volume : Measure (AddCircle L))) i).ae
      (ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ) volume (g i))
  filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ)
      (torusPiMeasure L r) (prodCont g),
    (memLp_prodFun (fun i => ContinuousMap.toLp 2 volume ℂ (g i))).coeFn_toLp,h]
    with x hx hy hh
  change prodLp (fun i => ContinuousMap.toLp 2 volume ℂ (g i)) x = _ at hy
  rw [hx,hy,prodCont_apply,prodFun]
  exact Finset.prod_congr rfl (fun i _ => (hh i).symm)

theorem append_split {α : Type*} (g : Fin (m+q) → α) :
    g = Fin.append (fun i => g (Fin.castAdd q i)) (fun i => g (Fin.natAdd m i)) := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
  · rw [Fin.append_right]

theorem tensorMap_product
    (A : SymSector ℂ (L2T L) m →L[ℂ] SymSector ℂ (L2T L) m)
    (k : Kernel (torusPiMeasure L m))
    (hk : ∀ v, physUnitary (extendSymKernel A v) = k.operator (physUnitary v))
    (g : Fin (m+q) → C(AddCircle L, ℂ)) :
    tensorMap L m q A (prodCont g) =
      blockProduct L m q
        (k.operator (prodLp (fun i => ContinuousMap.toLp 2 volume ℂ (g (Fin.castAdd q i)))))
        (prodLp (fun i => ContinuousMap.toLp 2 volume ℂ (g (Fin.natAdd m i)))) := by
  change physUnitary (firstPlacement (q := q) A
    ((physUnitary (L := L) (N := m+q)).symm
      (ContinuousMap.toLp 2 (torusPiMeasure L (m+q)) ℂ (prodCont g)))) = _
  rw [toLp_prodCont L, ← physUnitary_ptprod, LinearIsometryEquiv.symm_apply_apply,
    append_split m q (fun i => ContinuousMap.toLp 2 volume ℂ (g i))]
  simp only [firstPlacement,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,LinearIsometryEquiv.coe_toLinearIsometry]
  rw [splitIsometry_ptprod_append,htmap_htmul,ContinuousLinearMap.id_apply,
    physUnitary_join,hk,physUnitary_ptprod]

theorem sliceMap_product (k : Kernel (torusPiMeasure L m))
    (g : Fin (m+q) → C(AddCircle L, ℂ)) :
    sliceMap L m q k (prodCont g) =
      blockProduct L m q
        (k.operator (prodLp (fun i => ContinuousMap.toLp 2 volume ℂ (g (Fin.castAdd q i)))))
        (prodLp (fun i => ContinuousMap.toLp 2 volume ℂ (g (Fin.natAdd m i)))) := by
  let f : L2TN L m := prodLp (fun i => ContinuousMap.toLp 2 volume ℂ (g (Fin.castAdd q i)))
  let w : L2TN L q := prodLp (fun i => ContinuousMap.toLp 2 volume ℂ (g (Fin.natAdd m i)))
  have hf : f =ᵐ[torusPiMeasure L m] prodCont (fun i => g (Fin.castAdd q i)) := by
    rw [show f = ContinuousMap.toLp 2 (torusPiMeasure L m) ℂ (prodCont (fun i => g (Fin.castAdd q i))) from
      (toLp_prodCont L m _).symm]
    exact ContinuousMap.coeFn_toLp _ _
  have hw : w =ᵐ[torusPiMeasure L q] prodCont (fun i => g (Fin.natAdd m i)) := by
    rw [show w = ContinuousMap.toLp 2 (torusPiMeasure L q) ℂ (prodCont (fun i => g (Fin.natAdd m i))) from
      (toLp_prodCont L q _).symm]
    exact ContinuousMap.coeFn_toLp _ _
  apply Lp.ext
  filter_upwards [coe_sliceMap L m q k (prodCont g),
    coe_blockProduct L m q (k.operator f) w,head_ae L m q (k.operator_apply_ae f),
    tail_ae L m q hw] with x hx hp ha hb
  change blockProduct L m q (k.operator f) w x = _ at hp
  rw [hx,hp]
  simp only [blockProductFun,ha,hb]
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [hf] with t ht
  simp only [ht,prodCont_apply,Fin.prod_univ_add,Fin.append_left,Fin.append_right]
  ring

/-- The only compatibility hypothesis is the block kernel action; the entire
spectator/tensor bridge is proved here by product algebra density. The physical
compressed block compatibility is discharged in BetheHigherPlacement. -/
theorem tensorMap_eq_sliceMap
    (A : SymSector ℂ (L2T L) m →L[ℂ] SymSector ℂ (L2T L) m)
    (k : Kernel (torusPiMeasure L m))
    (hk : ∀ v, physUnitary (extendSymKernel A v) = k.operator (physUnitary v)) :
    tensorMap L m q A = sliceMap L m q k := by
  have hprod : ∀ F ∈ (prodAlgebra L (m+q) : Set C(Fin (m+q) → AddCircle L, ℂ)),
      tensorMap L m q A F = sliceMap L m q k F := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem F hF =>
      obtain ⟨g,rfl⟩ := hF
      rw [tensorMap_product L m q A k hk,sliceMap_product]
    | zero => rw [map_zero,map_zero]
    | add a b _ _ ha hb => rw [map_add,map_add,ha,hb]
    | smul c a _ ha => rw [map_smul,map_smul,ha]
  apply ContinuousLinearMap.ext
  intro F
  have hF : F ∈ closure (prodAlgebra L (m+q) : Set C(Fin (m+q) → AddCircle L, ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe,prodAlgebra_dense]; trivial
  exact closure_minimal hprod
    (isClosed_eq (tensorMap L m q A).continuous (sliceMap L m q k).continuous) hF

end QuantumNLS.BetheBlockSlice



#print axioms QuantumNLS.BetheBlockSlice.slice
#print axioms QuantumNLS.BetheBlockSlice.integrable_slice
#print axioms QuantumNLS.BetheBlockSlice.norm_slice_le
#print axioms QuantumNLS.BetheBlockSlice.memLp_slice
#print axioms QuantumNLS.BetheBlockSlice.sliceMap
#print axioms QuantumNLS.BetheBlockSlice.coe_sliceMap
#print axioms QuantumNLS.BetheBlockSlice.tensorMap
#print axioms QuantumNLS.BetheBlockSlice.toLp_prodCont
#print axioms QuantumNLS.BetheBlockSlice.append_split
#print axioms QuantumNLS.BetheBlockSlice.tensorMap_product
#print axioms QuantumNLS.BetheBlockSlice.sliceMap_product
#print axioms QuantumNLS.BetheBlockSlice.tensorMap_eq_sliceMap
