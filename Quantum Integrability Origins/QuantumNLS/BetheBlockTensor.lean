import QuantumNLS.BetheGeneralSliceEndpoints

/-! Arbitrary finite block/spectator splitting on the actual completed physical
tensor. The product measure has its original mass L^(m+q). -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace ComplexConjugate
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
namespace QuantumNLS.BetheBlockTensor
open TensorCarrier TensorPlacements PhysicalTensor TensorFourier BetheIntegralOperator
variable (L : ℝ) [Fact (0 < L)] (m q : ℕ)

def splitCoordinates : (Fin (m+q) → AddCircle L) ≃ᵐ
    (Fin m → AddCircle L) × (Fin q → AddCircle L) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (m+q) => AddCircle L) finSumFinEquiv).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin q => AddCircle L))

omit [Fact (0 < L)] in
theorem splitCoordinates_apply (x : Fin (m+q) → AddCircle L) :
    splitCoordinates L m q x =
      (fun i => x (Fin.castAdd q i), fun i => x (Fin.natAdd m i)) := rfl

theorem measurePreserving_splitCoordinates :
    MeasurePreserving (splitCoordinates L m q) (torusPiMeasure L (m+q))
      ((torusPiMeasure L m).prod (torusPiMeasure L q)) :=
  (measurePreserving_sumPiEquivProdPi (fun _ : Fin m ⊕ Fin q =>
    (volume : Measure (AddCircle L)))).comp
      (measurePreserving_piCongrLeft (fun _ : Fin (m+q) =>
        (volume : Measure (AddCircle L))) finSumFinEquiv).symm

theorem head_ae {P : (Fin m → AddCircle L) → Prop}
    (h : ∀ᵐ x ∂torusPiMeasure L m, P x) :
    ∀ᵐ x ∂torusPiMeasure L (m+q), P (fun i => x (Fin.castAdd q i)) :=
  (measurePreserving_splitCoordinates L m q).quasiMeasurePreserving.ae
    (Measure.quasiMeasurePreserving_fst.ae h)

theorem tail_ae {P : (Fin q → AddCircle L) → Prop}
    (h : ∀ᵐ x ∂torusPiMeasure L q, P x) :
    ∀ᵐ x ∂torusPiMeasure L (m+q), P (fun i => x (Fin.natAdd m i)) :=
  (measurePreserving_splitCoordinates L m q).quasiMeasurePreserving.ae
    (Measure.quasiMeasurePreserving_snd.ae h)

def blockProductFun (v : L2TN L m) (w : L2TN L q)
    (x : Fin (m+q) → AddCircle L) : ℂ :=
  v (fun i => x (Fin.castAdd q i)) * w (fun i => x (Fin.natAdd m i))

theorem memLp_blockProduct (v : L2TN L m) (w : L2TN L q) :
    MemLp (blockProductFun L m q v w) 2 (torusPiMeasure L (m+q)) := by
  have ha : AEStronglyMeasurable (fun p : (Fin m → AddCircle L) × (Fin q → AddCircle L) =>
      v p.1 * w p.2) ((torusPiMeasure L m).prod (torusPiMeasure L q)) :=
    (Lp.aestronglyMeasurable v).comp_fst.mul (Lp.aestronglyMeasurable w).comp_snd
  have hi := ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp
    (Lp.memLp v)).mul_prod
      ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable w)).mp (Lp.memLp w))
  have hp : MemLp (fun p : (Fin m → AddCircle L) × (Fin q → AddCircle L) =>
      v p.1 * w p.2) 2 ((torusPiMeasure L m).prod (torusPiMeasure L q)) := by
    apply (memLp_two_iff_integrable_sq_norm ha).mpr
    simpa only [norm_mul, mul_pow] using hi
  exact hp.comp_measurePreserving (measurePreserving_splitCoordinates L m q)

def blockProduct (v : L2TN L m) (w : L2TN L q) : L2TN L (m+q) :=
  (memLp_blockProduct L m q v w).toLp _

theorem coe_blockProduct (v : L2TN L m) (w : L2TN L q) :
    blockProduct L m q v w =ᵐ[torusPiMeasure L (m+q)] blockProductFun L m q v w :=
  (memLp_blockProduct L m q v w).coeFn_toLp

theorem inner_blockProduct (v v' : L2TN L m) (w w' : L2TN L q) :
    ⟪blockProduct L m q v w, blockProduct L m q v' w'⟫_ℂ =
      ⟪v,v'⟫_ℂ * ⟪w,w'⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x, (conj (v (fun i => x (Fin.castAdd q i))) * v' (fun i => x (Fin.castAdd q i))) *
        (conj (w (fun i => x (Fin.natAdd m i))) * w' (fun i => x (Fin.natAdd m i)))
          ∂torusPiMeasure L (m+q) := by
      apply integral_congr_ae
      filter_upwards [coe_blockProduct L m q v w, coe_blockProduct L m q v' w'] with x hx hy
      rw [hx,hy]
      simp only [blockProductFun, RCLike.inner_apply', map_mul]
      ring
    _ = ∫ p : (Fin m → AddCircle L) × (Fin q → AddCircle L),
        (conj (v p.1) * v' p.1) * (conj (w p.2) * w' p.2)
          ∂(torusPiMeasure L m).prod (torusPiMeasure L q) :=
      (measurePreserving_splitCoordinates L m q).integral_comp'
        (fun p => (conj (v p.1) * v' p.1) * (conj (w p.2) * w' p.2))
    _ = _ := by
      simp only [RCLike.inner_apply']
      exact integral_prod_mul (fun x => conj (v x) * v' x) (fun y => conj (w y) * w' y)

theorem norm_blockProduct (v : L2TN L m) (w : L2TN L q) :
    ‖blockProduct L m q v w‖ = ‖v‖ * ‖w‖ := by
  have h := congrArg norm (inner_blockProduct L m q v v w w)
  rw [norm_mul,inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K] at h
  simp only [norm_pow,RCLike.norm_ofReal,abs_norm] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg v) (norm_nonneg w))).mp
    (by nlinarith only [h])

def blockProductMap (w : L2TN L q) : L2TN L m →L[ℂ] L2TN L (m+q) :=
  LinearMap.mkContinuous
    { toFun := fun v => blockProduct L m q v w
      map_add' := by
        intro v v'
        apply Lp.ext
        filter_upwards [coe_blockProduct L m q (v+v') w,
          coe_blockProduct L m q v w, coe_blockProduct L m q v' w,
          head_ae L m q (Lp.coeFn_add v v'),
          Lp.coeFn_add (blockProduct L m q v w) (blockProduct L m q v' w)] with x h h1 h2 hv hs
        simp only [Pi.add_apply] at hv hs
        rw [h,hs,h1,h2]
        simp only [blockProductFun,hv,add_mul]
      map_smul' := by
        intro a v
        apply Lp.ext
        filter_upwards [coe_blockProduct L m q (a • v) w,
          coe_blockProduct L m q v w, head_ae L m q (Lp.coeFn_smul a v),
          Lp.coeFn_smul a (blockProduct L m q v w)] with x h h1 hv hs
        simp only [Pi.smul_apply,smul_eq_mul] at hv hs
        change blockProduct L m q (a • v) w x = (a • blockProduct L m q v w) x
        rw [h,hs,h1]
        simp only [blockProductFun,hv,mul_assoc] }
    ‖w‖ (fun v => by change ‖blockProduct L m q v w‖ ≤ _; rw [norm_blockProduct, mul_comm])

theorem blockProduct_prodLp (f : Fin m → L2T L) (g : Fin q → L2T L) :
    blockProduct L m q (prodLp f) (prodLp g) = prodLp (Fin.append f g) := by
  apply Lp.ext
  filter_upwards [coe_blockProduct L m q (prodLp f) (prodLp g),
    head_ae L m q (memLp_prodFun f).coeFn_toLp,
    tail_ae L m q (memLp_prodFun g).coeFn_toLp,
    (memLp_prodFun (Fin.append f g)).coeFn_toLp] with x hx hf hg hh
  change prodLp (Fin.append f g) x = _ at hh
  change prodLp f (fun i => x (Fin.castAdd q i)) = _ at hf
  change prodLp g (fun i => x (Fin.natAdd m i)) = _ at hg
  rw [hx,hh]
  simp only [blockProductFun, hf, hg, prodFun, Fin.prod_univ_add,
    Fin.append_left,Fin.append_right]

def tensorJoinMap (w : HilbertTensorPower ℂ (L2T L) q) :
    HilbertTensorPower ℂ (L2T L) m →L[ℂ]
      HilbertTensor ℂ (HilbertTensorPower ℂ (L2T L) m) (HilbertTensorPower ℂ (L2T L) q) :=
  LinearMap.mkContinuous
    { toFun := fun v => htmul v w
      map_add' := fun v v' => htmul_add_left v v' w
      map_smul' := fun a v => htmul_smul_left a v w }
    ‖w‖ (fun v => by change ‖htmul v w‖ ≤ _; rw [norm_htmul,mul_comm])

/-- The split completed tensor has the literal position product for an arbitrary
first-block vector and every spectator product, proved by tensor density. -/
theorem physUnitary_join (v : HilbertTensorPower ℂ (L2T L) m)
    (g : Fin q → L2T L) :
    physUnitary ((splitIsometry m q).symm (htmul v
      ((ptprod g : AlgTensorPower ℂ (L2T L) q) : HilbertTensorPower ℂ (L2T L) q))) =
      blockProduct L m q (physUnitary v) (prodLp g) := by
  have hc : Continuous (fun v : HilbertTensorPower ℂ (L2T L) m =>
      physUnitary ((splitIsometry m q).symm (htmul v
        ((ptprod g : AlgTensorPower ℂ (L2T L) q) : HilbertTensorPower ℂ (L2T L) q)))) := by
    apply physUnitary.continuous.comp
    apply (splitIsometry m q).symm.continuous.comp
    exact (tensorJoinMap L m q _).continuous
  induction v using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq hc ((blockProductMap L m q (prodLp g)).continuous.comp physUnitary.continuous)
  | ih a =>
    induction a using AlgTensorPower.induction_on with
    | smul_ptprod c f =>
      simp only [UniformSpace.Completion.coe_smul, htmul_smul_left, map_smul]
      change c • physUnitary ((splitIsometry m q).symm (htmul
        ((ptprod f : AlgTensorPower ℂ (L2T L) m) : HilbertTensorPower ℂ (L2T L) m)
        ((ptprod g : AlgTensorPower ℂ (L2T L) q) : HilbertTensorPower ℂ (L2T L) q))) =
          blockProductMap L m q (prodLp g) (c • physUnitary _)
      rw [map_smul, ← splitIsometry_ptprod_append, LinearIsometryEquiv.symm_apply_apply,
        physUnitary_ptprod,physUnitary_ptprod]
      exact congrArg (c • ·) (blockProduct_prodLp L m q f g).symm
    | add a b ha hb =>
      simp only [UniformSpace.Completion.coe_add,htmul_add_left,map_add]
      change _ = blockProductMap L m q (prodLp g) (physUnitary ↑a + physUnitary ↑b)
      rw [map_add,ha,hb]
      rfl

end QuantumNLS.BetheBlockTensor

#print axioms QuantumNLS.BetheBlockTensor.splitCoordinates
#print axioms QuantumNLS.BetheBlockTensor.splitCoordinates_apply
#print axioms QuantumNLS.BetheBlockTensor.measurePreserving_splitCoordinates
#print axioms QuantumNLS.BetheBlockTensor.head_ae
#print axioms QuantumNLS.BetheBlockTensor.tail_ae
#print axioms QuantumNLS.BetheBlockTensor.blockProductFun
#print axioms QuantumNLS.BetheBlockTensor.memLp_blockProduct
#print axioms QuantumNLS.BetheBlockTensor.blockProduct
#print axioms QuantumNLS.BetheBlockTensor.coe_blockProduct
#print axioms QuantumNLS.BetheBlockTensor.inner_blockProduct
#print axioms QuantumNLS.BetheBlockTensor.norm_blockProduct
#print axioms QuantumNLS.BetheBlockTensor.blockProductMap
#print axioms QuantumNLS.BetheBlockTensor.blockProduct_prodLp
#print axioms QuantumNLS.BetheBlockTensor.tensorJoinMap
#print axioms QuantumNLS.BetheBlockTensor.physUnitary_join
