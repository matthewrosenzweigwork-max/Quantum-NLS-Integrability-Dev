import QuantumNLS.BetheGeneralSliceEndpoints

/-! Literal P_m(K⁺+K⁻)P_m as an explicitly averaged bounded scalar kernel,
at every degree. Both m! averages and the e^(izL) branch remain visible. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace ComplexConjugate
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
namespace QuantumNLS.BetheCompressedKernel
open TensorCarrier TensorPlacements PhysicalTensor BetheIntegralOperator
open BethePhysicalTransfer BetheTransferOperators BetheTransferKernelAdjoint
variable (L : ℝ) [Fact (0 < L)] (m : ℕ)

def weightedKernel {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] [Fintype ι] (a : ι → ℂ) (k : ι → Kernel μ) : Kernel μ where
  fn p := ∑ i, a i * (k i).fn p
  measurable := Finset.measurable_sum _ (fun i _ => measurable_const.mul (k i).measurable)
  bound := ∑ i, ‖a i‖ * (k i).bound
  bound_nonneg := Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (k i).bound_nonneg)
  norm_le p := (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left ((k i).norm_le p) (norm_nonneg _)))

theorem weightedKernel_operator {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] [Fintype ι] (a : ι → ℂ) (k : ι → Kernel μ) :
    (weightedKernel a k).operator = ∑ i, a i • (k i).operator := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  simp only [sum_apply,smul_apply,inner_sum,inner_smul_right,Kernel.inner_operator,
    Kernel.form,Kernel.integrand,weightedKernel]
  calc
    _ = ∫ p, ∑ i, a i * (k i).integrand g f p ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards with p
      simp only [Finset.mul_sum,Finset.sum_mul,Kernel.integrand]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i, ∫ p, a i * (k i).integrand g f p ∂μ.prod μ :=
      integral_finsetSum _ (fun i _ => ((k i).integrable_integrand g f).const_mul (a i))
    _ = _ := by simp only [integral_const_mul,Kernel.integrand]

def permutedKernel (k : Kernel (torusPiMeasure L m))
    (σ τ : Equiv.Perm (Fin m)) : Kernel (torusPiMeasure L m) where
  fn p := k.fn (coordPerm σ p.1,coordPerm τ p.2)
  measurable := k.measurable.comp
    (((coordPerm σ).measurable.comp measurable_fst).prodMk
      ((coordPerm τ).measurable.comp measurable_snd))
  bound := k.bound
  bound_nonneg := k.bound_nonneg
  norm_le _p := k.norm_le _

theorem permutedKernel_operator (k : Kernel (torusPiMeasure L m))
    (σ τ : Equiv.Perm (Fin m)) (f : L2TN L m) :
    (permutedKernel L m k σ τ).operator f =
      physPerm σ (k.operator (physPerm τ.symm f)) := by
  apply Lp.ext
  filter_upwards [(permutedKernel L m k σ τ).operator_apply_ae f,
    coeFn_physPerm σ (k.operator (physPerm τ.symm f)),
    (measurePreserving_coordPerm (L := L) σ).quasiMeasurePreserving.ae
      (k.operator_apply_ae (physPerm τ.symm f))] with x hx hp hk
  rw [hx,hp,hk]
  change (∫ y, k.fn (coordPerm σ x,coordPerm τ y) * f y ∂torusPiMeasure L m) = _
  calc
    _ = ∫ y, k.fn (coordPerm σ x,y) * f (coordPerm τ.symm y) ∂torusPiMeasure L m := by
      have h := (measurePreserving_coordPerm (L := L) τ).integral_comp'
        (fun y => k.fn (coordPerm σ x,y) * f (coordPerm τ.symm y))
      have he (y : Fin m → AddCircle L) : coordPerm τ.symm (coordPerm τ y) = y := by
        ext i
        simp only [coordPerm_apply,Equiv.apply_symm_apply]
      simpa only [he] using h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [coeFn_physPerm τ.symm f] with y hy
      rw [hy]

def outputAverage (k : Kernel (torusPiMeasure L m)) : Kernel (torusPiMeasure L m) :=
  weightedKernel (fun _ : Equiv.Perm (Fin m) => (m.factorial : ℂ)⁻¹)
    (fun σ => permutedKernel L m k σ 1)

def inputAverage (k : Kernel (torusPiMeasure L m)) : Kernel (torusPiMeasure L m) :=
  weightedKernel (fun _ : Equiv.Perm (Fin m) => (m.factorial : ℂ)⁻¹)
    (fun τ => permutedKernel L m k 1 τ.symm)

def positionAverage : L2TN L m →L[ℂ] L2TN L m :=
  (m.factorial : ℂ)⁻¹ • ∑ σ : Equiv.Perm (Fin m), (physPerm σ).toContinuousLinearMap

theorem outputAverage_operator (k : Kernel (torusPiMeasure L m)) (f : L2TN L m) :
    (outputAverage L m k).operator f = positionAverage L m (k.operator f) := by
  rw [outputAverage,weightedKernel_operator]
  simp only [sum_apply,smul_apply,permutedKernel_operator,positionAverage,Finset.smul_sum]
  have h : physPerm (1 : Equiv.Perm (Fin m)) f = f := by
    apply Lp.ext
    filter_upwards [coeFn_physPerm (1 : Equiv.Perm (Fin m)) f] with x hx
    exact hx
  change (∑ σ : Equiv.Perm (Fin m), (m.factorial : ℂ)⁻¹ • physPerm σ (k.operator (physPerm 1 f))) = _
  rw [h]
  rfl

theorem inputAverage_operator (k : Kernel (torusPiMeasure L m)) (f : L2TN L m) :
    (inputAverage L m k).operator f = k.operator (positionAverage L m f) := by
  rw [inputAverage,weightedKernel_operator]
  simp only [sum_apply,smul_apply,permutedKernel_operator,Equiv.symm_symm,
    positionAverage,Finset.smul_sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro τ _
  congr 1
  apply Lp.ext
  filter_upwards [coeFn_physPerm (1 : Equiv.Perm (Fin m)) (k.operator (physPerm τ f))] with x hx
  exact hx

theorem physUnitary_symProj (v : HilbertTensorPower ℂ (L2T L) m) :
    physUnitary (symProj ℂ (L2T L) m v) = positionAverage L m (physUnitary v) := by
  rw [symProj_eq_factorial_average]
  simp only [smul_apply,sum_apply,map_smul,map_sum,positionAverage,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  exact congrArg (((m.factorial : ℂ)⁻¹) • ·) (physEmbed_permRep σ v)

/-- The two finite averages are exactly the two physical P_m compressions. -/
def compressedKernel (z : ℂ) : Kernel (torusPiMeasure L m) :=
  outputAverage L m (inputAverage L m
    (BetheTensorSlice.sumKernel (plusKernel L m z) (minusKernel L m z)))

theorem extend_physicalKernel (z : ℂ) (v : HilbertTensorPower ℂ (L2T L) m) :
    extendSymKernel (physicalKernel L m z) v =
      symProj ℂ (L2T L) m ((physUnitary (L := L) (N := m)).symm
        (rawOperator L m z (physUnitary (symProj ℂ (L2T L) m v)))) := by
  have hU := (physUnitary (L := L) (N := m)).adjoint_eq_symm
  simp only [extendSymKernel,physicalKernel,positionInclusion,
    ContinuousLinearMap.adjoint_comp,hU,ContinuousLinearMap.comp_apply]
  rw [Submodule.adjoint_subtypeL]
  simp only [Submodule.subtypeL_apply,Submodule.coe_orthogonalProjectionOnto_apply,
    ← symProj_eq_starProjection]
  rfl

/-- The block compatibility is proved for the actual constructed physical
kernel; there is no block action premise. -/
theorem physicalKernel_action (z : ℂ) (v : HilbertTensorPower ℂ (L2T L) m) :
    physUnitary (extendSymKernel (physicalKernel L m z) v) =
      (compressedKernel L m z).operator (physUnitary v) := by
  rw [extend_physicalKernel,physUnitary_symProj,
    LinearIsometryEquiv.apply_symm_apply,physUnitary_symProj,
    compressedKernel,outputAverage_operator,inputAverage_operator,
    BetheTensorSlice.operator_sumKernel]
  rfl

/-- The literal real-cube kernel with both m! averages exposed. Output and
input permutations are independent; the lower phase is included in rawKernel. -/
def averagedRaw (z : ℂ) (x y : Fin m → ℝ) : ℂ :=
  (m.factorial : ℂ)⁻¹ * ∑ σ : Equiv.Perm (Fin m),
    ((m.factorial : ℂ)⁻¹ * ∑ τ : Equiv.Perm (Fin m),
      rawKernel L z (x ∘ σ) (y ∘ τ.symm))

theorem compressedKernel_fn (z : ℂ) (x y : Fin m → AddCircle L) :
    (compressedKernel L m z).fn (x,y) =
      averagedRaw L m z (BetheWeakGradient.representatives L x)
        (BetheWeakGradient.representatives L y) := by
  simp only [compressedKernel,outputAverage,inputAverage,weightedKernel,permutedKernel,
    BetheTensorSlice.sumKernel,plusKernel,minusKernel,averagedRaw,Finset.mul_sum,
    rawKernel,BetheWeakGradient.representatives,Function.comp_def]
  rfl

omit [Fact (0 < L)] in
theorem measurable_averagedRaw (z : ℂ) :
    Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => averagedRaw L m z p.1 p.2) := by
  unfold averagedRaw
  apply Measurable.mul measurable_const
  apply Finset.measurable_sum
  intro σ _
  apply Measurable.mul measurable_const
  apply Finset.measurable_sum
  intro τ _
  exact ((measurable_rawPlus m L z).add (measurable_rawMinus m L z)).comp
    (show Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => (p.1 ∘ σ,p.2 ∘ τ.symm)) by fun_prop)

end QuantumNLS.BetheCompressedKernel

#print axioms QuantumNLS.BetheCompressedKernel.weightedKernel
#print axioms QuantumNLS.BetheCompressedKernel.weightedKernel_operator
#print axioms QuantumNLS.BetheCompressedKernel.permutedKernel
#print axioms QuantumNLS.BetheCompressedKernel.permutedKernel_operator
#print axioms QuantumNLS.BetheCompressedKernel.outputAverage
#print axioms QuantumNLS.BetheCompressedKernel.inputAverage
#print axioms QuantumNLS.BetheCompressedKernel.positionAverage
#print axioms QuantumNLS.BetheCompressedKernel.outputAverage_operator
#print axioms QuantumNLS.BetheCompressedKernel.inputAverage_operator
#print axioms QuantumNLS.BetheCompressedKernel.physUnitary_symProj
#print axioms QuantumNLS.BetheCompressedKernel.compressedKernel
#print axioms QuantumNLS.BetheCompressedKernel.extend_physicalKernel
#print axioms QuantumNLS.BetheCompressedKernel.physicalKernel_action
#print axioms QuantumNLS.BetheCompressedKernel.averagedRaw
#print axioms QuantumNLS.BetheCompressedKernel.compressedKernel_fn
#print axioms QuantumNLS.BetheCompressedKernel.measurable_averagedRaw
