import Mathlib
import QuantumNLS.Ext002MonoFields
import QuantumNLS.BetheHigherPlacement

/-!
# EXT-002 / V-01 full monodromy (owner decision D4), stage M4a: general-degree slice bridge

For an arbitrary bounded measurable kernel `k` on `𝕋_L^m × 𝕋_L^m` (A04.tex:57-59) this module
proves, on the actual completed tensor and with arbitrary spectator count `q`:

* `physOp k = P_m K̃ P_m` (the compressed integral operator `A` of A04.tex:58-59) satisfies the
  block compatibility `physOp_action` with the doubly averaged kernel `avgKernel k`
  (generalizing the frozen `BetheCompressedKernel.physicalKernel_action` from the transfer
  kernel to every kernel);
* `sliceOp_toLp`: on continuous functions the weak `L²` slice operator of `Ext002MonoFields`
  is the frozen pointwise slice `BetheBlockSlice.sliceMap`;
* `tensor_eq_sliceOp`: by density of continuous functions in `L²(𝕋_L^{m+q})`, the tensor
  placement `A ⊗ 1^{⊗q}` transported to position space IS the weak slice operator of the
  averaged kernel, on all of `L²` (the general-`m` slice formula).
No tensor/slice identity is postulated.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace QuantumNLS.Ext002MonoSlice
open PhysicalTensor TensorCarrier TensorPlacements BethePhysicalTransfer BetheIntegralOperator
open Ext002MonoLift Ext002MonoFields

variable (L : ℝ) [Fact (0 < L)]

/-- A square kernel as a monomial kernel (same function). -/
def ofKernel {m : ℕ} (k : Kernel (torusPiMeasure L m)) : MonoKernel L m m where
  fn := k.fn
  measurable := k.measurable
  bound := k.bound
  bound_nonneg := k.bound_nonneg
  norm_le := k.norm_le

/-- `P_m K̃ P_m` on the physical symmetric sector (A04.tex:58-59). -/
def physOp {m : ℕ} (k : Kernel (torusPiMeasure L m)) :
    SymSector ℂ (L2T L) m →L[ℂ] SymSector ℂ (L2T L) m :=
  (positionInclusion L m).adjoint ∘L k.operator ∘L positionInclusion L m

/-- Both `m!` averages of a kernel. -/
def avgKernel {m : ℕ} (k : Kernel (torusPiMeasure L m)) : Kernel (torusPiMeasure L m) :=
  BetheCompressedKernel.outputAverage L m (BetheCompressedKernel.inputAverage L m k)

theorem physOp_sumKernel (m : ℕ) (z : ℂ) :
    physOp L (BetheTensorSlice.sumKernel (BetheTransferOperators.plusKernel L m z)
      (BetheTransferOperators.minusKernel L m z)) = physicalKernel L m z := by
  unfold physOp physicalKernel
  rw [BetheTensorSlice.operator_sumKernel]
  try rfl

theorem extend_physOp {m : ℕ} (k : Kernel (torusPiMeasure L m))
    (v : HilbertTensorPower ℂ (L2T L) m) :
    extendSymKernel (physOp L k) v =
      symProj ℂ (L2T L) m ((physUnitary (L := L) (N := m)).symm
        (k.operator (physUnitary (symProj ℂ (L2T L) m v)))) := by
  have hU := (physUnitary (L := L) (N := m)).adjoint_eq_symm
  simp only [extendSymKernel, physOp, positionInclusion,
    ContinuousLinearMap.adjoint_comp, hU, ContinuousLinearMap.comp_apply]
  rw [Submodule.adjoint_subtypeL]
  simp only [Submodule.subtypeL_apply, Submodule.coe_orthogonalProjectionOnto_apply,
    ← symProj_eq_starProjection]
  rfl

/-- Block compatibility of `P_m K̃ P_m` for every bounded kernel. -/
theorem physOp_action {m : ℕ} (k : Kernel (torusPiMeasure L m))
    (v : HilbertTensorPower ℂ (L2T L) m) :
    physUnitary (extendSymKernel (physOp L k) v) = (avgKernel L k).operator (physUnitary v) := by
  rw [extend_physOp, BetheCompressedKernel.physUnitary_symProj,
    LinearIsometryEquiv.apply_symm_apply, BetheCompressedKernel.physUnitary_symProj,
    avgKernel, BetheCompressedKernel.outputAverage_operator,
    BetheCompressedKernel.inputAverage_operator]

theorem symm_split_apply (m q : ℕ) (p : (Fin m → AddCircle L) × (Fin q → AddCircle L)) :
    (BetheBlockTensor.splitCoordinates L m q).symm p = Fin.append p.1 p.2 :=
  splitCoordinates_symm_apply L m q p.1 p.2

/-- On continuous functions the weak slice operator is the pointwise slice integral. -/
theorem sliceOp_toLp {m : ℕ} (q : ℕ) (k : Kernel (torusPiMeasure L m))
    (F : C(Fin (m+q) → AddCircle L, ℂ)) :
    sliceOp L q (ofKernel L k) (ContinuousMap.toLp 2 (torusPiMeasure L (m+q)) ℂ F) =
      BetheBlockSlice.sliceMap L m q k F := by
  apply ext_inner_left ℂ
  intro Hh
  have hH : Integrable (fun p => Hh (outPt L p)) (tripMeasure L m m q) :=
    ((Lp.memLp (liftOut L m m q Hh)).integrable (by norm_num)).congr (coeFn_liftOut L m m q Hh)
  have hint : Integrable (fun p : Trip L m m q =>
      conj (Hh (outPt L p)) * k.fn (p.1.1, p.2) * F (inPt L p)) (tripMeasure L m m q) := by
    refine (hH.norm.mul_const (k.bound * ‖F‖)).mono' ?_ ?_
    · exact (hH.aestronglyMeasurable.star.mul
        (k.measurable.comp ((measurable_fst.comp measurable_fst).prodMk
          measurable_snd)).aestronglyMeasurable).mul
        (F.continuous.measurable.comp (measurable_inPt L m m q)).aestronglyMeasurable
    · filter_upwards with p
      show ‖conj (Hh (outPt L p)) * k.fn (p.1.1, p.2) * F (inPt L p)‖ ≤
        ‖Hh (outPt L p)‖ * (k.bound * ‖F‖)
      rw [norm_mul, norm_mul, Complex.norm_conj, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (k.norm_le _) (F.norm_coe_le_norm _) (norm_nonneg _) k.bound_nonneg)
        (norm_nonneg _)
  have hmp := ((BetheBlockTensor.measurePreserving_splitCoordinates L m q).symm
    (BetheBlockTensor.splitCoordinates L m q)).integral_comp'
    (fun u => conj (Hh u) * BetheBlockSlice.slice L m q k F u)
  simp only [symm_split_apply] at hmp
  calc ⟪Hh, sliceOp L q (ofKernel L k) (ContinuousMap.toLp 2 (torusPiMeasure L (m+q)) ℂ F)⟫_ℂ
      = ∫ p, conj (Hh (outPt L p)) * k.fn (p.1.1, p.2) * F (inPt L p) ∂tripMeasure L m m q := by
        rw [inner_sliceOp]
        apply integral_congr_ae
        filter_upwards [(qmp_inPt L m m q).ae_eq_comp
          (ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ) (torusPiMeasure L (m+q)) F)]
          with p hp
        simp only [Function.comp_apply] at hp
        simp only [hp, ofKernel]
    _ = ∫ xw, ∫ t, conj (Hh (Fin.append xw.1 xw.2)) * k.fn (xw.1, t) * F (Fin.append t xw.2)
          ∂torusPiMeasure L m ∂(torusPiMeasure L m).prod (torusPiMeasure L q) :=
        integral_prod _ hint
    _ = ∫ xw, conj (Hh (Fin.append xw.1 xw.2)) *
          ∫ t, k.fn (xw.1, t) * F (Fin.append t xw.2) ∂torusPiMeasure L m
          ∂(torusPiMeasure L m).prod (torusPiMeasure L q) := by
        congr 1
        funext xw
        rw [← integral_const_mul]
        congr 1
        funext t
        ring
    _ = ∫ u, conj (Hh u) * BetheBlockSlice.slice L m q k F u ∂torusPiMeasure L (m+q) := by
        rw [← hmp]
        congr 1
        funext xw
        simp only [BetheBlockSlice.slice, Fin.append_left, Fin.append_right]
        rfl
    _ = ⟪Hh, BetheBlockSlice.sliceMap L m q k F⟫_ℂ := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [BetheBlockSlice.coe_sliceMap L m q k F] with u hu
        rw [RCLike.inner_apply', hu]

/-- **General-degree slice formula on all of `L²`**: the transported tensor placement
`(P_m K̃ P_m) ⊗ 1^{⊗q}` is the weak slice operator of the averaged kernel. -/
theorem tensor_eq_sliceOp {m : ℕ} (q : ℕ) (k : Kernel (torusPiMeasure L m)) :
    (physUnitary (L := L) (N := m+q)).toContinuousLinearEquiv.toContinuousLinearMap ∘L
      firstPlacement (q := q) (physOp L k) ∘L
        (physUnitary (L := L) (N := m+q)).symm.toContinuousLinearEquiv.toContinuousLinearMap =
      sliceOp L q (ofKernel L (avgKernel L k)) := by
  have h1 := BetheBlockSlice.tensorMap_eq_sliceMap L m q (physOp L k) (avgKernel L k)
    (physOp_action L k)
  have hd := ContinuousMap.toLp_denseRange (E := ℂ) (𝕜 := ℂ)
    (μ := torusPiMeasure L (m+q)) (p := 2) (by norm_num)
  have heq : (⇑((physUnitary (L := L) (N := m+q)).toContinuousLinearEquiv.toContinuousLinearMap ∘L
      firstPlacement (q := q) (physOp L k) ∘L
        (physUnitary (L := L) (N := m+q)).symm.toContinuousLinearEquiv.toContinuousLinearMap) :
          L2TN L (m+q) → L2TN L (m+q)) = ⇑(sliceOp L q (ofKernel L (avgKernel L k))) := by
    refine hd.equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _) ?_
    funext F
    simp only [Function.comp_apply]
    rw [sliceOp_toLp]
    exact congrArg (fun M : C(Fin (m+q) → AddCircle L, ℂ) →L[ℂ] L2TN L (m+q) => M F) h1
  exact ContinuousLinearMap.ext (congrFun heq)

end QuantumNLS.Ext002MonoSlice

#print axioms QuantumNLS.Ext002MonoSlice.physOp_sumKernel
#print axioms QuantumNLS.Ext002MonoSlice.physOp_action
#print axioms QuantumNLS.Ext002MonoSlice.sliceOp_toLp
#print axioms QuantumNLS.Ext002MonoSlice.tensor_eq_sliceOp
