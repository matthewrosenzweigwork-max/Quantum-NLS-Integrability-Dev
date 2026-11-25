import QuantumNLS.BetheHigherPlacement
import QuantumNLS.BetheHigherCancellation

/-! Literal higher-degree cube action and phase endpoints of the constructed
physical placements. The strict alternating endpoints and all factorials
are exposed; no all-N eigenrelation is asserted. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace ComplexConjugate
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
namespace QuantumNLS.BetheHigherEndpoints
open TensorCarrier TensorPlacements PhysicalTensor TensorFourier BetheIntegralOperator
open BetheCompressedKernel BetheBlockSlice BetheHigherPlacement
open BetheWeakGradient BetheFiniteNAction BetheExtension
open BetheTransferKernelAdjoint BetheHigherCancellation
open BetheWavefunctions
variable (L : ℝ) [Fact (0 < L)] (m q : ℕ)

omit [Fact (0 < L)] in
/-- Exact upper alternating rectangle for an arbitrary integrand. This does
not require separability or a fixed ordering of the spectator coordinates. -/
theorem rawPlus_rectangle {x : Fin m → ℝ} (hx : x ∈ chamber m L)
    (z : ℂ) (f : (Fin m → ℝ) → ℂ) :
    (∫ y, rawPlus L z x y * f y ∂cubeMeasure m L) =
      ∫ y, Complex.exp (Complex.I*z*displacement x y) * f y
        ∂volume.restrict (Set.pi univ (fun i => Ioo (lower x i) (x i))) := by
  classical
  let D := Set.pi univ (fun i => Ioo (lower x i) (x i))
  have hD : MeasurableSet D := MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)
  have hsub : D ⊆ Icc (fun _ => 0) (fun _ => L) := by
    intro y hy
    have hb : ∀ i, y i ∈ Ioo (lower x i) (x i) := by simpa [D] using hy
    exact ⟨fun i => (lower_bounds hx i).1.trans (hb i).1.le,
      fun i => (hb i).2.le.trans (hx.2 i).2.le⟩
  have he (y : Fin m → ℝ) : rawPlus L z x y * f y =
      D.indicator (fun y => Complex.exp (Complex.I*z*displacement x y) * f y) y := by
    have hb : PlusOrder L x y ↔ y ∈ D := by simpa [D] using plusOrder_box hx y
    by_cases h : y ∈ D <;> simp [rawPlus,hb,h]
  simp_rw [he]
  rw [integral_indicator hD,cubeMeasure,Measure.restrict_restrict hD,
    inter_eq_left.mpr hsub]

omit [Fact (0 < L)] in
/-- Exact lower alternating rectangle, with the original exp(izL) phase. -/
theorem rawMinus_rectangle {x : Fin m → ℝ} (hx : x ∈ chamber m L)
    (z : ℂ) (f : (Fin m → ℝ) → ℂ) :
    (∫ y, rawMinus L z x y * f y ∂cubeMeasure m L) =
      Complex.exp (Complex.I*z*L) *
        ∫ y, Complex.exp (Complex.I*z*displacement x y) * f y
          ∂volume.restrict (Set.pi univ (fun i => Ioo (x i) (upper L x i))) := by
  classical
  let D := Set.pi univ (fun i => Ioo (x i) (upper L x i))
  have hD : MeasurableSet D := MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)
  have hsub : D ⊆ Icc (fun _ => 0) (fun _ => L) := by
    intro y hy
    have hb : ∀ i, y i ∈ Ioo (x i) (upper L x i) := by simpa [D] using hy
    exact ⟨fun i => (hx.2 i).1.le.trans (hb i).1.le,
      fun i => (hb i).2.le.trans (upper_bounds hx i).2⟩
  have he (y : Fin m → ℝ) : rawMinus L z x y * f y =
      D.indicator (fun y => Complex.exp (Complex.I*z*L) *
        (Complex.exp (Complex.I*z*displacement x y) * f y)) y := by
    have hb : MinusOrder L x y ↔ y ∈ D := by simpa [D] using minusOrder_box hx y
    by_cases h : y ∈ D
    · simp only [rawMinus,hb,h,ite_true,indicator_of_mem h]
      rw [lower_phase]
      ring
    · simp [rawMinus,hb,h]
  simp_rw [he]
  rw [integral_indicator hD,cubeMeasure,Measure.restrict_restrict hD,
    inter_eq_left.mpr hsub,integral_const_mul]

/-- Ordinary cube volume, literal upper/lower alternating indicators, full
lower phase, two independent m! averages, and unchanged spectators. -/
def cubeSlice (z : ℂ) (F : C(Fin (m+q) → AddCircle L, ℂ))
    (x : Fin (m+q) → AddCircle L) : ℂ :=
  ∫ y, averagedRaw L m z (representatives L (fun i => x (Fin.castAdd q i))) y *
    F (Fin.append (fun i => (y i : AddCircle L)) (fun i => x (Fin.natAdd m i)))
      ∂cubeMeasure m L

theorem slice_eq_cubeSlice (z : ℂ) (F : C(Fin (m+q) → AddCircle L, ℂ)) :
    BetheBlockSlice.slice L m q (compressedKernel L m z) F = cubeSlice L m q z F := by
  funext x
  unfold BetheBlockSlice.slice cubeSlice
  simp_rw [compressedKernel_fn]
  let f : (Fin m → ℝ) → ℂ := fun y =>
    averagedRaw L m z (representatives L (fun i => x (Fin.castAdd q i))) y *
      F (Fin.append (fun i => (y i : AddCircle L)) (fun i => x (Fin.natAdd m i)))
  have hf : Measurable f :=
    ((measurable_averagedRaw L m z).comp (measurable_const.prodMk measurable_id)).mul
      (F.continuous.measurable.comp (by fun_prop))
  have he (y : Fin m → AddCircle L) : (fun i => ((representatives L y i : ℝ) : AddCircle L)) = y := by
    ext i
    exact (AddCircle.equivIco L 0).symm_apply_apply (y i)
  calc
    _ = ∫ y, f (representatives L y) ∂torusPiMeasure L m := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [f,he]
    _ = _ := integral_representatives L f hf

/-- Unconditional arbitrary-degree endpoint/cube action of the actual
compressed physical block operator with all spectators retained. -/
theorem physical_firstPlacement_cube_ae (z : ℂ)
    (F : C(Fin (m+q) → AddCircle L, ℂ)) :
    physUnitary (firstPlacement (q := q) (BethePhysicalTransfer.physicalKernel L m z)
      ((physUnitary (L := L) (N := m+q)).symm
        (ContinuousMap.toLp 2 (torusPiMeasure L (m+q)) ℂ F))) =ᵐ[torusPiMeasure L (m+q)]
      cubeSlice L m q z F := by
  rw [← slice_eq_cubeSlice L m q z F]
  exact BetheHigherPlacement.physical_firstPlacement_ae L m q z F

open BetheGeneralSliceEndpoints

theorem sourceInput_closed_cube {M : ℕ} {c : ℝ} (hc : 0 < c)
    {n : Fin M → ℤ} (hn : Antitone n) (y : Fin M → ℝ)
    (hy : ∀ j, y j ∈ Icc 0 L) :
    sourceInput L hc hn (fun j => (y j : AddCircle L)) = symmetricExtension L c n y := by
  change torusExtension L c n (fun j => (y j : AddCircle L)) = _
  cases M with
  | zero =>
    unfold torusExtension
    exact congrArg (symmetricExtension L c n) (Subsingleton.elim _ _)
  | succ N => exact torusExtension_closed_cube hc hn y hy

/-- Literal real-cube source integrand, with original normalization and all
spectators fixed at their physical representatives. -/
def sourceCubeSlice {c : ℝ} (_hc : 0 < c) {n : Fin (m+q) → ℤ} (_hn : Antitone n)
    (z : ℂ) (x : Fin (m+q) → AddCircle L) : ℂ :=
  ∫ y, averagedRaw L m z (representatives L (fun i => x (Fin.castAdd q i))) y *
    symmetricExtension L c n
      (Fin.append y (representatives L (fun i => x (Fin.natAdd m i)))) ∂cubeMeasure m L

theorem cubeSlice_source {c : ℝ} (hc : 0 < c) {n : Fin (m+q) → ℤ}
    (hn : Antitone n) (z : ℂ) :
    cubeSlice L m q z (sourceInput L hc hn) = sourceCubeSlice L m q hc hn z := by
  funext x
  unfold cubeSlice sourceCubeSlice
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  have hy' : ∀ j, y j ∈ Icc 0 L := fun j => ⟨hy.1 j,hy.2 j⟩
  have hs : ∀ j : Fin q, representatives L (fun i => x (Fin.natAdd m i)) j ∈ Icc 0 L := by
    intro j
    exact ⟨(AddCircle.equivIco L 0 (x (Fin.natAdd m j))).property.1,
      by simpa only [representatives,zero_add] using
        (AddCircle.equivIco L 0 (x (Fin.natAdd m j))).property.2.le⟩
  have hall : ∀ j, (Fin.append y (representatives L (fun i => x (Fin.natAdd m i)))) j ∈ Icc 0 L := by
    intro j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa using hy' k
    · simpa using hs k
  have h := sourceInput_closed_cube L hc hn _ hall
  have he : (fun j => ((Fin.append y (representatives L (fun i => x (Fin.natAdd m i)))) j : AddCircle L)) =
      Fin.append (fun j => (y j : AddCircle L)) (fun i => x (Fin.natAdd m i)) := by
    ext j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
      exact AddCircle.coe_equivIco
  rw [he] at h
  rw [h]

/-- The literal higher-degree source cube formula acts on the constructed
source vector, exactly identified with physicalWave at every positive count. -/
theorem source_firstPlacement_cube_ae {c : ℝ} (hc : 0 < c)
    {n : Fin (m+q) → ℤ} (hn : Antitone n) (z : ℂ) :
    physUnitary (firstPlacement (q := q) (BethePhysicalTransfer.physicalKernel L m z)
      (sourceVector L hc hn).1) =ᵐ[torusPiMeasure L (m+q)] sourceCubeSlice L m q hc hn z := by
  change physUnitary (firstPlacement (q := q) (BethePhysicalTransfer.physicalKernel L m z)
      ((physUnitary (L := L) (N := m+q)).symm
        (ContinuousMap.toLp 2 (torusPiMeasure L (m+q)) ℂ (sourceInput L hc hn)))) =ᵐ[_] _
  rw [← cubeSlice_source L m q hc hn z]
  exact physical_firstPlacement_cube_ae L m q z (sourceInput L hc hn)

end QuantumNLS.BetheHigherEndpoints

#print axioms QuantumNLS.BetheHigherEndpoints.rawPlus_rectangle
#print axioms QuantumNLS.BetheHigherEndpoints.rawMinus_rectangle
#print axioms QuantumNLS.BetheHigherEndpoints.cubeSlice
#print axioms QuantumNLS.BetheHigherEndpoints.slice_eq_cubeSlice
#print axioms QuantumNLS.BetheHigherEndpoints.physical_firstPlacement_cube_ae
#print axioms QuantumNLS.BetheHigherEndpoints.sourceInput_closed_cube
#print axioms QuantumNLS.BetheHigherEndpoints.sourceCubeSlice
#print axioms QuantumNLS.BetheHigherEndpoints.cubeSlice_source
#print axioms QuantumNLS.BetheHigherEndpoints.source_firstPlacement_cube_ae

#check QuantumNLS.BetheHigherPlacement.physical_tensorMap_eq_sliceMap
#check QuantumNLS.BetheHigherPlacement.sourceVector_eq_physicalWave
#check QuantumNLS.BetheHigherPlacement.source_transferTerm
#check QuantumNLS.BetheHigherPlacement.coefficient_normalization
#check QuantumNLS.BetheCompressedKernel.compressedKernel_fn
#check QuantumNLS.BetheHigherEndpoints.rawPlus_rectangle
#check QuantumNLS.BetheHigherEndpoints.rawMinus_rectangle
#check QuantumNLS.BetheHigherEndpoints.source_firstPlacement_cube_ae
#check QuantumNLS.BetheHigherCancellation.source_selected_outer_cancel
#check QuantumNLS.BetheHigherCancellation.source_cyclic_block_outer_cancel
#check QuantumNLS.BetheHigherCancellation.integral_source_cyclic_outer_cancel

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.BetheHigherPlacement.physical_tensorMap_eq_sliceMap,
    ``QuantumNLS.BetheHigherPlacement.sourceVector_eq_physicalWave,
    ``QuantumNLS.BetheHigherPlacement.source_transferTerm,
    ``QuantumNLS.BetheHigherPlacement.coefficient_normalization,
    ``QuantumNLS.BetheCompressedKernel.compressedKernel_fn,
    ``QuantumNLS.BetheHigherEndpoints.rawPlus_rectangle,
    ``QuantumNLS.BetheHigherEndpoints.rawMinus_rectangle,
    ``QuantumNLS.BetheHigherEndpoints.source_firstPlacement_cube_ae,
    ``QuantumNLS.BetheHigherCancellation.source_selected_outer_cancel,
    ``QuantumNLS.BetheHigherCancellation.selectedDisplacement_firstBlock,
    ``QuantumNLS.BetheHigherCancellation.outerFaceMeasure_eq_open,
    ``QuantumNLS.BetheHigherCancellation.integral_source_cyclic_outer_cancel]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  for n in #[``QuantumNLS.BetheBlockTensor.measurePreserving_splitCoordinates,
      ``QuantumNLS.BetheBlockTensor.memLp_blockProduct,
      ``QuantumNLS.BetheBlockTensor.norm_blockProduct,
      ``QuantumNLS.BetheBlockTensor.physUnitary_join,
      ``QuantumNLS.BetheBlockSlice.tensorMap_product,
      ``QuantumNLS.BetheBlockSlice.sliceMap_product,
      ``QuantumNLS.BetheBlockSlice.tensorMap_eq_sliceMap,
      ``QuantumNLS.PhysicalTensor.prodAlgebra_dense,
      ``QuantumNLS.TensorCarrier.splitIsometry,
      ``QuantumNLS.TensorCarrier.splitIsometry_ptprod_append,
      ``QuantumNLS.BetheCompressedKernel.weightedKernel_operator,
      ``QuantumNLS.BetheCompressedKernel.permutedKernel_operator,
      ``QuantumNLS.BetheCompressedKernel.outputAverage,
      ``QuantumNLS.BetheCompressedKernel.inputAverage,
      ``QuantumNLS.BetheCompressedKernel.extend_physicalKernel,
      ``QuantumNLS.BetheCompressedKernel.physicalKernel_action,
      ``QuantumNLS.BethePhysicalTransfer.physicalKernel,
      ``QuantumNLS.BetheIntegralOperator.Kernel.operator_apply_ae,
      ``QuantumNLS.BetheTransferKernelAdjoint.rawPlus,
      ``QuantumNLS.BetheTransferKernelAdjoint.rawMinus,
      ``QuantumNLS.BetheTransferKernelAdjoint.PlusOrder,
      ``QuantumNLS.BetheTransferKernelAdjoint.MinusOrder,
      ``QuantumNLS.BetheFiniteNAction.plusOrder_box,
      ``QuantumNLS.BetheFiniteNAction.minusOrder_box,
      ``QuantumNLS.BetheFiniteNAction.integral_representatives,
      ``QuantumNLS.BetheHigherPlacement.normalized_placement,
      ``QuantumNLS.TensorCarrier.symProj_eq_factorial_average,
      ``QuantumNLS.BethePhysicalTransfer.transferTerm,
      ``Nat.factorial_mul_descFactorial,
      ``QuantumNLS.BetheFiniteNAction.physicalWave,
      ``QuantumNLS.BetheExtension.torusExtension_closed_cube,
      ``QuantumNLS.BetheExtension.symmetricExtension_update_faces,
      ``QuantumNLS.BetheHigherCancellation.selectedDisplacement_face,
      ``QuantumNLS.BetheHigherCancellation.source_cyclic_block_faces,
      ``QuantumNLS.BetheHigherCancellation.source_cyclic_block_outer_cancel,
      ``QuantumNLS.BethePeriodic.sourceRoots_term_periodic,
      ``QuantumNLS.BetheSmooth.sourceRoots] do
    unless seen.contains n do
      throwError "Higher-degree route missed actual source ingredient: {n}"
  for n in seen do
    if n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" then
      throwError "Higher-degree route used a special-particle action: {n}"
  for n in #[``QuantumNLS.BetheTensorSlice.firstPlacement_product,
      ``QuantumNLS.BetheTensorSlice.tensorMap_product,
      ``QuantumNLS.BetheTensorSlice.sliceMap_product,
      ``QuantumNLS.BetheTensorSlice.tensorMap_eq_sliceMap,
      ``QuantumNLS.BetheTensorSlice.physical_tensorMap_eq_sliceMap,
      ``QuantumNLS.BetheGeneralSlice.physical_tensorMap_eq_sliceMap] do
    if seen.contains n then
      throwError "Higher-degree route used a singleton/N2 action bridge: {n}"
  Lean.logInfo m!"Higher-degree placement route PASS: {seen.size} transitive constants; arbitrary block and spectators, density, both P_m compressions, literal source cube/rectangles, full lower phase, 1/N! average and c^m(N)_m, exact source vector, selected and cyclic integrated outer-face cancellation. No singleton/N2 action bridge; internal/cross-degree cancellation and allN eigenrelation/basis OPEN."
