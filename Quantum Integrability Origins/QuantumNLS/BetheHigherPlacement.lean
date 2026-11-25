import QuantumNLS.BetheCompressedKernel
import QuantumNLS.BetheBlockSlice

/-! Actual higher-degree physical placement with arbitrary spectators.
Source periodic_basis.tex:316–339. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace ComplexConjugate
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
namespace QuantumNLS.BetheHigherPlacement
open TensorCarrier TensorPlacements PhysicalTensor TensorFourier BetheIntegralOperator
open BetheCompressedKernel BetheBlockSlice
variable (L : ℝ) [Fact (0 < L)]

/-- All block degrees and spectator counts; actual P_m compressed kernel.
No action or eigenrelation hypothesis is required. -/
theorem physical_tensorMap_eq_sliceMap (m q : ℕ) (z : ℂ) :
    BetheBlockSlice.tensorMap L m q (BethePhysicalTransfer.physicalKernel L m z) =
      BetheBlockSlice.sliceMap L m q (compressedKernel L m z) :=
  BetheBlockSlice.tensorMap_eq_sliceMap L m q _ _ (physicalKernel_action L m z)

/-- The actual completed tensor block action has the literal compressed
integral, preserving every spectator. -/
theorem physical_firstPlacement_ae (m q : ℕ) (z : ℂ)
    (F : C(Fin (m+q) → AddCircle L, ℂ)) :
    physUnitary (firstPlacement (q := q) (BethePhysicalTransfer.physicalKernel L m z)
      ((physUnitary (L := L) (N := m+q)).symm
        (ContinuousMap.toLp 2 (torusPiMeasure L (m+q)) ℂ F))) =ᵐ[torusPiMeasure L (m+q)]
      BetheBlockSlice.slice L m q (compressedKernel L m z) F := by
  have h := congrArg (fun M : C(Fin (m+q) → AddCircle L, ℂ) →L[ℂ] L2TN L (m+q) => M F)
    (physical_tensorMap_eq_sliceMap L m q z)
  change physUnitary (firstPlacement (q := q) (BethePhysicalTransfer.physicalKernel L m z)
      ((physUnitary (L := L) (N := m+q)).symm
        (ContinuousMap.toLp 2 (torusPiMeasure L (m+q)) ℂ F))) = _ at h
  rw [h]
  exact BetheBlockSlice.coe_sliceMap L m q _ F

/-- Exact P_N normalization of the degree-m placement: the average of
literal slice outputs, with no probability-volume or extra factorial change.
The sole premise identifies the continuous representative of the input. -/
theorem normalized_placement (m q : ℕ) (z : ℂ)
    (F : C(Fin (m+q) → AddCircle L, ℂ))
    (ψ : SymSector ℂ (L2T L) (m+q))
    (hψ : physUnitary ψ.1 = ContinuousMap.toLp 2 (torusPiMeasure L (m+q)) ℂ F) :
    physUnitary ((BethePhysicalTransfer.placement (q := q)
      (BethePhysicalTransfer.physicalKernel L m z) ψ).1) =
      ((((m+q).factorial : ℂ)⁻¹) •
        ∑ σ : Equiv.Perm (Fin (m+q)), physPerm σ
          (BetheBlockSlice.sliceMap L m q (compressedKernel L m z) F)) := by
  have hi : ψ.1 = (physUnitary (L := L) (N := m+q)).symm
      (ContinuousMap.toLp 2 (torusPiMeasure L (m+q)) ℂ F) := by
    rw [← hψ, LinearIsometryEquiv.symm_apply_apply]
  have hs := congrArg (fun M : C(Fin (m+q) → AddCircle L, ℂ) →L[ℂ] L2TN L (m+q) => M F)
    (physical_tensorMap_eq_sliceMap L m q z)
  change physUnitary (firstPlacement (q := q) (BethePhysicalTransfer.physicalKernel L m z)
    ((physUnitary (L := L) (N := m+q)).symm
      (ContinuousMap.toLp 2 (torusPiMeasure L (m+q)) ℂ F))) = _ at hs
  change physUnitary (((SymSector ℂ (L2T L) (m+q)).subtypeL.adjoint
    (firstPlacement (q := q) (BethePhysicalTransfer.physicalKernel L m z) ψ.1)).1) = _
  rw [Submodule.adjoint_subtypeL, Submodule.coe_orthogonalProjectionOnto_apply,
    ← symProj_eq_starProjection, symProj_eq_factorial_average]
  simp only [smul_apply, sum_apply, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  change physEmbed (L := L) (N := m+q) ((permRep ℂ (L2T L) (m+q) σ : HilbertTensorPower ℂ (L2T L) (m+q) →L[ℂ] HilbertTensorPower ℂ (L2T L) (m+q))
    (firstPlacement (q := q) (BethePhysicalTransfer.physicalKernel L m z) ψ.1)) = _
  rw [physEmbed_permRep]
  change physPerm σ (physUnitary (firstPlacement (q := q)
    (BethePhysicalTransfer.physicalKernel L m z) ψ.1)) = _
  rw [hi, hs]

theorem totalPlacement_add (m q : ℕ)
    (A : SymSector ℂ (L2T L) m →L[ℂ] SymSector ℂ (L2T L) m) :
    BethePhysicalTransfer.totalPlacement (m+q) m (by omega) A =
      BethePhysicalTransfer.placement (q := q) A := by
  have hcast (r : ℕ) (hr : m+r=m+q) (hrq : r=q) :
      KernelDefinition.castSymSectorOperator hr
        (BethePhysicalTransfer.placement (q := r) A) =
          BethePhysicalTransfer.placement (q := q) A := by
    subst r
    rfl
  exact hcast ((m+q)-m) (Nat.add_sub_of_le (by omega)) (by omega)

/-- Every positive degree has the literal c^m (N)_m coefficient multiplying
the 1/N! outer average, with both inner 1/m! averages retained in the kernel. -/
theorem transferTerm_degree (m q : ℕ) (hm : 0 < m) (c : ℝ) (z : ℂ)
    (F : C(Fin (m+q) → AddCircle L, ℂ))
    (ψ : SymSector ℂ (L2T L) (m+q))
    (hψ : physUnitary ψ.1 = ContinuousMap.toLp 2 (torusPiMeasure L (m+q)) ℂ F) :
    physUnitary ((BethePhysicalTransfer.transferTerm L (m+q) c z ⟨m,by omega⟩ ψ).1) =
      ((c^m * (m+q).descFactorial m : ℝ) : ℂ) •
        ((((m+q).factorial : ℂ)⁻¹) •
          ∑ σ : Equiv.Perm (Fin (m+q)), physPerm σ
            (BetheBlockSlice.sliceMap L m q (compressedKernel L m z) F)) := by
  simp only [BethePhysicalTransfer.transferTerm,hm,↓reduceIte,totalPlacement_add]
  change physUnitary (((c^m * (m+q).descFactorial m : ℝ) : ℂ) •
    ((BethePhysicalTransfer.placement (q := q)
      (BethePhysicalTransfer.physicalKernel L m z) ψ).1)) = _
  rw [map_smul,normalized_placement L m q z F ψ hψ]

/-- Cancellation of the outer N! against (N)_m leaves exactly 1/q!.
The two P_m factors are still carried by compressedKernel. -/
theorem coefficient_normalization (m q : ℕ) (c : ℝ) :
    (((c^m * (m+q).descFactorial m : ℝ) : ℂ) * ((m+q).factorial : ℂ)⁻¹) =
      (c : ℂ)^m * (q.factorial : ℂ)⁻¹ := by
  have hnat := Nat.factorial_mul_descFactorial (n := m+q) (k := m) (by omega)
  rw [Nat.add_sub_cancel_left] at hnat
  have h : (q.factorial : ℂ) * ((m+q).descFactorial m : ℂ) = ((m+q).factorial : ℂ) := by
    exact_mod_cast hnat
  have hq : (q.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero q)
  have hN : ((m+q).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero (m+q))
  push_cast
  field_simp [hq,hN]
  linear_combination (c : ℂ)^m * h

open BetheGeneralSliceEndpoints BetheExtension

/-- The source's actual continuous torus wave, in the actual symmetric
completed tensor. This preserves its original normalization. -/
def sourceVector {M : ℕ} {c : ℝ} (hc : 0 < c) {n : Fin M → ℤ} (hn : Antitone n) :
    SymSector ℂ (L2T L) M :=
  ⟨(physUnitary (L := L) (N := M)).symm
    (ContinuousMap.toLp 2 (torusPiMeasure L M) ℂ (sourceInput L hc hn)),
      (mem_physSector_iff _).mpr (by
        intro σ
        rw [LinearIsometryEquiv.apply_symm_apply]
        apply Lp.ext
        filter_upwards [coeFn_physPerm σ
            (ContinuousMap.toLp 2 (torusPiMeasure L M) ℂ (sourceInput L hc hn)),
          (measurePreserving_coordPerm (L := L) σ).quasiMeasurePreserving.ae
            (ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ)
              (torusPiMeasure L M) (sourceInput L hc hn)),
          ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ)
            (torusPiMeasure L M) (sourceInput L hc hn)] with x hp hx hy
        rw [hp,hx,hy]
        exact torusExtension_permute L c n x σ)⟩

theorem sourceVector_position {M : ℕ} {c : ℝ} (hc : 0 < c)
    {n : Fin M → ℤ} (hn : Antitone n) :
    physUnitary (sourceVector L hc hn).1 =
      ContinuousMap.toLp 2 (torusPiMeasure L M) ℂ (sourceInput L hc hn) :=
  LinearIsometryEquiv.apply_symm_apply _ _

/-- Exact equality with the previously frozen physical source vector. -/
theorem sourceVector_eq_physicalWave {N : ℕ} {c : ℝ} (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    sourceVector L hc hn = BetheFiniteNAction.physicalWave L hc hn :=
  Subtype.ext (sourceInput_tensor_eq L hc hn)

/-- Actual source action at every positive degree with arbitrary spectators.
The wave is constructed above and is exactly physicalWave at positive N. -/
theorem source_transferTerm (m q : ℕ) (hm : 0 < m) {c : ℝ} (hc : 0 < c)
    {n : Fin (m+q) → ℤ} (hn : Antitone n) (z : ℂ) :
    physUnitary ((BethePhysicalTransfer.transferTerm L (m+q) c z ⟨m,by omega⟩
      (sourceVector L hc hn)).1) =
      ((c^m * (m+q).descFactorial m : ℝ) : ℂ) •
        ((((m+q).factorial : ℂ)⁻¹) •
          ∑ σ : Equiv.Perm (Fin (m+q)), physPerm σ
            (BetheBlockSlice.sliceMap L m q (compressedKernel L m z) (sourceInput L hc hn))) :=
  transferTerm_degree L m q hm c z (sourceInput L hc hn) (sourceVector L hc hn)
    (sourceVector_position L hc hn)

end QuantumNLS.BetheHigherPlacement


#print axioms QuantumNLS.BetheHigherPlacement.physical_tensorMap_eq_sliceMap
#print axioms QuantumNLS.BetheHigherPlacement.physical_firstPlacement_ae
#print axioms QuantumNLS.BetheHigherPlacement.normalized_placement
#print axioms QuantumNLS.BetheHigherPlacement.totalPlacement_add
#print axioms QuantumNLS.BetheHigherPlacement.transferTerm_degree
#print axioms QuantumNLS.BetheHigherPlacement.coefficient_normalization
#print axioms QuantumNLS.BetheHigherPlacement.sourceVector
#print axioms QuantumNLS.BetheHigherPlacement.sourceVector_position
#print axioms QuantumNLS.BetheHigherPlacement.sourceVector_eq_physicalWave
#print axioms QuantumNLS.BetheHigherPlacement.source_transferTerm
