import NlsGge.Spectral.ActualFullPeriodTwoSourceBlockOperatorV4
import NlsGge.Spectral.ActualFullPeriodTwoSourceBlockDomainDenseMinimumV1
import NlsGge.Spectral.ActualSourcePerturbedDiracSelfAdjointPhysicalSliceV2
import NlsGge.Spectral.ActualSourcePerturbedImaginaryShiftsUniformRangeV4
import NlsGge.Spectral.TwoImaginaryRangesSelfAdjointV2
import Mathlib.Analysis.InnerProductSpace.LinearPMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section
open scoped LinearPMap

namespace NlsGge.Schur
open NlsGge.Pilot
open TransportBridgeV4

/-- The actual full-carrier operator is the pullback of the direct sum of the
existing periodic and antiperiodic source `D+V` partial maps. Its domain is
exactly the pullback submodule established in BlockOperator V4. -/
def actualFullPeriodTwoDoubledCirclePerturbedDiracPMap
    (u₁ u₂ : PhysicalL2) :
    ActualTwoChannelSpectralL2 →ₗ.[ℂ] ActualTwoChannelSpectralL2 :=
  ⟨actualFullPeriodTwoSourceDoubledCircleDomain,
    actualFullPeriodTwoDoubledCirclePerturbedDiracAction u₁ u₂⟩

private def actualFullPeriodTwoSourceBlockComponentLocal
    (x : actualFullPeriodTwoSourceBlockDomain) (p : Fin 2) :
      recoveredActualSourceFreeWeightedDomain (p.val : ℤ) :=
  ⟨x.1 p, x.2 p⟩

private def actualFullPeriodTwoSourceDomainTransportLocal
    (x : actualFullPeriodTwoSourceDoubledCircleDomain) :
      actualFullPeriodTwoSourceBlockDomain :=
  ⟨actualFullPeriodTwoSourceIntervalAssembly x.1, x.2⟩

private theorem actualFullPeriodTwoSourceDomainTransportLocal_add
    (x y : actualFullPeriodTwoSourceDoubledCircleDomain) :
    actualFullPeriodTwoSourceDomainTransportLocal (x + y) =
      actualFullPeriodTwoSourceDomainTransportLocal x +
        actualFullPeriodTwoSourceDomainTransportLocal y := by
  apply Subtype.ext
  exact map_add actualFullPeriodTwoSourceIntervalAssembly x.1 y.1

private theorem actualFullPeriodTwoSourceDomainTransportLocal_smul
    (c : ℂ) (x : actualFullPeriodTwoSourceDoubledCircleDomain) :
    actualFullPeriodTwoSourceDomainTransportLocal (c • x) =
      c • actualFullPeriodTwoSourceDomainTransportLocal x := by
  apply Subtype.ext
  exact map_smul actualFullPeriodTwoSourceIntervalAssembly c x.1

private theorem actualFullPeriodTwoAction_repr_local
    (u₁ u₂ : PhysicalL2)
    (x : actualFullPeriodTwoSourceDoubledCircleDomain) :
    actualFullPeriodTwoSourceIntervalAssembly
        (actualFullPeriodTwoDoubledCirclePerturbedDiracAction u₁ u₂ x) =
      actualFullPeriodTwoSourceBlockPMap u₁ u₂
        (actualFullPeriodTwoSourceDomainTransportLocal x) := by
  change actualFullPeriodTwoSourceIntervalAssembly
      (actualFullPeriodTwoSourceIntervalAssembly.symm
        (actualFullPeriodTwoSourceBlockPMap u₁ u₂
          (⟨actualFullPeriodTwoSourceIntervalAssembly x.1, x.2⟩ :
            actualFullPeriodTwoSourceBlockDomain))) = _
  exact actualFullPeriodTwoSourceIntervalAssembly.apply_symm_apply _

/-- Pullback along the actual carrier isometry preserves density of the graph
domain on the two-channel doubled-circle L² carrier. -/
theorem actualFullPeriodTwoSourceDoubledCircleDomain_dense :
    Dense (actualFullPeriodTwoSourceDoubledCircleDomain :
      Set ActualTwoChannelSpectralL2) := by
  change Dense (actualFullPeriodTwoSourceIntervalAssembly ⁻¹'
    (actualFullPeriodTwoSourceBlockDomain : Set ActualFullPeriodTwoSourcePair))
  exact actualFullPeriodTwoSourceBlockDomain_dense_minimum.preimage
    actualFullPeriodTwoSourceIntervalAssembly.toHomeomorph.isOpenMap

/-- The source direct-sum action is formally symmetric on the physical slice,
by the already proved actual formal-symmetry theorem in each parity sector. -/
theorem actualFullPeriodTwoSourceBlockPMap_formalSelfAdjoint_of_physical_slice
    (u₁ u₂ : PhysicalL2) (hphysical : u₂ = star u₁) :
    (actualFullPeriodTwoSourceBlockPMap u₁ u₂).IsFormalAdjoint
      (actualFullPeriodTwoSourceBlockPMap u₁ u₂) := by
  intro x y
  change inner ℂ (actualFullPeriodTwoSourceBlockAction u₁ u₂ x) y.val =
    inner ℂ x.val (actualFullPeriodTwoSourceBlockAction u₁ u₂ y)
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro p hp
  exact actualSourcePerturbedDirac_formalSelfAdjoint_of_physical_slice
    (p.val : ℤ) u₁ u₂ hphysical
    (actualFullPeriodTwoSourceBlockComponentLocal x p)
    (actualFullPeriodTwoSourceBlockComponentLocal y p)

/-- Formal symmetry transports from the exact source-block PMap to the
full-carrier PMap through the actual period-two Hilbert isometry. -/
theorem actualFullPeriodTwoDoubledCirclePerturbedDiracPMap_formalSelfAdjoint_of_physical_slice
    (u₁ u₂ : PhysicalL2) (hphysical : u₂ = star u₁) :
    (actualFullPeriodTwoDoubledCirclePerturbedDiracPMap u₁ u₂).IsFormalAdjoint
      (actualFullPeriodTwoDoubledCirclePerturbedDiracPMap u₁ u₂) := by
  intro x y
  let xd : actualFullPeriodTwoSourceDoubledCircleDomain := ⟨x.1, x.2⟩
  let yd : actualFullPeriodTwoSourceDoubledCircleDomain := ⟨y.1, y.2⟩
  change inner ℂ
      (actualFullPeriodTwoDoubledCirclePerturbedDiracAction u₁ u₂ xd)
      (yd : ActualTwoChannelSpectralL2) =
    inner ℂ (xd : ActualTwoChannelSpectralL2)
      (actualFullPeriodTwoDoubledCirclePerturbedDiracAction u₁ u₂ yd)
  calc
    inner ℂ
        (actualFullPeriodTwoDoubledCirclePerturbedDiracAction u₁ u₂ xd)
        (yd : ActualTwoChannelSpectralL2) =
      inner ℂ
        (actualFullPeriodTwoSourceIntervalAssembly
          (actualFullPeriodTwoDoubledCirclePerturbedDiracAction u₁ u₂ xd))
        (actualFullPeriodTwoSourceIntervalAssembly (yd : ActualTwoChannelSpectralL2)) :=
      (actualFullPeriodTwoSourceIntervalAssembly.inner_map_map _ _).symm
    _ = inner ℂ
        (actualFullPeriodTwoSourceBlockPMap u₁ u₂
          (actualFullPeriodTwoSourceDomainTransportLocal xd))
        (actualFullPeriodTwoSourceIntervalAssembly (yd : ActualTwoChannelSpectralL2)) := by
      rw [actualFullPeriodTwoAction_repr_local]
    _ = inner ℂ
        (actualFullPeriodTwoSourceIntervalAssembly
          (xd : ActualTwoChannelSpectralL2))
        (actualFullPeriodTwoSourceBlockPMap u₁ u₂
          (actualFullPeriodTwoSourceDomainTransportLocal yd)) :=
      actualFullPeriodTwoSourceBlockPMap_formalSelfAdjoint_of_physical_slice
        u₁ u₂ hphysical
        (actualFullPeriodTwoSourceDomainTransportLocal xd)
        (actualFullPeriodTwoSourceDomainTransportLocal yd)
    _ = inner ℂ (xd : ActualTwoChannelSpectralL2)
        (actualFullPeriodTwoDoubledCirclePerturbedDiracAction u₁ u₂ yd) := by
      rw [← actualFullPeriodTwoAction_repr_local]
      exact actualFullPeriodTwoSourceIntervalAssembly.inner_map_map _ _

private theorem actualFullPeriodTwoSourceBlockPMap_minus_i_range
    (u₁ u₂ : PhysicalL2) (η : ℝ)
    (hranges : ∀ n : ℤ,
      Function.Surjective
        (actualSourcePerturbedShiftedDiracAfterAE n (Complex.I * (η : ℂ)) u₁ u₂) ∧
      Function.Surjective
        (actualSourcePerturbedShiftedDiracAfterAE n (-Complex.I * (η : ℂ)) u₁ u₂))
    (y : ActualFullPeriodTwoSourcePair) :
    ∃ x : actualFullPeriodTwoSourceBlockDomain,
      actualFullPeriodTwoSourceBlockPMap u₁ u₂ x -
        (Complex.I * (η : ℂ)) • (x : ActualFullPeriodTwoSourcePair) = y := by
  let wx : ∀ p : Fin 2, recoveredActualSourceFreeWeightedDomain (p.val : ℤ) :=
    fun p => Classical.choose ((hranges p.val).1 (-(y p)))
  have hwx (p : Fin 2) :
      actualSourcePerturbedShiftedDiracAfterAE (p.val : ℤ)
        (Complex.I * (η : ℂ)) u₁ u₂ (wx p) = -(y p) :=
    Classical.choose_spec ((hranges p.val).1 (-(y p)))
  let x : actualFullPeriodTwoSourceBlockDomain :=
    ⟨WithLp.toLp 2 (fun p : Fin 2 => wx p), fun p => (wx p).property⟩
  refine ⟨x, ?_⟩
  apply PiLp.ext
  intro p
  have hcomponent :
      actualFullPeriodTwoSourceBlockComponentLocal x p = wx p := by
    apply Subtype.ext
    rfl
  change actualSourcePerturbedDiracPMapAfterAE (p.val : ℤ) u₁ u₂
      (actualFullPeriodTwoSourceBlockComponentLocal x p) -
      (Complex.I * (η : ℂ)) • (x.1 p) = y p
  rw [hcomponent]
  calc
    actualSourcePerturbedDiracPMapAfterAE (p.val : ℤ) u₁ u₂ (wx p) -
        (Complex.I * (η : ℂ)) • (wx p : SourcePairL2) =
      -(actualSourcePerturbedShiftedDiracAfterAE (p.val : ℤ)
        (Complex.I * (η : ℂ)) u₁ u₂ (wx p)) := by
          rw [actualSourcePerturbedShiftedDirac_eq_smul_sub_sourcePMap]
          abel
    _ = y p := by rw [hwx p]; simp

private theorem actualFullPeriodTwoSourceBlockPMap_plus_i_range
    (u₁ u₂ : PhysicalL2) (η : ℝ)
    (hranges : ∀ n : ℤ,
      Function.Surjective
        (actualSourcePerturbedShiftedDiracAfterAE n (Complex.I * (η : ℂ)) u₁ u₂) ∧
      Function.Surjective
        (actualSourcePerturbedShiftedDiracAfterAE n (-Complex.I * (η : ℂ)) u₁ u₂))
    (y : ActualFullPeriodTwoSourcePair) :
    ∃ x : actualFullPeriodTwoSourceBlockDomain,
      actualFullPeriodTwoSourceBlockPMap u₁ u₂ x +
        (Complex.I * (η : ℂ)) • (x : ActualFullPeriodTwoSourcePair) = y := by
  let wx : ∀ p : Fin 2, recoveredActualSourceFreeWeightedDomain (p.val : ℤ) :=
    fun p => Classical.choose ((hranges p.val).2 (-(y p)))
  have hwx (p : Fin 2) :
      actualSourcePerturbedShiftedDiracAfterAE (p.val : ℤ)
        (-Complex.I * (η : ℂ)) u₁ u₂ (wx p) = -(y p) :=
    Classical.choose_spec ((hranges p.val).2 (-(y p)))
  let x : actualFullPeriodTwoSourceBlockDomain :=
    ⟨WithLp.toLp 2 (fun p : Fin 2 => wx p), fun p => (wx p).property⟩
  refine ⟨x, ?_⟩
  apply PiLp.ext
  intro p
  have hcomponent :
      actualFullPeriodTwoSourceBlockComponentLocal x p = wx p := by
    apply Subtype.ext
    rfl
  change actualSourcePerturbedDiracPMapAfterAE (p.val : ℤ) u₁ u₂
      (actualFullPeriodTwoSourceBlockComponentLocal x p) +
      (Complex.I * (η : ℂ)) • (x.1 p) = y p
  rw [hcomponent]
  calc
    actualSourcePerturbedDiracPMapAfterAE (p.val : ℤ) u₁ u₂ (wx p) +
        (Complex.I * (η : ℂ)) • (wx p : SourcePairL2) =
      -(actualSourcePerturbedShiftedDiracAfterAE (p.val : ℤ)
        (-Complex.I * (η : ℂ)) u₁ u₂ (wx p)) := by
          rw [actualSourcePerturbedShiftedDirac_eq_smul_sub_sourcePMap]
          rw [neg_mul, neg_smul]
          abel
    _ = y p := by rw [hwx p]; simp

private theorem actualFullPeriodTwoDoubledCirclePMap_minus_i_range
    (u₁ u₂ : PhysicalL2) (η : ℝ)
    (hranges : ∀ n : ℤ,
      Function.Surjective
        (actualSourcePerturbedShiftedDiracAfterAE n (Complex.I * (η : ℂ)) u₁ u₂) ∧
      Function.Surjective
        (actualSourcePerturbedShiftedDiracAfterAE n (-Complex.I * (η : ℂ)) u₁ u₂))
    (y : ActualTwoChannelSpectralL2) :
    ∃ x : (actualFullPeriodTwoDoubledCirclePerturbedDiracPMap u₁ u₂).domain,
      actualFullPeriodTwoDoubledCirclePerturbedDiracPMap u₁ u₂ x -
        (Complex.I * (η : ℂ)) • (x : ActualTwoChannelSpectralL2) = y := by
  let target := actualFullPeriodTwoSourceIntervalAssembly y
  obtain ⟨w, hw⟩ := actualFullPeriodTwoSourceBlockPMap_minus_i_range u₁ u₂ η hranges target
  let xd : actualFullPeriodTwoSourceDoubledCircleDomain :=
    ⟨actualFullPeriodTwoSourceIntervalAssembly.symm (w : ActualFullPeriodTwoSourcePair), by
      change actualFullPeriodTwoSourceIntervalAssembly
          (actualFullPeriodTwoSourceIntervalAssembly.symm
            (w : ActualFullPeriodTwoSourcePair)) ∈ actualFullPeriodTwoSourceBlockDomain
      rw [actualFullPeriodTwoSourceIntervalAssembly.apply_symm_apply]
      exact w.property⟩
  let x : (actualFullPeriodTwoDoubledCirclePerturbedDiracPMap u₁ u₂).domain :=
    ⟨xd.1, xd.2⟩
  refine ⟨x, ?_⟩
  apply actualFullPeriodTwoSourceIntervalAssembly.injective
  simp only [map_sub, map_smul]
  change actualFullPeriodTwoSourceIntervalAssembly
      (actualFullPeriodTwoDoubledCirclePerturbedDiracAction u₁ u₂
        (⟨x.1, x.2⟩ : actualFullPeriodTwoSourceDoubledCircleDomain)) -
      (Complex.I * (η : ℂ)) •
        actualFullPeriodTwoSourceIntervalAssembly x.1 = _
  rw [actualFullPeriodTwoAction_repr_local]
  have htransport :
      actualFullPeriodTwoSourceDomainTransportLocal
        (⟨x.1, x.2⟩ : actualFullPeriodTwoSourceDoubledCircleDomain) = w := by
    apply Subtype.ext
    dsimp only [actualFullPeriodTwoSourceDomainTransportLocal, x, xd]
    exact actualFullPeriodTwoSourceIntervalAssembly.apply_symm_apply _
  rw [htransport]
  have hsource :
      actualFullPeriodTwoSourceIntervalAssembly
        (x : ActualTwoChannelSpectralL2) = (w : ActualFullPeriodTwoSourcePair) := by
    dsimp only [x, xd]
    exact actualFullPeriodTwoSourceIntervalAssembly.apply_symm_apply _
  rw [hsource]
  exact hw

private theorem actualFullPeriodTwoDoubledCirclePMap_plus_i_range
    (u₁ u₂ : PhysicalL2) (η : ℝ)
    (hranges : ∀ n : ℤ,
      Function.Surjective
        (actualSourcePerturbedShiftedDiracAfterAE n (Complex.I * (η : ℂ)) u₁ u₂) ∧
      Function.Surjective
        (actualSourcePerturbedShiftedDiracAfterAE n (-Complex.I * (η : ℂ)) u₁ u₂))
    (y : ActualTwoChannelSpectralL2) :
    ∃ x : (actualFullPeriodTwoDoubledCirclePerturbedDiracPMap u₁ u₂).domain,
      actualFullPeriodTwoDoubledCirclePerturbedDiracPMap u₁ u₂ x +
        (Complex.I * (η : ℂ)) • (x : ActualTwoChannelSpectralL2) = y := by
  let target := actualFullPeriodTwoSourceIntervalAssembly y
  obtain ⟨w, hw⟩ := actualFullPeriodTwoSourceBlockPMap_plus_i_range u₁ u₂ η hranges target
  let xd : actualFullPeriodTwoSourceDoubledCircleDomain :=
    ⟨actualFullPeriodTwoSourceIntervalAssembly.symm (w : ActualFullPeriodTwoSourcePair), by
      change actualFullPeriodTwoSourceIntervalAssembly
          (actualFullPeriodTwoSourceIntervalAssembly.symm
            (w : ActualFullPeriodTwoSourcePair)) ∈ actualFullPeriodTwoSourceBlockDomain
      rw [actualFullPeriodTwoSourceIntervalAssembly.apply_symm_apply]
      exact w.property⟩
  let x : (actualFullPeriodTwoDoubledCirclePerturbedDiracPMap u₁ u₂).domain :=
    ⟨xd.1, xd.2⟩
  refine ⟨x, ?_⟩
  apply actualFullPeriodTwoSourceIntervalAssembly.injective
  simp only [map_add, map_smul]
  change actualFullPeriodTwoSourceIntervalAssembly
      (actualFullPeriodTwoDoubledCirclePerturbedDiracAction u₁ u₂
        (⟨x.1, x.2⟩ : actualFullPeriodTwoSourceDoubledCircleDomain)) +
      (Complex.I * (η : ℂ)) •
        actualFullPeriodTwoSourceIntervalAssembly x.1 = _
  rw [actualFullPeriodTwoAction_repr_local]
  have htransport :
      actualFullPeriodTwoSourceDomainTransportLocal
        (⟨x.1, x.2⟩ : actualFullPeriodTwoSourceDoubledCircleDomain) = w := by
    apply Subtype.ext
    dsimp only [actualFullPeriodTwoSourceDomainTransportLocal, x, xd]
    exact actualFullPeriodTwoSourceIntervalAssembly.apply_symm_apply _
  rw [htransport]
  have hsource :
      actualFullPeriodTwoSourceIntervalAssembly
        (x : ActualTwoChannelSpectralL2) = (w : ActualFullPeriodTwoSourcePair) := by
    dsimp only [x, xd]
    exact actualFullPeriodTwoSourceIntervalAssembly.apply_symm_apply _
  rw [hsource]
  exact hw

/-- The actual assembled period-two carrier operator is self-adjoint on the
pullback of both actual parity source graph domains for every physical
potential pair. This uses the existing uniform two-imaginary-range theorem
and the existing LinearPMap criterion; it does not identify eigenvectors or
spectra across the reflection convention. -/
theorem actualFullPeriodTwoDoubledCirclePerturbedDiracPMap_selfAdjoint_of_physical_slice
    (u₁ u₂ : PhysicalL2) (hphysical : u₂ = star u₁) :
    IsSelfAdjoint (actualFullPeriodTwoDoubledCirclePerturbedDiracPMap u₁ u₂) := by
  obtain ⟨η, hη, hranges⟩ := actualSourcePerturbedImaginaryShifts_surjective_uniform_y u₁ u₂
  apply NlsGge.Spectral.partialMap_selfAdjoint_of_two_imaginary_ranges
    (actualFullPeriodTwoDoubledCirclePerturbedDiracPMap u₁ u₂) η
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hη)
    (actualFullPeriodTwoSourceDoubledCircleDomain_dense)
    (actualFullPeriodTwoDoubledCirclePerturbedDiracPMap_formalSelfAdjoint_of_physical_slice
      u₁ u₂ hphysical)
  · intro y
    exact actualFullPeriodTwoDoubledCirclePMap_minus_i_range u₁ u₂ η hranges y
  · intro y
    exact actualFullPeriodTwoDoubledCirclePMap_plus_i_range u₁ u₂ η hranges y

end NlsGge.Schur

end
