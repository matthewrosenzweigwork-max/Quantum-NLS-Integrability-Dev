import NlsGge.Spectral.ActualSourcePerturbedDiracFormalSymmetryPhysicalSliceV6
import NlsGge.Spectral.ActualSourceWeightedDomainLInfRepresentativeMatchesSourceV5

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory

namespace NlsGge.Schur
open NlsGge.Pilot
open TransportBridgeV4

/-- The signed extension of an interval class depends on `n` only through its parity sign. -/
theorem scalarParityExtendValue_congr_parity (n n' : ℤ) (h : n % 2 = n' % 2)
    (u : SourceIntervalL2) :
    scalarParityExtendValue n u = scalarParityExtendValue n' u := by
  have hs : spectralSign n = spectralSign n' := spectralSign_eq_of_parity n n' h
  have hh : sourceSignedHalfValue n u = sourceSignedHalfValue n' u := by
    funext x
    simp only [sourceSignedHalfValue, hs]
  have hf : sourceSignedCircleValue n u = sourceSignedCircleValue n' u := by
    simp only [sourceSignedCircleValue, hh]
  apply Lp.ext
  filter_upwards [scalarParityExtendValue_ae n u, scalarParityExtendValue_ae n' u]
    with x h1 h2
  rw [h1, h2, hf]

theorem scalarParityIntervalEquiv_symm_val (n : ℤ) (u : SourceIntervalL2) :
    ((scalarParityIntervalEquiv n).symm u).val = scalarParityExtendValue n u := by
  have h : (scalarParityIntervalEquiv n) (scalarParityExtend n u) = u :=
    scalarParityRestrict_extend n u
  have h2 : (scalarParityIntervalEquiv n).symm u = scalarParityExtend n u :=
    ((scalarParityIntervalEquiv n).symm_apply_eq).mpr h.symm
  rw [h2]
  rfl

theorem sourcePairRepr_apply_eq (n : ℤ) (x : SourcePairL2) (i : Bool × Sector n) :
    sourcePairRepr n x i =
      (fourierBasis (T := (2 : ℝ))).repr (scalarParityExtendValue n (x i.1))
        (mixedIndex n i).val := by
  change parityPairRepr n ((parityPairIntervalEquiv n).symm x) i = _
  rw [parityPairRepr_apply, scalarParityRepr_apply]
  have h1 : ((parityPairIntervalEquiv n).symm x i.1).val = scalarParityExtendValue n (x i.1) :=
    scalarParityIntervalEquiv_symm_val n (x i.1)
  rw [h1]

/-- Identity-on-values reindexing of two signed parity sectors of equal parity. -/
def sectorReindex (n n' : ℤ) (h : n % 2 = n' % 2) : Sector n ≃ Sector n' :=
  Equiv.subtypeEquivRight (fun m => by rw [h])

@[simp] theorem sectorReindex_val (n n' : ℤ) (h : n % 2 = n' % 2) (m : Sector n) :
    (sectorReindex n n' h m).val = m.val := rfl

/-- Reindexing on pair labels. -/
def pairReindex (n n' : ℤ) (h : n % 2 = n' % 2) :
    Bool × Sector n ≃ Bool × Sector n' :=
  Equiv.prodCongr (Equiv.refl Bool) (sectorReindex n n' h)

theorem mixedIndex_val_reindex (n n' : ℤ) (h : n % 2 = n' % 2) (i : Bool × Sector n) :
    (mixedIndex n' (pairReindex n n' h i)).val = (mixedIndex n i).val := by
  rcases i with ⟨b, m⟩
  cases b <;> simp [pairReindex, mixedIndex, negateIndex, sectorReindex]

theorem sourcePairRepr_reindex (n n' : ℤ) (h : n % 2 = n' % 2) (x : SourcePairL2)
    (i : Bool × Sector n) :
    sourcePairRepr n' x (pairReindex n n' h i) = sourcePairRepr n x i := by
  rw [sourcePairRepr_apply_eq, sourcePairRepr_apply_eq,
    scalarParityExtendValue_congr_parity n' n h.symm, mixedIndex_val_reindex n n' h]
  rfl

theorem mem_recoveredActualSourceFreeWeightedDomain_iff (n : ℤ) (x : SourcePairL2) :
    x ∈ recoveredActualSourceFreeWeightedDomain n ↔
      Memℓp (fun i : Bool × Sector n => spectralCenter i.2.val * sourcePairRepr n x i) 2 :=
  Iff.rfl

theorem recoveredActualSourceFreeWeightedDomain_mem_congr (n n' : ℤ) (h : n % 2 = n' % 2)
    (x : SourcePairL2) :
    x ∈ recoveredActualSourceFreeWeightedDomain n →
      x ∈ recoveredActualSourceFreeWeightedDomain n' := by
  rw [mem_recoveredActualSourceFreeWeightedDomain_iff,
    mem_recoveredActualSourceFreeWeightedDomain_iff]
  intro hx
  rw [memℓp_gen_iff (by norm_num)] at hx ⊢
  refine (Equiv.summable_iff (pairReindex n n' h)).mp ?_
  convert hx using 2 with i
  simp only [Function.comp_apply, pairReindex, Equiv.prodCongr_apply, Prod.map_snd,
    sectorReindex_val]
  rw [← sourcePairRepr_reindex n n' h x i]
  rfl

theorem recoveredActualSourceFreeWeightedDomain_eq_of_parity (n n' : ℤ)
    (h : n % 2 = n' % 2) :
    recoveredActualSourceFreeWeightedDomain n = recoveredActualSourceFreeWeightedDomain n' := by
  apply Submodule.ext
  intro x
  exact ⟨recoveredActualSourceFreeWeightedDomain_mem_congr n n' h x,
    recoveredActualSourceFreeWeightedDomain_mem_congr n' n h.symm x⟩

theorem actualSourceFreeDiracMapAfterAE_parity (n n' : ℤ) (h : n % 2 = n' % 2)
    (x : recoveredActualSourceFreeWeightedDomain n)
    (x' : recoveredActualSourceFreeWeightedDomain n') (hx : x.val = x'.val) :
    actualSourceFreeDiracMapAfterAE n' x' = actualSourceFreeDiracMapAfterAE n x := by
  apply (sourcePairRepr n').injective
  rw [actualSourceFreeDiracMapAfterAE_repr_apply]
  apply lp.ext
  funext j
  obtain ⟨i, rfl⟩ := (pairReindex n n' h).surjective j
  have hl : freeCoordinateDirac n' (recoveredActualSourceWeightedDomainSequenceMapAfterAE n' x')
      (pairReindex n n' h i) =
      spectralCenter i.2.val * sourcePairRepr n x i := by
    rw [freeCoordinateDirac_apply]
    change spectralCenter (pairReindex n n' h i).2.val *
        sourcePairRepr n' x'.val (pairReindex n n' h i) = _
    rw [← hx, sourcePairRepr_reindex n n' h x.val i]
    rfl
  have hr : sourcePairRepr n' (actualSourceFreeDiracMapAfterAE n x) (pairReindex n n' h i) =
      spectralCenter i.2.val * sourcePairRepr n x i := by
    rw [sourcePairRepr_reindex n n' h, actualSourceFreeDiracMapAfterAE_repr_apply,
      freeCoordinateDirac_apply]
    rfl
  exact hl.trans hr.symm

theorem actualSourceWeightedDomainLInfRepresentativeMap_parity (n n' : ℤ)
    (x : recoveredActualSourceFreeWeightedDomain n)
    (x' : recoveredActualSourceFreeWeightedDomain n') (hx : x.val = x'.val) :
    actualSourceWeightedDomainLInfRepresentativeMap n'
        (recoveredActualSourceWeightedDomainSequenceMapAfterAE n' x') =
      actualSourceWeightedDomainLInfRepresentativeMap n
        (recoveredActualSourceWeightedDomainSequenceMapAfterAE n x) := by
  apply PiLp.ext
  intro b
  apply Lp.ext
  have h1 := actualSourceWeightedDomainLInfRepresentativeMap_matches_source_ae n' x' b
  have h2 := actualSourceWeightedDomainLInfRepresentativeMap_matches_source_ae n x b
  have h3 : (x'.val b : ℝ → ℂ) = (x.val b : ℝ → ℂ) :=
    congrArg (fun v : SourcePairL2 => (v b : ℝ → ℂ)) hx.symm
  exact h1.trans ((Filter.EventuallyEq.of_eq h3).trans h2.symm)

theorem actualSourcePotentialOnRecoveredWeightedDomainAfterAE_parity (n n' : ℤ)
    (u₁ u₂ : PhysicalL2)
    (x : recoveredActualSourceFreeWeightedDomain n)
    (x' : recoveredActualSourceFreeWeightedDomain n') (hx : x.val = x'.val) :
    actualSourcePotentialOnRecoveredWeightedDomainAfterAE n' u₁ u₂ x' =
      actualSourcePotentialOnRecoveredWeightedDomainAfterAE n u₁ u₂ x := by
  change (actualL2PotentialParityPairSourceOperator u₁ u₂).toLinearMap
      (actualSourceWeightedDomainLInfRepresentativeMap n'
        (recoveredActualSourceWeightedDomainSequenceMapAfterAE n' x')) =
    (actualL2PotentialParityPairSourceOperator u₁ u₂).toLinearMap
      (actualSourceWeightedDomainLInfRepresentativeMap n
        (recoveredActualSourceWeightedDomainSequenceMapAfterAE n x))
  rw [actualSourceWeightedDomainLInfRepresentativeMap_parity n n' x x' hx]

/-- The source perturbed Dirac operator depends on `n` only through `n % 2`. -/
theorem actualSourcePerturbedDiracPMapAfterAE_eq_of_parity (n n' : ℤ) (h : n % 2 = n' % 2)
    (u₁ u₂ : PhysicalL2) :
    actualSourcePerturbedDiracPMapAfterAE n u₁ u₂ =
      actualSourcePerturbedDiracPMapAfterAE n' u₁ u₂ := by
  apply LinearPMap.dExt
  · exact recoveredActualSourceFreeWeightedDomain_eq_of_parity n n' h
  · intro x x' hx
    change actualSourceFreeDiracMapAfterAE n x +
        actualSourcePotentialOnRecoveredWeightedDomainAfterAE n u₁ u₂ x =
      actualSourceFreeDiracMapAfterAE n' x' +
        actualSourcePotentialOnRecoveredWeightedDomainAfterAE n' u₁ u₂ x'
    rw [actualSourceFreeDiracMapAfterAE_parity n n' h x x' hx,
      actualSourcePotentialOnRecoveredWeightedDomainAfterAE_parity n n' u₁ u₂ x x' hx]

theorem actualSourcePerturbedDirac_eigen_iff_of_parity (n n' : ℤ) (h : n % 2 = n' % 2)
    (u₁ u₂ : PhysicalL2) (z : ℂ) :
    (∃ Y : recoveredActualSourceFreeWeightedDomain n, Y.val ≠ 0 ∧
        actualSourcePerturbedDiracPMapAfterAE n u₁ u₂ Y = z • Y.val) ↔
      (∃ Y : recoveredActualSourceFreeWeightedDomain n', Y.val ≠ 0 ∧
        actualSourcePerturbedDiracPMapAfterAE n' u₁ u₂ Y = z • Y.val) := by
  have hP := actualSourcePerturbedDiracPMapAfterAE_eq_of_parity n n' h u₁ u₂
  have hD := recoveredActualSourceFreeWeightedDomain_eq_of_parity n n' h
  have key : ∀ (m m' : ℤ) (hm : m % 2 = m' % 2)
      (Y : recoveredActualSourceFreeWeightedDomain m), Y.val ≠ 0 →
      actualSourcePerturbedDiracPMapAfterAE m u₁ u₂ Y = z • Y.val →
      ∃ Y' : recoveredActualSourceFreeWeightedDomain m', Y'.val ≠ 0 ∧
        actualSourcePerturbedDiracPMapAfterAE m' u₁ u₂ Y' = z • Y'.val := by
    intro m m' hm Y hY0 hY
    have hmem : Y.val ∈ recoveredActualSourceFreeWeightedDomain m' := by
      rw [← recoveredActualSourceFreeWeightedDomain_eq_of_parity m m' hm]
      exact Y.property
    refine ⟨⟨Y.val, hmem⟩, hY0, ?_⟩
    have hq := (LinearPMap.ext_iff.mp
      (actualSourcePerturbedDiracPMapAfterAE_eq_of_parity m m' hm u₁ u₂)).2
      (x := Y.val) (hf := Y.property) (hg := hmem)
    exact hq.symm.trans hY
  exact ⟨fun ⟨Y, h0, hY⟩ => key n n' h Y h0 hY,
    fun ⟨Y, h0, hY⟩ => key n' n h.symm Y h0 hY⟩

end NlsGge.Schur
