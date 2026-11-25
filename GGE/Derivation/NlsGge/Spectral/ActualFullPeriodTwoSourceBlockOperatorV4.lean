import NlsGge.Schur.ActualFullPeriodTwoSourceIntervalParityAssemblyV3
import NlsGge.Definitions.PilotInterfaces
import NlsGge.Spectral.ActualSourceWeightedDomainTransportBridgeV4
import NlsGge.Spectral.ActualSourcePerturbedDiracFormalSymmetryPhysicalSliceV6
import Mathlib.Analysis.InnerProductSpace.LinearPMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace NlsGge.Schur
open NlsGge.Pilot
open TransportBridgeV4

/-- The direct-sum graph domain of the two actual period-two source blocks.
Membership means that the periodic and antiperiodic source pairs lie in their
respective recovered weighted free domains. -/
def actualFullPeriodTwoSourceBlockDomain :
    Submodule ℂ ActualFullPeriodTwoSourcePair where
  carrier := {x | ∀ p : Fin 2,
    x p ∈ recoveredActualSourceFreeWeightedDomain (p.val : ℤ)}
  zero_mem' := by
    intro p
    exact (recoveredActualSourceFreeWeightedDomain (p.val : ℤ)).zero_mem
  add_mem' := by
    intro x y hx hy p
    exact (recoveredActualSourceFreeWeightedDomain (p.val : ℤ)).add_mem
      (hx p) (hy p)
  smul_mem' := by
    intro c x hx p
    exact (recoveredActualSourceFreeWeightedDomain (p.val : ℤ)).smul_mem c
      (hx p)

private def actualFullPeriodTwoSourceBlockDomainComponent
    (x : actualFullPeriodTwoSourceBlockDomain) (p : Fin 2) :
      recoveredActualSourceFreeWeightedDomain (p.val : ℤ) :=
  ⟨x.1 p, x.2 p⟩

/-- The direct sum of the existing actual `D+V` source actions, one in each
periodic/antiperiodic block. This is a linear map on the direct-sum graph
domain, assembled from the actual block partial maps. -/
def actualFullPeriodTwoSourceBlockAction
    (u₁ u₂ : PhysicalL2) :
    actualFullPeriodTwoSourceBlockDomain →ₗ[ℂ]
      ActualFullPeriodTwoSourcePair where
  toFun x := WithLp.toLp 2 (fun p : Fin 2 =>
    actualSourcePerturbedDiracPMapAfterAE (p.val : ℤ) u₁ u₂
      (actualFullPeriodTwoSourceBlockDomainComponent x p))
  map_add' x y := by
    apply PiLp.ext
    intro p
    have hcomponent :
        actualFullPeriodTwoSourceBlockDomainComponent (x + y) p =
          actualFullPeriodTwoSourceBlockDomainComponent x p +
            actualFullPeriodTwoSourceBlockDomainComponent y p := by
      apply Subtype.ext
      rfl
    change actualSourcePerturbedDiracPMapAfterAE (p.val : ℤ) u₁ u₂
        (actualFullPeriodTwoSourceBlockDomainComponent (x + y) p) =
      actualSourcePerturbedDiracPMapAfterAE (p.val : ℤ) u₁ u₂
          (actualFullPeriodTwoSourceBlockDomainComponent x p) +
        actualSourcePerturbedDiracPMapAfterAE (p.val : ℤ) u₁ u₂
          (actualFullPeriodTwoSourceBlockDomainComponent y p)
    rw [hcomponent]
    exact LinearPMap.map_add
      (actualSourcePerturbedDiracPMapAfterAE (p.val : ℤ) u₁ u₂) _ _
  map_smul' c x := by
    apply PiLp.ext
    intro p
    have hcomponent :
        actualFullPeriodTwoSourceBlockDomainComponent (c • x) p =
          c • actualFullPeriodTwoSourceBlockDomainComponent x p := by
      apply Subtype.ext
      rfl
    change actualSourcePerturbedDiracPMapAfterAE (p.val : ℤ) u₁ u₂
        (actualFullPeriodTwoSourceBlockDomainComponent (c • x) p) =
      c • actualSourcePerturbedDiracPMapAfterAE (p.val : ℤ) u₁ u₂
        (actualFullPeriodTwoSourceBlockDomainComponent x p)
    rw [hcomponent]
    exact LinearPMap.map_smul
      (actualSourcePerturbedDiracPMapAfterAE (p.val : ℤ) u₁ u₂) c _

/-- Actual finite direct sum of the two recovered source-domain operators. -/
def actualFullPeriodTwoSourceBlockPMap (u₁ u₂ : PhysicalL2) :
    ActualFullPeriodTwoSourcePair →ₗ.[ℂ] ActualFullPeriodTwoSourcePair :=
  ⟨actualFullPeriodTwoSourceBlockDomain,
    actualFullPeriodTwoSourceBlockAction u₁ u₂⟩

/-- Pull the two-block graph domain back to the actual full doubled-circle
two-channel carrier by the proved period-two source-interval isometry. -/
def actualFullPeriodTwoSourceDoubledCircleDomain :
    Submodule ℂ ActualTwoChannelSpectralL2 where
  carrier := {x | actualFullPeriodTwoSourceIntervalAssembly x ∈
    actualFullPeriodTwoSourceBlockDomain}
  zero_mem' := by
    change actualFullPeriodTwoSourceIntervalAssembly 0 ∈
      actualFullPeriodTwoSourceBlockDomain
    simp
  add_mem' := by
    intro x y hx hy
    change actualFullPeriodTwoSourceIntervalAssembly (x + y) ∈
      actualFullPeriodTwoSourceBlockDomain
    rw [map_add]
    exact actualFullPeriodTwoSourceBlockDomain.add_mem hx hy
  smul_mem' := by
    intro c x hx
    change actualFullPeriodTwoSourceIntervalAssembly (c • x) ∈
      actualFullPeriodTwoSourceBlockDomain
    rw [map_smul]
    exact actualFullPeriodTwoSourceBlockDomain.smul_mem c hx

private def actualFullPeriodTwoSourceDomainTransportElement
    (x : actualFullPeriodTwoSourceDoubledCircleDomain) :
      actualFullPeriodTwoSourceBlockDomain :=
  ⟨actualFullPeriodTwoSourceIntervalAssembly x.1, x.2⟩

private theorem actualFullPeriodTwoSourceDomainTransportElement_add
    (x y : actualFullPeriodTwoSourceDoubledCircleDomain) :
    actualFullPeriodTwoSourceDomainTransportElement (x + y) =
      actualFullPeriodTwoSourceDomainTransportElement x +
        actualFullPeriodTwoSourceDomainTransportElement y := by
  apply Subtype.ext
  exact map_add actualFullPeriodTwoSourceIntervalAssembly x.1 y.1

private theorem actualFullPeriodTwoSourceDomainTransportElement_smul
    (c : ℂ) (x : actualFullPeriodTwoSourceDoubledCircleDomain) :
    actualFullPeriodTwoSourceDomainTransportElement (c • x) =
      c • actualFullPeriodTwoSourceDomainTransportElement x := by
  apply Subtype.ext
  exact map_smul actualFullPeriodTwoSourceIntervalAssembly c x.1

/-- The blockwise `D+V` action transported back to actual two-channel L² on
the doubled circle. Its graph domain is exactly the pullback of the two
checked actual source graph domains. -/
def actualFullPeriodTwoDoubledCirclePerturbedDiracAction
    (u₁ u₂ : PhysicalL2) :
    actualFullPeriodTwoSourceDoubledCircleDomain →ₗ[ℂ]
      ActualTwoChannelSpectralL2 where
  toFun x := actualFullPeriodTwoSourceIntervalAssembly.symm
    (actualFullPeriodTwoSourceBlockPMap u₁ u₂
      (actualFullPeriodTwoSourceDomainTransportElement x))
  map_add' x y := by
    apply actualFullPeriodTwoSourceIntervalAssembly.injective
    rw [actualFullPeriodTwoSourceIntervalAssembly.map_add]
    change actualFullPeriodTwoSourceIntervalAssembly
        (actualFullPeriodTwoSourceIntervalAssembly.symm
          (actualFullPeriodTwoSourceBlockPMap u₁ u₂
            (actualFullPeriodTwoSourceDomainTransportElement (x + y)))) =
      actualFullPeriodTwoSourceIntervalAssembly
          (actualFullPeriodTwoSourceIntervalAssembly.symm
            (actualFullPeriodTwoSourceBlockPMap u₁ u₂
              (actualFullPeriodTwoSourceDomainTransportElement x))) +
        actualFullPeriodTwoSourceIntervalAssembly
          (actualFullPeriodTwoSourceIntervalAssembly.symm
            (actualFullPeriodTwoSourceBlockPMap u₁ u₂
              (actualFullPeriodTwoSourceDomainTransportElement y)))
    simp only [LinearIsometryEquiv.apply_symm_apply]
    rw [actualFullPeriodTwoSourceDomainTransportElement_add]
    exact LinearPMap.map_add
      (actualFullPeriodTwoSourceBlockPMap u₁ u₂) _ _
  map_smul' c x := by
    apply actualFullPeriodTwoSourceIntervalAssembly.injective
    rw [actualFullPeriodTwoSourceIntervalAssembly.map_smul]
    change actualFullPeriodTwoSourceIntervalAssembly
        (actualFullPeriodTwoSourceIntervalAssembly.symm
          (actualFullPeriodTwoSourceBlockPMap u₁ u₂
            (actualFullPeriodTwoSourceDomainTransportElement (c • x)))) =
      (RingHom.id ℂ) c • actualFullPeriodTwoSourceIntervalAssembly
          (actualFullPeriodTwoSourceIntervalAssembly.symm
            (actualFullPeriodTwoSourceBlockPMap u₁ u₂
              (actualFullPeriodTwoSourceDomainTransportElement x)))
    simp only [LinearIsometryEquiv.apply_symm_apply]
    rw [actualFullPeriodTwoSourceDomainTransportElement_smul]
    exact LinearPMap.map_smul
      (actualFullPeriodTwoSourceBlockPMap u₁ u₂) c _

/-- The full-carrier action is transported exactly to the actual direct sum
of the periodic and antiperiodic source block actions. This is a domain and
action assembly statement; it does not identify the source blocks with the
original-sign Zakharov--Shabat column before the reflected-convention bridge. -/
theorem actualFullPeriodTwoDoubledCirclePerturbedDiracAction_repr
    (u₁ u₂ : PhysicalL2)
    (x : actualFullPeriodTwoSourceDoubledCircleDomain) :
    actualFullPeriodTwoSourceIntervalAssembly
        (actualFullPeriodTwoDoubledCirclePerturbedDiracAction u₁ u₂ x) =
      actualFullPeriodTwoSourceBlockPMap u₁ u₂
        (actualFullPeriodTwoSourceDomainTransportElement x) := by
  change actualFullPeriodTwoSourceIntervalAssembly
      (actualFullPeriodTwoSourceIntervalAssembly.symm
        (actualFullPeriodTwoSourceBlockPMap u₁ u₂
          (actualFullPeriodTwoSourceDomainTransportElement x))) = _
  exact actualFullPeriodTwoSourceIntervalAssembly.apply_symm_apply _

end NlsGge.Schur

end
