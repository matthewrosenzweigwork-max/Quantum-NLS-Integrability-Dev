import QuantumNLS.Ext006SourceWeylR44a

/-! PROP-022 takeover, stage O1. Field covariance on the common smooth domain
implies covariance of the source Weyl operators. The proof shows that the
conjugated Weyl group is a Stone family for the original smearing, and then
uses the proved uniqueness of such families. No covariance, generator domain
or implementer property is assumed beyond field covariance on smooth vectors
and two-sided preservation of the smooth domain. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace
namespace QuantumNLS.Prop022OWeylField
open Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006SmoothOperatorsR34a
open Ext006StrongFieldR41a Ext006FieldClosureR42a Ext006SelfAdjointR44a
open Ext006StoneGeneratorR44a Ext006SourceStoneR44a Ext006BoundedExponentialR43a
open Ext006ModeDomainR33a Ext006SeriesIdentificationR43a Ext006ExponentialContinuityR43a

/-- Field covariance of a unitary on the common smooth domain, in occupation
coordinates. Smoothness is preserved in both directions. -/
def FieldCovariant (W : Fock ≃ₗᵢ[ℂ] Fock) (T : H → H) : Prop :=
  (∀ x : Fock, Smooth x ↔ Smooth (W x)) ∧
    ∀ (h : H) (v w : D), w.1 = W v.1 → W (field h v).1 = (field (T h) w).1

/-- The literal smooth graph of the field. -/
def smoothGraph (h : H) : Set (Fock × Fock) := {z | ∃ v : D, z = (v.1,(field h v).1)}

lemma closedFieldGraph_eq (h : H) : closedFieldGraph h = closure (smoothGraph h) := rfl

/-- The product homeomorphism induced by W. -/
def pairMap (W : Fock ≃ₗᵢ[ℂ] Fock) : (Fock × Fock) ≃ₜ (Fock × Fock) :=
  W.toHomeomorph.prodCongr W.toHomeomorph

lemma pairMap_apply (W : Fock ≃ₗᵢ[ℂ] Fock) (p : Fock × Fock) :
    pairMap W p = (W p.1,W p.2) := rfl

lemma image_smoothGraph (W : Fock ≃ₗᵢ[ℂ] Fock) (T : H → H) (hW : FieldCovariant W T)
    (h : H) : pairMap W '' smoothGraph h = smoothGraph (T h) := by
  ext z
  constructor
  · rintro ⟨p,⟨v,rfl⟩,rfl⟩
    let w : D := ⟨W v.1,(hW.1 v.1).mp v.2⟩
    refine ⟨w,?_⟩
    rw [pairMap_apply]
    exact Prod.ext rfl (hW.2 h v w rfl)
  · rintro ⟨w,rfl⟩
    have hs : Smooth (W (W.symm w.1)) := by
      rw [LinearIsometryEquiv.apply_symm_apply]
      exact w.2
    let v : D := ⟨W.symm w.1,(hW.1 _).mpr hs⟩
    refine ⟨(v.1,(field h v).1),⟨v,rfl⟩,?_⟩
    rw [pairMap_apply]
    have hv : w.1 = W v.1 := by
      change w.1 = W (W.symm w.1)
      rw [LinearIsometryEquiv.apply_symm_apply]
    exact Prod.ext (hv.symm) (hW.2 h v w hv)

lemma closed_graph_iff (W : Fock ≃ₗᵢ[ℂ] Fock) (T : H → H) (hW : FieldCovariant W T)
    (h : H) (x y : Fock) :
    (x,y) ∈ closedFieldGraph h ↔ (W x,W y) ∈ closedFieldGraph (T h) := by
  rw [closedFieldGraph_eq,closedFieldGraph_eq,← image_smoothGraph W T hW h,
    ← (pairMap W).image_closure]
  constructor
  · intro hp
    exact ⟨(x,y),hp,rfl⟩
  · rintro ⟨p,hp,he⟩
    have hp' : p = (x,y) := by
      apply (pairMap W).injective
      exact he
    rwa [← hp']

/-- Real-linear continuous version of a unitary. -/
def realMap (W : Fock ≃ₗᵢ[ℂ] Fock) : Fock →L[ℝ] Fock :=
  W.toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ

lemma realMap_apply (W : Fock ≃ₗᵢ[ℂ] Fock) (x : Fock) : realMap W x = W x := rfl

lemma hasDerivAt_map (W : Fock ≃ₗᵢ[ℂ] Fock) {f : ℝ → Fock} {y : Fock} {t : ℝ}
    (hf : HasDerivAt f y t) : HasDerivAt (fun s => W (f s)) (W y) t :=
  (realMap W).hasFDerivAt.comp_hasDerivAt t hf

/-- The conjugated Weyl group is a Stone family for the original smearing. -/
def conjugatedFamily (W : Fock ≃ₗᵢ[ℂ] Fock) (T : H → H) (hW : FieldCovariant W T)
    (h : H) : StoneFamily h where
  U t := (W.trans (unitary (T h) t)).trans W.symm
  zero x := by
    change W.symm (unitary (T h) 0 (W x)) = x
    rw [unitary_zero,LinearIsometryEquiv.symm_apply_apply]
  add s t x := by
    change W.symm (unitary (T h) s (W (W.symm (unitary (T h) t (W x))))) =
      W.symm (unitary (T h) (s+t) (W x))
    rw [LinearIsometryEquiv.apply_symm_apply,unitary_add]
  continuous x := W.symm.continuous.comp (unitary_strong_continuous (T h) (W x))
  generator x y := by
    change HasDerivAt (fun t : ℝ => W.symm (unitary (T h) t (W x))) (Complex.I • y) 0 ↔ _
    rw [closureField_graph,graph_mem_closed,closed_graph_iff W T hW h,
      ← graph_mem_closed,← closureField_graph,← generator_iff]
    constructor
    · intro hd
      have hd' := hasDerivAt_map W hd
      simpa only [LinearIsometryEquiv.apply_symm_apply,map_smul] using hd'
    · intro hd
      have hd' := hasDerivAt_map W.symm hd
      simpa only [LinearIsometryEquiv.symm_apply_apply,map_smul] using hd'

/-- Field covariance on smooth vectors gives covariance of every Weyl
operator of the original smearing, at every real parameter. -/
theorem unitary_covariant (W : Fock ≃ₗᵢ[ℂ] Fock) (T : H → H) (hW : FieldCovariant W T)
    (h : H) (t : ℝ) (x : Fock) :
    W (unitary h t x) = unitary (T h) t (W x) := by
  have he := family_unique h (conjugatedFamily W T hW h) t x
  change W.symm (unitary (T h) t (W x)) = unitary h t x at he
  rw [← he,LinearIsometryEquiv.apply_symm_apply]

open Ext006PhysFockCoord Ext006PhysQuasifree Ext006GlobalCovarianceR43a
open Ext006KernelHilbertSchmidt Ext006SourceWeylR44a
variable {L : ℝ} [Fact (0 < L)]

/-- The coordinate transport of a real-linear one-particle map. -/
def coordinateMap (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L) (h : H) : H :=
  (physicalBasis L).repr (S ((physicalBasis L).repr.symm h))

/-- Physical form: if the transported unitary is field covariant at the
coordinates of S, then U is a source Weyl implementer of S. -/
theorem sourceWeyl_of_field (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (U : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L)
    (hU : FieldCovariant (Vtil U) (coordinateMap S)) :
    SourceWeylImplementer S U := by
  intro f x
  rw [sourceWeyl_eq,sourceWeyl_eq,physicalExponential_apply,physicalExponential_apply]
  have hc := unitary_covariant (Vtil U) (coordinateMap S) hU ((physicalBasis L).repr f) 1
    (Phi (U.symm x))
  have hT : coordinateMap S ((physicalBasis L).repr f) = (physicalBasis L).repr (S f) := by
    simp only [coordinateMap,LinearIsometryEquiv.symm_apply_apply]
  rw [hT,Vtil_apply,Vtil_apply,LinearIsometryEquiv.symm_apply_apply,
    LinearIsometryEquiv.apply_symm_apply] at hc
  rw [← hc,LinearIsometryEquiv.symm_apply_apply]

end QuantumNLS.Prop022OWeylField

#print axioms QuantumNLS.Prop022OWeylField.unitary_covariant
#print axioms QuantumNLS.Prop022OWeylField.sourceWeyl_of_field
