import NlsGge.Sobolev.SourceWeighted

/-! Actual source Fourier preimages, with their induced weighted Hilbert norm. -/

set_option autoImplicit false
noncomputable section
open scoped ENNReal BigOperators

namespace NlsGge.Pilot

/-- Only an actual physical field and proved source Fourier membership are stored. -/
structure PhysicalWeighted {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (s : ℝ) where
  field : PhysicalL2
  membership : WeightedSquareSummable (sourceRate c) s (reflectedFourier field)

@[ext]
theorem physicalWeighted_ext {lower upper : ℝ} {c : BoundedCoefficients lower upper}
    {s : ℝ} {u v : PhysicalWeighted c s} (h : u.field = v.field) : u = v := by
  cases u
  cases v
  cases h
  rfl

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

/-- The actual source minus-reflected coefficients, with membership proved. -/
def physicalWeightedCoordinates (u : PhysicalWeighted c s) : FullWeightedHilbert c s := by
  let x : WeightedHilbert (fullModeWeight c s) :=
    ⟨reflectedFourier u.field,
      (fullWeightedHilbert_membership_iff c s (reflectedFourier u.field)).2 u.membership⟩
  exact x

theorem physicalWeightedCoordinates_apply (u : PhysicalWeighted c s) (n : ℤ) :
    (show WeightedHilbert (fullModeWeight c s) from physicalWeightedCoordinates c s u) n =
      reflectedFourier u.field n := rfl

/-- Actual Fourier reconstruction uses the proved plain lp2 coordinates. -/
def physicalWeightedReconstruct (x : FullWeightedHilbert c s) : PhysicalWeighted c s := by
  refine ⟨reflectedFourierL2.symm (fullWeightedSequenceL2 c s x), ?_⟩
  have hcoeff (n : ℤ) :
      reflectedFourier (reflectedFourierL2.symm (fullWeightedSequenceL2 c s x)) n =
        (show WeightedHilbert (fullModeWeight c s) from x) n := by
    rw [← reflectedFourierL2_apply, LinearIsometryEquiv.apply_symm_apply]
    exact fullWeightedSequenceL2_apply c s x n
  have hfun : reflectedFourier (reflectedFourierL2.symm (fullWeightedSequenceL2 c s x)) =
      fun n => (show WeightedHilbert (fullModeWeight c s) from x) n := funext hcoeff
  rw [hfun]
  exact (fullWeightedHilbert_membership_iff c s
    (fun n => (show WeightedHilbert (fullModeWeight c s) from x) n)).1
      (show WeightedHilbert (fullModeWeight c s) from x).property

/-- A derived bijection; neither inverse nor realization is assumed by the carrier. -/
def physicalWeightedEquiv : PhysicalWeighted c s ≃ FullWeightedHilbert c s where
  toFun := physicalWeightedCoordinates c s
  invFun := physicalWeightedReconstruct c s
  left_inv u := by
    apply physicalWeighted_ext
    apply reflectedFourierL2.injective
    apply lp.ext
    funext n
    change reflectedFourierL2 (reflectedFourierL2.symm
      (fullWeightedSequenceL2 c s (physicalWeightedCoordinates c s u))) n =
        reflectedFourierL2 u.field n
    rw [LinearIsometryEquiv.apply_symm_apply, fullWeightedSequenceL2_apply,
      physicalWeightedCoordinates_apply, reflectedFourierL2_apply]
  right_inv x := by
    apply Subtype.ext
    funext n
    change reflectedFourier (reflectedFourierL2.symm (fullWeightedSequenceL2 c s x)) n =
      (show WeightedHilbert (fullModeWeight c s) from x) n
    rw [← reflectedFourierL2_apply, LinearIsometryEquiv.apply_symm_apply,
      fullWeightedSequenceL2_apply]

instance physicalWeightedAddCommGroup : AddCommGroup (PhysicalWeighted c s) :=
  (physicalWeightedEquiv c s).addCommGroup

def physicalWeightedAddEquiv : PhysicalWeighted c s ≃+ FullWeightedHilbert c s :=
  (physicalWeightedEquiv c s).addEquiv

instance physicalWeightedModule : Module ℝ (PhysicalWeighted c s) :=
  (physicalWeightedAddEquiv c s).module ℝ

def physicalWeightedLinearEquiv : PhysicalWeighted c s ≃ₗ[ℝ] FullWeightedHilbert c s :=
  (physicalWeightedAddEquiv c s).linearEquiv ℝ

/-- The transported addition is actual addition of physical L2 classes. -/
theorem physicalWeighted_field_add (u v : PhysicalWeighted c s) :
    (u + v).field = u.field + v.field := by
  apply reflectedFourierL2.injective
  rw [map_add]
  apply lp.ext
  funext n
  have h := congrArg (fun x : FullWeightedHilbert c s =>
    (show WeightedHilbert (fullModeWeight c s) from x) n)
      ((physicalWeightedLinearEquiv c s).map_add u v)
  change reflectedFourier (u + v).field n =
    reflectedFourier u.field n + reflectedFourier v.field n at h
  simpa only [reflectedFourierL2_apply, lp.coeFn_add, Pi.add_apply] using h

/-- The transported real action is actual real multiplication of physical fields. -/
theorem physicalWeighted_field_smul (r : ℝ) (u : PhysicalWeighted c s) :
    (r • u).field = r • u.field := by
  apply reflectedFourierL2.injective
  rw [LinearMapClass.map_smul_of_tower]
  apply lp.ext
  funext n
  have h := congrArg (fun x : FullWeightedHilbert c s =>
    (show WeightedHilbert (fullModeWeight c s) from x) n)
      ((physicalWeightedLinearEquiv c s).map_smul r u)
  change reflectedFourier (r • u).field n = r • reflectedFourier u.field n at h
  simpa only [reflectedFourierL2_apply, lp.coeFn_smul, Pi.smul_apply] using h

def physicalWeightedFieldLinear : PhysicalWeighted c s →ₗ[ℝ] PhysicalL2 where
  toFun := PhysicalWeighted.field
  map_add' := physicalWeighted_field_add c s
  map_smul' := physicalWeighted_field_smul c s

instance physicalWeightedNormedAddCommGroup : NormedAddCommGroup (PhysicalWeighted c s) :=
  NormedAddCommGroup.induced _ _ (physicalWeightedLinearEquiv c s).toLinearMap
    (physicalWeightedLinearEquiv c s).injective

instance physicalWeightedNormedSpace : NormedSpace ℝ (PhysicalWeighted c s) where
  norm_smul_le r u := by
    change ‖physicalWeightedLinearEquiv c s (r • u)‖ ≤
      ‖r‖ * ‖physicalWeightedLinearEquiv c s u‖
    rw [map_smul]
    exact norm_smul_le r (physicalWeightedLinearEquiv c s u)

instance physicalWeightedInnerProductSpace : InnerProductSpace ℝ (PhysicalWeighted c s) :=
  InnerProductSpace.induced (physicalWeightedLinearEquiv c s).toLinearMap

/-- The actual E_s norm is transported through the derived real Fourier bijection. -/
def physicalWeightedFourier : PhysicalWeighted c s ≃ₗᵢ[ℝ] FullWeightedHilbert c s where
  __ := physicalWeightedLinearEquiv c s
  norm_map' _ := rfl

instance physicalWeightedCompleteSpace : CompleteSpace (PhysicalWeighted c s) := by
  letI : CompleteSpace (FullWeightedHilbert c s) :=
    inferInstanceAs (CompleteSpace (WeightedHilbert (fullModeWeight c s)))
  exact (physicalWeightedFourier c s).toIsometryEquiv.completeSpace

theorem physicalWeightedFourier_apply (u : PhysicalWeighted c s) (n : ℤ) :
    (show WeightedHilbert (fullModeWeight c s) from physicalWeightedFourier c s u) n =
      reflectedFourier u.field n := rfl

theorem physicalWeightedFourier_symm_field (x : FullWeightedHilbert c s) :
    ((physicalWeightedFourier c s).symm x).field =
      reflectedFourierL2.symm (fullWeightedSequenceL2 c s x) := rfl

theorem physicalWeighted_norm_sq (u : PhysicalWeighted c s) :
    ‖u‖ ^ 2 = ∑' n : ℤ, fullModeWeight c s n * ‖reflectedFourier u.field n‖ ^ 2 := by
  have h := fullWeightedHilbert_norm_sq c s (physicalWeightedFourier c s u)
  rw [(physicalWeightedFourier c s).norm_map] at h
  simpa only [fullModeWeight, physicalWeightedFourier_apply] using h

end NlsGge.Pilot
