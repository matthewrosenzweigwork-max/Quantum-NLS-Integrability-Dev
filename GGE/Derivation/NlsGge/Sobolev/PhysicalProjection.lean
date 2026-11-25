import NlsGge.Sobolev.PhysicalWeighted
import NlsGge.Sobolev.WeightedProjection

set_option autoImplicit false
noncomputable section
open Filter
open scoped ENNReal Topology

namespace NlsGge.Pilot

section RealProjection
variable (w : ℤ → ℝ) [Fact (∀ n : ℤ, 0 < w n)]

def weightedRealProjectionLinear (m : Finset ℤ) : WeightedRealHilbert w →ₗ[ℝ] WeightedRealHilbert w where
  toFun x := weightedProjection w m (show WeightedHilbert w from x)
  map_add' x y := (weightedProjectionLinear w m).map_add x y
  map_smul' r x := by
    change weightedProjectionLinear w m ((r : ℂ) • (show WeightedHilbert w from x)) =
      (r : ℂ) • weightedProjectionLinear w m (show WeightedHilbert w from x)
    exact (weightedProjectionLinear w m).map_smul (r : ℂ) x

def weightedRealProjectionContinuous (m : Finset ℤ) :
    WeightedRealHilbert w →L[ℝ] WeightedRealHilbert w :=
  (weightedRealProjectionLinear w m).mkContinuous 1
    (fun x => by
      have hn : ‖weightedRealProjectionLinear w m x‖ ≤ ‖x‖ :=
        weightedProjection_norm_le w m (show WeightedHilbert w from x)
      exact hn.trans_eq (one_mul ‖x‖).symm)

theorem weightedRealProjection_apply (m : Finset ℤ) (x : WeightedRealHilbert w) (n : ℤ) :
    (show WeightedHilbert w from weightedRealProjectionContinuous w m x) n =
      if n ∈ m then (show WeightedHilbert w from x) n else 0 :=
  weightedProjection_apply w m (show WeightedHilbert w from x) n

theorem weightedRealProjection_norm_le (m : Finset ℤ) (x : WeightedRealHilbert w) :
    ‖weightedRealProjectionContinuous w m x‖ ≤ ‖x‖ :=
  weightedProjection_norm_le w m (show WeightedHilbert w from x)

theorem weightedRealProjection_range_residual (m : Finset ℤ) (x y : WeightedRealHilbert w) :
    inner ℝ (weightedRealProjectionContinuous w m y)
      (x - weightedRealProjectionContinuous w m x) = 0 := by
  change (inner ℂ (weightedProjection w m (show WeightedHilbert w from y))
    ((show WeightedHilbert w from x) - weightedProjection w m (show WeightedHilbert w from x))).re = 0
  rw [weightedProjection_range_residual]
  rfl

end RealProjection

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

def physicalWeightedProjection (m : Finset ℤ) : PhysicalWeighted c s →L[ℝ] PhysicalWeighted c s :=
  (physicalWeightedFourier c s).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((weightedRealProjectionContinuous (fullModeWeight c s) m).comp
      (physicalWeightedFourier c s).toContinuousLinearEquiv.toContinuousLinearMap)

theorem physicalWeightedProjection_fourier (m : Finset ℤ) (u : PhysicalWeighted c s) (n : ℤ) :
    reflectedFourier (physicalWeightedProjection c s m u).field n =
      if n ∈ m then reflectedFourier u.field n else 0 := by
  rw [← physicalWeightedFourier_apply]
  change (show WeightedHilbert (fullModeWeight c s) from physicalWeightedFourier c s
    ((physicalWeightedFourier c s).symm
      (weightedRealProjectionContinuous (fullModeWeight c s) m (physicalWeightedFourier c s u)))) n = _
  rw [LinearIsometryEquiv.apply_symm_apply, weightedRealProjection_apply,
    physicalWeightedFourier_apply]

theorem physicalWeightedProjection_norm_le (m : Finset ℤ) (u : PhysicalWeighted c s) :
    ‖physicalWeightedProjection c s m u‖ ≤ ‖u‖ := by
  change ‖(physicalWeightedFourier c s).symm
    (weightedRealProjectionContinuous (fullModeWeight c s) m (physicalWeightedFourier c s u))‖ ≤ ‖u‖
  rw [LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map] using weightedRealProjection_norm_le
    (fullModeWeight c s) m (physicalWeightedFourier c s u)

theorem physicalWeightedProjection_idempotent (m : Finset ℤ) (u : PhysicalWeighted c s) :
    physicalWeightedProjection c s m (physicalWeightedProjection c s m u) =
      physicalWeightedProjection c s m u := by
  apply physicalWeighted_ext
  apply reflectedFourierL2.injective
  apply lp.ext
  funext n
  simp only [reflectedFourierL2_apply, physicalWeightedProjection_fourier]
  by_cases hn : n ∈ m <;> simp [hn]

theorem physicalWeightedProjection_range_residual (m : Finset ℤ) (u v : PhysicalWeighted c s) :
    inner ℝ (physicalWeightedProjection c s m v) (u - physicalWeightedProjection c s m u) = 0 := by
  change inner ℝ (physicalWeightedLinearEquiv c s (physicalWeightedProjection c s m v))
    (physicalWeightedLinearEquiv c s (u - physicalWeightedProjection c s m u)) = 0
  have hsub := (physicalWeightedLinearEquiv c s).map_sub u (physicalWeightedProjection c s m u)
  have hinner := congrArg (fun z : FullWeightedHilbert c s =>
    inner ℝ (physicalWeightedLinearEquiv c s (physicalWeightedProjection c s m v)) z) hsub
  apply hinner.trans
  change inner ℝ
    (physicalWeightedFourier c s ((physicalWeightedFourier c s).symm
      (weightedRealProjectionContinuous (fullModeWeight c s) m (physicalWeightedFourier c s v))))
    (physicalWeightedFourier c s u -
      physicalWeightedFourier c s ((physicalWeightedFourier c s).symm
        (weightedRealProjectionContinuous (fullModeWeight c s) m (physicalWeightedFourier c s u)))) = 0
  rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  exact weightedRealProjection_range_residual (fullModeWeight c s) m
    (physicalWeightedFourier c s u) (physicalWeightedFourier c s v)

theorem physicalWeightedProjection_tendsto (u : PhysicalWeighted c s) :
    Tendsto (fun N : ℕ => physicalWeightedProjection c s (symmetricModes N) u) atTop (𝓝 u) := by
  have ht := weightedProjection_tendsto (fullModeWeight c s)
    (show WeightedHilbert (fullModeWeight c s) from physicalWeightedFourier c s u)
  have h := ((physicalWeightedFourier c s).symm.continuous.tendsto
    (physicalWeightedFourier c s u)).comp ht
  rw [LinearIsometryEquiv.symm_apply_apply] at h
  change Tendsto (fun N : ℕ => (physicalWeightedFourier c s).symm
    (weightedProjection (fullModeWeight c s) (symmetricModes N)
      (show WeightedHilbert (fullModeWeight c s) from physicalWeightedFourier c s u))) atTop (𝓝 u)
  exact h

end NlsGge.Pilot
