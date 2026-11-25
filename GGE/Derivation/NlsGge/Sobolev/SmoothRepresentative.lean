import NlsGge.Sobolev.SmoothFourier

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Real ENNReal
namespace NlsGge.Pilot

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

theorem summable_physicalWeighted_continuousTerms (u : PhysicalWeighted c s) :
    Summable (fun n : ℤ => physicalFourier u.field n • (fourier n : C(PhysicalCircle, ℂ))) := by
  apply Summable.of_norm
  have h := summable_physicalWeighted_fourier_amplitude c s u 0
  simpa only [norm_smul, fourier_norm, mul_one, pow_zero, one_mul] using h

/-- The actual sup-norm Fourier sum, with norm summability proved above. -/
def physicalWeightedContinuous (u : PhysicalWeighted c s) : C(PhysicalCircle, ℂ) :=
  ∑' n : ℤ, physicalFourier u.field n • (fourier n : C(PhysicalCircle, ℂ))

theorem physicalWeightedContinuous_hasSum (u : PhysicalWeighted c s) :
    HasSum (fun n : ℤ => physicalFourier u.field n • (fourier n : C(PhysicalCircle, ℂ)))
      (physicalWeightedContinuous c s u) :=
  (summable_physicalWeighted_continuousTerms c s u).hasSum

/-- Derivatives are taken on this actual real periodic representative. -/
def physicalWeightedReal (u : PhysicalWeighted c s) (y : ℝ) : ℂ :=
  physicalWeightedContinuous c s u (y : PhysicalCircle)

theorem physicalWeightedReal_series (u : PhysicalWeighted c s) (y : ℝ) :
    physicalWeightedReal c s u y = ∑' n : ℤ, fourierRealTerm n (physicalFourier u.field n) y := by
  have h := (physicalWeightedContinuous_hasSum c s u).mapL
    (ContinuousMap.evalCLM ℂ (y : PhysicalCircle))
  change HasSum (fun n : ℤ => fourierRealTerm n (physicalFourier u.field n) y)
    (physicalWeightedReal c s u y) at h
  exact h.tsum_eq.symm

theorem physicalWeightedReal_periodic (u : PhysicalWeighted c s) :
    Function.Periodic (physicalWeightedReal c s u) 1 := by
  intro y
  simp only [physicalWeightedReal, AddCircle.coe_add_period]

theorem contDiff_physicalWeightedReal (u : PhysicalWeighted c s) :
    ContDiff ℝ (⊤ : ℕ∞) (physicalWeightedReal c s u) := by
  have hfun : physicalWeightedReal c s u =
      fun y : ℝ => ∑' n : ℤ, fourierRealTerm n (physicalFourier u.field n) y :=
    funext (physicalWeightedReal_series c s u)
  rw [hfun]
  exact contDiff_tsum (fun n => contDiff_fourierRealTerm n (physicalFourier u.field n))
    (fun k _ => (summable_physicalWeighted_fourier_amplitude c s u k).mul_left ((2 * π) ^ k))
    (fun k n y _ => norm_iteratedFDeriv_fourierRealTerm_le n (physicalFourier u.field n) k y)

theorem physicalWeightedContinuous_toLp (u : PhysicalWeighted c s) :
    ContinuousMap.toLp 2 spatialMeasure ℂ (physicalWeightedContinuous c s u) = u.field := by
  have h := (physicalWeightedContinuous_hasSum c s u).mapL
    (ContinuousMap.toLp 2 spatialMeasure ℂ)
  simp only [map_smul] at h
  change HasSum (fun n : ℤ => physicalFourier u.field n • fourierLp (T := (1 : ℝ)) 2 n)
    (ContinuousMap.toLp 2 spatialMeasure ℂ (physicalWeightedContinuous c s u)) at h
  exact h.unique (hasSum_fourier_series_L2 u.field)

theorem physicalWeightedContinuous_ae (u : PhysicalWeighted c s) :
    (physicalWeightedContinuous c s u : PhysicalCircle → ℂ) =ᵐ[spatialMeasure] u.field := by
  have h := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure
    (physicalWeightedContinuous c s u)
  rw [physicalWeightedContinuous_toLp] at h
  exact h.symm

end NlsGge.Pilot
