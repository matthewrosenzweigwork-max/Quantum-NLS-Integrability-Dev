import NlsGge.Definitions.PilotInterfaces

/-! Concrete finite Fourier planes, with period one and normalized spatial measure. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace NlsGge.Pilot

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

theorem continuous_planeField (N : ℕ) (z : FourierPlane N) :
    Continuous (planeField N z) := by
  unfold planeField
  fun_prop

theorem measurable_planeField (N : ℕ) (z : FourierPlane N) :
    Measurable (planeField N z) :=
  (continuous_planeField N z).measurable

theorem integrable_planeField (N : ℕ) (z : FourierPlane N) :
    Integrable (planeField N z) spatialMeasure := by
  apply (continuous_planeField N z).integrable_of_hasCompactSupport
  exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)

theorem integrable_planeTerm (N : ℕ) (z : FourierPlane N)
    (i : Fin (2 * N + 1)) :
    Integrable (fun x : PhysicalCircle => z i * fourier (modeIndex N i) x)
      spatialMeasure := by
  apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
  exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)

theorem physicalFourier_planeField_sum (N : ℕ) (z : FourierPlane N) (n : ℤ) :
    physicalFourier (planeField N z) n =
      ∑ i : Fin (2 * N + 1), z i * (Pi.single (modeIndex N i) 1 : ℤ → ℂ) n := by
  classical
  unfold physicalFourier planeField
  have h := congrFun (fourierCoeff.sum Finset.univ
    (fun i : Fin (2 * N + 1) => fun x : PhysicalCircle =>
      z i * fourier (modeIndex N i) x)
    (fun i _ => integrable_planeTerm N z i)) n
  have hf : (fun x : PhysicalCircle =>
      ∑ i : Fin (2 * N + 1), z i * fourier (modeIndex N i) x) =
      ∑ i : Fin (2 * N + 1), fun x : PhysicalCircle =>
        z i * fourier (modeIndex N i) x := by
    funext x
    simp only [Finset.sum_apply]
  rw [hf]
  simpa only [Finset.sum_apply, fourierCoeff.const_mul, fourierCoeff_fourier] using h

theorem physicalFourier_planeField (N : ℕ) (z : FourierPlane N)
    (i : Fin (2 * N + 1)) :
    physicalFourier (planeField N z) (modeIndex N i) = z i := by
  classical
  rw [physicalFourier_planeField_sum]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hmode : modeIndex N i ≠ modeIndex N j := by
      intro h
      exact hji ((modeIndex_injective N h).symm)
    simp [hmode]
  · simp

theorem physicalFourier_planeField_outside (N : ℕ) (z : FourierPlane N)
    (n : ℤ) (hn : n < -(N : ℤ) ∨ (N : ℤ) < n) :
    physicalFourier (planeField N z) n = 0 := by
  classical
  rw [physicalFourier_planeField_sum]
  apply Finset.sum_eq_zero
  intro i _
  have hmode : n ≠ modeIndex N i := by
    have hb := modeIndex_bounds N i
    omega
  simp [hmode]

theorem physicalFourier_planeField_zero (N : ℕ) (z : FourierPlane N) :
    physicalFourier (planeField N z) 0 = z (zeroMode N) := by
  simpa only [modeIndex_zero] using physicalFourier_planeField N z (zeroMode N)

theorem reflectedFourier_planeField (N : ℕ) (z : FourierPlane N)
    (i : Fin (2 * N + 1)) :
    reflectedFourier (planeField N z) (modeIndex N i) = reflectPlane N z i := by
  unfold reflectedFourier reflectPlane
  rw [← modeIndex_reflect, physicalFourier_planeField]

/-- The actual continuous representative used for the L2 realization. -/
def planeContinuous (N : ℕ) (z : FourierPlane N) : C(PhysicalCircle, ℂ) :=
  ⟨planeField N z, continuous_planeField N z⟩

/-- The equivalence class of the finite plane field in genuine spatial L2. -/
def planeL2 (N : ℕ) (z : FourierPlane N) : PhysicalL2 :=
  ContinuousMap.toLp 2 spatialMeasure ℂ (planeContinuous N z)

theorem planeL2_ae (N : ℕ) (z : FourierPlane N) :
    (planeL2 N z : PhysicalCircle → ℂ) =ᵐ[spatialMeasure] planeField N z := by
  exact ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure (planeContinuous N z)

theorem memLp_planeField (N : ℕ) (z : FourierPlane N) :
    MemLp (planeField N z) 2 spatialMeasure :=
  (Lp.memLp (planeL2 N z)).ae_eq (planeL2_ae N z)

theorem physicalFourier_planeL2 (N : ℕ) (z : FourierPlane N) (n : ℤ) :
    physicalFourier (planeL2 N z) n = physicalFourier (planeField N z) n := by
  exact congrFun (fourierCoeff_congr_ae (planeL2_ae N z)) n

theorem planeL2_injective (N : ℕ) : Function.Injective (planeL2 N) := by
  intro z w h
  funext i
  rw [← physicalFourier_planeField N z i, ← physicalFourier_planeField N w i,
    ← physicalFourier_planeL2, ← physicalFourier_planeL2, h]

end NlsGge.Pilot
