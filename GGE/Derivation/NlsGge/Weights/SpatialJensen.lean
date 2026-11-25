import NlsGge.Sobolev.PeriodicBridge
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

/-! UNCOMPILED RECOVERABLE PROOF SCRATCH ONLY.
Reviewed J01/P01–P05 targets; no assigned ordinary proof module yet.
No actual spectral/charge identification or energy finiteness is asserted.
-/
set_option autoImplicit false
noncomputable section
universe u
open MeasureTheory NlsGge.Pilot
open scoped BigOperators ENNReal ComplexConjugate
namespace NlsGge.Weights

lemma probability_integral_pow_le {α : Type u} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (j : ℕ)
    (hnonneg : ∀ᵐ x ∂μ, 0 ≤ f x) (hfirst : Integrable f μ)
    (hmoment : Integrable (fun x : α => f x ^ j) μ) :
    (∫ x : α, f x ∂μ) ^ j ≤ ∫ x : α, f x ^ j ∂μ := by
  exact (convexOn_pow j : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ j)).map_integral_le
    (continuous_id.pow j).continuousOn isClosed_Ici
    (by simpa only [Set.mem_Ici] using hnonneg) hfirst
    (by simpa only [Function.comp_def] using hmoment)

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

lemma plane_norm_pow_integrable (N : ℕ) (z : FourierPlane N) (p : ℕ) :
    Integrable (fun x : PhysicalCircle => ‖planeField N z x‖ ^ p) spatialMeasure := by
  apply ((continuous_planeField N z).norm.pow p).integrable_of_hasCompactSupport
  exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)

lemma plane_mass_integral_eq_sum (N : ℕ) (z : FourierPlane N) :
    (∫ x : PhysicalCircle, ‖planeField N z x‖ ^ 2 ∂spatialMeasure) =
      ∑ i : Fin (2 * N + 1), ‖z i‖ ^ 2 := by
  have hint := plane_norm_pow_integrable N z 2
  have hinner : ((∑ i : Fin (2 * N + 1), ‖z i‖ ^ 2 : ℝ) : ℂ) =
      ((∫ x : PhysicalCircle, ‖planeField N z x‖ ^ 2 ∂spatialMeasure) : ℂ) := by
    calc
      ((∑ i : Fin (2 * N + 1), ‖z i‖ ^ 2 : ℝ) : ℂ) =
          (‖planeL2 N z‖ : ℂ) ^ 2 := by
        rw [← planeL2_norm_sq N z]
        norm_cast
      _ = inner ℂ (planeL2 N z) (planeL2 N z) :=
        (inner_self_eq_norm_sq_to_K (planeL2 N z)).symm
      _ = ∫ x : PhysicalCircle,
          inner ℂ ((planeL2 N z : PhysicalCircle → ℂ) x)
            ((planeL2 N z : PhysicalCircle → ℂ) x) ∂spatialMeasure :=
        MeasureTheory.L2.inner_def (planeL2 N z) (planeL2 N z)
      _ = ((∫ x : PhysicalCircle, ‖planeField N z x‖ ^ 2 ∂spatialMeasure) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [planeL2_ae N z] with x hx
        simp only [hx, inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
        with_reducible_and_instances rfl
  exact_mod_cast hinner.symm

lemma plane_derivative_sq_integral_eq_sum (N : ℕ) (z : FourierPlane N) :
    (∫ x : PhysicalCircle, ‖planeField N (derivativePlane N z) x‖ ^ 2 ∂spatialMeasure) =
      4 * Real.pi ^ 2 *
        (∑ i : Fin (2 * N + 1), (modeIndex N i : ℝ) ^ 2 * ‖z i‖ ^ 2) := by
  rw [plane_mass_integral_eq_sum N (derivativePlane N z)]
  calc
    (∑ i : Fin (2 * N + 1), ‖derivativePlane N z i‖ ^ 2) =
        ∑ i : Fin (2 * N + 1),
          4 * Real.pi ^ 2 * ((modeIndex N i : ℝ) ^ 2 * ‖z i‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [derivativePlane, norm_mul, Complex.norm_two, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, Complex.norm_intCast,
        mul_pow, one_pow, mul_one, sq_abs]
      ring
    _ = 4 * Real.pi ^ 2 *
        (∑ i : Fin (2 * N + 1), (modeIndex N i : ℝ) ^ 2 * ‖z i‖ ^ 2) := by
      rw [Finset.mul_sum]

lemma plane_mass_sq_le_quartic (N : ℕ) (z : FourierPlane N) :
    (∫ x : PhysicalCircle, ‖planeField N z x‖ ^ 2 ∂spatialMeasure) ^ 2 ≤
      ∫ x : PhysicalCircle, ‖planeField N z x‖ ^ 4 ∂spatialMeasure := by
  have h := probability_integral_pow_le spatialMeasure
    (fun x : PhysicalCircle => ‖planeField N z x‖ ^ 2) 2
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖planeField N z x‖))
    (plane_norm_pow_integrable N z 2)
    (by simpa only [← pow_mul] using plane_norm_pow_integrable N z 4)
  simpa only [← pow_mul] using h

lemma plane_q2_radius_lower (N : ℕ) (z : FourierPlane N) (R : ℝ) (hR : 1 ≤ R)
    (hradius : R ^ 2 ≤
      (∑ i : Fin (2 * N + 1), ‖z i‖ ^ 2) +
      (∑ i : Fin (2 * N + 1), (modeIndex N i : ℝ) ^ 2 * ‖z i‖ ^ 2)) :
    (1 / 4 : ℝ) * R ^ 2 ≤
      ∫ x : PhysicalCircle,
        (‖planeField N (derivativePlane N z) x‖ ^ 2 + ‖planeField N z x‖ ^ 4)
        ∂spatialMeasure := by
  let M : ℝ := ∑ i : Fin (2 * N + 1), ‖z i‖ ^ 2
  let D : ℝ := ∑ i : Fin (2 * N + 1), (modeIndex N i : ℝ) ^ 2 * ‖z i‖ ^ 2
  let K : ℝ := ∫ x : PhysicalCircle, ‖planeField N z x‖ ^ 4 ∂spatialMeasure
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hD0 : 0 ≤ D := Finset.sum_nonneg (fun _ _ => by positivity)
  have hK0 : 0 ≤ K := integral_nonneg (fun _ => by positivity)
  have hMK : M ^ 2 ≤ K := by
    dsimp [M, K]
    rw [← plane_mass_integral_eq_sum N z]
    exact plane_mass_sq_le_quartic N z
  have hsum :
      (∫ x : PhysicalCircle,
        (‖planeField N (derivativePlane N z) x‖ ^ 2 + ‖planeField N z x‖ ^ 4)
          ∂spatialMeasure) = 4 * Real.pi ^ 2 * D + K := by
    rw [integral_add (plane_norm_pow_integrable N (derivativePlane N z) 2)
      (plane_norm_pow_integrable N z 4), plane_derivative_sq_integral_eq_sum N z]
  rw [hsum]
  have hrad : R ^ 2 ≤ M + D := hradius
  have hRR : 1 ≤ R ^ 2 := by nlinarith
  by_cases hm : R ^ 2 / 2 ≤ M
  · have hs : (R ^ 2 / 2) ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (by positivity) hm 2
    have hfour : R ^ 2 ≤ (R ^ 2) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg R) (by linarith : 0 ≤ R ^ 2 - 1)]
    have hpD : 0 ≤ 4 * Real.pi ^ 2 * D := by positivity
    nlinarith
  · have hD : R ^ 2 / 2 ≤ D := by linarith
    have hpi : (1 / 8 : ℝ) ≤ Real.pi ^ 2 := by
      nlinarith [Real.two_le_pi, Real.pi_pos]
    have hbound : (1 / 4 : ℝ) * R ^ 2 ≤ 4 * Real.pi ^ 2 * D := by
      calc
        (1 / 4 : ℝ) * R ^ 2 ≤ (2 * Real.pi ^ 2) * R ^ 2 :=
          mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg R)
        _ = (4 * Real.pi ^ 2) * (R ^ 2 / 2) := by ring
        _ ≤ 4 * Real.pi ^ 2 * D :=
          mul_le_mul_of_nonneg_left hD (by positivity)
    linarith

end NlsGge.Weights
