import Mathlib
import NlsGge.Hierarchy.GaussianTailCovarianceBernstein38
import NlsGge.Sobolev.PeriodicBridge

                                                                                                                   
                                                                                                                             
                                                                                                                  
                                                                                        

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal ContDiff
open NlsGge.Pilot NlsGge.HierarchyRiccati.Core

namespace NlsGge.Atomic.F017

theorem FourierPlane_Bernstein (a : ℕ) :
    let C : ℝ := Real.sqrt 3 * (2*Real.pi)^a
    0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ z : FourierPlane N,
      Real.sqrt (∫ x in (0:ℝ)..1,
        ‖iteratedDeriv a (planeReal N z) x‖^2) ≤
          C * (N:ℝ)^a * Real.sqrt (∫ x in (0:ℝ)..1, ‖planeReal N z x‖^2) ∧
      ∀ x : ℝ, ‖iteratedDeriv a (planeReal N z) x‖ ≤
        C * Real.rpow (N:ℝ) ((a:ℝ) + 1/2) *
          Real.sqrt (∫ y in (0:ℝ)..1, ‖planeReal N z y‖^2) := by
  intro C
  have hsq3 : (1:ℝ) ≤ Real.sqrt 3 := by
    rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hC0 : 0 < C := by
    have : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    positivity
  refine ⟨hC0, fun N hN z => ⟨?_, ?_⟩⟩
  · have h := bernstein_L2_38 N z a
    have hN0 : (0:ℝ) ≤ (N:ℝ)^a := by positivity
    have hS : 0 ≤ Real.sqrt (∫ x in (0:ℝ)..1, ‖planeReal N z x‖^2) := Real.sqrt_nonneg _
    have hpow : (2*Real.pi*(N:ℝ))^a = (2*Real.pi)^a * (N:ℝ)^a := mul_pow (2*Real.pi) (N:ℝ) a
    have hpos : 0 ≤ (2*Real.pi)^a * (N:ℝ)^a := by positivity
    have hle1 : (2*Real.pi)^a * (N:ℝ)^a ≤ Real.sqrt 3 * ((2*Real.pi)^a * (N:ℝ)^a) :=
      le_mul_of_one_le_left hpos hsq3
    have hCe : C * (N:ℝ)^a = Real.sqrt 3 * ((2*Real.pi)^a * (N:ℝ)^a) := by
      simp only [C]; ring
    calc Real.sqrt (∫ x in (0:ℝ)..1, ‖iteratedDeriv a (planeReal N z) x‖^2)
        ≤ (2*Real.pi*(N:ℝ))^a * Real.sqrt (∫ x in (0:ℝ)..1, ‖planeReal N z x‖^2) := h
      _ = (2*Real.pi)^a * (N:ℝ)^a * Real.sqrt (∫ x in (0:ℝ)..1, ‖planeReal N z x‖^2) := by rw [hpow]
      _ ≤ C * (N:ℝ)^a * Real.sqrt (∫ x in (0:ℝ)..1, ‖planeReal N z x‖^2) := by
        rw [hCe]
        exact mul_le_mul_of_nonneg_right hle1 hS
  · intro x
    have h := bernstein_sup_38 N z a x
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have hN0 : (0:ℝ) < (N:ℝ) := by linarith
    have hsqrt : Real.sqrt (2*(N:ℝ)+1) ≤ Real.sqrt 3 * Real.sqrt (N:ℝ) := by
      rw [← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt (by linarith)
    have hrpow : Real.rpow (N:ℝ) ((a:ℝ) + 1/2) = (N:ℝ)^a * Real.sqrt (N:ℝ) := by
      show (N:ℝ)^((a:ℝ) + 1/2) = _
      rw [Real.rpow_add hN0, Real.rpow_natCast, Real.sqrt_eq_rpow]
    have hM : 0 ≤ Real.sqrt (∫ y in (0:ℝ)..1, ‖planeReal N z y‖^2) := Real.sqrt_nonneg _
    have hpow : (2*Real.pi*(N:ℝ))^a = (2*Real.pi)^a * (N:ℝ)^a := mul_pow (2*Real.pi) (N:ℝ) a
    calc ‖iteratedDeriv a (planeReal N z) x‖
        ≤ (2*Real.pi*(N:ℝ))^a * Real.sqrt (2*(N:ℝ)+1) *
            Real.sqrt (∫ y in (0:ℝ)..1, ‖planeReal N z y‖^2) := h
      _ ≤ (2*Real.pi*(N:ℝ))^a * (Real.sqrt 3 * Real.sqrt (N:ℝ)) *
            Real.sqrt (∫ y in (0:ℝ)..1, ‖planeReal N z y‖^2) := by
        apply mul_le_mul_of_nonneg_right _ hM
        exact mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ = C * Real.rpow (N:ℝ) ((a:ℝ) + 1/2) *
            Real.sqrt (∫ y in (0:ℝ)..1, ‖planeReal N z y‖^2) := by
        rw [hrpow, hpow]
        simp only [C]
        ring

end NlsGge.Atomic.F017
