import NlsGge.Spectral.GenericRoughMatrixVolterraFactorial32V1
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Order.Compact
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
namespace NlsGge.SpectralFoundations
open CumulativePowerV3 CumulativePowerGeneralEndpointV1
/-- Arbitrary bounded homogeneous states vanish under a genuine nonnegative
integrable coefficient majorant; no uniqueness assumption is imported. -/
theorem genericRoughMatrixHomogeneousVolterra_bounded_eq_zero32
    (B : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (q : ℝ → ℝ) (T : ℝ)
    (hq : IntervalIntegrable q volume 0 T) (hqpos : ∀ s, 0 ≤ q s)
    (hmajorant : ∀ s ∈ Set.Icc (0 : ℝ) T, actualComplexMatrixEntrySup (B s) ≤ q s)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i j : Fin 2, ‖H t i j‖ ≤ K)
    (hVolterra : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i j : Fin 2,
      H t i j = ∫ s in (0 : ℝ)..t,
        (B s * H s) i j) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, H t = 0 := by
  intro t ht
  ext i j
  let Q : ℝ := actualCumulativeRealIntegral q t
  have hs : Summable (fun n : ℕ => (2 * Q) ^ n / (n.factorial : ℝ)) :=
    (NormedSpace.expSeries_div_hasSum_exp (2 * Q)).summable
  have hlim : Tendsto (fun n : ℕ => K * ((2 * Q) ^ n / (n.factorial : ℝ)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using hs.tendsto_atTop_zero.const_mul K
  have hle (n : ℕ) : ‖H t i j‖ ≤ K * ((2 * Q) ^ n / (n.factorial : ℝ)) := by
    have hb := genericRoughMatrixHomogeneousVolterra_factorial_bound32
      B q T hq hqpos hmajorant H K hK hbound hVolterra n t ht i j
    change ‖H t i j‖ ≤ K * (2 ^ n / (n.factorial : ℝ)) * Q ^ n at hb
    calc
      ‖H t i j‖ ≤ K * (2 ^ n / (n.factorial : ℝ)) * Q ^ n := hb
      _ = K * ((2 * Q) ^ n / (n.factorial : ℝ)) := by rw [mul_pow]; ring
  have hn : ‖H t i j‖ ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hle
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

/-- Continuity supplies the finite bound on the true compact coefficient
interval. There is no pointwise continuous-field or bounded-coefficient
assumption. This is homogeneous uniqueness; inhomogeneous fundamental
solution identification and spectral data are separate obligations. -/
theorem genericRoughMatrixHomogeneousVolterra_continuous_eq_zero32
    (B : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (q : ℝ → ℝ) (T : ℝ)
    (hq : IntervalIntegrable q volume 0 T) (hqpos : ∀ s, 0 ≤ q s)
    (hmajorant : ∀ s ∈ Set.Icc (0 : ℝ) T, actualComplexMatrixEntrySup (B s) ≤ q s)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hH : ContinuousOn H (Set.Icc (0 : ℝ) T))
    (hVolterra : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i j : Fin 2,
      H t i j = ∫ s in (0 : ℝ)..t,
        (B s * H s) i j) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, H t = 0 := by
  have hb (i j : Fin 2) : ∃ C : ℝ,
      ∀ t ∈ Set.Icc (0 : ℝ) T, ‖H t i j‖ ≤ C :=
    isCompact_Icc.exists_bound_of_continuousOn
      ((continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hH))
  choose C hC using hb
  let K : ℝ := |C 0 0| + |C 0 1| + |C 1 0| + |C 1 1|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i j : Fin 2, ‖H t i j‖ ≤ K := by
    intro t ht i j
    have hentry := hC i j t ht
    have hk : C i j ≤ K := by
      fin_cases i <;> fin_cases j <;> dsimp [K]
      all_goals linarith [le_abs_self (C 0 0), le_abs_self (C 0 1),
        le_abs_self (C 1 0), le_abs_self (C 1 1), abs_nonneg (C 0 0),
        abs_nonneg (C 0 1), abs_nonneg (C 1 0), abs_nonneg (C 1 1)]
    exact hentry.trans hk
  exact genericRoughMatrixHomogeneousVolterra_bounded_eq_zero32 B q T hq hqpos hmajorant H K hK hbound hVolterra
end NlsGge.SpectralFoundations
end
