import NlsGge.Spectral.ActualPhysicalL2ZsDysonFactorialBoundV1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis
open CumulativePowerV3 CumulativePowerGeneralEndpointV1

/-- Factorial iteration for an arbitrary bounded homogeneous solution of the
actual rough-L² Volterra equation. The bound and equation are explicit
hypotheses; this is a uniqueness prerequisite, not an assumed uniqueness
result and not merely an estimate for the constructed Dyson iterates. -/
theorem actualPhysicalL2ZsHomogeneousVolterra_factorial_bound
    (u : PhysicalL2) (z : ℂ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) 2, ∀ i j : Fin 2, ‖H t i j‖ ≤ K)
    (hVolterra : ∀ t ∈ Set.Icc (0 : ℝ) 2, ∀ i j : Fin 2,
      H t i j = ∫ s in (0 : ℝ)..t,
        (zsCoefficientComplex
          (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
          z s * H s) i j) :
    ∀ (n : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 2 → ∀ i j : Fin 2,
      ‖H t i j‖ ≤ K * (2 ^ n / (n.factorial : ℝ)) *
        actualPhysicalL2ZsCumulativeMajorant u z t ^ n := by
  let U : ℝ → ℂ := fun s =>
    (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle)
  let q : ℝ → ℝ := actualPhysicalL2ZsMajorant u z
  let Q : ℝ → ℝ := actualCumulativeRealIntegral q
  have hq : IntervalIntegrable q volume 0 2 :=
    actualPhysicalL2ZsMajorant_intervalIntegrable u z
  have hqpos : ∀ s, 0 ≤ q s := actualPhysicalL2ZsMajorant_nonneg u z
  intro n
  induction n with
  | zero =>
      intro t ht i j
      simpa only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one] using hbound t ht i j
  | succ n ih =>
      intro t ht i j
      let C : ℝ := K * (2 ^ n / (n.factorial : ℝ))
      have hC : 0 ≤ C := by dsimp [C]; positivity
      have hB (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) t) :
          actualComplexMatrixEntrySup (H s) ≤ C * Q s ^ n := by
        have hs2 : s ∈ Set.Icc (0 : ℝ) 2 := ⟨hs.1, hs.2.trans ht.2⟩
        unfold actualComplexMatrixEntrySup
        exact max_le (max_le (ih s hs2 0 0) (ih s hs2 0 1))
          (max_le (ih s hs2 1 0) (ih s hs2 1 1))
      have hnorm (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) t) :
          ‖(zsCoefficientComplex U z s * H s) i j‖ ≤
            (2 * C) * (q s * Q s ^ n) := by
        have hA : actualComplexMatrixEntrySup (zsCoefficientComplex U z s) ≤ q s :=
          actualPhysicalL2ZsCoefficient_entrySup_le_majorant u z s
        have hBpos : 0 ≤ actualComplexMatrixEntrySup (H s) :=
          (norm_nonneg _).trans (norm_entry_le_actualComplexMatrixEntrySup _ 0 0)
        calc
          ‖(zsCoefficientComplex U z s * H s) i j‖ ≤
              actualComplexMatrixEntrySup
                (zsCoefficientComplex U z s * H s) :=
            norm_entry_le_actualComplexMatrixEntrySup _ i j
          _ ≤ 2 * actualComplexMatrixEntrySup (zsCoefficientComplex U z s) *
              actualComplexMatrixEntrySup (H s) :=
            actualComplexMatrixEntrySup_mul_le _ _
          _ ≤ 2 * q s * (C * Q s ^ n) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hA (by norm_num))
              (hB s hs) hBpos (mul_nonneg (by norm_num) (hqpos s))
          _ = (2 * C) * (q s * Q s ^ n) := by ring
      have hint : IntervalIntegrable (fun s => (2 * C) * (q s * Q s ^ n)) volume 0 t :=
        (intervalIntegrable_cumulativePower q 2 hq n t ht.1 ht.2).const_mul (2 * C)
      have hstep := intervalIntegral.norm_integral_le_of_norm_le ht.1
        (Filter.Eventually.of_forall (fun s (hs : s ∈ Set.Ioc (0 : ℝ) t) =>
          hnorm s ⟨le_of_lt hs.1, hs.2⟩)) hint
      have hcum := intervalIntegral_cumulativePower_eq q 2 hq n t ht.1 ht.2
      have hfactorial : ((n + 1).factorial : ℝ) =
          (n + 1 : ℝ) * (n.factorial : ℝ) := by
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
      calc
        ‖H t i j‖ = ‖∫ s in (0 : ℝ)..t, (zsCoefficientComplex U z s * H s) i j‖ :=
          congrArg norm (hVolterra t ht i j)
        _ ≤ ∫ s in (0 : ℝ)..t, (2 * C) * (q s * Q s ^ n) := hstep
        _ = (2 * C) * (Q t ^ (n + 1) / (n + 1 : ℝ)) := by
          rw [intervalIntegral.integral_const_mul, hcum]
        _ = K * (2 ^ (n + 1) / ((n + 1).factorial : ℝ)) * Q t ^ (n + 1) := by
          dsimp [C]
          rw [hfactorial]
          have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
          have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
          field_simp [hn1, hfac]
          <;> ring

end NlsGge.SpectralFoundations
end
