import NlsGge.Spectral.ActualPhysicalL2ZsMajorantAndFiniteDysonV2
import NlsGge.Spectral.CumulativePowerIntegralGeneralEndpointV1
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory

namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis
open CumulativePowerV3 CumulativePowerGeneralEndpointV1

/-- The true cumulative L¹ coefficient majorant on the doubled interval. -/
def actualPhysicalL2ZsCumulativeMajorant (u : PhysicalL2) (z : ℂ) (t : ℝ) : ℝ :=
  actualCumulativeRealIntegral (actualPhysicalL2ZsMajorant u z) t

theorem actualPhysicalL2ZsCumulativeMajorant_nonneg
    (u : PhysicalL2) (z : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ actualPhysicalL2ZsCumulativeMajorant u z t := by
  exact intervalIntegral.integral_nonneg_of_forall ht
    (actualPhysicalL2ZsMajorant_nonneg u z)

/-- The actual Picard iterates have a factorial bound for every physical L²
input and complex parameter, using the cumulative L¹ majorant. No uniform or
continuous representative of the field is assumed. -/
theorem actualPhysicalL2ZsDysonTerm_entry_factorial_bound
    (u : PhysicalL2) (z : ℂ) :
    ∀ (n : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 2 → ∀ i j : Fin 2,
      ‖actualComplexZsDysonTerm
          (fun s => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
          z n t i j‖ ≤
        (2 ^ n / (n.factorial : ℝ)) * actualPhysicalL2ZsCumulativeMajorant u z t ^ n := by
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
      by_cases hij : i = j <;>
        simp [actualComplexZsDysonTerm, Matrix.one_apply, hij]
  | succ n ih =>
      intro t ht i j
      let C : ℝ := 2 ^ n / (n.factorial : ℝ)
      have hC : 0 ≤ C := by dsimp [C]; positivity
      have hB (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) t) :
          actualComplexMatrixEntrySup (actualComplexZsDysonTerm U z n s) ≤ C * Q s ^ n := by
        have hs2 : s ∈ Set.Icc (0 : ℝ) 2 := ⟨hs.1, hs.2.trans ht.2⟩
        unfold actualComplexMatrixEntrySup
        exact max_le (max_le (ih s hs2 0 0) (ih s hs2 0 1))
          (max_le (ih s hs2 1 0) (ih s hs2 1 1))
      have hnorm (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) t) :
          ‖(zsCoefficientComplex U z s * actualComplexZsDysonTerm U z n s) i j‖ ≤
            (2 * C) * (q s * Q s ^ n) := by
        have hA : actualComplexMatrixEntrySup (zsCoefficientComplex U z s) ≤ q s :=
          actualPhysicalL2ZsCoefficient_entrySup_le_majorant u z s
        have hBpos : 0 ≤ actualComplexMatrixEntrySup (actualComplexZsDysonTerm U z n s) :=
          (norm_nonneg _).trans (norm_entry_le_actualComplexMatrixEntrySup _ 0 0)
        calc
          ‖(zsCoefficientComplex U z s * actualComplexZsDysonTerm U z n s) i j‖ ≤
              actualComplexMatrixEntrySup
                (zsCoefficientComplex U z s * actualComplexZsDysonTerm U z n s) :=
            norm_entry_le_actualComplexMatrixEntrySup _ i j
          _ ≤ 2 * actualComplexMatrixEntrySup (zsCoefficientComplex U z s) *
              actualComplexMatrixEntrySup (actualComplexZsDysonTerm U z n s) :=
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
      change ‖∫ s in (0 : ℝ)..t,
        (zsCoefficientComplex U z s * actualComplexZsDysonTerm U z n s) i j‖ ≤
          (2 ^ (n + 1) / ((n + 1).factorial : ℝ)) * Q t ^ (n + 1)
      calc
        _ ≤ ∫ s in (0 : ℝ)..t, (2 * C) * (q s * Q s ^ n) := hstep
        _ = (2 * C) * (Q t ^ (n + 1) / (n + 1 : ℝ)) := by
          rw [intervalIntegral.integral_const_mul, hcum]
        _ = (2 ^ (n + 1) / ((n + 1).factorial : ℝ)) * Q t ^ (n + 1) := by
          dsimp [C]
          rw [hfactorial]
          have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
          have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
          field_simp [hn1, hfac]
          <;> ring

end NlsGge.SpectralFoundations
end
