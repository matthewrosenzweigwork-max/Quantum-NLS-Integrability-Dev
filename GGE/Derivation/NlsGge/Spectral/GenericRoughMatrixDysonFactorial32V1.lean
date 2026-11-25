import NlsGge.Spectral.ActualPhysicalL2ZsDysonFactorialBoundV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open CumulativePowerV3 CumulativePowerGeneralEndpointV1
/-- Actual left-ordered matrix Picard iterates for an arbitrary integrable coefficient.
This generic infrastructure is not a replacement for the concrete NLS equation. -/
def genericRoughMatrixDysonTerm32
    (B : ℝ → Matrix (Fin 2) (Fin 2) ℂ) : ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℂ
  | 0, _ => 1
  | n + 1, t => fun i j => ∫ s in (0 : ℝ)..t, (B s * genericRoughMatrixDysonTerm32 B n s) i j

/-- The factorial bound uses exactly an integrable nonnegative majorant of the
actual coefficient. Its later application must realize these conditions for B. -/
theorem genericRoughMatrixDysonTerm_factorial_bound32
    (B : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (q : ℝ → ℝ) (T : ℝ)
    (hq : IntervalIntegrable q volume 0 T) (hqpos : ∀ s, 0 ≤ q s)
    (hmajorant : ∀ s ∈ Set.Icc (0 : ℝ) T, actualComplexMatrixEntrySup (B s) ≤ q s) :
    ∀ (n : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T → ∀ i j : Fin 2,
      ‖genericRoughMatrixDysonTerm32 B n t i j‖ ≤
        (2 ^ n / (n.factorial : ℝ)) * actualCumulativeRealIntegral q t ^ n := by
  let Q : ℝ → ℝ := actualCumulativeRealIntegral q
  intro n
  induction n with
  | zero =>
      intro t ht i j
      by_cases hij : i = j <;>
        simp [genericRoughMatrixDysonTerm32, Matrix.one_apply, hij]
  | succ n ih =>
      intro t ht i j
      let C : ℝ := 2 ^ n / (n.factorial : ℝ)
      have hC : 0 ≤ C := by dsimp [C]; positivity
      have hB (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) t) :
          actualComplexMatrixEntrySup (genericRoughMatrixDysonTerm32 B n s) ≤ C * Q s ^ n := by
        have hs2 : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
        unfold actualComplexMatrixEntrySup
        exact max_le (max_le (ih s hs2 0 0) (ih s hs2 0 1))
          (max_le (ih s hs2 1 0) (ih s hs2 1 1))
      have hnorm (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) t) :
          ‖(B s * genericRoughMatrixDysonTerm32 B n s) i j‖ ≤
            (2 * C) * (q s * Q s ^ n) := by
        have hA : actualComplexMatrixEntrySup (B s) ≤ q s :=
          hmajorant s ⟨hs.1, hs.2.trans ht.2⟩
        have hBpos : 0 ≤ actualComplexMatrixEntrySup (genericRoughMatrixDysonTerm32 B n s) :=
          (norm_nonneg _).trans (norm_entry_le_actualComplexMatrixEntrySup _ 0 0)
        calc
          ‖(B s * genericRoughMatrixDysonTerm32 B n s) i j‖ ≤
              actualComplexMatrixEntrySup
                (B s * genericRoughMatrixDysonTerm32 B n s) :=
            norm_entry_le_actualComplexMatrixEntrySup _ i j
          _ ≤ 2 * actualComplexMatrixEntrySup (B s) *
              actualComplexMatrixEntrySup (genericRoughMatrixDysonTerm32 B n s) :=
            actualComplexMatrixEntrySup_mul_le _ _
          _ ≤ 2 * q s * (C * Q s ^ n) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hA (by norm_num))
              (hB s hs) hBpos (mul_nonneg (by norm_num) (hqpos s))
          _ = (2 * C) * (q s * Q s ^ n) := by ring
      have hint : IntervalIntegrable (fun s => (2 * C) * (q s * Q s ^ n)) volume 0 t :=
        (intervalIntegrable_cumulativePower q T hq n t ht.1 ht.2).const_mul (2 * C)
      have hstep := intervalIntegral.norm_integral_le_of_norm_le ht.1
        (Filter.Eventually.of_forall (fun s (hs : s ∈ Set.Ioc (0 : ℝ) t) =>
          hnorm s ⟨le_of_lt hs.1, hs.2⟩)) hint
      have hcum := intervalIntegral_cumulativePower_eq q T hq n t ht.1 ht.2
      have hfactorial : ((n + 1).factorial : ℝ) =
          (n + 1 : ℝ) * (n.factorial : ℝ) := by
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
      change ‖∫ s in (0 : ℝ)..t,
        (B s * genericRoughMatrixDysonTerm32 B n s) i j‖ ≤
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
