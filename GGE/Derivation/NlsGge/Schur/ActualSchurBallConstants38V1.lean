import NlsGge.Weights.Entire
import NlsGge.Definitions.PilotInterfaces
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# NEW-F05: low-mode constant arithmetic (source line 1307)

For admitted coefficients `c ∈ [c₋, c₊]`, `a_n = W(2πn)` satisfies
`log a_n ≤ log c₊ + 4√(2π|n|)` (`weight_upper`).  For `R ≥ 1`, `A ≥ 1`, `M ≤ A R^6 + 1`
and any family of at most `2M+1` modes with `|n| ≤ M`,
`∏ R² a_n ≤ exp(C (1+R)^9)` with `C` depending only on `A`, `c₊`.
-/

set_option autoImplicit false
noncomputable section
open NlsGge.Pilot

namespace NlsGge.Schur

/-- The explicit constant. -/
def ballLowConstant38 (A cp : ℝ) : ℝ :=
  (2 * A + 3) * (2 + |Real.log cp| + 4 * Real.sqrt (2 * Real.pi * (A + 1)))

theorem ballLowConstant38_nonneg (A cp : ℝ) (hA : 0 ≤ A) : 0 ≤ ballLowConstant38 A cp := by
  unfold ballLowConstant38; positivity

theorem ballLowProduct_le38 {ι : Type*} (cm cp : ℝ) (c : ℕ → ℝ)
    (hadm : AdmittedCoefficients cm cp c) (A R : ℝ) (hA : 1 ≤ A) (hR : 1 ≤ R) (M : ℕ)
    (hM : (M : ℝ) ≤ A * R ^ 6 + 1) (s : Finset ι) (n : ι → ℤ)
    (hn : ∀ i ∈ s, |n i| ≤ (M : ℤ)) (hcard : (s.card : ℝ) ≤ 2 * M + 1) :
    ∏ i ∈ s, (R ^ 2 * NlsGge.Weights.weight c (2 * Real.pi * (n i : ℝ))) ≤
      Real.exp (ballLowConstant38 A cp * (1 + R) ^ 9) := by
  obtain ⟨hcm, hcmp, hcb⟩ := hadm
  have hcp : 0 < cp := lt_of_lt_of_le hcm hcmp
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hpi : 0 < Real.pi := Real.pi_pos
  -- per-factor bound
  set K : ℝ := 2 * Real.log R + |Real.log cp| + 4 * Real.sqrt (2 * Real.pi * M) with hK
  have hfac : ∀ i ∈ s, R ^ 2 * NlsGge.Weights.weight c (2 * Real.pi * (n i : ℝ)) ≤
      Real.exp K := by
    intro i hi
    have hw := NlsGge.Weights.weight_upper cm cp c hcm (fun j => (hcb j).1) (fun j => (hcb j).2)
      (2 * Real.pi * (n i : ℝ))
    have hni : |(n i : ℝ)| ≤ M := by exact_mod_cast hn i hi
    have habs : |2 * Real.pi * (n i : ℝ)| ≤ 2 * Real.pi * M := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
      exact mul_le_mul_of_nonneg_left hni (by positivity)
    have hsq : Real.sqrt |2 * Real.pi * (n i : ℝ)| ≤ Real.sqrt (2 * Real.pi * M) :=
      Real.sqrt_le_sqrt habs
    have hcpl : cp ≤ Real.exp |Real.log cp| := by
      calc cp = Real.exp (Real.log cp) := (Real.exp_log hcp).symm
        _ ≤ Real.exp |Real.log cp| := Real.exp_le_exp.mpr (le_abs_self _)
    have hR2 : R ^ 2 = Real.exp (2 * Real.log R) := by
      rw [← Real.exp_log (by positivity : (0:ℝ) < R ^ 2), Real.log_pow]; push_cast; ring_nf
    calc R ^ 2 * NlsGge.Weights.weight c (2 * Real.pi * (n i : ℝ))
        ≤ R ^ 2 * (cp * Real.exp (4 * Real.sqrt |2 * Real.pi * (n i : ℝ)|)) :=
          mul_le_mul_of_nonneg_left hw (by positivity)
      _ = Real.exp (2 * Real.log R) * (cp * Real.exp (4 * Real.sqrt |2 * Real.pi * (n i : ℝ)|)) := by
          rw [hR2]
      _ ≤ Real.exp (2 * Real.log R) * (Real.exp |Real.log cp| *
            Real.exp (4 * Real.sqrt (2 * Real.pi * M))) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact mul_le_mul hcpl (Real.exp_le_exp.mpr (by linarith [hsq])) (Real.exp_pos _).le
            (Real.exp_pos _).le
      _ = Real.exp K := by
          rw [hK, ← Real.exp_add, ← Real.exp_add]; ring_nf
  have hK0 : 0 ≤ K := by
    have : 0 ≤ Real.log R := Real.log_nonneg hR
    positivity
  have hprod : ∏ i ∈ s, (R ^ 2 * NlsGge.Weights.weight c (2 * Real.pi * (n i : ℝ))) ≤
      Real.exp K ^ s.card := by
    calc _ ≤ ∏ _i ∈ s, Real.exp K := by
          apply Finset.prod_le_prod₀
          · intro i hi
            have := NlsGge.Weights.weight_pos cm cp c hcm (fun j => (hcb j).1)
              (fun j => (hcb j).2) (2 * Real.pi * (n i : ℝ))
            positivity
          · exact hfac
      _ = Real.exp K ^ s.card := by simp
  rw [← Real.exp_nat_mul] at hprod
  refine le_trans hprod (Real.exp_le_exp.mpr ?_)
  -- arithmetic: card * K ≤ C (1+R)^9
  have hlogR : Real.log R ≤ R := by
    have := Real.log_le_sub_one_of_pos hR0; linarith
  have hM1 : (M : ℝ) ≤ (A + 1) * R ^ 6 := by
    have : (1 : ℝ) ≤ R ^ 6 := one_le_pow₀ hR
    nlinarith
  have hR6 : Real.sqrt (R ^ 6) = R ^ 3 := by
    rw [show R ^ 6 = (R ^ 3) ^ 2 by ring]; exact Real.sqrt_sq (by positivity)
  have hsqM : Real.sqrt (2 * Real.pi * M) ≤ Real.sqrt (2 * Real.pi * (A + 1)) * R ^ 3 := by
    calc Real.sqrt (2 * Real.pi * M) ≤ Real.sqrt (2 * Real.pi * (A + 1) * R ^ 6) := by
          apply Real.sqrt_le_sqrt
          have := mul_le_mul_of_nonneg_left hM1 (by positivity : (0:ℝ) ≤ 2 * Real.pi)
          linarith
      _ = Real.sqrt (2 * Real.pi * (A + 1)) * R ^ 3 := by
          rw [Real.sqrt_mul (by positivity), hR6]
  set S := Real.sqrt (2 * Real.pi * (A + 1)) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hcard' : (s.card : ℝ) ≤ (2 * A + 3) * R ^ 6 := by
    have h6 : (1 : ℝ) ≤ R ^ 6 := one_le_pow₀ hR
    have := mul_le_mul_of_nonneg_left h6 (by norm_num : (0:ℝ) ≤ 3)
    linarith
  have hKb : K ≤ (2 + |Real.log cp| + 4 * S) * R ^ 3 := by
    have h3 : (1 : ℝ) ≤ R ^ 3 := one_le_pow₀ hR
    have hR3 : R ≤ R ^ 3 := by
      have h2 : (1 : ℝ) ≤ R ^ 2 := one_le_pow₀ hR
      have := mul_le_mul_of_nonneg_left h2 hR0.le
      calc R = R * 1 := by ring
        _ ≤ R * R ^ 2 := this
        _ = R ^ 3 := by ring
    have habs0 : 0 ≤ |Real.log cp| := abs_nonneg _
    rw [hK]
    nlinarith
  have hR9 : R ^ 9 ≤ (1 + R) ^ 9 := pow_le_pow_left₀ hR0.le (by linarith) 9
  have hK0' : 0 ≤ (2 + |Real.log cp| + 4 * S) := by positivity
  calc (s.card : ℝ) * K ≤ ((2 * A + 3) * R ^ 6) * ((2 + |Real.log cp| + 4 * S) * R ^ 3) := by
        apply mul_le_mul hcard' hKb hK0 (by positivity)
    _ = ballLowConstant38 A cp * R ^ 9 := by unfold ballLowConstant38; rw [← hS]; ring
    _ ≤ ballLowConstant38 A cp * (1 + R) ^ 9 :=
        mul_le_mul_of_nonneg_left hR9 (ballLowConstant38_nonneg A cp (by linarith))

end NlsGge.Schur
