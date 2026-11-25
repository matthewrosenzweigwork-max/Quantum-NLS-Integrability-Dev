import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
/-! Concrete W02 prerequisites. Targets independently source-reviewed; actual
convergence/moment identities and factorial bounds are proved from pinned inputs. -/
set_option autoImplicit false
noncomputable section
namespace NlsGge.Weights

lemma factorial_stirling_bounds (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (2 * Real.pi) * Real.sqrt (n : ℝ) *
        ((n : ℝ) / Real.exp 1)^n ≤ (Nat.factorial n : ℝ) ∧
      (Nat.factorial n : ℝ) ≤
        Real.exp 1 * Real.sqrt (n : ℝ) * ((n : ℝ) / Real.exp 1)^n := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  constructor
  · simpa only [Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ) * Real.pi)] using
      Stirling.le_factorial_stirling n
  · have hs : Stirling.stirlingSeq n ≤ Real.exp 1 / Real.sqrt 2 := by
      have h := Stirling.stirlingSeq'_antitone (Nat.zero_le (n-1))
      simpa only [Function.comp_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hn, Nat.zero_add,
        Stirling.stirlingSeq_one] using h
    have hd : 0 < Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1)^n := by positivity
    unfold Stirling.stirlingSeq at hs
    have hfac := (div_le_iff₀ hd).mp hs
    calc
      (Nat.factorial n : ℝ) ≤ (Real.exp 1 / Real.sqrt 2) *
          (Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1)^n) := hfac
      _ = Real.exp 1 * Real.sqrt (n : ℝ) * ((n : ℝ) / Real.exp 1)^n := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        field_simp
        <;> ring

end NlsGge.Weights
