import Mathlib

/-! # Trunk C (generic), missing lemma M9: the action map is locally Lipschitz `ℓ² → ℓ¹`

Author: Claude Opus 5.5 (trunk C preparation).  Not self-reviewed, not accepted.
Namespace `NlsGge.ALLS.TransCPrep` (preparatory, non-approved `prep_` names).  Plan: PROOF_PLAN_TRUNK_C.md, M9:
`Σ ||z_n|² − |w_n|²| ≤ (‖z‖₂ + ‖w‖₂)‖z − w‖₂`.

English interpretation of the declarations.
* `prep_abs_normSq_sub_le (a b : ℂ)`: for all complex `a b`,
  `|‖a‖² − ‖b‖²| ≤ (‖a‖ + ‖b‖) ‖a − b‖` (pointwise version).
* `prep_action_l1_bound (z w : lp (fun _ : ℤ => ℂ) 2)`: for every two elements `z, w` of the genuine
  mathlib `ℓ²(ℤ; ℂ)` space, the family `n ↦ |‖z n‖² − ‖w n‖²|` is summable (so its `tsum` is the
  true sum, not a totalized junk value), and that sum is at most `(‖z‖ + ‖w‖) · ‖z − w‖`
  (all norms are the `ℓ²` norms).
* `prep_action_l1_bound_seq (z w : ℤ → ℂ) (hz hw)`: the same for plain sequences `z, w : ℤ → ℂ`
  whose squared moduli are summable (`hz`, `hw`), with the `ℓ²` norms written as
  `√(∑' n, ‖z n‖²)`, `√(∑' n, ‖w n‖²)`, `√(∑' n, ‖z n − w n‖²)`; the summability of
  `‖z n − w n‖²` is part of the conclusion, not an assumption.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.ALLS.TransCPrep

open scoped ENNReal

/-- Pointwise: `|‖a‖² − ‖b‖²| ≤ (‖a‖ + ‖b‖) ‖a − b‖`. -/
theorem prep_abs_normSq_sub_le (a b : ℂ) :
    |‖a‖ ^ 2 - ‖b‖ ^ 2| ≤ (‖a‖ + ‖b‖) * ‖a - b‖ := by
  have h1 : ‖a‖ ^ 2 - ‖b‖ ^ 2 = (‖a‖ + ‖b‖) * (‖a‖ - ‖b‖) := by ring
  rw [h1, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖a‖ + ‖b‖)]
  exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le a b) (by positivity)

theorem prep_holder_two_two : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
  rw [ENNReal.toReal_ofNat]
  exact Real.HolderConjugate.two_two

/-- **M9** (ℓ² form). -/
theorem prep_action_l1_bound (z w : lp (fun _ : ℤ => ℂ) 2) :
    Summable (fun n : ℤ => |‖(z : ℤ → ℂ) n‖ ^ 2 - ‖(w : ℤ → ℂ) n‖ ^ 2|) ∧
      ∑' n : ℤ, |‖(z : ℤ → ℂ) n‖ ^ 2 - ‖(w : ℤ → ℂ) n‖ ^ 2| ≤ (‖z‖ + ‖w‖) * ‖z - w‖ := by
  obtain ⟨hs1, hb1⟩ := lp.tsum_mul_le_mul_norm prep_holder_two_two z (z - w)
  obtain ⟨hs2, hb2⟩ := lp.tsum_mul_le_mul_norm prep_holder_two_two w (z - w)
  have hsub : ∀ n, ((z - w : lp (fun _ : ℤ => ℂ) 2) : ℤ → ℂ) n = (z : ℤ → ℂ) n - (w : ℤ → ℂ) n :=
    fun n => rfl
  simp only [hsub] at hs1 hb1 hs2 hb2
  have hdom : ∀ n : ℤ, |‖(z : ℤ → ℂ) n‖ ^ 2 - ‖(w : ℤ → ℂ) n‖ ^ 2| ≤
      ‖(z : ℤ → ℂ) n‖ * ‖(z : ℤ → ℂ) n - (w : ℤ → ℂ) n‖ +
        ‖(w : ℤ → ℂ) n‖ * ‖(z : ℤ → ℂ) n - (w : ℤ → ℂ) n‖ := by
    intro n
    have := prep_abs_normSq_sub_le ((z : ℤ → ℂ) n) ((w : ℤ → ℂ) n)
    linarith
  have hsum : Summable (fun n : ℤ => |‖(z : ℤ → ℂ) n‖ ^ 2 - ‖(w : ℤ → ℂ) n‖ ^ 2|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hdom (hs1.add hs2)
  refine ⟨hsum, ?_⟩
  calc ∑' n : ℤ, |‖(z : ℤ → ℂ) n‖ ^ 2 - ‖(w : ℤ → ℂ) n‖ ^ 2|
      ≤ ∑' n : ℤ, (‖(z : ℤ → ℂ) n‖ * ‖(z : ℤ → ℂ) n - (w : ℤ → ℂ) n‖ +
          ‖(w : ℤ → ℂ) n‖ * ‖(z : ℤ → ℂ) n - (w : ℤ → ℂ) n‖) :=
        hsum.tsum_le_tsum hdom (hs1.add hs2)
    _ = ∑' n : ℤ, ‖(z : ℤ → ℂ) n‖ * ‖(z : ℤ → ℂ) n - (w : ℤ → ℂ) n‖ +
          ∑' n : ℤ, ‖(w : ℤ → ℂ) n‖ * ‖(z : ℤ → ℂ) n - (w : ℤ → ℂ) n‖ := hs1.tsum_add hs2
    _ ≤ ‖z‖ * ‖z - w‖ + ‖w‖ * ‖z - w‖ := add_le_add hb1 hb2
    _ = (‖z‖ + ‖w‖) * ‖z - w‖ := by ring

theorem prep_memℓp_two_of_summable_sq (z : ℤ → ℂ) (hz : Summable fun n => ‖z n‖ ^ 2) :
    Memℓp z 2 := by
  refine memℓp_gen ?_
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hz

theorem prep_lp_two_norm_eq_sqrt (z : lp (fun _ : ℤ => ℂ) 2) :
    ‖z‖ = Real.sqrt (∑' n : ℤ, ‖(z : ℤ → ℂ) n‖ ^ 2) := by
  have h := (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) z).tsum_eq
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [h, Real.sqrt_sq (norm_nonneg _)]

/-- **M9** (sequence form). -/
theorem prep_action_l1_bound_seq (z w : ℤ → ℂ) (hz : Summable fun n => ‖z n‖ ^ 2)
    (hw : Summable fun n => ‖w n‖ ^ 2) :
    Summable (fun n : ℤ => ‖z n - w n‖ ^ 2) ∧
    Summable (fun n : ℤ => |‖z n‖ ^ 2 - ‖w n‖ ^ 2|) ∧
      ∑' n : ℤ, |‖z n‖ ^ 2 - ‖w n‖ ^ 2| ≤
        (Real.sqrt (∑' n : ℤ, ‖z n‖ ^ 2) + Real.sqrt (∑' n : ℤ, ‖w n‖ ^ 2)) *
          Real.sqrt (∑' n : ℤ, ‖z n - w n‖ ^ 2) := by
  let Z : lp (fun _ : ℤ => ℂ) 2 := ⟨z, prep_memℓp_two_of_summable_sq z hz⟩
  let W : lp (fun _ : ℤ => ℂ) 2 := ⟨w, prep_memℓp_two_of_summable_sq w hw⟩
  have hD : Summable (fun n : ℤ => ‖z n - w n‖ ^ 2) := by
    have h := (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (Z - W)).summable
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
    exact h
  obtain ⟨h1, h2⟩ := prep_action_l1_bound Z W
  refine ⟨hD, h1, ?_⟩
  have eZ := prep_lp_two_norm_eq_sqrt Z
  have eW := prep_lp_two_norm_eq_sqrt W
  have eD := prep_lp_two_norm_eq_sqrt (Z - W)
  rw [eZ, eW, eD] at h2
  exact h2

end NlsGge.ALLS.TransCPrep
