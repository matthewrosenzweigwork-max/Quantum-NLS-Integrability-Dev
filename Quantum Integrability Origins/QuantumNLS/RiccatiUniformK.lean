import Mathlib
import QuantumNLS.RiccatiExpansions

/-!
# R-3FEAD88B stage (c-iv): uniformity over a compact `K ⊂ (0, ∞)`

Frozen inputs (read only): `RiccatiChargeLevels.bnd`, `bnd_rec` (the majorant recursion),
`RiccatiExpansions` (`remH`, `remQ`, `remR`, `remC`, `logB`, `logR`, `logC`, `physK`).

Content: every constant `remR`, `remC`, `logR`, `logC` is monotone in `|κ|` (with `β, δ` fixed,
`δ > 0`, `β ≥ 0`), because the majorant `bnd N` is monotone in `‖κ‖` and nonnegative. Hence on a
compact `K` with `|κ| ≤ k` the constants at any `κ ∈ K` are bounded by the constants at `k`.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology

namespace QuantumNLS.RiccatiUniformK

open QuantumNLS.RiccatiChargeLevels QuantumNLS.RiccatiExpansions QuantumNLS.RiccatiSobolevBanach

theorem bnd_zero_eq (L S : ℝ) (M : ℕ) (κ : ℂ) (ρ : ℝ) : bnd L S M κ ρ 0 = 0 := rfl

theorem bnd_one_eq (L S : ℝ) (M : ℕ) (κ : ℂ) (ρ : ℝ) : bnd L S M κ ρ 1 = ρ := by
  show hst 0 (valBnd L S M κ ρ) 1 1 = ρ
  rfl

/-- Nonnegativity of the majorant for `ρ ≥ 0`. -/
theorem bnd_nonneg (L S : ℝ) (M : ℕ) (κ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∀ N : ℕ, 0 ≤ bnd L S M κ ρ N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases N with _ | _ | n
    · rw [bnd_zero_eq]
    · rw [bnd_one_eq]
      exact hρ
    · rw [bnd_rec]
      have hS : 0 ≤ ∑ j ∈ Finset.Ico 1 (n + 1), bnd L S M κ ρ j * bnd L S M κ ρ (n + 1 - j) :=
        Finset.sum_nonneg fun j hj =>
          mul_nonneg (ih j (by simp only [Finset.mem_Ico] at hj; omega))
            (ih (n + 1 - j) (by simp only [Finset.mem_Ico] at hj; omega))
      exact add_nonneg (ih (n + 1) (by omega))
        (mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)) hρ) hS)

/-- Monotonicity of the majorant in `‖κ‖`, for `ρ ≥ 0`. -/
theorem bnd_mono (L S : ℝ) (M : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∀ N : ℕ, ∀ κ κ' : ℂ, ‖κ‖ ≤ ‖κ'‖ → bnd L S M κ ρ N ≤ bnd L S M κ' ρ N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro κ κ' hκ
    rcases N with _ | _ | n
    · rw [bnd_zero_eq, bnd_zero_eq]
    · rw [bnd_one_eq, bnd_one_eq]
    · rw [bnd_rec, bnd_rec]
      have hsum : ∑ j ∈ Finset.Ico 1 (n + 1), bnd L S M κ ρ j * bnd L S M κ ρ (n + 1 - j)
          ≤ ∑ j ∈ Finset.Ico 1 (n + 1), bnd L S M κ' ρ j * bnd L S M κ' ρ (n + 1 - j) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : j < n + 1 := by simp only [Finset.mem_Ico] at hj; omega
        exact mul_le_mul (ih j (by omega) κ κ' hκ) (ih (n + 1 - j) (by omega) κ κ' hκ)
          (bnd_nonneg L S M κ hρ _) (bnd_nonneg L S M κ' hρ _)
      have hS0 : 0 ≤ ∑ j ∈ Finset.Ico 1 (n + 1), bnd L S M κ ρ j * bnd L S M κ ρ (n + 1 - j) :=
        Finset.sum_nonneg fun j _ =>
          mul_nonneg (bnd_nonneg L S M κ hρ _) (bnd_nonneg L S M κ hρ _)
      have hcoef : ‖κ‖ * (Cmul L (lv S M (n + 2))) ^ 2 * ρ
          ≤ ‖κ'‖ * (Cmul L (lv S M (n + 2))) ^ 2 * ρ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hκ (sq_nonneg _)) hρ
      have hprod : ‖κ‖ * (Cmul L (lv S M (n + 2))) ^ 2 * ρ *
            ∑ j ∈ Finset.Ico 1 (n + 1), bnd L S M κ ρ j * bnd L S M κ ρ (n + 1 - j)
          ≤ ‖κ'‖ * (Cmul L (lv S M (n + 2))) ^ 2 * ρ *
            ∑ j ∈ Finset.Ico 1 (n + 1), bnd L S M κ' ρ j * bnd L S M κ' ρ (n + 1 - j) :=
        mul_le_mul hcoef hsum hS0 (mul_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)) hρ)
      exact add_le_add (ih (n + 1) (by omega) κ κ' hκ) hprod

/-- `|κ/L|` is monotone in `|κ|`. -/
theorem abs_div_mono {L κ κ' : ℝ} (hL : 0 < L) (h : |κ| ≤ |κ'|) : |κ / L| ≤ |κ' / L| := by
  rw [abs_div, abs_div, abs_of_pos hL]
  exact div_le_div_of_nonneg_right h hL.le

/-- `‖(κ : ℂ)‖ = |κ|`, monotone. -/
theorem norm_real_cast_mono {κ κ' : ℝ} (h : |κ| ≤ |κ'|) :
    ‖(κ : ℂ)‖ ≤ ‖(κ' : ℂ)‖ := by
  rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  exact h

/-- `remH` is monotone in `|κ|`. -/
theorem remH_mono (L a S : ℝ) (M : ℕ) (κ κ' β δ : ℝ) (hβ : 0 ≤ β) (hδ : 0 < δ)
    (h : |κ| ≤ |κ'|) :
    remH L a S M κ β δ ≤ remH L a S M κ' β δ := by
  unfold remH
  have hsum : ∑ N ∈ Finset.range (M + 1), bnd L S M (κ : ℂ) β N
      ≤ ∑ N ∈ Finset.range (M + 1), bnd L S M (κ' : ℂ) β N :=
    Finset.sum_le_sum fun N _ => bnd_mono L S M hβ N _ _ (norm_real_cast_mono h)
  have hA : 0 ≤ 2 * β / δ + ∑ N ∈ Finset.range (M + 1), bnd L S M (κ : ℂ) β N := by
    have h0 : 0 ≤ ∑ N ∈ Finset.range (M + 1), bnd L S M (κ : ℂ) β N :=
      Finset.sum_nonneg fun N _ => bnd_nonneg L S M (κ : ℂ) hβ N
    have h1 : 0 ≤ 2 * β / δ := div_nonneg (by linarith) hδ.le
    linarith
  have hc : 0 ≤ 4 * Cmul L a ^ 2 * β := mul_nonneg (by positivity) hβ
  have hcoef : 4 * |κ| * Cmul L a ^ 2 * β ≤ 4 * |κ'| * Cmul L a ^ 2 * β := by
    have := mul_le_mul_of_nonneg_left h hc
    linarith
  have hcoef0 : 0 ≤ 4 * |κ'| * Cmul L a ^ 2 * β := mul_nonneg (by positivity) hβ
  have hrhs : 2 * β / δ + ∑ N ∈ Finset.range (M + 1), bnd L S M (κ : ℂ) β N
      ≤ 2 * β / δ + ∑ N ∈ Finset.range (M + 1), bnd L S M (κ' : ℂ) β N := by linarith
  have hA' : 0 ≤ 2 * β / δ + ∑ N ∈ Finset.range (M + 1), bnd L S M (κ : ℂ) β N := hA
  exact mul_le_mul hcoef hrhs hA' hcoef0

/-- `remQ` is monotone in `|κ|`. -/
theorem remQ_mono (L a : ℝ) (κ κ' β : ℝ) (h : |κ| ≤ |κ'|) :
    remQ L a κ β ≤ remQ L a κ' β := by
  unfold remQ
  have hc : 0 ≤ 16 * Cmul L a ^ 2 * β ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left h hc
  linarith

theorem remR_mono (L a S : ℝ) (M : ℕ) (κ κ' β δ : ℝ) (hβ : 0 ≤ β) (hδ : 0 < δ)
    (h : |κ| ≤ |κ'|) :
    remR L a S M κ β δ ≤ remR L a S M κ' β δ := by
  unfold remR
  apply max_le_max le_rfl
  apply max_le_max
  · exact div_le_div_of_nonneg_right (remH_mono L a S M κ κ' β δ hβ hδ h) hδ.le
  · exact div_le_div_of_nonneg_right (remQ_mono L a κ κ' β h) (by positivity)

/-- `remC` is nonnegative. -/
theorem remC_nonneg (L a S : ℝ) (M : ℕ) (κ β δ : ℝ) (hβ : 0 ≤ β) (hδ : 0 < δ) :
    0 ≤ remC L a S M κ β δ := by
  unfold remC
  have hc : 0 ≤ Cmul L a := Real.sqrt_nonneg _
  have hcM : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hb : 0 ≤ bnd L S M (κ : ℂ) β M := bnd_nonneg L S M (κ : ℂ) hβ M
  have hsum0 : 0 ≤ ∑ N ∈ Finset.range (M + 1), bnd L S M (κ : ℂ) β N :=
    Finset.sum_nonneg fun N _ => bnd_nonneg L S M (κ : ℂ) hβ N
  have hY : 0 ≤ ‖(κ : ℂ)‖ * (Cmul L a * β) * ((M : ℝ) * ((M : ℝ) * (Cmul L a *
        (∑ N ∈ Finset.range (M + 1), bnd L S M (κ : ℂ) β N) ^ 2))) :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (mul_nonneg hc hβ))
      (mul_nonneg hcM (mul_nonneg hcM (mul_nonneg hc (sq_nonneg _))))
  exact div_nonneg (mul_nonneg (by norm_num) (add_nonneg hb hY)) hδ.le

/-- `remC` is monotone in `|κ|`. -/
theorem remC_mono (L a S : ℝ) (M : ℕ) (κ κ' β δ : ℝ) (hβ : 0 ≤ β) (hδ : 0 < δ)
    (h : |κ| ≤ |κ'|) :
    remC L a S M κ β δ ≤ remC L a S M κ' β δ := by
  unfold remC
  have hκ := norm_real_cast_mono h
  have hbM : bnd L S M (κ : ℂ) β M ≤ bnd L S M (κ' : ℂ) β M := bnd_mono L S M hβ M _ _ hκ
  have hsum : ∑ N ∈ Finset.range (M + 1), bnd L S M (κ : ℂ) β N
      ≤ ∑ N ∈ Finset.range (M + 1), bnd L S M (κ' : ℂ) β N :=
    Finset.sum_le_sum fun N _ => bnd_mono L S M hβ N _ _ hκ
  have hsum0 : 0 ≤ ∑ N ∈ Finset.range (M + 1), bnd L S M (κ : ℂ) β N :=
    Finset.sum_nonneg fun N _ => bnd_nonneg L S M (κ : ℂ) hβ N
  have hc : 0 ≤ Cmul L a := Real.sqrt_nonneg _
  have hcM : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hsq : (∑ N ∈ Finset.range (M + 1), bnd L S M (κ : ℂ) β N) ^ 2
      ≤ (∑ N ∈ Finset.range (M + 1), bnd L S M (κ' : ℂ) β N) ^ 2 :=
    pow_le_pow_left₀ hsum0 hsum 2
  have hT : ‖(κ : ℂ)‖ * (Cmul L a * β) * ((M : ℝ) * ((M : ℝ) * (Cmul L a *
        (∑ N ∈ Finset.range (M + 1), bnd L S M (κ : ℂ) β N) ^ 2)))
      ≤ ‖(κ' : ℂ)‖ * (Cmul L a * β) * ((M : ℝ) * ((M : ℝ) * (Cmul L a *
        (∑ N ∈ Finset.range (M + 1), bnd L S M (κ' : ℂ) β N) ^ 2))) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hκ (mul_nonneg hc hβ))
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsq hc) hcM) hcM)
      (mul_nonneg hcM (mul_nonneg hcM (mul_nonneg hc (sq_nonneg _))))
      (mul_nonneg (norm_nonneg _) (mul_nonneg hc hβ))
  have hbig : (bnd L S M (κ : ℂ) β M + ‖(κ : ℂ)‖ * (Cmul L a * β) * ((M : ℝ) * ((M : ℝ) *
        (Cmul L a * (∑ N ∈ Finset.range (M + 1), bnd L S M (κ : ℂ) β N) ^ 2))))
      ≤ bnd L S M (κ' : ℂ) β M + ‖(κ' : ℂ)‖ * (Cmul L a * β) * ((M : ℝ) * ((M : ℝ) *
        (Cmul L a * (∑ N ∈ Finset.range (M + 1), bnd L S M (κ' : ℂ) β N) ^ 2))) := by
    linarith
  exact div_le_div_of_nonneg_right (by linarith) hδ.le

/-- `logR` is monotone in `|κ|`. -/
theorem logR_mono (L a S : ℝ) (M : ℕ) (κ κ' β δ : ℝ) (ha : 0 ≤ a) (hL : 0 < L) (hβ : 0 ≤ β)
    (hδ : 0 < δ) (h : |κ| ≤ |κ'|) :
    logR L a S M κ β δ ≤ logR L a S M κ' β δ := by
  unfold logR
  have hpk : 0 ≤ physK L a := physK_nonneg ha
  have hB : 0 ≤ logB L a β δ := by
    unfold logB
    exact mul_nonneg (mul_nonneg hL.le (mul_nonneg hpk hβ))
      (mul_nonneg hpk (div_nonneg (by linarith) hδ.le))
  have hr := remR_mono L a S M (κ / L) (κ' / L) β δ hβ hδ (abs_div_mono hL h)
  have h2 : (2 * |κ| * logB L a β δ + Real.log 2) / (δ * L)
      ≤ (2 * |κ'| * logB L a β δ + Real.log 2) / (δ * L) :=
    div_le_div_of_nonneg_right (by linarith [mul_le_mul_of_nonneg_right h hB])
      (mul_pos hδ hL).le
  exact max_le_max hr (max_le_max le_rfl h2)

/-- `logC` is monotone in `|κ|`. -/
theorem logC_mono (L a S : ℝ) (M : ℕ) (κ κ' β δ : ℝ) (ha : 0 ≤ a) (hL : 0 < L) (hβ : 0 ≤ β)
    (hδ : 0 < δ) (h : |κ| ≤ |κ'|) :
    logC L a S M κ β δ ≤ logC L a S M κ' β δ := by
  unfold logC
  have hpk : 0 ≤ physK L a := physK_nonneg ha
  have hB : 0 ≤ logB L a β δ := by
    unfold logB
    exact mul_nonneg (mul_nonneg hL.le (mul_nonneg hpk hβ))
      (mul_nonneg hpk (div_nonneg (by linarith) hδ.le))
  have hR := remC_mono L a S M (κ / L) (κ' / L) β δ hβ hδ (abs_div_mono hL h)
  have hRn := remC_nonneg L a S M (κ / L) β δ hβ hδ
  have ht1 : |κ| * L * (physK L a * β) * (physK L a * remC L a S M (κ / L) β δ)
      ≤ |κ'| * L * (physK L a * β) * (physK L a * remC L a S M (κ' / L) β δ) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hL.le)
        (mul_nonneg hpk hβ))
      (mul_le_mul_of_nonneg_left hR hpk)
      (mul_nonneg hpk hRn)
      (mul_nonneg (mul_nonneg (abs_nonneg _) hL.le) (mul_nonneg hpk hβ))
  have hfac : 0 ≤ ((Nat.factorial (M + 1) : ℝ)) / (δ * L) ^ (M + 1) :=
    div_nonneg (Nat.cast_nonneg _) (pow_nonneg (mul_pos hδ hL).le _)
  have hexp : Real.exp (2 * |κ| * logB L a β δ) ≤ Real.exp (2 * |κ'| * logB L a β δ) :=
    Real.exp_le_exp.mpr (by linarith [mul_le_mul_of_nonneg_right h hB])
  have ht2 : 3 / 2 * Real.exp (2 * |κ| * logB L a β δ) * ((Nat.factorial (M + 1) : ℝ) / (δ * L) ^ (M + 1))
      ≤ 3 / 2 * Real.exp (2 * |κ'| * logB L a β δ) * ((Nat.factorial (M + 1) : ℝ) / (δ * L) ^ (M + 1)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by norm_num)) hfac
  exact add_le_add ht1 ht2

/-- A compact set of reals is bounded by some `k > 0` in absolute value. -/
theorem exists_abs_bound {K : Set ℝ} (hK : IsCompact K) :
    ∃ k : ℝ, 0 < k ∧ ∀ κ ∈ K, |κ| ≤ k := by
  obtain ⟨c, hc⟩ := isBounded_iff_forall_norm_le.1 hK.isBounded
  refine ⟨max c 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun κ hκ => ?_⟩
  have h1 := hc κ hκ
  rw [Real.norm_eq_abs] at h1
  exact h1.trans (le_max_left _ _)

end QuantumNLS.RiccatiUniformK

#print axioms QuantumNLS.RiccatiUniformK.bnd_mono
#print axioms QuantumNLS.RiccatiUniformK.remH_mono
#print axioms QuantumNLS.RiccatiUniformK.remR_mono
#print axioms QuantumNLS.RiccatiUniformK.remC_mono
#print axioms QuantumNLS.RiccatiUniformK.logR_mono
#print axioms QuantumNLS.RiccatiUniformK.logC_mono
#print axioms QuantumNLS.RiccatiUniformK.exists_abs_bound
