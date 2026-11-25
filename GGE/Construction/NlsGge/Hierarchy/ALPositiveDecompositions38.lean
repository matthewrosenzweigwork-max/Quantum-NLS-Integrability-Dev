import Mathlib

/-! L04: positive decompositions of the discrete AL charges (`C:eq:Msplit`,
`C:eq:Hsplit`, `C:eq:Ksquares`, paper/v2.tex l.2068-2077; coefficients `D:eq:C12`,
l.1898-1902) and the continuum `C:eq:Q4` / `C:eq:V2positive` pointwise identities. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open Complex Finset

section Lattice

variable {L : ℕ} [NeZero L]

/-- `r_j = |α_j|²`. -/
def alR (α : ZMod L → ℂ) (j : ZMod L) : ℝ := ‖α j‖ ^ 2

/-- `M_d = -∑ log (1 - r_j)`. -/
def alMd (α : ZMod L → ℂ) : ℝ := -∑ j, Real.log (1 - alR α j)

/-- `C₁ = ∑ α_j conj α_{j-1}`. -/
def alC1 (α : ZMod L → ℂ) : ℂ := ∑ j, α j * (starRingEnd ℂ) (α (j - 1))

/-- `C₂ = ∑ α_j conj α_{j-2} (1 - r_{j-1}) - ½ ∑ (α_j conj α_{j-1})²`. -/
def alC2 (α : ZMod L → ℂ) : ℂ :=
  ∑ j, α j * (starRingEnd ℂ) (α (j - 2)) * (1 - (alR α (j - 1) : ℂ))
    - (1 / 2 : ℂ) * ∑ j, (α j * (starRingEnd ℂ) (α (j - 1))) ^ 2

/-- `H_d = 2 M_d - 2 Re C₁`. -/
def alHd (α : ZMod L → ℂ) : ℝ := 2 * alMd α - 2 * (alC1 α).re

/-- `K_d = 6 M_d - 8 Re C₁ + 2 Re C₂`. -/
def alKd (α : ZMod L → ℂ) : ℝ := 6 * alMd α - 8 * (alC1 α).re + 2 * (alC2 α).re

/-- `ℓ(r) = -log(1-r) - r`. -/
def alEll (r : ℝ) : ℝ := -Real.log (1 - r) - r

private def pp (α : ZMod L → ℂ) (j : ZMod L) : ℝ := (α j * (starRingEnd ℂ) (α (j - 1))).re
private def qq (α : ZMod L → ℂ) (j : ZMod L) : ℝ := (α j * (starRingEnd ℂ) (α (j - 1))).im
private def ss (α : ZMod L → ℂ) (j : ZMod L) : ℝ := (α j * (starRingEnd ℂ) (α (j - 2))).re

private lemma sum_shift_add (f : ZMod L → ℝ) : ∑ j, f (j + 1) = ∑ j, f j :=
  Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)

private lemma sum_shift_sub (f : ZMod L → ℝ) : ∑ j, f (j - 1) = ∑ j, f j :=
  Fintype.sum_equiv (Equiv.subRight 1) _ _ (fun _ => rfl)

private lemma alR_eq (α : ZMod L → ℂ) (j : ZMod L) :
    alR α j = (α j).re ^ 2 + (α j).im ^ 2 := by
  simp [alR, Complex.sq_norm, Complex.normSq_apply]; ring

private lemma pp_eq (α : ZMod L → ℂ) (j : ZMod L) :
    pp α j = (α j).re * (α (j-1)).re + (α j).im * (α (j-1)).im := by
  simp [pp]

private lemma qq_eq (α : ZMod L → ℂ) (j : ZMod L) :
    qq α j = (α j).im * (α (j-1)).re - (α j).re * (α (j-1)).im := by
  simp [qq]; ring

private lemma ss_eq (α : ZMod L → ℂ) (j : ZMod L) :
    ss α j = (α j).re * (α (j-2)).re + (α j).im * (α (j-2)).im := by
  simp [ss]

theorem alMd_split (α : ZMod L → ℂ) :
    alMd α = ∑ j, alR α j + ∑ j, alEll (alR α j) := by
  simp only [alMd, alEll, Finset.sum_sub_distrib, Finset.sum_neg_distrib]; ring

private lemma re_C1 (α : ZMod L → ℂ) : (alC1 α).re = ∑ j, pp α j := by
  simp [alC1, pp, Complex.re_sum]

private lemma re_C2 (α : ZMod L → ℂ) :
    (alC2 α).re = ∑ j, ss α j * (1 - alR α (j - 1))
      - (1 / 2) * ∑ j, (pp α j ^ 2 - qq α j ^ 2) := by
  have h1 : ∀ j, (α j * (starRingEnd ℂ) (α (j - 2)) * (1 - (alR α (j - 1) : ℂ))).re
      = ss α j * (1 - alR α (j - 1)) := by
    intro j
    have : (1 - (alR α (j - 1) : ℂ)) = ((1 - alR α (j - 1) : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.re_mul_ofReal]; rfl
  have h2 : ∀ j, ((α j * (starRingEnd ℂ) (α (j - 1))) ^ 2).re = pp α j ^ 2 - qq α j ^ 2 := by
    intro j; simp [pp, qq, sq]
  simp only [alC2, Complex.sub_re, Complex.re_sum, h1, h2]
  have : ((1 / 2 : ℂ) * ∑ j, (α j * (starRingEnd ℂ) (α (j - 1))) ^ 2).re
      = (1 / 2) * ∑ j, (pp α j ^ 2 - qq α j ^ 2) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul,
      Complex.re_sum]
    simp only [h2]
  rw [this]

theorem alHd_split (α : ZMod L → ℂ) :
    alHd α = ∑ j, ‖α j - α (j - 1)‖ ^ 2 + 2 * ∑ j, alEll (alR α j) := by
  have h : ∀ j, ‖α j - α (j - 1)‖ ^ 2 = alR α j + alR α (j - 1) - 2 * pp α j := by
    intro j
    simp only [Complex.sq_norm, Complex.normSq_apply, alR_eq, pp_eq]
    simp; ring
  simp only [h, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_shift_sub (alR α)]
  rw [alHd, alMd_split, re_C1]; ring

/-- `C:eq:Ksquares`. -/
theorem alKd_squares (α : ZMod L → ℂ) :
    alKd α = ∑ j, ‖α (j + 1) - 2 * α j + α (j - 1)‖ ^ 2
      + (3 / 2) * ∑ j, (alR α (j + 1) - alR α j) ^ 2
      + ∑ j, alR α j * ‖α (j + 1) - α (j - 1)‖ ^ 2
      + 2 * ∑ j, (qq α j) ^ 2
      + 6 * ∑ j, (-Real.log (1 - alR α j) - alR α j - (1 / 2) * alR α j ^ 2) := by
  -- pointwise expansions
  have hs : ∀ j : ZMod L, ss α (j + 1) = (α (j + 1)).re * (α (j - 1)).re
      + (α (j + 1)).im * (α (j - 1)).im := by
    intro j; rw [ss_eq]; rw [show j + 1 - 2 = j - 1 by ring]
  have hp : ∀ j : ZMod L, pp α (j + 1) = (α (j + 1)).re * (α j).re
      + (α (j + 1)).im * (α j).im := by
    intro j; rw [pp_eq]; rw [show j + 1 - 1 = j by ring]
  have h1 : ∀ j, ‖α (j + 1) - 2 * α j + α (j - 1)‖ ^ 2 =
      alR α (j + 1) + 4 * alR α j + alR α (j - 1) - 4 * pp α (j + 1)
        + 2 * ss α (j + 1) - 4 * pp α j := by
    intro j
    rw [hs, hp]
    simp only [Complex.sq_norm, Complex.normSq_apply, alR_eq, pp_eq]
    simp; ring
  have h3 : ∀ j, alR α j * ‖α (j + 1) - α (j - 1)‖ ^ 2 =
      alR α j * alR α (j + 1) + alR α j * alR α (j - 1) - 2 * (alR α j * ss α (j + 1)) := by
    intro j
    rw [hs]
    simp only [Complex.sq_norm, Complex.normSq_apply, alR_eq]
    simp; ring
  have h4 : ∀ j, 2 * qq α j ^ 2 = alR α j * alR α (j - 1) - (pp α j ^ 2 - qq α j ^ 2) := by
    intro j
    rw [qq_eq, pp_eq, alR_eq, alR_eq]; ring
  have h5 : ∀ j, (alR α (j + 1) - alR α j) ^ 2 =
      alR α (j + 1) ^ 2 + alR α j ^ 2 - 2 * (alR α j * alR α (j + 1)) := by
    intro j; ring
  -- shift facts
  have e1 := sum_shift_add (alR α)
  have e2 := sum_shift_sub (alR α)
  have e3 := sum_shift_add (pp α)
  have e4 := sum_shift_add (ss α)
  have e5 := sum_shift_add (fun j => alR α j ^ 2)
  have e6 := sum_shift_sub (fun j => alR α j * alR α (j + 1))
  have e7 := sum_shift_sub (fun j => alR α j * ss α (j + 1))
  have e8 := sum_shift_sub (fun j => alR α j * alR α (j - 1))
  simp only [show ∀ j : ZMod L, j - 1 + 1 = j from fun j => by ring] at e6 e7
  have hL : ∀ j : ZMod L, ss α j * (1 - alR α (j - 1)) = ss α j - ss α j * alR α (j - 1) := by
    intro j; ring
  have e9 : ∑ j, ss α j * alR α (j - 1) = ∑ j, alR α j * ss α (j + 1) := by
    rw [← sum_shift_add (fun j => ss α j * alR α (j - 1))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show j + 1 - 1 = j by ring]; ring
  have e10 : ∑ j, alR α j * alR α (j - 1) = ∑ j, alR α j * alR α (j + 1) := by
    rw [← sum_shift_add (fun j => alR α j * alR α (j - 1))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show j + 1 - 1 = j by ring]; ring
  have hlog : ∑ j, (-Real.log (1 - alR α j) - alR α j - (1 / 2) * alR α j ^ 2)
      = alMd α - ∑ j, alR α j - (1 / 2) * ∑ j, alR α j ^ 2 := by
    simp only [alMd, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  rw [alKd, re_C1, re_C2]
  simp only [h1, h3, h5, hL, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    hlog]
  have h4' : 2 * ∑ j, qq α j ^ 2 = ∑ j, alR α j * alR α (j - 1)
      - ∑ j, (pp α j ^ 2 - qq α j ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => h4 j)
  rw [Finset.sum_sub_distrib] at h4'
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at *
  rw [e9]
  linarith

theorem alEll_nonneg {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : 0 ≤ alEll r := by
  have := Real.log_le_sub_one_of_pos (show 0 < 1 - r by linarith)
  unfold alEll; linarith

theorem alEll_sq_nonneg {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    0 ≤ -Real.log (1 - r) - r - (1 / 2) * r ^ 2 := by
  have hab : |r| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one hab
  have := sum_le_hasSum (Finset.range 2)
    (fun i _ => by positivity) hs
  simp [Finset.sum_range_succ] at this
  linarith

private lemma alR_nonneg (α : ZMod L → ℂ) (j : ZMod L) : 0 ≤ alR α j := by
  unfold alR; positivity

theorem alR_lt_one (α : ZMod L → ℂ) (hα : ∀ j, ‖α j‖ < 1) (j : ZMod L) : alR α j < 1 := by
  have := hα j; have h0 := norm_nonneg (α j); unfold alR; nlinarith

theorem alMd_nonneg (α : ZMod L → ℂ) (hα : ∀ j, ‖α j‖ < 1) : 0 ≤ alMd α := by
  rw [alMd_split]
  exact add_nonneg (Finset.sum_nonneg fun j _ => alR_nonneg α j)
    (Finset.sum_nonneg fun j _ => alEll_nonneg (alR_nonneg α j) (alR_lt_one α hα j))

theorem alHd_nonneg (α : ZMod L → ℂ) (hα : ∀ j, ‖α j‖ < 1) : 0 ≤ alHd α := by
  rw [alHd_split]
  exact add_nonneg (Finset.sum_nonneg fun j _ => by positivity)
    (mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ =>
      alEll_nonneg (alR_nonneg α j) (alR_lt_one α hα j)))

theorem alKd_nonneg (α : ZMod L → ℂ) (hα : ∀ j, ‖α j‖ < 1) : 0 ≤ alKd α := by
  rw [alKd_squares]
  have hl : 0 ≤ ∑ j, (-Real.log (1 - alR α j) - alR α j - (1 / 2) * alR α j ^ 2) :=
    Finset.sum_nonneg fun j _ => alEll_sq_nonneg (alR_nonneg α j) (alR_lt_one α hα j)
  have a1 : 0 ≤ ∑ j, ‖α (j + 1) - 2 * α j + α (j - 1)‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => by positivity
  have a2 : 0 ≤ ∑ j, (alR α (j + 1) - alR α j) ^ 2 :=
    Finset.sum_nonneg fun j _ => by positivity
  have a3 : 0 ≤ ∑ j, alR α j * ‖α (j + 1) - α (j - 1)‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (alR_nonneg α j) (by positivity)
  have a4 : 0 ≤ ∑ j, (qq α j) ^ 2 := Finset.sum_nonneg fun j _ => by positivity
  linarith

end Lattice

section Continuum

/-- `C:eq:Q4`: the two forms of the integrand agree pointwise (`(|u|²)' = 2 Re(ū u')`). -/
theorem q4_integrand_eq (u u' u'' : ℂ) :
    ‖u''‖ ^ 2 + 2 * ‖u‖ ^ 6 + 8 * ‖u‖ ^ 2 * ‖u'‖ ^ 2
        + 2 * (u ^ 2 * (starRingEnd ℂ) u' ^ 2).re
      = ‖u''‖ ^ 2 + 2 * ‖u‖ ^ 6 + 6 * ‖u‖ ^ 2 * ‖u'‖ ^ 2
        + (2 * ((starRingEnd ℂ) u * u').re) ^ 2 := by
  have h6 : ‖u‖ ^ 6 = (‖u‖ ^ 2) ^ 3 := by ring
  simp only [Complex.sq_norm, Complex.normSq_apply, h6]
  simp [sq]; ring

/-- `C:eq:V2positive`: the integrand of `V₂` is pointwise nonnegative. -/
theorem V2_integrand_nonneg (β₁ β₂ : ℝ) (h1 : 0 ≤ β₁) (h2 : 0 ≤ β₂) (u u' : ℂ) :
    0 ≤ β₁ * ‖u‖ ^ 4 + β₂ * (2 * ‖u‖ ^ 6 + 6 * ‖u‖ ^ 2 * ‖u'‖ ^ 2
        + (2 * ((starRingEnd ℂ) u * u').re) ^ 2) := by
  positivity

end Continuum

end NlsGge.HierarchyRiccati.Core
