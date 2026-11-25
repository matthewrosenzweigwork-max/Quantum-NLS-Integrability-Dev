import Mathlib.Basic.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace NlsGge.Schur

/-- Strict monotonicity of `F - β` and `F + β` on `[a,b]` (lower slope `1 - 2d > 0`). -/
theorem gapCenter_shifted_strictMonoOn38V1 (a b d : ℝ) (F β : ℝ → ℝ)
    (hd0 : 0 ≤ d) (hd : d ≤ 1/4)
    (hFinc : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x ≤ y → (1 - d) * (y - x) ≤ F y - F x)
    (hβlip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |β y - β x| ≤ d * |y - x|) :
    StrictMonoOn (fun x => F x - β x) (Set.Icc a b) ∧
      StrictMonoOn (fun x => F x + β x) (Set.Icc a b) := by
  have key : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x < y →
      d * (y - x) ≥ |β y - β x| := by
    intro x hx y hy hxy
    have := hβlip x hx y hy
    rwa [abs_of_pos (sub_pos.mpr hxy)] at this
  constructor
  · intro x hx y hy hxy
    have h1 := hFinc x hx y hy hxy.le
    have h2 := key x hx y hy hxy
    have h3 := (abs_le.mp h2).2
    have h4 : 0 < y - x := sub_pos.mpr hxy
    show F x - β x < F y - β y
    nlinarith
  · intro x hx y hy hxy
    have h1 := hFinc x hx y hy hxy.le
    have h2 := key x hx y hy hxy
    have h3 := (abs_le.mp h2).1
    have h4 : 0 < y - x := sub_pos.mpr hxy
    show F x + β x < F y + β y
    nlinarith

/-- Comparison of the gap endpoints with the center `σ`. -/
theorem gapCenter_comparison38V1 (a b d σ lm lp : ℝ) (F β : ℝ → ℝ)
    (hd0 : 0 ≤ d) (hd : d ≤ 1/4)
    (hσ : σ ∈ Set.Icc a b) (hlm : lm ∈ Set.Icc a b) (hlp : lp ∈ Set.Icc a b)
    (hFinc : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x ≤ y → (1 - d) * (y - x) ≤ F y - F x)
    (hFlip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x ≤ y → F y - F x ≤ (1 + d) * (y - x))
    (hβlip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |β y - β x| ≤ d * |y - x|)
    (hβ0 : ∀ x ∈ Set.Icc a b, 0 ≤ β x)
    (hFσ : F σ = 0) (hp : F lp - β lp = 0) (hm : F lm + β lm = 0) :
    lm ≤ σ ∧ σ ≤ lp ∧ β σ ≤ (1 + 2 * d) * (lp - σ) ∧ β σ ≤ (1 + 2 * d) * (σ - lm) ∧
      2 * β σ / (1 + 2 * d) ≤ lp - lm := by
  have hβp := hβ0 lp hlp
  have hβm := hβ0 lm hlm
  have hσp : σ ≤ lp := by
    by_contra h
    have h := not_le.mp h
    have := hFinc lp hlp σ hσ h.le
    nlinarith
  have hmσ : lm ≤ σ := by
    by_contra h
    have h := not_le.mp h
    have := hFinc σ hσ lm hlm h.le
    nlinarith
  have h3 : β σ ≤ (1 + 2 * d) * (lp - σ) := by
    have h1 := hβlip σ hσ lp hlp
    rw [abs_of_nonneg (sub_nonneg.mpr hσp)] at h1
    have h2 := (abs_le.mp h1).1
    have h5 := hFlip σ hσ lp hlp hσp
    nlinarith
  have h4 : β σ ≤ (1 + 2 * d) * (σ - lm) := by
    have h1 := hβlip lm hlm σ hσ
    rw [abs_of_nonneg (sub_nonneg.mpr hmσ)] at h1
    have h2 := (abs_le.mp h1).2
    have h5 := hFlip lm hlm σ hσ hmσ
    nlinarith
  refine ⟨hmσ, hσp, h3, h4, ?_⟩
  have hpos : 0 < 1 + 2 * d := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith

end NlsGge.Schur
