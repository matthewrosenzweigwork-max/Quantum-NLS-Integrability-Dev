import Mathlib

/-! # Track B, step B1: the Japanese bracket `⟨r⟩ = √(1 + r²)`

Elementary facts about the bracket used in the nonendpoint spacetime estimates of the
all-real-`s` NLS plan (Pro report, section "The genuine PDE bridge", equations
(timeconv) and (latticesum)). Nothing here depends on the NLS model; these are standalone
real-variable lemmas. Negative powers are taken with `Real.rpow`, always of the strictly
positive number `⟨r⟩`, so no totalized branch of `rpow` is used.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

/-- The Japanese bracket `⟨r⟩ = √(1 + r²)` of a real number. -/
def brk (r : ℝ) : ℝ := Real.sqrt (1 + r ^ 2)

/-- `⟨r⟩` is strictly positive. -/
theorem brk_pos (r : ℝ) : 0 < brk r := Real.sqrt_pos.2 (by positivity)

/-- `⟨r⟩ ≥ 1`. -/
theorem one_le_brk (r : ℝ) : 1 ≤ brk r := by
  unfold brk
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (1 + r ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg r])

/-- `|r| ≤ ⟨r⟩`. -/
theorem abs_le_brk (r : ℝ) : |r| ≤ brk r := by
  unfold brk
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by linarith)

/-- The square of the bracket. -/
theorem brk_sq (r : ℝ) : brk r ^ 2 = 1 + r ^ 2 := by
  unfold brk
  rw [Real.sq_sqrt (by positivity)]

/-- `⟨-r⟩ = ⟨r⟩`. -/
theorem brk_neg (r : ℝ) : brk (-r) = brk r := by
  unfold brk
  rw [neg_sq]

/-- The bracket is monotone in the absolute value. -/
theorem brk_le_brk {r s : ℝ} (h : |r| ≤ |s|) : brk r ≤ brk s := by
  unfold brk
  apply Real.sqrt_le_sqrt
  have h2 : |r| ^ 2 ≤ |s| ^ 2 := pow_le_pow_left₀ (abs_nonneg r) h 2
  rw [sq_abs, sq_abs] at h2
  linarith

/-- Negative powers of the bracket are antitone in the absolute value. -/
theorem brk_rpow_neg_le {r s : ℝ} {p : ℝ} (hp : 0 ≤ p) (h : |r| ≤ |s|) :
    brk s ^ (-p) ≤ brk r ^ (-p) :=
  Real.rpow_le_rpow_of_nonpos (brk_pos r) (brk_le_brk h) (by linarith)

/-- Negative powers of the bracket are nonnegative. -/
theorem brk_rpow_nonneg (r p : ℝ) : 0 ≤ brk r ^ p := Real.rpow_nonneg (brk_pos r).le p

/-- Negative powers of the bracket are at most one. -/
theorem brk_rpow_neg_le_one (r : ℝ) {p : ℝ} (hp : 0 ≤ p) : brk r ^ (-p) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (one_le_brk r) (by linarith)

/-- Comparison with a pure power: for `x > 0` with `x ≤ ⟨r⟩`, `⟨r⟩^{-p} ≤ x^{-p}` (`p ≥ 0`). -/
theorem brk_rpow_neg_le_of_le {r x p : ℝ} (hx : 0 < x) (hxr : x ≤ brk r) (hp : 0 ≤ p) :
    brk r ^ (-p) ≤ x ^ (-p) :=
  Real.rpow_le_rpow_of_nonpos hx hxr (by linarith)

end LiebLiniger.FixedPeriod.ALLS.PdeB
