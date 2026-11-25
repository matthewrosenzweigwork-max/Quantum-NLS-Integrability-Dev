import QuantumNLS.CountFunctionsS01Dirac

/-!
# CountFunctionsS01Phase: regularized relative phases belong to the first-order class

PRINTED SOURCE `source-text/chapters/core/canonical_algebra.tex:56-57` (sha256 `b2a1e9c4…0395`):
```
If χ_a, χ_b are smooth and vanish near zero, the function f(x) = χ_a(x_a)χ_b(x_b)/√(x_a x_b), extended by zero near
the excluded faces, is smooth. Thus E^q_{N,ab} f(B_{N,J}) belongs to this class. Its symbol is χ_a(a_a)χ_b(a_b)ζ_ab.
At a fixed positive tested pair the cutoffs can equal one on neighborhoods of both actions, including vanishing cutoff
derivatives there. A cutoff approaching zero action with N is not asserted.
```
Proved here: `regPhase_c2` (the regularized phase function is `C²` on a neighborhood of the cube; indeed smooth),
`regPhaseExpr` (the expression `E^q_{N,ab} f(B_{N,J})` as an element of `Expr J`), `regPhase_cl` (its classical symbol is
`χ_a(a_a) χ_b(a_b) ζ_ab`, with `ζ_ab = z_a z̄_b/√(a_a a_b)`; at zero action both sides vanish, using the total division and
square-root conventions), and `cutoff_exists` (smooth cutoffs vanishing near zero and equal to one on a neighborhood of a
positive action).  Hence eq:dirac-main (`CountFunctionsS01Dirac.dynamic_dirac`) applies to every polynomial in these
regularized relative phases.  No acceptance claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open scoped ComplexConjugate
open QuantumNLS CountFunctionsS01Ops CountFunctionsS01Calc CountFunctionsS01Poisson CountFunctionsS01Class

namespace QuantumNLS.CountFunctionsS01Phase

variable {J : Finset ℤ}

/-- The regularized relative phase function `x ↦ χ_a(x_a) χ_b(x_b) / √(x_a x_b)` (zero where `x_a x_b ≤ 0`,
by the total square-root and division conventions). -/
def regPhase (a b : ↥J) (χa χb : ℝ → ℝ) : (↥J → ℝ) → ℂ :=
  fun x => ((χa (x a) * χb (x b) / Real.sqrt (x a * x b) : ℝ) : ℂ)

theorem regPhase_c2 (a b : ↥J) {χa χb : ℝ → ℝ} (ha : ContDiff ℝ 2 χa) (hb : ContDiff ℝ 2 χb) {δ : ℝ}
    (hδ : 0 < δ) (hza : ∀ x, |x| < δ → χa x = 0) (hzb : ∀ x, |x| < δ → χb x = 0) :
    C2Near J (regPhase a b χa χb) := by
  set U : Set (↥J → ℝ) := {x | -δ < x a ∧ -δ < x b} with hU
  have hUo : IsOpen U := by
    refine IsOpen.inter (isOpen_lt continuous_const (continuous_apply a))
      (isOpen_lt continuous_const (continuous_apply b))
  have hcU : cube J ⊆ U := fun x hx => ⟨by linarith [(hx a).1], by linarith [(hx b).1]⟩
  refine ⟨U, hUo, hcU, ?_⟩
  have hreal : ContDiffOn ℝ 2 (fun x : ↥J → ℝ => χa (x a) * χb (x b) / Real.sqrt (x a * x b)) U := by
    refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
    by_cases h1 : |x a| < δ
    · refine ⟨{y | |y a| < δ}, isOpen_lt (continuous_abs.comp (continuous_apply a)) continuous_const, h1, ?_⟩
      refine (contDiffOn_const (c := (0 : ℝ))).congr fun y hy => ?_
      have := hza (y a) hy.2
      simp [this]
    by_cases h2 : |x b| < δ
    · refine ⟨{y | |y b| < δ}, isOpen_lt (continuous_abs.comp (continuous_apply b)) continuous_const, h2, ?_⟩
      refine (contDiffOn_const (c := (0 : ℝ))).congr fun y hy => ?_
      have := hzb (y b) hy.2
      simp [this]
    · have hxa : δ ≤ x a := by
        have : δ ≤ |x a| := not_lt.1 h1
        rcases abs_cases (x a) with ⟨h, _⟩ | ⟨h, h'⟩
        · linarith
        · linarith [hx.1]
      have hxb : δ ≤ x b := by
        have : δ ≤ |x b| := not_lt.1 h2
        rcases abs_cases (x b) with ⟨h, _⟩ | ⟨h, h'⟩
        · linarith
        · linarith [hx.2]
      refine ⟨{y | 0 < y a ∧ 0 < y b},
        (isOpen_lt continuous_const (continuous_apply a)).inter (isOpen_lt continuous_const (continuous_apply b)),
        ⟨by linarith, by linarith⟩, ?_⟩
      have hA : ContDiff ℝ 2 (fun x : ↥J → ℝ => x a) := contDiff_apply ℝ ℝ a
      have hB : ContDiff ℝ 2 (fun x : ↥J → ℝ => x b) := contDiff_apply ℝ ℝ b
      have hnum : ContDiffOn ℝ 2 (fun x : ↥J → ℝ => χa (x a) * χb (x b)) (U ∩ {y | 0 < y a ∧ 0 < y b}) :=
        ((ha.comp hA).mul (hb.comp hB)).contDiffOn
      have hden : ContDiffOn ℝ 2 (fun x : ↥J → ℝ => Real.sqrt (x a * x b)) (U ∩ {y | 0 < y a ∧ 0 < y b}) :=
        ContDiffOn.sqrt ((hA.mul hB).contDiffOn) (fun y hy => (mul_pos hy.2.1 hy.2.2).ne')
      exact hnum.div hden (fun y hy => (Real.sqrt_pos.2 (mul_pos hy.2.1 hy.2.2)).ne')
  exact (Complex.ofRealCLM.contDiff.comp_contDiffOn hreal : _)

/-- The regularized relative phase `E^q_{N,ab} f(B_{N,J})` as an element of the first-order class. -/
def regPhaseExpr (a b : ↥J) {χa χb : ℝ → ℝ} (ha : ContDiff ℝ 2 χa) (hb : ContDiff ℝ 2 χb) {δ : ℝ} (hδ : 0 < δ)
    (hza : ∀ x, |x| < δ → χa x = 0) (hzb : ∀ x, |x| < δ → χb x = 0) : Expr J :=
  .mul (.gen a b) (.fn (regPhase a b χa χb) (regPhase_c2 a b ha hb hδ hza hzb))

/-- **The symbol of `E^q_{N,ab} f(B_{N,J})` is `χ_a(a_a) χ_b(a_b) ζ_ab`**, `ζ_ab = z_a z̄_b/√(a_a a_b)`,
`a_j = |z_j|²` (`canonical_algebra.tex:57`). -/
theorem regPhase_cl (a b : ↥J) {χa χb : ℝ → ℝ} (ha : ContDiff ℝ 2 χa) (hb : ContDiff ℝ 2 χb) {δ : ℝ}
    (hδ : 0 < δ) (hza : ∀ x, |x| < δ → χa x = 0) (hzb : ∀ x, |x| < δ → χb x = 0) (z : CPt J) :
    (regPhaseExpr a b ha hb hδ hza hzb).cl z =
      ((χa (‖z a‖ ^ 2) * χb (‖z b‖ ^ 2) : ℝ) : ℂ) *
        ((z a * conj (z b)) / ((Real.sqrt (‖z a‖ ^ 2 * ‖z b‖ ^ 2) : ℝ) : ℂ)) := by
  simp only [regPhaseExpr, Expr.cl, genF, cntF, regPhase, apt]
  push_cast
  ring

/-- Smooth cutoffs vanishing near zero and equal to one on a neighborhood of a positive action. -/
theorem cutoff_exists {α : ℝ} (hα : 0 < α) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ 2 χ ∧ (∀ x, |x| < α / 2 → χ x = 0) ∧ (∀ x, |x - α| ≤ α / 4 → χ x = 1) := by
  let f : ContDiffBump α := ⟨α / 4, α / 2, by positivity, by linarith⟩
  refine ⟨f, f.contDiff, fun x hx => ?_, fun x hx => ?_⟩
  · apply f.zero_of_le_dist
    show α / 2 ≤ dist x α
    rw [Real.dist_eq]
    rcases abs_lt.1 hx with ⟨h1, h2⟩
    rw [le_abs]
    right
    linarith
  · apply f.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq]
    exact hx

end QuantumNLS.CountFunctionsS01Phase
