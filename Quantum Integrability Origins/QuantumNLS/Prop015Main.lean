import QuantumNLS.Interpolation

/-!
# PROP-015 main packaging: `Q7A:lem:interp` as one named theorem

Source: `source-text/chapters/propagation/window_reconstruction.tex:57`, label `Q7A:lem:interp`,
`\ReportID{PROP-015}`.

This module imports the frozen `QuantumNLS.Interpolation` (sha256 `69351dac…`) and does not edit it.
No hypothesis is added beyond those printed: distinct nodes `zs` (injectivity), fixed `H`, `H1`.

Clause correspondence:
* Identity clause (printed eq. `Q7A:eq:interp`): conjunct 1. It is quantified over all complex
  `q`, `z` with `zs j ≠ q` and `z ≠ q`, outside every large-`R` assumption. Proof:
  `QuantumNLS.Interpolation.cauchy_remainder`.
* Bound clause: conjunct 2. The constants `C` and `R0` depend only on `m`, `H`, `H1` and are
  chosen before the moving quantities `q`, `z`, `a`, `R`. Proof:
  `QuantumNLS.Interpolation.cauchy_remainder_bound`, with `C = 2^(m+2) (H+H1)^(m+1)` and
  `R0 = max 1 (max (2H) (2H1))`. The printed `C R^(-m-2)` is `C / R^(m+2)` for `R > 0`.
* Complex centre to real centre: the printed centre is a real `a ≥ 2R`. Specialise the complex
  centre `a` to `(a_real : ℂ)`. Then `‖(a_real : ℂ)‖ = |a_real| ≥ a_real ≥ 2R`, so the
  complex-centre hypothesis `2R ≤ ‖a‖` holds, and the printed real-centre bound is a special case.
-/

namespace QuantumNLS.Prop015Main

open Finset
open QuantumNLS.Interpolation

/-- PROP-015 (`Q7A:lem:interp`): the Cauchy-kernel Lagrange remainder, both printed clauses.
Identity outside the large-`R` assumptions; constants `C`, `R0` depend only on `m`, `H`, `H1`
and precede all moving quantities. -/
theorem interpolation_lemma {m : ℕ} (zs : Fin (m + 1) → ℂ)
    (hz : Function.Injective zs) (H H1 : ℝ) :
    (∀ q z : ℂ, (∀ j, zs j ≠ q) → z ≠ q →
      1 / (z - q) - ∑ j, lagrangeValue zs j z / (zs j - q) =
        (-1) ^ (m + 1) * (∏ j, (z - zs j)) / ((z - q) * ∏ j, (zs j - q))) ∧
    (∃ C R0 : ℝ, ∀ (q z a : ℂ) (R : ℝ), R0 ≤ R →
      ‖z - a‖ ≤ H → (∀ j, ‖zs j - a‖ ≤ H1) → ‖q‖ ≤ R → 2 * R ≤ ‖a‖ →
      ‖(-1 : ℂ) ^ (m + 1) * (∏ j, (z - zs j)) / ((z - q) * ∏ j, (zs j - q))‖
        ≤ C / R ^ (m + 2)) := by
  constructor
  · intro q z hq hzq
    exact cauchy_remainder zs hz q z hq hzq
  · refine ⟨2 ^ (m + 2) * (H + H1) ^ (m + 1), max 1 (max (2 * H) (2 * H1)), ?_⟩
    intro q z a R hR hza hzsa hq ha
    have h1 : (1 : ℝ) ≤ R := (le_max_left _ _).trans hR
    have h2 : 2 * H ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
    have h3 : 2 * H1 ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans hR)
    exact cauchy_remainder_bound zs q z a R H H1 (by linarith) h2 h3 hza hzsa hq ha

end QuantumNLS.Prop015Main

#print axioms QuantumNLS.Prop015Main.interpolation_lemma
