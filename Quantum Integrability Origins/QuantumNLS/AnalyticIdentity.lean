import Mathlib

/-!
# R-2535E8FD (`global:analytic-identity`): identity theorem in a real Hilbert space

Source: `source/chapters/global/individual_periods.tex`, lemma labelled `global:analytic-identity`
(around line 115), with its printed proof. "Real analytic" is DEF-017
(`source-text/chapters/definitions.tex`, lines 103-105).

Statement (source-literal form: `AnalyticIdentity.identity_of_vanishing_ball`). Let `E`, `F` be real Hilbert
spaces and `A : E → F` locally real analytic everywhere (`∀ x, AnalyticAt ℝ A x`). If `A` vanishes on an open
ball `Metric.ball 0 ρ` with `0 < ρ`, then `A x = 0` for every `x : E`.

Correspondence of "real analytic". Mathlib's `AnalyticAt ℝ A x` is a power series
`HasFPowerSeriesAt A p x` whose coefficients `p n` are continuous ℝ-multilinear maps, with a positive radius.
DEF-017 asks for a norm-convergent series of continuous real homogeneous polynomials near each input. The two
notions agree by the standard equivalence: evaluating `p n` on the diagonal gives a continuous homogeneous
polynomial, and conversely a polynomial is the diagonal of a symmetric multilinear map (polarization, constant
`n^n / n!`). Only the radius changes. That equivalence is not formalized in this file.

Proof route. `identity_of_vanishing_ball` follows the printed proof. For fixed `x` and each bounded linear
functional `ℓ`, the line function `r ↦ ℓ (A (r • x))` is analytic on `ℝ` and vanishes near `0`. Mathlib's
identity theorem then gives it on all of `ℝ`, so `ℓ (A x) = 0`. The Riesz functional `⟪A x, ·⟫` separates points,
so `A x = 0`.

Route note. Mathlib's identity theorem `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` applies
directly on the connected space `E`. `identity_of_vanishing_ball_direct` records that cross-check. The printed
one-variable step is the same Mathlib theorem specialised to `ℝ`, so it is not an independent input.

No `sorry`, no `admit`, no new axiom, no `native_decide`. Hypotheses are exactly the source's, plus `0 < ρ`
(an open ball about zero is nonempty only for positive radius; with `ρ ≤ 0` the statement would be false).
Completeness of `E` and `F` is part of the source's "Hilbert" and is not used by the proof.
-/

namespace AnalyticIdentity

open Filter Topology Set

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Printed proof, step 1: for fixed `x` and a bounded real-linear functional `ℓ`, the scalar function
`r ↦ ℓ (A (r • x))` is real analytic on `ℝ`. -/
theorem lineFunctional_analytic (A : E → F) (hA : ∀ x : E, AnalyticAt ℝ A x) (x : E) (ℓ : F →L[ℝ] ℝ) :
    AnalyticOnNhd ℝ (fun r : ℝ => ℓ (A (r • x))) univ := by
  intro r _
  have hline : AnalyticAt ℝ (fun s : ℝ => s • x) r := analyticAt_id.smul analyticAt_const
  have hAline : AnalyticAt ℝ (fun s : ℝ => A (s • x)) r :=
    AnalyticAt.comp (g := A) (f := fun s : ℝ => s • x) (hA (r • x)) hline
  exact AnalyticAt.comp (g := ℓ) (f := fun s : ℝ => A (s • x)) (ℓ.analyticAt (A (r • x))) hAline

omit [CompleteSpace E] [CompleteSpace F] in
/-- Printed proof, step 2: the same line function vanishes in a neighbourhood of `0`, because
`r • x` lies in `Metric.ball 0 ρ` for `r` near `0`. -/
theorem lineFunctional_eventually_zero (A : E → F) {ρ : ℝ} (hρ : 0 < ρ)
    (hzero : ∀ y ∈ Metric.ball (0 : E) ρ, A y = 0) (x : E) (ℓ : F →L[ℝ] ℝ) :
    (fun r : ℝ => ℓ (A (r • x))) =ᶠ[𝓝 (0 : ℝ)] 0 := by
  have hc : Continuous (fun s : ℝ => s • x) := continuous_id.smul continuous_const
  have h0 : (0 : ℝ) • x ∈ Metric.ball (0 : E) ρ := by
    rw [zero_smul]
    exact Metric.mem_ball_self hρ
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ), r • x ∈ Metric.ball (0 : E) ρ :=
    (hc.tendsto 0).eventually (Metric.isOpen_ball.mem_nhds h0)
  filter_upwards [hev] with r hr
  simp [hzero _ hr]

/-- Source statement `global:analytic-identity` (printed route). -/
theorem identity_of_vanishing_ball {ρ : ℝ} (A : E → F) (hA : ∀ x : E, AnalyticAt ℝ A x)
    (hρ : 0 < ρ) (hzero : ∀ y ∈ Metric.ball (0 : E) ρ, A y = 0) :
    ∀ x : E, A x = 0 := by
  intro x
  -- Printed steps 1-2 and the one-variable identity theorem: `ℓ (A x) = 0` for every bounded `ℓ`.
  have hfun : ∀ ℓ : F →L[ℝ] ℝ, ℓ (A x) = 0 := by
    intro ℓ
    have h1 := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (lineFunctional_analytic A hA x ℓ) isPreconnected_univ (mem_univ (0 : ℝ))
      (lineFunctional_eventually_zero A hρ hzero x ℓ)
    have h2 : ℓ (A ((1 : ℝ) • x)) = 0 := h1 (mem_univ 1)
    simpa using h2
  -- Separation (Riesz): take the bounded functional `⟪A x, ·⟫`.
  have h := hfun (innerSL ℝ (A x))
  rw [innerSL_apply_apply] at h
  exact inner_self_eq_zero.1 h

omit [CompleteSpace E] [CompleteSpace F] in
/-- Route cross-check: Mathlib's identity theorem directly on the connected space `E`. -/
theorem identity_of_vanishing_ball_direct {ρ : ℝ} (A : E → F) (hA : ∀ x : E, AnalyticAt ℝ A x)
    (hρ : 0 < ρ) (hzero : ∀ y ∈ Metric.ball (0 : E) ρ, A y = 0) :
    ∀ x : E, A x = 0 := by
  have hev : A =ᶠ[𝓝 (0 : E)] 0 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ)] with y hy
    exact hzero y hy
  have h := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (fun x _ => hA x) isPreconnected_univ (mem_univ (0 : E)) hev
  exact fun x => h (mem_univ x)

end AnalyticIdentity

#print axioms AnalyticIdentity.lineFunctional_analytic
#print axioms AnalyticIdentity.lineFunctional_eventually_zero
#print axioms AnalyticIdentity.identity_of_vanishing_ball
#print axioms AnalyticIdentity.identity_of_vanishing_ball_direct
