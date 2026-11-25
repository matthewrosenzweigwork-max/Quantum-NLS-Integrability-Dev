import Mathlib
import QuantumNLS.DetGapMain
import QuantumNLS.F04Selection

/-!
# CC:F04:deterministic-gap (R-C455C541) as one named theorem

Source: `F04.tex` line 315, Proposition `CC:F04:deterministic-gap` (`\\ReportID{R-C455C541}`):

  *In the transfer setting above, assume in addition that the endpoint empirical measures converge to `μ` in quadratic Wasserstein
  distance and use Theorem CC:F03:deterministic.  Then the receiver-minus-donor energy difference tends to
  `ω_ab = 4π ∫_b^a f_ext(x(λ)) dλ`.  The integral is finite.  Values at integer `λ` can be assigned arbitrarily.*

* transfer setting (F04.tex:152-160): `a > b`, `I_a, I_b > 0`, old arrays `η^{(N)}` with `η_b ≥ 1`, `m = η − e_b + e_a`
  (`transfer`), `η^{(N)}/N → I` in `ℓ¹`, endpoint empirical root measures converge weakly (`hend`);
* additionally quadratic Wasserstein convergence of the endpoint measures (`hW2`, `W₂(μ_N(0), μ) → 0`; the path-distance
  identity gives it at every `s`);
* `hbulk`: `μ = M_u` satisfies the standing hypotheses of `CC:F03:section` (including `∫ x² dμ < ∞`, F03.tex:163), carried
  exactly as printed;
* `F` the response (`IsResponse`, the unique minimiser of CC:F04:bulk-functional), `f` with `f(Q(t)) = F(t)` a.e.
  (`exists_response_pullback` shows these exist);
* `x(λ)`: any function with `θ(x(λ)) = πλ` at non-integer `λ` (the selection proposition shows it exists, and that every
  solution gives the same limit);
* conclusion: the integrand is integrable (finite integral; values at integers immaterial) and
  `Q₂(m^{(N)}) − Q₂(η^{(N)}) → 4π ∫_b^a f_ext(x(λ)) dλ`.
The selection clause `CC:F04:selection` is `F04Selection.selection` (R-F4C3E5BE).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace QuantumNLS.DetGapFinal

open QuantumNLS.BetheLabels QuantumNLS.F02FiniteGap QuantumNLS.AdjacentResponse QuantumNLS.BetheRoots
open QuantumNLS.F04SelSetup QuantumNLS.F04SelBand QuantumNLS.LocalHeight QuantumNLS.DetGapRowLim
open QuantumNLS.DetGapMain
open QuantumNLS.BulkResponseForm (L2Unit BulkResponseData BulkMeasure)
open QuantumNLS.QuantileForm (uI exists_pullback)
open QuantumNLS.QuantileTransport (qm empirical W2)
open PhysicalTensor (L2T)

theorem exists_pullback_L2 (σ : Measure ℝ) [IsProbabilityMeasure σ] (hna : ∀ x, σ {x} = 0) (F : L2Unit) :
    ∃ f : ℝ → ℝ, Measurable f ∧ (F : ℝ → ℝ) =ᵐ[uI] fun t => f (qm σ t) := by
  set Fm := (Lp.aestronglyMeasurable F).mk (F : ℝ → ℝ) with hFm
  have hm : Measurable Fm := (Lp.aestronglyMeasurable F).stronglyMeasurable_mk.measurable
  obtain ⟨h, hhm, hh⟩ := exists_pullback σ hna Fm hm
  refine ⟨h, hhm, ?_⟩
  filter_upwards [(Lp.aestronglyMeasurable F).ae_eq_mk, ae_restrict_mem measurableSet_Ioo] with t h1 h2
  rw [h1]
  exact (hh t h2).symm

/-- The hypotheses on `F, f` are satisfiable. -/
theorem exists_response_pullback {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1)
    (hbulk : BulkMeasure (Mu hκ u)) :
    ∃ F : L2Unit, (⟨L, κ, Fact.out, hκ, Mu hκ u, hbulk⟩ : BulkResponseData).IsResponse F ∧
      ∃ f : ℝ → ℝ, Measurable f ∧ (F : ℝ → ℝ) =ᵐ[uI] fun t => f (qm (Mu hκ u) t) := by
  haveI := Mu_prob hκ u hu
  obtain ⟨F, hF, -⟩ := (⟨L, κ, Fact.out, hκ, Mu hκ u, hbulk⟩ : BulkResponseData).existsUnique_response
  exact ⟨F, hF, exists_pullback_L2 (Mu hκ u) (Mu_singleton hκ u) F⟩

/-- **`CC:F04:deterministic-gap`** (R-C455C541). -/
theorem deterministic_gap {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ) (u : L2T L)
    (hu : ‖u‖ = 1) (hbulk : BulkMeasure (Mu hκ u))
    {b a : ℤ} (hab : b < a) (hb : 0 < II hκ u b) (ha : 0 < II hκ u a)
    (η : (n : ℕ) → MArr (n + 1)) (hηb : ∀ n, 1 ≤ (η n).1 b)
    (hη : Tendsto (fun n : ℕ => ∑' m : ℤ, |(((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) - II hκ u m|)
      atTop (𝓝 0))
    (hend : EmpiricalWeakConv (fun n : ℕ => arrRoots L (κ / ((n : ℝ) + 1)) (η n)) (Mu hκ u))
    (hW2 : Tendsto (fun n : ℕ => W2 (empirical (n + 1) (arrRoots L (κ / ((n : ℝ) + 1)) (η n)))
      (Mu hκ u)) atTop (𝓝 0))
    {F : L2Unit} (hF : (⟨L, κ, Fact.out, hκ, Mu hκ u, hbulk⟩ : BulkResponseData).IsResponse F)
    {f : ℝ → ℝ} (hfm : Measurable f) (hFf : (F : ℝ → ℝ) =ᵐ[uI] fun t => f (qm (Mu hκ u) t))
    (xl : ℝ → ℝ)
    (hxl : ∀ k : ℤ, b ≤ k → k < a → ∀ lam : ℝ, (k : ℝ) < lam → lam < (k : ℝ) + 1 →
      th hκ u (xl lam) = lam * Real.pi) :
    IntervalIntegrable (fun lam => fext L κ (Mu hκ u) f (xl lam)) volume (b : ℝ) a ∧
    Tendsto (fun n : ℕ => ∑ i, arrRoots L (κ / ((n : ℝ) + 1)) (transfer (η n) (hηb n) a) i ^ 2 -
        ∑ i, arrRoots L (κ / ((n : ℝ) + 1)) (η n) i ^ 2) atTop
      (𝓝 (4 * Real.pi * ∫ lam in (b : ℝ)..(a : ℝ), fext L κ (Mu hκ u) f (xl lam))) :=
  deterministic_gap_of_selection hκ u hu hbulk hab hb ha η hηb hη hW2
    (fun {_} hbk hka {_} h1 h2 => F04Selection.selection hκ u hu hbk hka hb ha η hηb hη hend h1 h2)
    hF hfm hFf xl hxl

end QuantumNLS.DetGapFinal

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.DetGapFinal.exists_response_pullback
#print axioms QuantumNLS.DetGapFinal.deterministic_gap
