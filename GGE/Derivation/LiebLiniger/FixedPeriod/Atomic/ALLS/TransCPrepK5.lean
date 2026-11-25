import Mathlib
import LiebLiniger.FixedPeriod.Atomic.ALLS.TransCPrepK4Borel
import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB10Flow
import NlsGge.ThirdConsultation.G6.BirkhoffBasic

/-! # Trunk C PREPARATORY (K5): C-MAIN assembly from the explicit K2 interface

Author: Claude Opus 5.5 (preparatory author P3).  NOT self-reviewed, NOT accepted, NOT rooted.
Namespace `NlsGge.ALLS.TransCPrep`; non-approved name `prep_allS_birkhoff_conjugacy_of_K2`.
This is a CONDITIONAL lemma: it takes the K2 interface `hK2` as an explicit hypothesis.  Its
conclusion is, verbatim, the body of the owner-approved C-MAIN `allS_birkhoff_conjugacy`
(STATEMENTS_TRUNK_C.md sha256 787e9e77…).  The final theorem is NOT stated here.

Binders / conclusions (one line each):
* `prep_summable_norm_sq x` : for `x : lp (fun _ : ℤ => ℂ) 2`, `k ↦ ‖x k‖²` is summable.
* `prep_sqrtSection_norm_sq x` : `√(‖x k‖²) = ‖x k‖` coordinatewise (as functions).
* `prep_allS_birkhoff_conjugacy_of_K2 hK2` : hypothesis `hK2` (K2 interface, per mode `n`): there is
  `rate : (ℤ → ℝ) → ℝ` with (i) ε–δ continuity on the nonnegative `ℓ²` cone for `Σ (p − q)²`,
  (ii) for EVERY `u : PhysicalL2` and real `t`,
  `Φ_n(l2Flow t u) = exp(−(t · rate(k ↦ ‖Φ_k u‖)) i) · Φ_n u` (amplitudes, not actions, as the
  argument of `rate`; exponential written exactly as in C-MAIN clause 5), (iii)
  `rate (k ↦ √(J k)) = actualOmega n J` for every finitely supported `J ≥ 0` with `0 < J n`.
  Conclusion: the five C-MAIN clauses for `Ω n := prep_omegaOfRate rate n` (zero off `ℓ¹₊`;
  measurable; ε–δ `ℓ¹`-continuous on `ℓ¹₊`; `= actualOmega n` on `positiveActionCone`; global
  conjugacy for all `u`, `t`, `n`). -/

set_option autoImplicit false
noncomputable section

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.PDE LiebLiniger.FixedPeriod.ALLS.PdeB

namespace NlsGge.ALLS.TransCPrep

theorem prep_summable_norm_sq (x : lp (fun _ : ℤ => ℂ) 2) :
    Summable (fun k => ‖(x : ℤ → ℂ) k‖ ^ 2) := by
  have h := (lp.hasSum_norm (p := 2) (by norm_num) x).summable
  refine h.congr (fun k => ?_)
  simp only [ENNReal.toReal_ofNat]
  exact Real.rpow_two _

theorem prep_sqrtSection_norm_sq (x : lp (fun _ : ℤ => ℂ) 2) :
    prep_sqrtSection (fun k => ‖(x : ℤ → ℂ) k‖ ^ 2) = fun k => ‖(x : ℤ → ℂ) k‖ := by
  funext k
  exact Real.sqrt_sq (norm_nonneg _)

/-- **C-MAIN from the K2 interface** (conditional, preparatory). -/
theorem prep_allS_birkhoff_conjugacy_of_K2
    (hK2 : ∀ n : ℤ, ∃ rate : (ℤ → ℝ) → ℝ,
      (∀ q : ℤ → ℝ, ((∀ k, 0 ≤ q k) ∧ Summable (fun k => q k ^ 2)) →
        ∀ ε > 0, ∃ δ > 0, ∀ p : ℤ → ℝ, ((∀ k, 0 ≤ p k) ∧ Summable (fun k => p k ^ 2)) →
          ∑' k, (p k - q k) ^ 2 < δ → |rate p - rate q| < ε) ∧
      (∀ (u : PhysicalL2) (t : ℝ),
        (physicalBirkhoff (l2Flow t u) : ℤ → ℂ) n =
          Complex.exp (-(((t * rate (fun k => ‖(physicalBirkhoff u : ℤ → ℂ) k‖)) : ℝ) : ℂ) *
            Complex.I) * (physicalBirkhoff u : ℤ → ℂ) n) ∧
      (∀ J : ℤ → ℝ, (∀ k, 0 ≤ J k) → (∃ s : Finset ℤ, ∀ k ∉ s, J k = 0) → 0 < J n →
        rate (fun k => Real.sqrt (J k)) = actualOmega n J)) :
    ∃ Ω : ℤ → (ℤ → ℝ) → ℝ,
      (∀ (n : ℤ) (I : ℤ → ℝ), ¬ ((∀ k, 0 ≤ I k) ∧ Summable I) → Ω n I = 0) ∧
      (∀ n : ℤ, Measurable (Ω n)) ∧
      (∀ (n : ℤ) (I : ℤ → ℝ), ((∀ k, 0 ≤ I k) ∧ Summable I) →
        ∀ ε > 0, ∃ δ > 0, ∀ J : ℤ → ℝ, ((∀ k, 0 ≤ J k) ∧ Summable J) →
          ∑' k, |J k - I k| < δ → |Ω n J - Ω n I| < ε) ∧
      (∀ (n : ℤ) (I : ℤ → ℝ), I ∈ positiveActionCone → Ω n I = actualOmega n I) ∧
      (∀ (u : PhysicalL2) (t : ℝ) (n : ℤ),
        (physicalBirkhoff (l2Flow t u) : ℤ → ℂ) n =
          Complex.exp (-(((t * Ω n (fun k => ‖(physicalBirkhoff u : ℤ → ℂ) k‖ ^ 2)) : ℝ) : ℂ) *
            Complex.I) * (physicalBirkhoff u : ℤ → ℂ) n) := by
  choose rate hrate hconj hD using hK2
  refine ⟨prep_omegaOfRate rate, fun n I hI => prep_omegaOfRate_of_not_mem rate n I hI,
    fun n => prep_measurable_omegaOfRate rate n (hrate n),
    fun n => prep_omegaOfRate_continuous rate n (hrate n),
    fun n => prep_omegaOfRate_eq_actualOmega rate n (hrate n) (hD n), ?_⟩
  intro u t n
  have hmem : (∀ k, 0 ≤ ‖(physicalBirkhoff u : ℤ → ℂ) k‖ ^ 2) ∧
      Summable (fun k => ‖(physicalBirkhoff u : ℤ → ℂ) k‖ ^ 2) :=
    ⟨fun k => sq_nonneg _, prep_summable_norm_sq (physicalBirkhoff u)⟩
  rw [prep_omegaOfRate_of_mem rate n _ hmem, prep_sqrtSection_norm_sq (physicalBirkhoff u)]
  exact hconj n u t

end NlsGge.ALLS.TransCPrep
