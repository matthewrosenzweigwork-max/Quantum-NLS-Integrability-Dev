/- I-043 PRODUCTION01 (codex_luna16, AUTHOR; uncompiled worker draft).
   Intended target: NlsGge/Atomic/I/I043.lean.
   The exact source-compatible finiteOrderFourierLaw abbreviation is imported
   from I043Transport; boundedLipschitzDistance and its weak-limit leaf are
   imported unchanged from I043BL. -/
import Mathlib
import NlsGge.Birkhoff.H03Diagonal38
import NlsGge.ThirdConsultation.I.FiniteOrderLaw
import NlsGge.ThirdConsultation.I.I043BL
import NlsGge.ThirdConsultation.I.I043Transport

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff BoundedContinuousFunction
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.HierarchyRiccati.Core NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.I

private def i043_strictifyThresholds (T : ℕ → ℕ) : ℕ → ℕ
  | 0 => T 0
  | n + 1 => max (T (n + 1)) (i043_strictifyThresholds T n + 1)

private theorem i043_strictifyThresholds_dominates (T : ℕ → ℕ) (k : ℕ) :
    T k ≤ i043_strictifyThresholds T k := by
  induction k with
  | zero => simp [i043_strictifyThresholds]
  | succ k _ =>
      exact le_max_left _ _

private theorem i043_strictifyThresholds_step (T : ℕ → ℕ) (k : ℕ) :
    i043_strictifyThresholds T k < i043_strictifyThresholds T (k + 1) := by
  change i043_strictifyThresholds T k <
    max (T (k + 1)) (i043_strictifyThresholds T k + 1)
  exact (Nat.lt_succ_self _).trans_le (Nat.le_max_right _ _)

private theorem i043_strictifyThresholds_strictMono (T : ℕ → ℕ) :
    StrictMono (i043_strictifyThresholds T) := by
  intro a b hab
  induction b with
  | zero => omega
  | succ b ih =>
      by_cases heq : a = b
      · subst a
        exact i043_strictifyThresholds_step T b
      · have hab' : a < b := by omega
        exact (ih hab').trans (i043_strictifyThresholds_step T b)

theorem i043 (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    ∃ Nk : ℕ → ℕ, StrictMono Nk ∧ (∀ k : ℕ, k ≤ Nk k) ∧
      ∀ k : ℕ, 2 ≤ k → ∀ N : ℕ, Nk k ≤ N → ∀ r : ℕ, r < k →
        IsProbabilityMeasure (finiteOrderFourierLaw c.val r k N) ∧
        IsProbabilityMeasure (finiteOrderLaw c.val r k) ∧
        boundedLipschitzDistance (finiteOrderFourierLaw c.val r k N)
          (finiteOrderLaw c.val r k) ≤ 1 / (k : ℝ) := by
  let distanceSequence : ∀ r : ℕ, ℕ → ℕ → ℝ := fun r k N =>
    if 2 ≤ k then
      boundedLipschitzDistance (finiteOrderFourierLaw c.val r k N)
        (finiteOrderLaw c.val r k)
    else 0
  let distanceLimit : ∀ r : ℕ, ℕ → ℝ := fun _ _ => 0
  have hdistTendsto : ∀ r k, r < k →
      Tendsto (fun N => distanceSequence r k N) atTop
        (𝓝 (distanceLimit r k)) := by
    intro r k hr
    by_cases hk : 2 ≤ k
    · have hμ : ∀ N : ℕ,
          IsProbabilityMeasure (finiteOrderFourierLaw c.val r k N) := by
        intro N
        exact i043_isProbabilityMeasure_finiteOrderFourierLaw
          lower upper c k r N hk
      have hν : IsProbabilityMeasure (finiteOrderLaw c.val r k) :=
        i043_isProbabilityMeasure_finiteOrderLaw lower upper c k r hk
      have hweak := i043_finiteOrderFourierLaw_tendsto_integral
        lower upper c k r hk hr
      have hBL := boundedLipschitzDistance_tendsto_zero_of_weak
        (fun N : ℕ => finiteOrderFourierLaw c.val r k N)
        (finiteOrderLaw c.val r k) hμ hν hweak
      simpa [distanceSequence, distanceLimit, hk] using hBL
    · simp [distanceSequence, distanceLimit, hk]
  obtain ⟨T, hTindex, hTbound⟩ :=
    NlsGge.Birkhoff.exists_thresholds38 distanceSequence distanceLimit hdistTendsto
  refine ⟨i043_strictifyThresholds T,
    i043_strictifyThresholds_strictMono T, ?_, ?_⟩
  · intro k
    exact (hTindex k).trans (i043_strictifyThresholds_dominates T k)
  · intro k hk N hNk r hr
    refine ⟨i043_isProbabilityMeasure_finiteOrderFourierLaw
      lower upper c k r N hk,
      i043_isProbabilityMeasure_finiteOrderLaw lower upper c k r hk, ?_⟩
    let d : ℝ := boundedLipschitzDistance
      (finiteOrderFourierLaw c.val r k N) (finiteOrderLaw c.val r k)
    have hselected : dist (distanceSequence r k N) (distanceLimit r k) ≤
        1 / ((k : ℝ) + 1) :=
      hTbound k N
        ((i043_strictifyThresholds_dominates T k).trans hNk) r hr
    have hdistance : d ≤ 1 / ((k : ℝ) + 1) := by
      calc
        d ≤ dist (distanceSequence r k N) (distanceLimit r k) := by
          simpa [distanceSequence, distanceLimit, hk, d] using
            (calc
              d ≤ |d| := le_abs_self d
              _ = dist d 0 := by simp)
        _ ≤ 1 / ((k : ℝ) + 1) := by simpa [distanceSequence, distanceLimit, hk, d] using hselected
    have hkposN : 0 < k := by omega
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkposN
    have htol : 1 / ((k : ℝ) + 1) ≤ 1 / (k : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hkpos]
      nlinarith
    exact hdistance.trans htol

end NlsGge.ThirdConsultation.I

end
