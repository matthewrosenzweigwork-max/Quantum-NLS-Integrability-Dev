import NlsGge.Spectral.NonlinRiccatiAllK38
import NlsGge.Spectral.F04Continuity38
import NlsGge.Spectral.F04EnergyIdentity38
import NlsGge.Spectral.TraceFormulaHk38

/-!
# F04.04, F04.06 and TF-H^k for all orders

`nonlinRiccatiSmoothBound38_all` discharges the R3c hypothesis for every `k ≥ 1`. The three
downstream results of `F04Instances38` therefore hold without hypotheses:

* `spectralRemainder_continuous_all38`: F04.04 for every `m ≥ 2` (needs `k = m - 1 ≥ 1`);
* `energyIdentity_spectral_all38`: the spectral half of F04.06 for every `m ≥ 2` (needs `k = m`);
* `actualTraceFormula_Hk_all38`: TF-H^k for every `k ≥ 1`.
-/

open Filter Set MeasureTheory
open scoped Topology Interval
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core NlsGge.Sobolev38

/-- **F04.04 for all `m ≥ 2`, unconditional.** For positive coefficients `β₀, …, β_m`, the spectral
remainder `R_m(u) = Σₙ (2/π)∫_{gₙ} (W_m(2λ) − W_m(2πn)) v` is a continuous function of `u ∈ H^{m-1}`. -/
theorem spectralRemainder_continuous_all38 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j) :
    Continuous fun y : SobolevHilbert ((m - 1 : ℕ) : ℝ) => ∑' n : ℤ,
      gapRemainderTermE02_38 (finiteWeightE02_38 m β) ((sobolevToL2_38 (m - 1)) y) n :=
  spectralRemainder_continuous38 m hm β hβ (nonlinRiccatiSmoothBound38_all (m - 1) (by omega))

/-- **F04.06, first (spectral) identity, for all `m ≥ 2`, unconditional.** On `H^m`, the energy `E_m`
equals the action series plus the spectral remainder. -/
theorem energyIdentity_spectral_all38 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j) (y : SobolevHilbert ((m : ℕ) : ℝ)) :
    energySobolev38 m β y =
      ∑' n : ℤ, finiteWeightE02_38 m β (2 * Real.pi * (n : ℝ)) *
          actualGapActionAllE02_38 ((sobolevToL2_38 m) y) n +
      ∑' n : ℤ, gapRemainderTermE02_38 (finiteWeightE02_38 m β) ((sobolevToL2_38 m) y) n :=
  energyIdentity_spectral38 m hm β hβ (nonlinRiccatiSmoothBound38_all m (by omega)) y

/-- **TF-H^k for all `k ≥ 1`, unconditional.** For `u ∈ H^k` the `2k`-moment of the gap height is
finite and `(2/π) ∫ (2t)^{2k} v = Q_{2k}`. -/
theorem actualTraceFormula_Hk_all38 (k : ℕ) (hk : 1 ≤ k) (u : PhysicalL2)
    (y : SobolevHilbert ((k + 1 - 1 : ℕ) : ℝ))
    (hy : ∀ n : ℤ, (show WeightedHilbert (sobolevModeWeight ((k + 1 - 1 : ℕ) : ℝ)) from y) n =
      physicalFourier u n) :
    Integrable (fun t : ℝ => (2 * t) ^ (2 * k) * actualGapHeightE02_38 u t) ∧
    (2 / Real.pi) * ∫ t : ℝ, (2 * t) ^ (2 * k) * actualGapHeightE02_38 u t =
      chargeSobolev38 (k + 1) k y :=
  actualTraceFormula_Hk38 k hk (nonlinRiccatiSmoothBound38_all k hk) u y hy

end NlsGge.SpectralFoundations
