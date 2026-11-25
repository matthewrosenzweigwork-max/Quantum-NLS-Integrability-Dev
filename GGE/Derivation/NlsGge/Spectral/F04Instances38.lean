import NlsGge.Spectral.F04Continuity38
import NlsGge.Spectral.R3cExpansionK1_38
import NlsGge.Spectral.R3cExpansionK2_38
import NlsGge.Spectral.F04EnergyIdentity38
import NlsGge.Spectral.TraceFormulaHk38

/-!
# F04.04 instances discharged by the proved R3c bounds

`spectralRemainder_continuous38` at `m = 2` needs `NonlinRiccatiSmoothBound38 1`, which is
`nonlinRiccatiSmoothBound38_one`; at `m = 3` it needs the `k = 2` bound
`nonlinRiccatiSmoothBound38_two`, which also gives the first (spectral) identity of F04.06 at `m = 2` and the order-4 trace formula on
`H²`.
-/

open Filter Set MeasureTheory
open scoped Topology Interval
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core NlsGge.Sobolev38

/-- **F04.04 at `m = 2`, unconditional.** For positive coefficients `β₀, β₁, β₂`, the spectral
remainder `R₂(u) = Σₙ (2/π)∫_{gₙ} (W₂(2λ) − W₂(2πn)) v` is a continuous function of `u ∈ H¹`. -/
theorem spectralRemainder_continuous_two38 (β : ℕ → ℝ) (hβ : ∀ j ≤ 2, 0 < β j) :
    Continuous fun y : SobolevHilbert ((2 - 1 : ℕ) : ℝ) => ∑' n : ℤ,
      gapRemainderTermE02_38 (finiteWeightE02_38 2 β) ((sobolevToL2_38 (2 - 1)) y) n :=
  spectralRemainder_continuous38 2 le_rfl β hβ nonlinRiccatiSmoothBound38_one

/-- **F04.04 at `m = 3`, unconditional.** For positive `β₀, …, β₃`, the spectral remainder `R₃` is a
continuous function of `u ∈ H²`. -/
theorem spectralRemainder_continuous_three38 (β : ℕ → ℝ) (hβ : ∀ j ≤ 3, 0 < β j) :
    Continuous fun y : SobolevHilbert ((3 - 1 : ℕ) : ℝ) => ∑' n : ℤ,
      gapRemainderTermE02_38 (finiteWeightE02_38 3 β) ((sobolevToL2_38 (3 - 1)) y) n :=
  spectralRemainder_continuous38 3 (by norm_num) β hβ nonlinRiccatiSmoothBound38_two

/-- **F04.06 at `m = 2`, unconditional.** On `H²`, the energy `E₂` equals the action series plus the
spectral remainder. -/
theorem energyIdentity_spectral_two38 (β : ℕ → ℝ) (hβ : ∀ j ≤ 2, 0 < β j)
    (y : SobolevHilbert ((2 : ℕ) : ℝ)) :
    energySobolev38 2 β y =
      ∑' n : ℤ, finiteWeightE02_38 2 β (2 * Real.pi * (n : ℝ)) *
          actualGapActionAllE02_38 ((sobolevToL2_38 2) y) n +
      ∑' n : ℤ, gapRemainderTermE02_38 (finiteWeightE02_38 2 β) ((sobolevToL2_38 2) y) n :=
  energyIdentity_spectral38 2 le_rfl β hβ nonlinRiccatiSmoothBound38_two y

/-- **Order-4 trace formula on `H²`, unconditional.** -/
theorem actualTraceFormula_H2_38 (u : PhysicalL2)
    (y : SobolevHilbert ((2 + 1 - 1 : ℕ) : ℝ))
    (hy : ∀ n : ℤ, (show WeightedHilbert (sobolevModeWeight ((2 + 1 - 1 : ℕ) : ℝ)) from y) n =
      physicalFourier u n) :
    Integrable (fun t : ℝ => (2*t)^(2*2) * actualGapHeightE02_38 u t) ∧
    (2/Real.pi) * ∫ t : ℝ, (2*t)^(2*2) * actualGapHeightE02_38 u t = chargeSobolev38 (2 + 1) 2 y :=
  actualTraceFormula_Hk38 2 (by norm_num) nonlinRiccatiSmoothBound38_two u y hy

end NlsGge.SpectralFoundations
