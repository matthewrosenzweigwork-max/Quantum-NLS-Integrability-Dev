import QuantumNLS.ActualGapR26
/-! integrator-authored trusted spec for R-1E0C40B3 CC:F04:actual-gap (terra_review r200 PASS): headline statement(s) copied verbatim from ActualGapR26 (QuantumNLS.ActualGapR26). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators
namespace QuantumNLS.R1E0Spec
open QuantumNLS.ActualGapR26
open ActualGapDataR26 ActualGapTransferR26 ActualGapMomentsR26
open PhysicalTensor (L2T)
open BetheLabels (MArr)
open F04SelBand (II)
open RootEnergyMomentLaws (law)
open RootOccupationLimit (occVec)
open BornConvergence (TendstoInProbability)
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem actual_law_cubic_energy_gaps_spec (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1)
    (hH : ProductEnergyPreparation.OneH1 u) :
    ∃ D : Data hκ u,
      (∀ a b : ℤ, 0 < II hκ u a → 0 < II hκ u b →
        IntervalIntegrable D.integrand volume (b : ℝ) a) ∧
      (∀ a : ℤ, D.omega a a = 0) ∧
      (∀ a b : ℤ, D.omega a b = -D.omega b a) ∧
      (∀ a b d : ℤ, 0 < II hκ u a → 0 < II hκ u b → 0 < II hκ u d →
        D.omega a b + D.omega b d = D.omega a d) ∧
      Tendsto (meanOccupationError hκ u hu) atTop (𝓝 0) ∧
      (∀ (default : ∀ N, MArr N → ℝ) (a b : ℤ), a ≠ b → 0 < II hκ u a → 0 < II hκ u b →
        TendstoInProbability (law hκ u hu) (fun _ => gapWithDefault L κ a b default) (D.omega a b) ∧
        Tendsto (V hκ u hu a b default (D.omega a b)) atTop (𝓝 0) ∧
        (∀ T : ℝ,
          (∀ N : ℕ, EpsSq hκ u hu a b default (D.omega a b) T N ≤
            ENNReal.ofReal (T ^ 2) * V hκ u hu a b default (D.omega a b) N +
              4 * meanOccupationError hκ u hu N / ENNReal.ofReal (radius hκ u a b)) ∧
          Tendsto (EpsSq hκ u hu a b default (D.omega a b) T) atTop (𝓝 0))) := by
  exact QuantumNLS.ActualGapR26.actual_law_cubic_energy_gaps hκ u hu hH

end QuantumNLS.R1E0Spec
#print axioms QuantumNLS.R1E0Spec.actual_law_cubic_energy_gaps_spec
