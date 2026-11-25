import Mathlib
import QuantumNLS.REF88StageA
import QuantumNLS.REF88PrintedChart

/-!
# REF88StageB: INTERMEDIATE theorem of R-EF8C2837 with exactly the printed chart hypotheses

`REF88StageA.stageA` with the continuity hypotheses `hcΦ`, `hcΨ` and the exact-moduli hypothesis replaced
by the printed chart hypotheses `REF88PrintedChart.PrintedChart` (real-analytic strong symplectic
diffeomorphism with exact moduli and the printed normalization), the continuity of `Φ` and `Φ⁻¹` being
derived from the accepted R-CA92819A (`printedChart_continuity`).

Remaining hypotheses: `hR : Reg015Input L κ hκ` (the named REG-015 input) and the OPEN obligation
`hFR : FieldRotation hΦ.symp κ` (finite-action field identity; see `REF88Finite`), NOT REG-015.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ENNReal Topology
open Filter

namespace QuantumNLS.REF88StageB

open QuantumNLS.StrongSymplectic QuantumNLS.L2Flow QuantumNLS.REF88Chart QuantumNLS.REF88Reg015
open QuantumNLS.REF88Finite QuantumNLS.REF88PrintedChart QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.Fourier
open QuantumNLS.PhysicalTensor (L2T)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

theorem stageB {Φ : L2T L → K} (hκ : 0 < κ) (hR : Reg015Input L κ hκ)
    (hΦ : PrintedChart hκ Φ) (hFR : FieldRotation hΦ.symp κ) :
    (∃ ν : ℤ → ActionTorus.PosL1 → ℝ,
      (∀ (u : L2T L) (t : ℝ) (n : ℤ), 0 < (RootIndexedMasses.masses hκ u).1 n →
        Φ (flowMap hκ.le u t) n =
          Complex.exp (-Complex.I * ((t * ν n (RootIndexedMasses.masses hκ u) : ℝ) : ℂ)) *
            Φ u n) ∧
      (∀ (u : L2T L) (t : ℝ) (n : ℤ), (RootIndexedMasses.masses hκ u).1 n = 0 →
        Φ (flowMap hκ.le u t) n = 0) ∧
      (∀ (u : L2T L) (n : ℤ), 0 < (RootIndexedMasses.masses hκ u).1 n → ∀ ν' : ℝ,
        (∀ t : ℝ, Φ (flowMap hκ.le u t) n =
          Complex.exp (-Complex.I * ((t * ν' : ℝ) : ℂ)) * Φ u n) →
          ν' = ν n (RootIndexedMasses.masses hκ u)) ∧
      (∀ n : ℤ, ContinuousOn (ν n) {a : ActionTorus.PosL1 | 0 < a.1 n}) ∧
      (∀ a : ActionTorus.PosL1, ∀ z ∈ ActionTorus.actionTorus a, ∀ s t : ℝ,
        chartFlow hΦ.symp hκ.le t z ∈ ActionTorus.actionTorus a ∧ chartFlow hΦ.symp hκ.le 0 z = z ∧
        chartFlow hΦ.symp hκ.le (s + t) z = chartFlow hΦ.symp hκ.le s (chartFlow hΦ.symp hκ.le t z) ∧
        Continuous (fun t : ℝ => chartFlow hΦ.symp hκ.le t z)) ∧
      (∀ w : ℤ → ℝ, (∀ n, 0 ≤ w n) → ∀ z : K, (Summable fun n => w n * ‖z n‖ ^ 2) →
        (∀ t : ℝ, ∑' n, w n * ‖chartFlow hΦ.symp hκ.le t z n‖ ^ 2 = ∑' n, w n * ‖z n‖ ^ 2) ∧
        ∀ t0 : ℝ, Tendsto (fun t : ℝ => ∑' n, w n * ‖chartFlow hΦ.symp hκ.le t z n -
          chartFlow hΦ.symp hκ.le t0 z n‖ ^ 2) (𝓝 t0) (𝓝 0))) ∧
    (∀ (s : ℝ) (hs : 0 ≤ s), ∃ e : H02 L s ≃ₜ h02 L s,
      ∀ u : H02 L s, toK hs (e u) = Φ (H02.toL2 hs u)) ∧
    (∀ (u : L2T L), (∃ F : Finset ℤ, ∀ n, n ∉ F → (RootIndexedMasses.masses hκ u).1 n = 0) →
      ∀ (s : ℝ), 0 ≤ s → MemHsLp L s u) :=
  QuantumNLS.REF88StageA.stageA hκ hR hΦ.symp (printedChart_continuity hκ hΦ).1
    (printedChart_continuity hκ hΦ).2 hΦ.moduli hFR

#print axioms stageB

end QuantumNLS.REF88StageB
