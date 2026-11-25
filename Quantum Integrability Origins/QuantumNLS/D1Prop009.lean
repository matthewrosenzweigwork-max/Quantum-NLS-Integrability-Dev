import QuantumNLS.D1Def043
import QuantumNLS.Prop009Branch

/-!
# PROP-009 (finite probes, branch form), owner decision D1 reading (author bridge, NEW module)

D1 reading (Terra-B r51, `finite_probes_d1`): the same scalar fields (carrier `S : IndexedScalarMeasureCuts L κ`, whose
`cuts` field is NOT read) plus D1 separation `hd : D1Sep S` at every D1 regular cut (`QuantumNLS.D1Def043`);
exterior membership `xm, xp ∉ supp μ`, `xm < xp`, `0 < h`, the four printed force inequalities; the accepted
conclusion of `Prop009Branch.finite_probes_branch` VERBATIM, including the quantifier order (the branch radius `r0`,
`r ≤ r0`, is chosen before the probes `m, z, ε, N₀, C`).
Proof: the accepted headline applied to `(d1Full S hd).toCuts`.  No hypothesis added; no frozen module edited.
Reviewer modules are not imported.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Complex Filter Topology Asymptotics Set Metric
open scoped ENNReal NNReal BigOperators
open QuantumNLS QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts
open QuantumNLS.PeriodReconstructionCore QuantumNLS.PeriodReconstructionAsymp
  QuantumNLS.PeriodReconstructionBigO QuantumNLS.PeriodReconstruction
  QuantumNLS.LabelJointLimit QuantumNLS.LabelJointWeak QuantumNLS.LabelBlock
  QuantumNLS.PeriodTwoTerm QuantumNLS.Prop009Branch
open QuantumNLS.RootMeasureComplex (HighHalf)
open QuantumNLS.EmpiricalRapidity (cauchyTransform)
open QuantumNLS.D1Def043

namespace QuantumNLS.D1Prop009

set_option maxHeartbeats 8000000 in
/-- **PROP-009, owner decision D1**. -/
theorem finite_probes_d1 {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ) (hd : D1Sep S) {n : ℤ}
    {xm xp h : ℝ}
    (hxm : xm ∉ S.μ.support) (hxp : xp ∉ S.μ.support) (hlt : xm < xp) (hh : 0 < h)
    (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
    (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
    (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
    (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)) :
    ∃ M η : ℝ, 1 ≤ M ∧ 0 < η ∧ ∃ δ > 0, ∃ r0 > 0, r0 ≤ min δ h / 2 ∧ ∀ r : ℝ, 0 < r → r ≤ r0 →
      ∃ m : ℕ, ∃ z : Fin m → ℂ, (∀ j, HighHalf L κ (z j)) ∧ ∃ ε > 0, ∃ N₀ : ℕ, ∃ C : ℝ,
        ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N → ∀ B : OnShellBethe L κ N,
          (∀ j, ‖sNf L (κ / N) B.q (z j) - sf L κ (cauchyTransform S.μ) (z j)‖ < ε) →
          BlockConclusion B n xm xp δ ∧
          (∀ w ∈ Gam xm xp h, ‖remf κ L (fun _ => N) (fun _ => B.q) (cauchyTransform S.μ) (0, w)‖ ≤
            C * ((N : ℝ)⁻¹) ^ 2) ∧
          ∀ w ∈ nb (Gam xm xp h) r, BranchGood L κ (κ / N) (2 * M) (η / 2) (cauchyTransform S.μ) B.q w := by
  exact QuantumNLS.Prop009Branch.finite_probes_branch (d1Full S hd).toCuts hxm hxp hlt hh h1 h2 h3 h4

end QuantumNLS.D1Prop009

#print axioms QuantumNLS.D1Prop009.finite_probes_d1
