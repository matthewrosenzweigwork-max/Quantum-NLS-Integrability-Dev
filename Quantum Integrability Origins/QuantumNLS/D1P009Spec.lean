import QuantumNLS.D1Prop009
/-! integrator-authored trusted spec for PROP-009 D1 bridge (review record r52 PASS): headline statement(s) copied verbatim from D1Prop009 (QuantumNLS.D1Prop009). -/
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
namespace QuantumNLS.D1P009Spec
open QuantumNLS.D1Prop009


set_option maxHeartbeats 8000000 in
theorem finite_probes_d1_spec {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ) (hd : D1Sep S) {n : ℤ}
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
  exact QuantumNLS.D1Prop009.finite_probes_d1 S hd hxm hxp hlt hh h1 h2 h3 h4

end QuantumNLS.D1P009Spec
#print axioms QuantumNLS.D1P009Spec.finite_probes_d1_spec
