import QuantumNLS.Prop009Branch
/-! integrator-authored trusted spec for PROP-009 lem:B4-finite-probes (Terra r161 FULL ACCEPT): headline statement(s) copied verbatim from Prop009Branch (QuantumNLS.Prop009Branch). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Set Filter Topology Complex Metric
open scoped ENNReal
namespace QuantumNLS.P009Spec
open QuantumNLS.Prop009Branch
open QuantumNLS.PeriodReconstructionCore QuantumNLS.PeriodReconstructionBigO QuantumNLS.PeriodReconstruction
open QuantumNLS.LabelJointLimit QuantumNLS.LabelJointWeak QuantumNLS.LabelBlock
open QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts
open QuantumNLS.RootMeasureComplex (HighHalf)
open QuantumNLS.PeriodTwoTerm (eventual_props)
open QuantumNLS.Prop009ProbeDev (probes_generic gam_supp_dist)
open QuantumNLS.MPFixedContour (gam_background)
open QuantumNLS.EmpiricalRapidity (cauchyTransform)

set_option maxHeartbeats 8000000 in
theorem finite_probes_branch_spec {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ) {n : ℤ} {xm xp h : ℝ}
    (hxm : xm ∈ S.cuts) (hxp : xp ∈ S.cuts) (hlt : xm < xp) (hh : 0 < h)
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
  first
  | exact QuantumNLS.Prop009Branch.finite_probes_branch
  | (apply QuantumNLS.Prop009Branch.finite_probes_branch <;> assumption)

end QuantumNLS.P009Spec
#print axioms QuantumNLS.P009Spec.finite_probes_branch_spec
