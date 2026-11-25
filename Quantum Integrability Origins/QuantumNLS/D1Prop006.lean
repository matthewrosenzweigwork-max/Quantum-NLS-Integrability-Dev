import QuantumNLS.D1Def043
import QuantumNLS.PeriodTwoTerm

/-!
# PROP-006 (period reconstruction), owner decision D1 reading (author bridge, NEW module)

D1 reading (Terra-B r51, `period_reconstruction_d1`): the same scalar fields (carrier `S : IndexedScalarMeasureCuts L κ`,
whose `cuts` field is NOT read) plus D1 separation `hd : D1Sep S` at every D1 regular cut (`QuantumNLS.D1Def043`);
exterior membership `xm, xp ∉ supp μ`, `xm < xp`, `0 < h`, and the four printed force inequalities; the four conclusion
clauses of the accepted `PeriodTwoTerm.period_reconstruction` VERBATIM (quantifier order and constants unchanged).
Proof: the accepted headline applied to `(d1Full S hd).toCuts` (cuts = full exterior; the bracket inequalities place
`xm`, `xp` there).  No hypothesis added; no frozen module edited.  Reviewer modules are not imported.
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
  QuantumNLS.PeriodTwoTerm
open QuantumNLS.EmpiricalRapidity (cauchyTransform)
open QuantumNLS.D1Def043

namespace QuantumNLS.D1Prop006

set_option maxHeartbeats 8000000 in
/-- **PROP-006, owner decision D1**. -/
theorem period_reconstruction_d1 {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ) (hd : D1Sep S)
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ) {N : ℕ → ℕ} {hN : ∀ k, 0 < N k}
    {B : ∀ k, OnShellBethe L κ (N k)}
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ)) (hNtop : Tendsto N atTop atTop)
    {n : ℤ} {xm xp h : ℝ} (hxm : xm ∉ S.μ.support) (hxp : xp ∉ S.μ.support) (hlt : xm < xp)
    (hh : 0 < h)
    (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
    (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
    (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
    (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)) :
    (∃ C : ℝ, ∀ᶠ k in atTop, ∀ z ∈ Gam xm xp h,
      ‖remf κ L N (fun k => (B k).q) (cauchyTransform S.μ) (k, z)‖ ≤ C * ((N k : ℝ)⁻¹) ^ 2) ∧
    (∃ C : ℝ, ∀ᶠ k in atTop,
      ‖twoTermErr L κ (cauchyTransform S.μ) (B k) n xm xp h‖ ≤ C * ((N k : ℝ)⁻¹) ^ 2) ∧
    (∃ C : ℝ, ∃ U ∈ 𝓝 μ, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
      ∀ B : OnShellBethe L κ N, rootP B hN ∈ U → ∀ z ∈ Gam xm xp h,
        ‖remOne κ L (cauchyTransform S.μ) B.q z‖ ≤ C * ((N : ℝ)⁻¹) ^ 2) ∧
    (∃ C : ℝ, ∃ U ∈ 𝓝 μ, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
      ∀ B : OnShellBethe L κ N, rootP B hN ∈ U →
        ‖twoTermErr L κ (cauchyTransform S.μ) B n xm xp h‖ ≤ C * ((N : ℝ)⁻¹) ^ 2) := by
  exact QuantumNLS.PeriodTwoTerm.period_reconstruction (d1Full S hd).toCuts hμ hconv hNtop hxm hxp
    hlt hh h1 h2 h3 h4

end QuantumNLS.D1Prop006

#print axioms QuantumNLS.D1Prop006.period_reconstruction_d1
