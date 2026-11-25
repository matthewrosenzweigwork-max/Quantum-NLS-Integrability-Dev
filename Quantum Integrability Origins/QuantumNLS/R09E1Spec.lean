import QuantumNLS.RootMeasureConcentrationSharp
import QuantumNLS.RootMeasureContinuity
/-! integrator-authored trusted spec for R-09E1EAE9 thm:root-measure (Terra r142 FULL ACCEPT, with
r140 existence/Cauchy characterization and r141 continuity). Statements copied verbatim:
existence and uniqueness of the limiting rapidity measure (weak convergence in Born probability of the
DEF-006/DEF-010 empirical measures on the UBB1 physical basis), its Cauchy-transform characterization
on the high half-plane, the printed uniform concentration bound C/(N η²), and continuity on the unit
L² sphere. The direct proof imports no EXT-025 module (scope edge GP-10 met by a direct proof). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
namespace R09E1Spec
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.RootMeasureComplex (fz HighHalf)
open QuantumNLS.NormalizedTransfer (productSymbol)
open QuantumNLS.RootMeasureConcentration (gStar)
open QuantumNLS.EmpiricalRapidity (bornMeasure empiricalMeasureκ)
open QuantumNLS.BulkResponseActual (physBasis empiricalProb IsLimitingRapidityMeasure)
open QuantumNLS.CauchyUniqueness (cauchyTransform)
open QuantumNLS.BornConvergence (TendstoInProbabilityWeak TendstoInProbability)
open QuantumNLS.RootMeasureConcentrationSharp (Csharp Kc T)
open QuantumNLS.RootMeasureContinuity (muOf)

set_option maxHeartbeats 4000000 in
theorem exists_limiting_measure_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) :
    ∃ μ : ProbabilityMeasure ℝ, IsLimitingRapidityMeasure L κ hκ u hu μ := by
  apply QuantumNLS.RootMeasureExistence.exists_limiting_measure <;> assumption

theorem unique_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} {hκ : 0 < κ} {u : L2T L} {hu : ‖u‖ = 1}
    {μ μ' : ProbabilityMeasure ℝ} (h : IsLimitingRapidityMeasure L κ hκ u hu μ)
    (h' : IsLimitingRapidityMeasure L κ hκ u hu μ') : μ = μ' :=
  QuantumNLS.BulkResponseActual.IsLimitingRapidityMeasure.unique h h'

set_option maxHeartbeats 4000000 in
theorem cauchy_limiting_measure_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1)
    {μ : ProbabilityMeasure ℝ} (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {z : ℂ} (hz : HighHalf L κ z) :
    cauchyTransform (μ : Measure ℝ) z = gStar L κ hκ u hu z := by
  apply QuantumNLS.RootMeasureExistence.cauchy_limiting_measure <;> assumption

set_option maxHeartbeats 4000000 in
theorem gStar_spec_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ}
    (hz : HighHalf L κ z) :
    ‖gStar L κ hκ u hu z‖ ≤ (z.im)⁻¹ ∧ fz L κ z (gStar L κ hκ u hu z) = productSymbol L κ u z := by
  apply QuantumNLS.RootMeasureConcentration.gStar_spec <;> assumption

set_option maxHeartbeats 4000000 in
theorem unique_fixed_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {z : ℂ} (hz : HighHalf L κ z) {g g' : ℂ}
    (hg : ‖g‖ ≤ (z.im)⁻¹) (hg' : ‖g'‖ ≤ (z.im)⁻¹) (h : fz L κ z g = fz L κ z g') : g = g' := by
  exact QuantumNLS.RootMeasureConcentration.unique_fixed (L := L) hκ hz hg hg' h

set_option maxHeartbeats 4000000 in
theorem concentration_sharp_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)
    (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ} (hz : HighHalf L κ z) :
    ∫ m : MArr N, ‖cauchyTransform (empiricalProb L κ N m : Measure ℝ) z - gStar L κ hκ u hu z‖ ^ 2
        ∂(bornMeasure (physBasis L hκ N) u hu) ≤ Csharp / (N * z.im ^ 2) := by
  apply QuantumNLS.RootMeasureConcentrationSharp.concentration_sharp <;> assumption

set_option maxHeartbeats 4000000 in
theorem continuity_limiting_measure_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) (u : L2T L)
    (hu : ‖u‖ = 1) (un : ℕ → L2T L)
    (hun : ∀ n, ‖un n‖ = 1) (hlim : Tendsto un atTop (𝓝 u)) (μn : ℕ → ProbabilityMeasure ℝ)
    (hμn : ∀ n, IsLimitingRapidityMeasure L κ hκ (un n) (hun n) (μn n)) (μ : ProbabilityMeasure ℝ)
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) : Tendsto μn atTop (𝓝 μ) := by
  exact QuantumNLS.RootMeasureContinuity.continuity_limiting_measure (L := L) hκ u hu un hun hlim μn hμn μ hμ

theorem muOf_spec_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) (u : Metric.sphere (0 : L2T L) 1) :
    IsLimitingRapidityMeasure L κ hκ u.1 (by simpa using u.2) (muOf hκ u) :=
  QuantumNLS.RootMeasureContinuity.muOf_spec hκ u

theorem continuous_muOf_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) :
    Continuous (muOf (L := L) hκ) :=
  QuantumNLS.RootMeasureContinuity.continuous_muOf hκ

/-! Defining equations (rfl). -/
theorem IsLimitingRapidityMeasure_def (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1)
    (μ : ProbabilityMeasure ℝ) : IsLimitingRapidityMeasure L κ hκ u hu μ =
  TendstoInProbabilityWeak (fun N => bornMeasure (physBasis L hκ N) u hu)
    (fun N m => empiricalProb L κ N m) μ := rfl
theorem physBasis_def (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) (N : ℕ) : physBasis L hκ N =
  if hN : 1 ≤ N then QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ
  else QuantumNLS.BetheCoefficientTransform.freeBasis L N := rfl
theorem empiricalProb_def (L κ : ℝ) (N : ℕ) (m : MArr N) : empiricalProb L κ N m =
  if h : 0 < N then ⟨empiricalMeasureκ L κ m,
      QuantumNLS.EmpiricalRapidity.isProbabilityMeasure_empiricalMeasure L (κ / N) h m⟩
  else ⟨Measure.dirac 0, inferInstance⟩ := rfl
theorem empiricalMeasureκ_def (L κ : ℝ) {N : ℕ} (m : MArr N) :
    empiricalMeasureκ L κ m = QuantumNLS.EmpiricalRapidity.empiricalMeasure L (κ / N) m := rfl
theorem HighHalf_def (L κ : ℝ) (z : ℂ) : HighHalf L κ z = (4 * κ ≤ z.im ∧ Real.log 16 ≤ L * z.im) := rfl
theorem fz_def (L κ : ℝ) (z w : ℂ) : fz L κ z w =
  Complex.exp (Complex.I * κ * w) + Complex.exp (Complex.I * z * L) * Complex.exp (-(Complex.I * κ * w)) := rfl
theorem Csharp_def : Csharp = 9 / 2 + 8 * Kc := rfl
theorem Kc_def : Kc = 2 * (2 * T 2 + 2 * T 1) ^ 2 + 32 * (2 * T 4) ^ 2 := rfl
theorem T_def (q : ℕ) : T q = ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ q * (1 / 4 : ℝ) ^ j := rfl
end R09E1Spec
#print axioms R09E1Spec.concentration_sharp_spec
#print axioms R09E1Spec.continuous_muOf_spec
#print axioms R09E1Spec.exists_limiting_measure_spec
