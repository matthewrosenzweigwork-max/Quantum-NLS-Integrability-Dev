import QuantumNLS.FullMassLimit
import QuantumNLS.TranslationInvariance
/-! integrator-authored trusted spec for R-043AB9AA prop:root-full-mass (Terra r146/r147/r149 ACCEPT of own
clauses; prerequisite R-28C650F0 accepted r153). M_{κ,u} = ‖u‖² μ_{κ‖u‖²,u/‖u‖}, M_{κ,0} = 0: total mass,
Cauchy-transform characterization with uniqueness in |G| ≤ ‖u‖²/Im z, zero-coupling extension, common-phase and
translation invariance, joint weak continuity on {κ ≥ 0} × L², and the unique weak-in-probability (Lévy–Prokhorov)
limit of the scaled empirical measures under the actual Bethe Born law. Statements verbatim. No Ext025 module. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal NNReal
open Classical
namespace R043Spec
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.FreeLimit (freeMeasure freeProb muKappa)
open QuantumNLS.FullMass (Mmeas Mfin unitDir norm_unitDir)
open QuantumNLS.FullMassLimit (scaledFin)
open QuantumNLS.BulkResponseActual (IsLimitingRapidityMeasure physBasis empiricalProb)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BornConvergence (TendstoInProbability)
open QuantumNLS.CauchyUniqueness (cauchyTransform)
open QuantumNLS.RootMeasureComplex (fz HighHalf)
open QuantumNLS.NormalizedTransfer (productSymbol)

set_option maxHeartbeats 4000000 in
theorem Mmeas_univ_spec {L : ℝ} [Fact (0 < L)] (κ : ℝ) (u : L2T L) : Mmeas κ u Set.univ = ENNReal.ofReal (‖u‖ ^ 2) := by
  first
  | exact QuantumNLS.FullMass.Mmeas_univ ..
  | apply QuantumNLS.FullMass.Mmeas_univ <;> assumption

set_option maxHeartbeats 4000000 in
theorem mass_characterization_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {u : L2T L} (h : u ≠ 0) {z : ℂ}
    (hz : HighHalf L (κ * ‖u‖ ^ 2) z) :
    ‖cauchyTransform (Mmeas κ u) z‖ ≤ ‖u‖ ^ 2 / z.im ∧
    fz L κ z (cauchyTransform (Mmeas κ u) z) = productSymbol L κ u z ∧
    ∀ G' : ℂ, ‖G'‖ ≤ ‖u‖ ^ 2 / z.im → fz L κ z G' = productSymbol L κ u z →
      G' = cauchyTransform (Mmeas κ u) z := by
  first
  | exact QuantumNLS.FullMass.mass_characterization ..
  | apply QuantumNLS.FullMass.mass_characterization <;> assumption

set_option maxHeartbeats 4000000 in
theorem mass_characterization_zero_spec {L : ℝ} [Fact (0 < L)] (κ : ℝ) {z : ℂ} (hz : 0 < z.im) :
    cauchyTransform (Mmeas κ (0 : L2T L)) z = 0 ∧
    fz L κ z 0 = productSymbol L κ (0 : L2T L) z ∧
    ∀ G' : ℂ, ‖G'‖ ≤ ‖(0 : L2T L)‖ ^ 2 / z.im → G' = 0 := by
  first
  | exact QuantumNLS.FullMass.mass_characterization_zero ..
  | apply QuantumNLS.FullMass.mass_characterization_zero <;> assumption

set_option maxHeartbeats 4000000 in
theorem Mmeas_zero_coupling_spec {L : ℝ} [Fact (0 < L)] (u : L2T L) : Mmeas 0 u = freeMeasure L u := by
  first
  | exact QuantumNLS.FullMass.Mmeas_zero_coupling ..
  | apply QuantumNLS.FullMass.Mmeas_zero_coupling <;> assumption

set_option maxHeartbeats 4000000 in
theorem Mmeas_phase_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) (u : L2T L) {c : ℂ} (hc : ‖c‖ = 1) :
    Mmeas κ (c • u) = Mmeas κ u := by
  first
  | exact QuantumNLS.FullMass.Mmeas_phase ..
  | apply QuantumNLS.FullMass.Mmeas_phase <;> assumption

set_option maxHeartbeats 4000000 in
theorem Mmeas_phase_zero_spec {L : ℝ} [Fact (0 < L)] (u : L2T L) {c : ℂ} (hc : ‖c‖ = 1) : Mmeas 0 (c • u) = Mmeas 0 u := by
  first
  | exact QuantumNLS.FullMass.Mmeas_phase_zero ..
  | apply QuantumNLS.FullMass.Mmeas_phase_zero <;> assumption

set_option maxHeartbeats 4000000 in
theorem continuous_Mfin_spec {L : ℝ} [Fact (0 < L)] :
    Continuous (fun p : {κ : ℝ // 0 ≤ κ} × L2T L => Mfin p.1.1 p.2) := by
  first
  | exact QuantumNLS.FullMassLimit.continuous_Mfin ..
  | apply QuantumNLS.FullMassLimit.continuous_Mfin <;> assumption

set_option maxHeartbeats 4000000 in
theorem born_product_limit_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {u : L2T L} (h : u ≠ 0) :
    IsLimitingRapidityMeasure L (κ * ‖u‖ ^ 2) (mul_pos hκ (pow_pos (norm_pos_iff.2 h) 2)) (unitDir u)
      (norm_unitDir h) (muKappa (unitDir u) (norm_unitDir h) (κ * ‖u‖ ^ 2)) ∧
    TendstoInProbability
      (fun N => bornMeasure (physBasis L (mul_pos hκ (pow_pos (norm_pos_iff.2 h) 2)) N) (unitDir u)
        (norm_unitDir h))
      (fun N (ω : MArr N) => (LevyProkhorov.ofMeasure
        (scaledFin (‖u‖ ^ 2) (empiricalProb L (κ * ‖u‖ ^ 2) N ω)) : LevyProkhorov (FiniteMeasure ℝ)))
      (LevyProkhorov.ofMeasure (Mfin κ u)) := by
  first
  | exact QuantumNLS.FullMassLimit.born_product_limit ..
  | apply QuantumNLS.FullMassLimit.born_product_limit <;> assumption

set_option maxHeartbeats 4000000 in
theorem born_product_unique_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {u : L2T L} (h : u ≠ 0) (M' : FiniteMeasure ℝ)
    (hM' : TendstoInProbability
      (fun N => bornMeasure (physBasis L (mul_pos hκ (pow_pos (norm_pos_iff.2 h) 2)) N) (unitDir u)
        (norm_unitDir h))
      (fun N (ω : MArr N) => (LevyProkhorov.ofMeasure
        (scaledFin (‖u‖ ^ 2) (empiricalProb L (κ * ‖u‖ ^ 2) N ω)) : LevyProkhorov (FiniteMeasure ℝ)))
      (LevyProkhorov.ofMeasure M')) :
    M' = Mfin κ u := by
  first
  | exact QuantumNLS.FullMassLimit.born_product_unique ..
  | apply QuantumNLS.FullMassLimit.born_product_unique <;> assumption

set_option maxHeartbeats 4000000 in
theorem Mmeas_translate_spec {L : ℝ} [Fact (0 < L)] (κ : ℝ) (u : L2T L) (a : ℝ) : Mmeas κ (QuantumNLS.BornTranslation.trans a u) = Mmeas κ u := by
  first
  | exact QuantumNLS.TranslationInvariance.Mmeas_translate ..
  | apply QuantumNLS.TranslationInvariance.Mmeas_translate <;> assumption

theorem Mmeas_def {L : ℝ} [Fact (0 < L)] (κ : ℝ) (u : L2T L) : Mmeas κ u =
  if h : u = 0 then 0 else
    ENNReal.ofReal (‖u‖ ^ 2) • (muKappa (unitDir u) (norm_unitDir h) (κ * ‖u‖ ^ 2) : Measure ℝ) := rfl
theorem unitDir_def {L : ℝ} [Fact (0 < L)] (u : L2T L) : unitDir u = ((‖u‖⁻¹ : ℝ) : ℂ) • u := rfl
theorem trans_apply_def {L : ℝ} [Fact (0 < L)] (a : ℝ) : (QuantumNLS.BornTranslation.trans (L := L) a) =
  Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ (fun x : AddCircle L => x + (a : AddCircle L))
    (measurePreserving_add_right (volume : Measure (AddCircle L)) (a : AddCircle L)) := rfl
end R043Spec
#print axioms R043Spec.born_product_limit_spec
#print axioms R043Spec.continuous_Mfin_spec
