import QuantumNLS.TerraMultiRound64PhysicalBridge
import QuantumNLS.TerraMultiRound64BaseCoefficient
import QuantumNLS.TerraMultiRound64FirstRetained

/-! The actual fourth-moment regularized difference has its finite limit on H¹. -/
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.FreeLimit QuantumNLS.Sobolev
open QuantumNLS.TranslatedCorrelation QuantumNLS.TerraMultiRound49SobolevBridge
open QuantumNLS.TerraMultiRound59REG007 QuantumNLS.TerraMultiRound59SignedCharges
open QuantumNLS.TerraMultiRound60Kernel QuantumNLS.TerraMultiRound64PhysicalBridge
open QuantumNLS.TerraMultiRound64BaseCoefficient QuantumNLS.TerraMultiRound64FirstRetained
namespace QuantumNLS.TerraMultiRound64SecondLimit

theorem physical_fourth_regularized_limit (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ)
    (u : L2T L) (hu : hsq L (1 : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤) :
    ∃ x : Ell2, ∃ ha0 : 0 ≤ ((1 : ℕ) : ℝ), fieldMap L (1 : ℕ) ha0 x = u ∧
      Tendsto (fun Y : ℝ => (∫ t, kernel 2 Y t ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) -
        (∫ t, kernel 2 Y t ∂(freeMeasure L u))) atTop
        (𝓝 (retainedR (L := L) 2 (by omega) κ (physicalToHk (L := L) (2-1) x) 2)) := by
  obtain ⟨x, ha0, hx, hlim⟩ := physical_limit_from_lower_moments L 1 (by omega) κ hκ u hu
  let hst : ((1 : ℕ) : ℝ) ≤ ((2-1 : ℕ) : ℝ) := by norm_num
  let v : Hk L 1 := H02.mono (L := L) (s := ((1 : ℕ) : ℝ))
    (t := ((2-1 : ℕ) : ℝ)) hst (physicalToHk (L := L) (2-1) x)
  have hv : v.val = u := by
    have hval := physicalToHk_val_eq_fieldMap L 1 ha0 x
    have hm : v.val = (physicalToHk (L := L) (2-1) x).val := by
      dsimp only [v, H02.mono]
      exact fieldIncl_val _ _ _ _ _
    exact hm.trans (hval.trans hx)
  have hH := representative_oneH1 u v hv
  have hμ1 : Integrable (fun t : ℝ => t^2) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) := by
    rw [QuantumNLS.PhysicalL2Normalization.measure_eq_Mmeas hκ u]
    exact (QuantumNLS.RDF8Main.root_H1_characterization hκ u).1.mp hH
  have hν1 := free_second_integrable u hH
  have hμ : ∀ j < 1+1, Integrable (fun t : ℝ => t^(2*j)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) := by
    intro j hj
    interval_cases j
    · simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u))
    · simpa using hμ1
  haveI : IsFiniteMeasure (freeMeasure L u) := by
    rw [← QuantumNLS.FullMass.Mmeas_zero_coupling]
    infer_instance
  have hν : ∀ j < 1+1, Integrable (fun t : ℝ => t^(2*j)) (freeMeasure L u) := by
    intro j hj
    interval_cases j
    · simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) (freeMeasure L u))
    · simpa using hν1
  have hc : ∀ j, 1 ≤ j → j < 1+1 →
      (∫ t : ℝ, t^(2*j) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) -
      (∫ t : ℝ, t^(2*j) ∂(freeMeasure L u)) =
        retainedR (L := L) (1+1) (by omega) κ (physicalToHk (L := L) (1+1-1) x) j := by
    intro j hj hj'
    have : j = 1 := by omega
    subst j
    rw [retained_one 2 (by omega) κ x hst]
    exact first_moment_correction hκ u v hv
  exact ⟨x, ha0, hx, hlim hμ hν hc⟩

#print axioms physical_fourth_regularized_limit
end QuantumNLS.TerraMultiRound64SecondLimit
