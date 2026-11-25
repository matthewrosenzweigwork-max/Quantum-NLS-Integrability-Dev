import QuantumNLS.TerraMultiRound64PhysicalBridge
import QuantumNLS.TerraMultiRound64FirstRetained
import QuantumNLS.TerraMultiRound64BaseCriterion
import QuantumNLS.TerraMultiRound64LowerMoment

/-! The general limit step, with only the higher lower-order corrections left to induction. -/
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.FreeLimit QuantumNLS.Sobolev
open QuantumNLS.TranslatedCorrelation QuantumNLS.TerraMultiRound49SobolevBridge
open QuantumNLS.TerraMultiRound59REG007 QuantumNLS.TerraMultiRound59SignedCharges
open QuantumNLS.TerraMultiRound60Kernel QuantumNLS.TerraMultiRound64PhysicalBridge
open QuantumNLS.TerraMultiRound64BaseCoefficient QuantumNLS.TerraMultiRound64FirstRetained
open QuantumNLS.TerraMultiRound64FreeSobolev QuantumNLS.TerraMultiRound64LowerMoment
namespace QuantumNLS.TerraMultiRound64InductiveLimit

theorem physical_limit_from_higher_corrections (L : ℝ) [Fact (0 < L)] (n : ℕ) (hs : 2 ≤ n+1)
    (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (hu : hsq L (n : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤)
    (hμn : Integrable (fun t : ℝ => t^(2*n)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) :
    ∃ x : Ell2, ∃ ha0 : 0 ≤ ((n : ℕ) : ℝ), fieldMap L n ha0 x = u ∧
      ((∀ j, 2 ≤ j → j < n+1 →
        (∫ t : ℝ, t^(2*j) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) -
        (∫ t : ℝ, t^(2*j) ∂(freeMeasure L u)) =
          retainedR (L := L) (n+1) hs κ (physicalToHk (L := L) (n+1-1) x) j) →
      Tendsto (fun Y : ℝ => (∫ t, kernel (n+1) Y t ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) -
        (∫ t, kernel (n+1) Y t ∂(freeMeasure L u))) atTop
        (𝓝 (retainedR (L := L) (n+1) hs κ (physicalToHk (L := L) (n+1-1) x) (n+1)))) := by
  obtain ⟨x, ha0, hx, hlim⟩ := physical_limit_from_lower_moments L n hs κ hκ u hu
  let hst : ((1 : ℕ) : ℝ) ≤ ((n+1-1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n+1-1 by omega)
  let v : Hk L 1 := H02.mono (L := L) (s := ((1 : ℕ) : ℝ))
    (t := ((n+1-1 : ℕ) : ℝ)) hst (physicalToHk (L := L) (n+1-1) x)
  have hv : v.val = u := by
    have hval := physicalToHk_val_eq_fieldMap L (n+1-1) (by exact_mod_cast (Nat.zero_le (n+1-1))) x
    have hm : v.val = (physicalToHk (L := L) (n+1-1) x).val := by
      dsimp only [v, H02.mono]
      exact fieldIncl_val _ _ _ _ _
    have hx' : fieldMap L (n+1-1 : ℕ) (by exact_mod_cast (Nat.zero_le (n+1-1))) x = u := by
      simpa only [Nat.add_sub_cancel] using hx
    exact hm.trans (hval.trans hx')
  have hμ : ∀ j < n+1, Integrable (fun t : ℝ => t^(2*j)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) := by
    intro j hj
    exact even_integrable_of_higher _ j n (by omega) hμn
  haveI : IsFiniteMeasure (freeMeasure L u) := by
    rw [← QuantumNLS.FullMass.Mmeas_zero_coupling]
    infer_instance
  have hνn : Integrable (fun t : ℝ => t^(2*n)) (freeMeasure L u) :=
    (free_even_integrable_iff_hsq u n).mpr hu
  have hν : ∀ j < n+1, Integrable (fun t : ℝ => t^(2*j)) (freeMeasure L u) := by
    intro j hj
    exact even_integrable_of_higher _ j n (by omega) hνn
  refine ⟨x, ha0, hx, ?_⟩
  intro hhigher
  apply hlim hμ hν
  intro j hj hj'
  by_cases h1 : j = 1
  · subst j
    rw [retained_one (n+1) hs κ x hst]
    exact first_moment_correction hκ u v hv
  · exact hhigher j (by omega) hj'

#print axioms physical_limit_from_higher_corrections
end QuantumNLS.TerraMultiRound64InductiveLimit
