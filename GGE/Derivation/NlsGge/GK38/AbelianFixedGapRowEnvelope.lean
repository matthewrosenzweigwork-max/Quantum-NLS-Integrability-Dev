import NlsGge.GK38.AbelianFixedGapCube
import NlsGge.GK38.AbelianGapChoiceGeometry
import NlsGge.GK38.AbelianRowEnvelope

/-! UNCOMPILED actual fixed-gap row domination. A fixed physical potential
earns one genuine square-summable envelope BEFORE all full gap selections.
No common pointwise envelope is asserted over an open potential/input ball. -/
set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

def p6FixedGapRowEnvelope38 (u : PhysicalL2) (m : ℤ) : ℝ :=
  p5GapEnvelope38 u m + ‖tauN (realSlice u) m-(m : ℂ)*(Real.pi : ℂ)‖ +
    ‖lamPlus (realSlice u) m-lamMinus (realSlice u) m‖/2

theorem p6FixedGapRowEnvelope_nonneg38 (u : PhysicalL2) (m : ℤ) :
    0 ≤ p6FixedGapRowEnvelope38 u m := by
  unfold p6FixedGapRowEnvelope38 p5GapEnvelope38
  positivity

theorem p6FixedGapRowEnvelope_summable38 (u : PhysicalL2) :
    Summable (fun m : ℤ => p6FixedGapRowEnvelope38 u m^2) := by
  obtain ⟨U,hU,_hUW,B,_hB,h⟩ := tauGamma_common_value_bound38 discC discR
    isolating_selectors_admissible38 (realSlice u) (realSlice_mem_gkW u)
  have ht := h (realSlice u) (mem_of_mem_nhds hU)
  have hs := p5GapEnvelope_summable38 u
  have hτ : Summable (fun m : ℤ =>
      ‖tauN (realSlice u) m-(m : ℂ)*(Real.pi : ℂ)‖^2) := ht.1
  have hγ := ht.2.1
  have hdom := ((hs.add hτ).add (hγ.div_const 4)).mul_left 3
  apply hdom.of_nonneg_of_le (fun _ => sq_nonneg _)
  intro m
  change (p5GapEnvelope38 u m +
      ‖tauN (realSlice u) m-(m : ℂ)*(Real.pi : ℂ)‖ +
      ‖lamPlus (realSlice u) m-lamMinus (realSlice u) m‖/2)^2 ≤
    3*(p5GapEnvelope38 u m^2 +
      ‖tauN (realSlice u) m-(m : ℂ)*(Real.pi : ℂ)‖^2 +
      ‖lamPlus (realSlice u) m-lamMinus (realSlice u) m‖^2/4)
  nlinarith [sq_nonneg (p5GapEnvelope38 u m-
      ‖tauN (realSlice u) m-(m : ℂ)*(Real.pi : ℂ)‖),
    sq_nonneg (p5GapEnvelope38 u m-
      ‖lamPlus (realSlice u) m-lamMinus (realSlice u) m‖/2),
    sq_nonneg (‖tauN (realSlice u) m-(m : ℂ)*(Real.pi : ℂ)‖-
      ‖lamPlus (realSlice u) m-lamMinus (realSlice u) m‖/2)]

theorem p6FullGap_input_envelope38 (u : PhysicalL2) (s : Lib.L2Seq)
    (hs : ∀ m : ℤ, Lib.sigmaOf s m ∈
      segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m)) :
    ∀ m : ℤ, ‖s m‖ ≤ p5GapEnvelope38 u m := by
  intro m
  have h := p5GapChoice_norm_bound38 u (Lib.sigmaOf s) hs m
  simpa only [Lib.sigmaOf,countingCenter38,add_sub_cancel_left,p5GapEnvelope38] using h

theorem p6FullGap_row_envelope38 (u : PhysicalL2) (s : Lib.L2Seq)
    (hs : ∀ m : ℤ, Lib.sigmaOf s m ∈
      segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m)) :
    ∀ m : ℤ, p2RowEnvelope38 (realSlice u) s m ≤ p6FixedGapRowEnvelope38 u m := by
  intro m
  unfold p2RowEnvelope38 p6FixedGapRowEnvelope38
  exact add_le_add (add_le_add (p6FullGap_input_envelope38 u s hs m) le_rfl) le_rfl

end
end NlsGge.GK38
