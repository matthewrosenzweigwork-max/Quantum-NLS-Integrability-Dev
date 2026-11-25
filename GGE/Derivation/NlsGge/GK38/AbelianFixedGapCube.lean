import NlsGge.GK38.AbelianCompactCoordinateBox
import Mathlib.Analysis.Convex.Segment

/-! Uncompiled fixed actual spectral gap cubes. The potential is FIXED before
the genuine lp2 envelope is chosen; no varying-potential envelope is asserted. -/
set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

def p5GapEnvelope38 (u : PhysicalL2) (m : ℤ) : ℝ :=
  ‖lamMinus (realSlice u) m-countingCenter38 m‖+
    ‖lamPlus (realSlice u) m-countingCenter38 m‖

theorem p5GapEnvelope_summable38 (u : PhysicalL2) :
    Summable (fun m : ℤ => p5GapEnvelope38 u m^2) := by
  have hs := ((periodic_minus_summable38 (realSlice u)).add
    (periodic_plus_summable38 (realSlice u))).mul_left 2
  apply hs.of_nonneg_of_le (fun _ => sq_nonneg _)
  intro m
  dsimp only [p5GapEnvelope38,countingCenter38]
  nlinarith [sq_nonneg (‖lamMinus (realSlice u) m-(m : ℂ)*(Real.pi : ℂ)‖-
    ‖lamPlus (realSlice u) m-(m : ℂ)*(Real.pi : ℂ)‖)]

theorem p5Complex_segment_isCompact38 (a b : ℂ) : IsCompact (segment ℝ a b) := by
  rw [segment_eq_image]
  exact isCompact_Icc.image (by fun_prop)

theorem p5GapCube_injective_isCompact38 (ι : Type*) (j : ι → ℤ)
    (hj : Function.Injective j) (u : PhysicalL2) :
    IsCompact {t : lp (fun _ : ι => ℝ) 2 | ∀ i,
      countingCenter38 (j i)+(t i : ℂ) ∈
        segment ℝ (lamMinus (realSlice u) (j i)) (lamPlus (realSlice u) (j i))} := by
  have henv := (p5GapEnvelope_summable38 u).comp_injective hj
  have hcompact := p5Lp_coordinate_box_isCompact38 ι (fun i => p5GapEnvelope38 u (j i))
    (fun i => add_nonneg (norm_nonneg _) (norm_nonneg _)) henv
  have hclosed : IsClosed {t : lp (fun _ : ι => ℝ) 2 | ∀ i,
      countingCenter38 (j i)+(t i : ℂ) ∈
        segment ℝ (lamMinus (realSlice u) (j i)) (lamPlus (realSlice u) (j i))} := by
    have hi (i : ι) : IsClosed {t : lp (fun _ : ι => ℝ) 2 |
        countingCenter38 (j i)+(t i : ℂ) ∈
          segment ℝ (lamMinus (realSlice u) (j i)) (lamPlus (realSlice u) (j i))} := by
      apply (p5Complex_segment_isCompact38 _ _).isClosed.preimage
      exact continuous_const.add (Complex.continuous_ofReal.comp
        (lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i).continuous)
    simpa only [ofPred_forall] using isClosed_iInter hi
  apply hcompact.of_isClosed_subset hclosed
  intro t ht i
  have ha : lamMinus (realSlice u) (j i) ∈
      closedBall (countingCenter38 (j i)) (p5GapEnvelope38 u (j i)) := by
    rw [mem_closedBall,dist_eq_norm]
    exact le_add_of_nonneg_right (norm_nonneg _)
  have hb : lamPlus (realSlice u) (j i) ∈
      closedBall (countingCenter38 (j i)) (p5GapEnvelope38 u (j i)) := by
    rw [mem_closedBall,dist_eq_norm]
    exact le_add_of_nonneg_left (norm_nonneg _)
  have hc := (convex_closedBall (countingCenter38 (j i))
    (p5GapEnvelope38 u (j i))).segment_subset ha hb (ht i)
  have he : countingCenter38 (j i)+(t i : ℂ)-countingCenter38 (j i)=(t i : ℂ) := by abel
  simpa only [mem_closedBall,dist_eq_norm,he,Complex.norm_real] using hc

def p5RealGapCube38 (n : ℤ) (u : PhysicalL2) : Set (P3RealSpace38 n) :=
  {t | ∀ m : P2Index38 n, countingCenter38 m.1+(t m : ℂ) ∈
    segment ℝ (lamMinus (realSlice u) m.1) (lamPlus (realSlice u) m.1)}

theorem p5RealGapCube_isCompact38 (n : ℤ) (u : PhysicalL2) :
    IsCompact (p5RealGapCube38 n u) :=
  p5GapCube_injective_isCompact38 (P2Index38 n) Subtype.val Subtype.val_injective u

def p5FullRealGapCube38 (u : PhysicalL2) : Set (lp (fun _ : ℤ => ℝ) 2) :=
  {t | ∀ m : ℤ, countingCenter38 m+(t m : ℂ) ∈
    segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m)}

theorem p5FullRealGapCube_isCompact38 (u : PhysicalL2) :
    IsCompact (p5FullRealGapCube38 u) :=
  p5GapCube_injective_isCompact38 ℤ id Function.injective_id u

end
end NlsGge.GK38
