import NlsGge.GK38.F04AtOne
import NlsGge.GK38.EigenvalueCompactnessStrong

/-! Actual weighted height primitives on strong L2, before remainder continuity. -/
set_option autoImplicit false
open Filter Set MeasureTheory
open scoped Topology
open NlsGge.SpectralFoundations NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.Sobolev38
namespace NlsGge.GK38
noncomputable section

theorem remainderHeight_joint_continuous38 (W : ℝ → ℝ) (hW : Continuous W) (n : ℤ) :
    Continuous (fun p : PhysicalL2 × ℝ =>
      (W (2 * p.2) - W (2 * Real.pi * n)) * actualGapHeightE02_38 p.1 p.2) := by
  exact ((hW.comp (continuous_const.mul continuous_snd)).sub continuous_const).mul
    gapHeight_joint_continuous_L2_38

theorem remainderHeight_intervalIntegrable38 (W : ℝ → ℝ) (hW : Continuous W)
    (u : PhysicalL2) (n : ℤ) (a b : ℝ) :
    IntervalIntegrable (fun x => (W (2 * x) - W (2 * Real.pi * n)) *
      actualGapHeightE02_38 u x) volume a b := by
  exact (((hW.comp (continuous_const.mul continuous_id)).sub continuous_const).mul
    (continuous_actualGapHeightE02_38 u)).intervalIntegrable a b

theorem remainderHeight_primitive_continuous38 (W : ℝ → ℝ) (hW : Continuous W) (n : ℤ) :
    Continuous (fun p : PhysicalL2 × ℝ => ∫ x in (0 : ℝ)..p.2,
      (W (2 * x) - W (2 * Real.pi * n)) * actualGapHeightE02_38 p.1 x) := by
  have _hi : ∀ u : PhysicalL2, ∀ b : ℝ,
      IntervalIntegrable (fun x => (W (2 * x) - W (2 * Real.pi * n)) *
        actualGapHeightE02_38 u x) volume 0 b :=
    fun u b => remainderHeight_intervalIntegrable38 W hW u n 0 b
  exact intervalIntegral.continuous_parametric_primitive_of_continuous
    (f := fun u x => (W (2 * x) - W (2 * Real.pi * n)) * actualGapHeightE02_38 u x)
    (remainderHeight_joint_continuous38 W hW n)

theorem gapRemainderTerm_L2_continuous38 (W : ℝ → ℝ) (hW : Continuous W) (n : ℤ) :
    Continuous (fun u : PhysicalL2 => gapRemainderTermE02_38 W u n) := by
  have he (u : PhysicalL2) : gapRemainderTermE02_38 W u n = (2 / Real.pi) *
      ((∫ x in (0 : ℝ)..actualGapUpperAllE02_38 u n,
        (W (2 * x) - W (2 * Real.pi * n)) * actualGapHeightE02_38 u x) -
      ∫ x in (0 : ℝ)..actualGapLowerAllE02_38 u n,
        (W (2 * x) - W (2 * Real.pi * n)) * actualGapHeightE02_38 u x) := by
    rw [gapRemainderTermE02_38, intervalIntegral.integral_interval_sub_left
      (remainderHeight_intervalIntegrable38 W hW u n 0 _)
      (remainderHeight_intervalIntegrable38 W hW u n 0 _)]
  simp_rw [he]
  have hu := (remainderHeight_primitive_continuous38 W hW n).comp
    (continuous_id.prodMk (gapEndpoints_L2_continuous38 n).2)
  have hl := (remainderHeight_primitive_continuous38 W hW n).comp
    (continuous_id.prodMk (gapEndpoints_L2_continuous38 n).1)
  simpa only [Function.comp_def, Pi.sub_apply, id_eq] using
    (hu.sub hl).const_mul (2 / Real.pi)

end
end NlsGge.GK38
