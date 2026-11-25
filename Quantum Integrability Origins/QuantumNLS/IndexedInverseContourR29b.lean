import QuantumNLS.IndexedKernelIntegralR29b
import QuantumNLS.IndexedCFCBindingR29b

/-! The actual inverse series on the four literal rectangle edges: chosen
radius-8 convergence and representation of the LOCAL-009 CFC integral.
The correction's kernel expansion and the period theorem remain separate. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000
noncomputable section
open Set Metric Filter Topology Complex MeasureTheory
namespace QuantumNLS.IndexedInverseContourR29b
open PhysicalTensor KernelDefinition KernelConvergence LocalPlacement
  IndexedInverseR28b IndexedInverseSeriesR28b IndexedInverseBoundsR29b
  IndexedKernelContinuityR29b IndexedKernelIntegralR29b IndexedCFCBindingR29b
  LOCAL009R23PhysicalInverse LOCAL009R22LiteralScalar LOCAL009R22Geometry
  LOCAL009R23OperatorContour PeriodReconstruction
attribute [local instance] IndexedKernelContinuityR29b.kernelNormed
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
variable {L κ : ℝ} [Fact (0 < L)]

def SegmentResult (κ : ℝ) (a b : ℝ) (γ : ℝ → ℂ) : Prop :=
  ConvergesOnRadius 8
    (intList (fun x => inverseKernels (L := L) κ (γ x)) a b)
    (intLimit (fun x => inverseLimit (L := L) κ (γ x)) a b) ∧
  ∀ N : ℕ, 0 < N →
    RadiusBound.represented (intList (fun x => inverseKernels (L := L) κ (γ x)) a b N) =
      ∫ x in a..b, inverseOp L κ 1 (eps N) N (γ x)

theorem contour_mem_tube (n : ℤ) {z : ℂ}
    (hz : z ∈ Gam (momentum L n-halfWidth L) (momentum L n+halfWidth L) (halfWidth L)) :
    z ∈ tube L n := by
  have hL : 0 < L := Fact.out
  exact contour_ball_subset_band (by unfold halfWidth; positivity) hz
    (mem_closedBall_self (by unfold halfWidth; positivity))

theorem actual_segment (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000) (n : ℤ)
    {a b : ℝ} (hab : a ≤ b) (γ : ℝ → ℂ) (hc : Continuous γ)
    (hm : ∀ x ∈ Icc a b, γ x ∈ tube L n) : SegmentResult (L := L) κ a b γ := by
  have hK (N : ℕ) (p : Fin (N+1)) :
      ContinuousOn (fun x => inverseKernels (L := L) κ (γ x) N p) (Icc a b) :=
    (continuousOn_inverseKernels (L := L) hκ hs n N p).comp hc.continuousOn hm
  refine ⟨integrated_converges (by norm_num : (1 : ℝ) ≤ 8) hab
    (fun x => inverseKernels (L := L) κ (γ x))
    (fun x => inverseLimit (L := L) κ (γ x)) hK
    (fun x hx N => radius_bound_inverse hκ hs n (hm x hx) N)
    (fun x hx => (inverse_series_converges hκ hs n (hm x hx)).1), ?_⟩
  intro N hN
  rw [represented_intList (fun x => inverseKernels (L := L) κ (γ x))
    (fun M p => by simpa only [uIcc_of_le hab] using hK M p) N]
  apply intervalIntegral.integral_congr
  intro x hx
  exact represented_actual_cfc hκ hs hN n (hm x (by simpa only [uIcc_of_le hab] using hx))

/-- All four source rectangle segments satisfy the chosen-kernel convergence
and literal CFC representation. No contour/limit exchange is a premise. -/
theorem literal_inverse_edges (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000) (n : ℤ) :
    let a := momentum L n-halfWidth L
    let b := momentum L n+halfWidth L
    let h := halfWidth L
    SegmentResult (L := L) κ a b (fun x => (x : ℂ)+(-h : ℝ)*I) ∧
    SegmentResult (L := L) κ a b (fun x => (x : ℂ)+h*I) ∧
    SegmentResult (L := L) κ (-h) h (fun y => (b : ℂ)+y*I) ∧
    SegmentResult (L := L) κ (-h) h (fun y => (a : ℂ)+y*I) := by
  dsimp only
  have hL : 0 < L := Fact.out
  have hh : 0 < halfWidth L := by unfold halfWidth; positivity
  have hab : momentum L n-halfWidth L ≤ momentum L n+halfWidth L := by linarith
  have hv : -halfWidth L ≤ halfWidth L := by linarith
  refine ⟨actual_segment hκ hs n hab _ (by fun_prop) ?_,
    actual_segment hκ hs n hab _ (by fun_prop) ?_,
    actual_segment hκ hs n hv _ (by fun_prop) ?_,
    actual_segment hκ hs n hv _ (by fun_prop) ?_⟩
  · intro x hx; exact contour_mem_tube n (horizontal_mem hx (Or.inl rfl))
  · intro x hx; exact contour_mem_tube n (horizontal_mem hx (Or.inr rfl))
  · intro y hy; exact contour_mem_tube n (vertical_mem hy (Or.inr rfl))
  · intro y hy; exact contour_mem_tube n (vertical_mem hy (Or.inl rfl))

end QuantumNLS.IndexedInverseContourR29b
#print axioms QuantumNLS.IndexedInverseContourR29b.literal_inverse_edges
