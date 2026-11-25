import QuantumNLS.Q07LogBoundsR16
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Full-operator continuity and differentiation of finite parameter integrals.
These lemmas are for the actual remaining rectangular contour interchange. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Metric Filter Topology MeasureTheory
namespace QuantumNLS.Q07ContourDifferentiationR16

section Partial
variable {E Z F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def fieldPartial (f : E × Z → F) (p : E × Z) : E →L[ℝ] F :=
  fderiv ℝ (fun u => f (u,p.2)) p.1

omit [CompleteSpace F] in
theorem partial_eq {f : E × Z → F} {p : E × Z} (hf : DifferentiableAt ℝ f p) :
    fieldPartial f p = (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ E Z) := by
  exact (hf.hasFDerivAt.comp p.1
    ((hasFDerivAt_id p.1).prodMk (hasFDerivAt_const (c := p.2) p.1))).fderiv

/-- Partial derivatives of a joint analytic map remain analytic in the full
operator norm. The germ identity with the joint derivative is proved. -/
theorem analytic_partial {f : E × Z → F} {p : E × Z} (hf : AnalyticAt ℝ f p) :
    AnalyticAt ℝ (fieldPartial f) p := by
  let A : ((E × Z) →L[ℝ] F) →L[ℝ] (E →L[ℝ] F) :=
    (ContinuousLinearMap.compL ℝ E (E × Z) F).flip (ContinuousLinearMap.inl ℝ E Z)
  have ha : AnalyticAt ℝ (fun q => A (fderiv ℝ f q)) p :=
    (A.analyticAt _).comp hf.fderiv
  apply ha.congr
  filter_upwards [hf.eventually_analyticAt] with q hq
  exact (partial_eq hq.differentiableAt).symm
end Partial

section Intervals
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Joint analyticity and a proved full operator bound justify the first
finite-interval differentiation, including operator-valued targets. -/
theorem first_interval {U : Set E} (hU : IsOpen U) {a b : ℝ} (hab : a ≤ b)
    {f : E × ℝ → F} (hf : ∀ x ∈ U, ∀ t ∈ Icc a b, AnalyticAt ℝ f (x,t))
    {C : ℝ} (hB : ∀ x ∈ U, ∀ t ∈ Icc a b, ‖fieldPartial f (x,t)‖ ≤ C)
    {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun y => ∫ t in a..b, f (y,t))
      (∫ t in a..b, fieldPartial f (x,t)) x := by
  have hc : ∀ y ∈ U, ContinuousOn (fun t => f (y,t)) (Icc a b) := by
    intro y hy t ht
    exact ((hf y hy t ht).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hdc : ∀ y ∈ U, ContinuousOn (fun t => fieldPartial f (y,t)) (Icc a b) := by
    intro y hy t ht
    exact ((analytic_partial (hf y hy t ht)).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ := volume)
    (s := U) (F := fun y t => f (y,t)) (F' := fun y t => fieldPartial f (y,t))
    (bound := fun _ => C) (hU.mem_nhds hx)
  · filter_upwards [hU.mem_nhds hx] with y hy
    rw [uIoc_of_le hab]
    exact (hc y hy).aestronglyMeasurable_of_subset_isCompact isCompact_Icc
      measurableSet_Ioc Ioc_subset_Icc_self
  · apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using hc x hx
  · rw [uIoc_of_le hab]
    exact (hdc x hx).aestronglyMeasurable_of_subset_isCompact isCompact_Icc
      measurableSet_Ioc Ioc_subset_Icc_self
  · rw [uIoc_of_le hab]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht y hy
    exact hB y hy t ⟨ht.1.le,ht.2⟩
  · exact intervalIntegrable_const
  · rw [uIoc_of_le hab]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht y hy
    have ha : AnalyticAt ℝ (fun z : E => f (z,t)) y :=
      (hf y hy t ⟨ht.1.le,ht.2⟩).comp (f := fun z : E => (z,t))
        (analyticAt_id.prod analyticAt_const)
    exact ha.differentiableAt.hasFDerivAt

/-- Twice differentiating the finite integral in the full Frechet sense.
Both derivative fields are the canonical actual partial derivatives. -/
theorem second_interval {U : Set E} (hU : IsOpen U) {a b : ℝ} (hab : a ≤ b)
    {f : E × ℝ → F} (hf : ∀ x ∈ U, ∀ t ∈ Icc a b, AnalyticAt ℝ f (x,t))
    {C1 C2 : ℝ}
    (hB1 : ∀ x ∈ U, ∀ t ∈ Icc a b, ‖fieldPartial f (x,t)‖ ≤ C1)
    (hB2 : ∀ x ∈ U, ∀ t ∈ Icc a b, ‖fieldPartial (fieldPartial f) (x,t)‖ ≤ C2)
    {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun y => ∫ t in a..b, f (y,t)) (∫ t in a..b, fieldPartial f (x,t)) x ∧
    HasFDerivAt (fderiv ℝ (fun y => ∫ t in a..b, f (y,t)))
      (∫ t in a..b, fieldPartial (fieldPartial f) (x,t)) x := by
  have hd1 := fun y hy => first_interval hU hab hf hB1 (x := y) hy
  have hd2 := first_interval hU hab
    (fun y hy t ht => analytic_partial (hf y hy t ht)) hB2 hx
  have he : fderiv ℝ (fun y => ∫ t in a..b, f (y,t)) =ᶠ[𝓝 x]
      (fun y => ∫ t in a..b, fieldPartial f (y,t)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hd1 y hy).fderiv
  exact ⟨hd1 x hx, hd2.congr_of_eventuallyEq he⟩
end Intervals

open PhysicalTensor (L2T)
open Q07LogDifferentialsR16
variable {L κ : ℝ} [Fact (0 < L)]

theorem analytic_joint_logarithm (hκ : 0 < κ) {p : L2T L × ℂ}
    (hp : RootCauchyJointR9.Regular κ p) :
    AnalyticAt ℝ (fun q : L2T L × ℂ => logarithm hκ q.2 q.1) p :=
  analyticAt_const.mul (RootCauchyJointR9.analyticAt_joint_regular hκ p hp)

theorem analytic_joint_first (hκ : 0 < κ) {p : L2T L × ℂ}
    (hp : RootCauchyJointR9.Regular κ p) :
    AnalyticAt ℝ (fun q : L2T L × ℂ => fderiv ℝ (logarithm hκ q.2) q.1) p :=
  analytic_partial (analytic_joint_logarithm hκ hp)

/-- In particular the actual full second field differential is continuous in
operator norm on the spectral contour, including its real band crossings. -/
theorem analytic_joint_second (hκ : 0 < κ) {p : L2T L × ℂ}
    (hp : RootCauchyJointR9.Regular κ p) :
    AnalyticAt ℝ (fun q : L2T L × ℂ => fderiv ℝ (fderiv ℝ (logarithm hκ q.2)) q.1) p :=
  analytic_partial (analytic_joint_first hκ hp)

end QuantumNLS.Q07ContourDifferentiationR16
