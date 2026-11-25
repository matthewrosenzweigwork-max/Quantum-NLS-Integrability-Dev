import QuantumNLS.IndexedQuotientKernelsR30b

/-! Parameter continuity of the actual quotient kernels, proved through
joint scalar holomorphy and the uniform geometric coefficient majorant. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 20000
set_option linter.unusedSectionVars false
noncomputable section
open Set Metric Filter Topology Complex
namespace QuantumNLS.IndexedQuotientContinuityR30b
open Local013Powers
open PhysicalTensor TensorCarrier KernelDefinition KernelConvergence LocalPlacement Local013PowerSeries
  IndexedInverseR28b IndexedTransferR28b IndexedInverseBoundsR29b IndexedCoefficientAnalyticR29b
  IndexedQuotientKernelsR30b IndexedKernelContinuityR29b
  LOCAL009R22Geometry LOCAL009R22Ratio Ext025A7
attribute [local instance] IndexedKernelContinuityR29b.kernelNormed
attribute [local instance] IndexedCauchyKernelsR30b.kernelComplexSpace
variable {L κ : ℝ} [Fact (0 < L)]

def jointScalar (κ : ℝ) (p : ℂ × ℂ) : ℂ := scalar (L := L) κ p.1 p.2

theorem analytic_jointScalar (hκ : 0 < κ) (n : ℤ) :
    AnalyticOnNhd ℂ (jointScalar (L := L) κ) (tube L n ×ˢ ball 0 rstar) := by
  intro p hp
  have hi := analytic_jointCentered hκ n p hp
  have hw := (inverse_disk hκ n hp.1 (y := spectralMap κ L p.1 0+p.2)
    (by simpa only [add_sub_cancel_left] using mem_ball_zero_iff.mp hp.2)).1
  have hn : spectralDerivative κ L p.1 (jointCentered (L := L) κ p) ≠ 0 :=
    norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le (by positivity : (0 : ℝ) < 3*κ/8)
      (derivative_lower hκ (W_small hκ).le
        (source_phase_bound (Fact.out : 0 < L) n hp.1)
        (source_gap_bound (Fact.out : 0 < L) n hp.1) (ball_subset_closedBall hw))))
  change AnalyticAt ℂ (fun q : ℂ × ℂ =>
    spectralMap κ L q.1 (jointCentered (L := L) κ q) /
    spectralDerivative κ L q.1 (jointCentered (L := L) κ q)) p
  have hnum : AnalyticAt ℂ (fun q : ℂ × ℂ => spectralMap κ L q.1 (jointCentered (L := L) κ q)) p :=
    (spectralMap_analyticAt κ L _).comp (analyticAt_fst.prod hi)
  have hden : AnalyticAt ℂ (fun q : ℂ × ℂ => spectralDerivative κ L q.1 (jointCentered (L := L) κ q)) p := by
    unfold spectralDerivative
    exact ((analyticAt_const.mul (analyticAt_const.mul hi).cexp).add
      (((analyticAt_const.mul analyticAt_fst).mul analyticAt_const).cexp.mul
        (analyticAt_const.mul (analyticAt_const.mul hi).cexp)))
  exact hnum.div hden hn

theorem coeff_eq_partial (hκ : 0 < κ) (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) (k : ℕ) :
    IndexedQuotientKernelsR30b.coeff (L := L) κ z k = partialSecond (jointScalar (L := L) κ) k (z,0)/(k.factorial : ℂ) := by
  have hs := (IndexedQuotientKernelsR30b.series_represents hκ n hz).factorial_smul (1 : ℂ) k
  rw [← iteratedDeriv_eq_iteratedFDeriv] at hs
  change k.factorial • IndexedQuotientKernelsR30b.coeff (L := L) κ z k = iteratedDeriv k (scalar (L := L) κ z) 0 at hs
  have hp := partialSecond_eq_slice (analytic_jointScalar hκ n) isOpen_ball k hz
    (show (0 : ℂ) ∈ ball 0 rstar by simp [rstar])
  rw [hp]
  apply (eq_div_iff (by exact_mod_cast k.factorial_ne_zero : (k.factorial : ℂ) ≠ 0)).mpr
  simpa only [jointScalar,nsmul_eq_mul,mul_comm] using hs

/-- Each actual quotient coefficient is holomorphic on every source tube. -/
theorem analytic_coeff (hκ : 0 < κ) (n : ℤ) (k : ℕ) :
    AnalyticOnNhd ℂ (fun z => IndexedQuotientKernelsR30b.coeff (L := L) κ z k) (tube L n) := by
  intro z hz
  have hp := (analytic_partialSecond (analytic_jointScalar hκ n) k) (z,0)
    ⟨hz,by simp [rstar]⟩
  have ha := (hp.comp (x := z) (f := fun a : ℂ => (a,0))
    (analyticAt_id.prod analyticAt_const)).div_const (c := (k.factorial : ℂ))
  exact ha.congr (by
    filter_upwards [(LOCAL009R22Geometry.band_open _ _).mem_nhds hz] with w hw
    exact (coeff_eq_partial hκ n hw k).symm)

theorem continuousOn_quotientKernels (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    (n : ℤ) (N : ℕ) (p : Fin (N+1)) :
    ContinuousOn (fun z => quotientKernels (L := L) κ z N p) (tube L n) := by
  have hq := q_bounds hκ hs
  have hq1 : q κ L < 1 := by linarith
  have hg : Summable (fun k : ℕ => ratioBound κ (W κ)*(q κ L)^k) :=
    (summable_geometric_of_lt_one hq.1 hq1).mul_left _
  change ContinuousOn (fun z => ∑' k, IndexedQuotientKernelsR30b.coeff (L := L) κ z k •
    powList (kernels (L := L) κ z) k N p) (tube L n)
  refine continuousOn_tsum (F := BoundedSymmetricKernel (L2T L) p.1)
    (f := fun k z => IndexedQuotientKernelsR30b.coeff (L := L) κ z k • powList (kernels (L := L) κ z) k N p) ?_ hg ?_
  · intro k
    exact ((analytic_coeff (L := L) hκ n k).continuousOn).smul
      ((continuous_apply p).comp (continuous_powList (L := L) κ k N)).continuousOn
  · intro k z hz
    rw [RadiusBound.norm_smul_kernel (H := L2T L)]
    have hk := (norm_coeff_le_radiusBound (H := L2T L) (by norm_num : (1 : ℝ) ≤ 8)
      (powList (kernels (L := L) κ z) k N) p).trans
      (radiusBound_powList_le (H := L2T L) (by norm_num) (radius_bound (L := L) hκ hs n hz) k N)
    calc
      _ ≤ (ratioBound κ (W κ)*(rstar/2)⁻¹^k)*(256*(κ*L))^k :=
        mul_le_mul (IndexedQuotientKernelsR30b.norm_coeff_le_uniform (L := L) hκ n hz k) hk (norm_nonneg _) (by
          exact mul_nonneg (show 0 ≤ ratioBound κ (W κ) by unfold ratioBound; positivity) (pow_nonneg (by norm_num [rstar]) _))
      _ = ratioBound κ (W κ)*(q κ L)^k := by
        rw [mul_assoc,← mul_pow]
        congr 2
        unfold q
        ring


end QuantumNLS.IndexedQuotientContinuityR30b
#print axioms QuantumNLS.IndexedQuotientContinuityR30b.continuousOn_quotientKernels
