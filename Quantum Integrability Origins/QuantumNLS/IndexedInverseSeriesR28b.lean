import QuantumNLS.IndexedTransferR28b

/-! LOCAL-016: construct the larger inverse's scalar series and apply the
proved LOCAL-013 functional calculus to the actual transfer perturbation.
No expansion or convergence is supplied as an assumption. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
noncomputable section
open Set Metric Filter Topology Complex
open scoped NNReal ENNReal BigOperators
namespace QuantumNLS.IndexedInverseSeriesR28b
open PhysicalTensor KernelDefinition KernelConvergence LocalPlacement
  IndexedInverseR28b IndexedTransferR28b Local013PowerSeries Ext025A7
variable {L κ : ℝ} [Fact (0 < L)]

def centered (κ : ℝ) (z x : ℂ) : ℂ :=
  spectralInverse κ L (W κ) z (spectralMap κ L z 0+x)

def series (κ : ℝ) (z : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  cauchyPowerSeries (centered (L := L) κ z) 0 (rstar/2)

def coeff (κ : ℝ) (z : ℂ) (k : ℕ) : ℂ := series (L := L) κ z k (fun _ => 1)

def inverseKernels (κ : ℝ) (z : ℂ) := psList (coeff (L := L) κ z) (kernels (L := L) κ z)
def inverseLimit (κ : ℝ) (z : ℂ) := psLim (coeff (L := L) κ z) (limitKernels (L := L) κ z)

theorem analytic_centered (hκ : 0 < κ) (n : ℤ) {z x : ℂ}
    (hz : z ∈ tube L n) (hx : ‖x‖ < rstar) : AnalyticAt ℂ (centered (L := L) κ z) x := by
  have hh := (inverse_disk hκ n hz (y := spectralMap κ L z 0+x)
    (by simpa only [add_sub_cancel_left] using hx)).2.2.2.1
  have hc : AnalyticAt ℂ (fun a : ℂ => (z,spectralMap κ L z 0+a)) x :=
    analyticAt_const.prod (analyticAt_const.add analyticAt_id)
  exact hh.comp (x := x) (f := fun a : ℂ => (z,spectralMap κ L z 0+a)) hc

theorem series_represents (hκ : 0 < κ) (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) :
    HasFPowerSeriesOnBall (centered (L := L) κ z) (series (L := L) κ z) 0
      (ENNReal.ofReal (rstar/2)) := by
  let R : ℝ≥0 := ⟨rstar/2,by norm_num [rstar]⟩
  have hR : (0 : ℝ) < R := by change 0 < rstar/2; norm_num [rstar]
  have hd : DifferentiableOn ℂ (centered (L := L) κ z) (closedBall 0 R) := by
    intro x hx
    apply (analytic_centered hκ n hz _).differentiableAt.differentiableWithinAt
    have hh : ‖x‖ ≤ rstar/2 := by simpa only [mem_closedBall_zero_iff,show (R : ℝ) = rstar/2 from rfl] using hx
    linarith [show (0 : ℝ) < rstar by norm_num [rstar]]
  have hp := hd.hasFPowerSeriesOnBall (show 0 < R by exact_mod_cast hR)
  rw [show ENNReal.ofReal (rstar/2) = (R : ℝ≥0∞) from (ENNReal.coe_nnreal_eq R).symm]
  exact hp

theorem scalar_series (hκ : 0 < κ) (n : ℤ) {z x : ℂ}
    (hz : z ∈ tube L n) (hx : ‖x‖ < rstar/2) :
    HasSum (fun k => coeff (L := L) κ z k*x^k) (centered (L := L) κ z x) := by
  have hm : x ∈ eball (0 : ℂ) (ENNReal.ofReal (rstar/2)) := by
    simpa only [mem_eball,edist_dist,dist_zero_right,ENNReal.ofReal_lt_ofReal_iff
      (show 0 < rstar/2 by norm_num [rstar])] using hx
  have hh := (series_represents hκ n hz).hasSum hm
  simpa only [zero_add] using (show HasSum (fun k => coeff (L := L) κ z k*x^k)
      (centered (L := L) κ z (0+x)) from by
    convert hh using 1
    funext k
    simp only [coeff,series,cauchyPowerSeries,ContinuousMultilinearMap.mkPiRing_apply,
      Fin.prod_const,one_pow,smul_eq_mul]
    ring)

theorem norm_coeff_le (κ : ℝ) (z : ℂ) (k : ℕ) :
    ‖coeff (L := L) κ z k‖ ≤ ‖series (L := L) κ z k‖ := by
  have hh := (series (L := L) κ z k).le_opNorm (fun _ => (1 : ℂ))
  simpa only [coeff,norm_one,Finset.prod_const_one,mul_one] using hh

theorem coefficient_summable (hκ : 0 < κ) (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) :
    Summable (fun k => ‖coeff (L := L) κ z k‖*(rstar/4)^k) := by
  have hp := series_represents hκ n hz
  let ρ : ℝ≥0 := ⟨rstar/4,by norm_num [rstar]⟩
  have hh : (ρ : ℝ≥0∞) < (series (L := L) κ z).radius := by
    apply lt_of_lt_of_le _ hp.r_le
    rw [ENNReal.coe_nnreal_eq]
    apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num [rstar])).mpr
    change rstar/4 < rstar/2
    norm_num [rstar]
  have hs := (series (L := L) κ z).summable_norm_mul_pow hh
  have hρ0 : (0 : ℝ) ≤ rstar/4 := by norm_num [rstar]
  exact Summable.of_nonneg_of_le
    (fun k => mul_nonneg (norm_nonneg _) (pow_nonneg hρ0 k))
    (fun k => mul_le_mul_of_nonneg_right (norm_coeff_le κ z k) (pow_nonneg hρ0 k)) hs

/-- A radius-8 convergent expansion of the larger inverse power series,
with its represented operator and principal symbol proved by LOCAL-013. -/
theorem inverse_series_converges (hκ : 0 < κ) (hsmall : κ*L ≤ 1/1000000000000)
    (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) :
    ConvergesOnRadius 8 (inverseKernels (L := L) κ z) (inverseLimit (L := L) κ z) ∧
    (∀ N, RadiusBound.represented (inverseKernels (L := L) κ z N) =
      ∑' k, coeff (L := L) κ z k • (RadiusBound.represented (kernels (L := L) κ z N))^k) ∧
    (∀ v : L2T L, ‖v‖^2 ≤ 8 → symbol (inverseLimit (L := L) κ z) v =
      ∑' k, coeff (L := L) κ z k * (symbol (limitKernels (L := L) κ z) v)^k) := by
  have hM : (0 : ℝ) ≤ 256*(κ*L) := by have hL : 0 < L := Fact.out; positivity
  have hρ : 256*(κ*L) < rstar/4 := by norm_num [rstar] at *; linarith
  exact powerSeries_converges (H := L2T L) (r := 8) (M := 256*(κ*L))
    (ρ := rstar/4) (c := coeff (L := L) κ z)
    (A := kernels (L := L) κ z) (Alim := limitKernels (L := L) κ z)
    (by norm_num) (transfer_converges hκ hsmall n hz)
    hM (radius_bound hκ hsmall n hz) hρ (coefficient_summable hκ n hz)

end QuantumNLS.IndexedInverseSeriesR28b
#print axioms QuantumNLS.IndexedInverseSeriesR28b.scalar_series
#print axioms QuantumNLS.IndexedInverseSeriesR28b.coefficient_summable
#print axioms QuantumNLS.IndexedInverseSeriesR28b.inverse_series_converges
