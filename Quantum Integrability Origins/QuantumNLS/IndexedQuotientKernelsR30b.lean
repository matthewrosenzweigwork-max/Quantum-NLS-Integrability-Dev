import QuantumNLS.IndexedCauchyKernelsR30b

/-! A direct scalar holomorphic functional calculus for the literal f/f'
quotient composed with the larger inverse. All disk, denominator and series
hypotheses are proved for the physical objects. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
noncomputable section
open Set Metric Filter Topology Complex
open scoped NNReal ENNReal BigOperators
namespace QuantumNLS.IndexedQuotientKernelsR30b
open PhysicalTensor KernelDefinition KernelConvergence LocalPlacement Local013PowerSeries
  IndexedInverseR28b IndexedTransferR28b IndexedInverseBoundsR29b IndexedCFCBindingR29b
  LOCAL009R22Ratio LOCAL009R22Geometry LOCAL009R23PhysicalInverse
  LOCAL009R23OperatorContour LOCAL009R22LiteralScalar Ext025A7
variable {L κ : ℝ} [Fact (0 < L)]

def scalar (κ : ℝ) (z x : ℂ) : ℂ :=
  ratio κ L z (IndexedInverseSeriesR28b.centered (L := L) κ z x)

theorem analytic_scalar (hκ : 0 < κ) (n : ℤ) {z x : ℂ}
    (hz : z ∈ tube L n) (hx : ‖x‖ < rstar) : AnalyticAt ℂ (scalar (L := L) κ z) x := by
  have hw := (inverse_disk hκ n hz (y := spectralMap κ L z 0+x)
    (by simpa only [add_sub_cancel_left] using hx)).1
  have hn : spectralDerivative κ L z (IndexedInverseSeriesR28b.centered (L := L) κ z x) ≠ 0 :=
    norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le (by positivity : (0 : ℝ) < 3*κ/8)
      (derivative_lower hκ (W_small hκ).le
        (source_phase_bound (Fact.out : 0 < L) n hz)
        (source_gap_bound (Fact.out : 0 < L) n hz) (ball_subset_closedBall hw))))
  have ha : AnalyticAt ℂ (ratio κ L z) (IndexedInverseSeriesR28b.centered (L := L) κ z x) := by
    change AnalyticAt ℂ (fun w => spectralMap κ L z w/spectralDerivative κ L z w) _
    apply AnalyticAt.div _ _ hn
    · unfold spectralMap; fun_prop
    · unfold spectralDerivative; fun_prop
  exact ha.comp (x := x) (IndexedInverseSeriesR28b.analytic_centered hκ n hz hx)

def series (κ : ℝ) (z : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  cauchyPowerSeries (scalar (L := L) κ z) 0 (rstar/2)

def coeff (κ : ℝ) (z : ℂ) (k : ℕ) : ℂ := series (L := L) κ z k (fun _ => 1)

def quotientKernels (κ : ℝ) (z : ℂ) := psList (coeff (L := L) κ z) (kernels (L := L) κ z)
def quotientLimit (κ : ℝ) (z : ℂ) := psLim (coeff (L := L) κ z) (limitKernels (L := L) κ z)

theorem series_represents (hκ : 0 < κ) (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) :
    HasFPowerSeriesOnBall (scalar (L := L) κ z) (series (L := L) κ z) 0
      (ENNReal.ofReal (rstar/2)) := by
  let R : ℝ≥0 := ⟨rstar/2,by norm_num [rstar]⟩
  have hR : (0 : ℝ) < R := by change 0 < rstar/2; norm_num [rstar]
  have hd : DifferentiableOn ℂ (scalar (L := L) κ z) (closedBall 0 R) := by
    intro x hx
    apply (analytic_scalar hκ n hz _).differentiableAt.differentiableWithinAt
    have hh : ‖x‖ ≤ rstar/2 := by simpa only [mem_closedBall_zero_iff,show (R : ℝ) = rstar/2 from rfl] using hx
    linarith [show (0 : ℝ) < rstar by norm_num [rstar]]
  have hp := hd.hasFPowerSeriesOnBall (show 0 < R by exact_mod_cast hR)
  rw [show ENNReal.ofReal (rstar/2) = (R : ℝ≥0∞) from (ENNReal.coe_nnreal_eq R).symm]
  exact hp

theorem scalar_series (hκ : 0 < κ) (n : ℤ) {z x : ℂ}
    (hz : z ∈ tube L n) (hx : ‖x‖ < rstar/2) :
    HasSum (fun k => coeff (L := L) κ z k*x^k) (scalar (L := L) κ z x) := by
  have hm : x ∈ eball (0 : ℂ) (ENNReal.ofReal (rstar/2)) := by
    simpa only [mem_eball,edist_dist,dist_zero_right,ENNReal.ofReal_lt_ofReal_iff
      (show 0 < rstar/2 by norm_num [rstar])] using hx
  have hh := (series_represents hκ n hz).hasSum hm
  simpa only [zero_add] using (show HasSum (fun k => coeff (L := L) κ z k*x^k)
      (scalar (L := L) κ z (0+x)) from by
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


theorem scalar_bound (hκ : 0 < κ) (n : ℤ) {z x : ℂ}
    (hz : z ∈ tube L n) (hx : ‖x‖ < rstar) :
    ‖scalar (L := L) κ z x‖ ≤ ratioBound κ (W κ) := by
  exact ratio_norm_le hκ (W_small hκ).le
    (source_phase_bound (Fact.out : 0 < L) n hz)
    (source_gap_bound (Fact.out : 0 < L) n hz)
    (ball_subset_closedBall (inverse_disk hκ n hz (y := spectralMap κ L z 0+x)
      (by simpa only [add_sub_cancel_left] using hx)).1)

theorem norm_coeff_le_uniform (hκ : 0 < κ) (n : ℤ) {z : ℂ}
    (hz : z ∈ tube L n) (k : ℕ) :
    ‖coeff (L := L) κ z k‖ ≤ ratioBound κ (W κ)*(rstar/2)⁻¹^k := by
  have hb : ∀ θ : ℝ, ‖scalar (L := L) κ z (circleMap 0 (rstar/2) θ)‖ ≤ ratioBound κ (W κ) := by
    intro θ
    apply scalar_bound hκ n hz
    rw [norm_circleMap_zero,abs_of_pos (by norm_num [rstar] : 0 < rstar/2)]
    norm_num [rstar]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 2*Real.pi)
    (f := fun θ => ‖scalar (L := L) κ z (circleMap 0 (rstar/2) θ)‖)
    (fun θ _ => by simpa only [Real.norm_eq_abs,abs_norm] using hb θ)
  have hi' : (∫ θ : ℝ in 0..2*Real.pi,
      ‖scalar (L := L) κ z (circleMap 0 (rstar/2) θ)‖) ≤ ratioBound κ (W κ)*(2*Real.pi) := by
    have hp : |2*Real.pi-0| = 2*Real.pi := by
      rw [sub_zero,abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    have hh := (le_abs_self _).trans hi
    simpa only [hp] using hh
  calc
    _ ≤ ‖series (L := L) κ z k‖ := norm_coeff_le κ z k
    _ ≤ ((2*Real.pi)⁻¹ * ∫ θ : ℝ in 0..2*Real.pi,
        ‖scalar (L := L) κ z (circleMap 0 (rstar/2) θ)‖)*(rstar/2)⁻¹^k := by
      simpa only [series,abs_of_pos (by norm_num [rstar] : 0 < rstar/2)] using
        norm_cauchyPowerSeries_le (scalar (L := L) κ z) 0 (rstar/2) k
    _ ≤ ((2*Real.pi)⁻¹*(ratioBound κ (W κ)*(2*Real.pi)))*(rstar/2)⁻¹^k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi' (by positivity))
        (by norm_num [rstar])
    _ = _ := by field_simp

theorem quotient_converges (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) :
    ConvergesOnRadius 8 (quotientKernels (L := L) κ z) (quotientLimit (L := L) κ z) ∧
    (∀ N, RadiusBound.represented (quotientKernels (L := L) κ z N) =
      ∑' k, coeff (L := L) κ z k • (RadiusBound.represented (kernels (L := L) κ z N))^k) ∧
    (∀ v : L2T L, ‖v‖^2 ≤ 8 → symbol (quotientLimit (L := L) κ z) v =
      ∑' k, coeff (L := L) κ z k * (symbol (limitKernels (L := L) κ z) v)^k) := by
  exact powerSeries_converges (H := L2T L) (r := 8) (M := 256*(κ*L))
    (ρ := rstar/4) (c := coeff (L := L) κ z)
    (A := kernels (L := L) κ z) (Alim := limitKernels (L := L) κ z)
    (by norm_num) (transfer_converges hκ hs n hz)
    (by have hL : 0 < L := Fact.out; positivity) (radius_bound hκ hs n hz)
    (by norm_num [rstar] at *; linarith) (coefficient_summable hκ n hz)


def quotientBound (κ L : ℝ) : ℝ := ratioBound κ (W κ)/(1-q κ L)

theorem quotient_radius_bound (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) (N : ℕ) :
    RadiusBound.radiusBound 8 (quotientKernels (L := L) κ z N) ≤ quotientBound κ L := by
  have hq := q_bounds hκ hs
  have hg : Summable (fun k : ℕ => ratioBound κ (W κ)*(q κ L)^k) :=
    (summable_geometric_of_lt_one hq.1 (by linarith)).mul_left _
  have hm := summable_majorant
    (show 0 ≤ 256*(κ*L) by have hL : 0 < L := Fact.out; positivity)
    (show 256*(κ*L) < rstar/4 by norm_num [rstar] at *; linarith)
    (coefficient_summable hκ n hz)
  calc
    _ ≤ ∑' k, ‖coeff (L := L) κ z k‖*(256*(κ*L))^k :=
      radiusBound_psList_le (by norm_num) (radius_bound hκ hs n hz) hm N
    _ ≤ ∑' k, ratioBound κ (W κ)*(q κ L)^k := by
      apply Summable.tsum_le_tsum _ hm hg
      intro k
      calc
        _ ≤ (ratioBound κ (W κ)*(rstar/2)⁻¹^k)*(256*(κ*L))^k :=
          mul_le_mul_of_nonneg_right (norm_coeff_le_uniform hκ n hz k)
            (by have hL : 0 < L := Fact.out; positivity)
        _ = _ := by rw [mul_assoc,← mul_pow]; congr 2; unfold q; ring
    _ = quotientBound κ L := by
      rw [tsum_mul_left,tsum_geometric_of_lt_one hq.1 (by linarith)]
      unfold quotientBound
      ring

/-- The series represents exactly the actual diagonal f/f' quotient. -/
theorem represented_quotient (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    {N : ℕ} (hN : 0 < N) (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) :
    RadiusBound.represented (quotientKernels (L := L) κ z N) = quotientOp L κ 1 (eps N) N z := by
  let b := basis (L := L) hκ (eps_pos hN) hN
  let s := fun m : BetheLabels.MArr N =>
    TransferProductCorrection.transferS (κ*eps N) L (BetheLabels.arrRoots L (κ*eps N) m) z
  let s0 := spectralMap κ L z 0
  let Y := RadiusBound.represented (kernels (L := L) κ z N)
  have hy : ∀ m, Y (b m) = (s m-s0) • b m := perturbation_eigen hκ hN hs n hz
  have hY : ‖Y‖ ≤ 256*(κ*L) := perturbation_norm hκ hs n hz N
  have hval : ∀ m, ‖s m-s0‖ ≤ 256*(κ*L) := fun m =>
    (norm_eigen_le b Y _ m (hy m)).trans hY
  have hc := summable_majorant
    (show 0 ≤ 256*(κ*L) by have hL : 0 < L := Fact.out; positivity)
    (show 256*(κ*L) < rstar/4 by norm_num [rstar] at *; linarith)
    (coefficient_summable hκ n hz)
  apply NormalityBridge.clm_ext_basis b
  intro m
  rw [(quotient_converges hκ hs n hz).2.1 N]
  have hv := scalar_series hκ n hz
    (show ‖s m-s0‖ < rstar/2 by have := hval m; norm_num [rstar] at *; linarith)
  have he := series_eigen Y (b m) (s m-s0) (hy m) (coeff (L := L) κ z)
    (show 0 ≤ 256*(κ*L) by have hL : 0 < L := Fact.out; positivity) hY hc hv
  change (∑' k, coeff (L := L) κ z k • Y^k) (b m) = _
  rw [he]
  have hq := (quotient_spec hκ (by norm_num : (0 : ℝ) < 1)
    (show κ*L*1 ≤ 1/1000000 by nlinarith) hN (eps_pos hN) (eps_le_one hN)
    (by rw [eps_budget hN]) n hz).1 m
  rw [show quotientOp L κ 1 (eps N) N z (b m) = _ from hq]
  congr 1
  unfold scalar IndexedInverseSeriesR28b.centered
  dsimp [s0]
  rw [add_sub_cancel]
  exact congrArg (ratio κ L z) (actual_scalar_branch hκ hs hN n hz m)

end QuantumNLS.IndexedQuotientKernelsR30b
#print axioms QuantumNLS.IndexedQuotientKernelsR30b.analytic_scalar
#print axioms QuantumNLS.IndexedQuotientKernelsR30b.quotient_converges

#print axioms QuantumNLS.IndexedQuotientKernelsR30b.quotient_radius_bound
#print axioms QuantumNLS.IndexedQuotientKernelsR30b.represented_quotient
