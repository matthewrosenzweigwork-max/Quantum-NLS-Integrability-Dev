import QuantumNLS.IndexedInverseSeriesR28b

/-! LOCAL-016: identify the constructed series with the actual LOCAL-009 CFC
inverse at coupling κ/N. Imported modules are read-only. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
noncomputable section
open Complex Set Metric Filter Topology
open scoped BigOperators
namespace QuantumNLS.IndexedCFCBindingR29b
open PhysicalTensor KernelDefinition KernelConvergence LocalPlacement
  IndexedInverseR28b IndexedTransferR28b IndexedInverseSeriesR28b
  LOCAL009R23PhysicalInverse LOCAL009R22LiteralScalar LOCAL009R22Geometry
  LOCAL009R23TransferSpectrum LOCAL009R22Derivative Ext025A7

section Generic
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
theorem pow_eigen (A : H →L[ℂ] H) (v : H) (a : ℂ) (he : A v = a • v)
    (k : ℕ) : (A^k) v = a^k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',mul_apply_eq_comp,ih,map_smul,he,smul_smul,pow_succ]

theorem series_eigen (A : H →L[ℂ] H) (v : H) (a : ℂ) (he : A v = a • v)
    (c : ℕ → ℂ) {M : ℝ} (hM : 0 ≤ M) (hA : ‖A‖ ≤ M)
    (hc : Summable (fun k => ‖c k‖*M^k)) {s : ℂ}
    (hs : HasSum (fun k => c k*a^k) s) :
    (∑' k, c k • A^k) v = s • v := by
  have hp (k : ℕ) : ‖A^k‖ ≤ M^k := by
    induction k with
    | zero =>
      change ‖ContinuousLinearMap.id ℂ H‖ ≤ 1
      exact ContinuousLinearMap.norm_id_le
    | succ k ih =>
      rw [pow_succ,pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul ih hA (norm_nonneg _) (pow_nonneg hM _))
  have hsum : Summable (fun k => c k • A^k) :=
    Summable.of_norm_bounded hc (fun k => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left
        (hp k) (norm_nonneg _))
  have hh := hsum.hasSum.mapL (ContinuousLinearMap.apply ℂ H v)
  have hv := hs.smul_const v
  apply hh.unique
  simpa only [ContinuousLinearMap.apply_apply,smul_apply,pow_eigen A v a he,
    smul_smul,smul_eq_mul] using hv
end Generic

variable {L κ : ℝ} [Fact (0 < L)]
def eps (N : ℕ) : ℝ := (N : ℝ)⁻¹

theorem eps_pos {N : ℕ} (hN : 0 < N) : 0 < eps N := by unfold eps; positivity

theorem eps_budget {N : ℕ} (hN : 0 < N) : eps N*N = 1 := by
  unfold eps
  exact inv_mul_cancel₀ (by exact_mod_cast hN.ne')

theorem eps_le_one {N : ℕ} (hN : 0 < N) : eps N ≤ 1 := by
  unfold eps
  exact inv_le_one_of_one_le₀ (by exact_mod_cast hN)

theorem transfer_eq {N : ℕ} (hN : 0 < N) (z : ℂ) :
    transfer L κ (eps N) N z = NormalizedTransfer.normalizedTransfer L κ N z := by
  unfold transfer
  rw [mul_assoc,eps_budget hN,mul_one]

theorem perturbation_norm (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) (N : ℕ) :
    ‖RadiusBound.represented (kernels (L := L) κ z N)‖ ≤ 256*(κ*L) :=
  (RadiusBound.norm_le_radiusBound (by norm_num) rfl).trans (radius_bound hκ hs n hz N)

theorem perturbation_eigen (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)
    (hs : κ*L ≤ 1/1000000000000) (n : ℤ) {z : ℂ} (hz : z ∈ tube L n)
    (m : BetheLabels.MArr N) :
    RadiusBound.represented (kernels (L := L) κ z N) (basis hκ (eps_pos hN) hN m) =
      (TransferProductCorrection.transferS (κ*eps N) L (BetheLabels.arrRoots L (κ*eps N) m) z -
        spectralMap κ L z 0) • basis hκ (eps_pos hN) hN m := by
  have hn : ∀ j, z ≠ (BetheLabels.arrRoots L (κ*eps N) m j : ℂ) := by
    intro j he
    have hb := actual_band_separation hκ (eps_pos hN) hN (M := 1)
      (by nlinarith) (by rw [eps_budget hN]) n m hz j
    rw [he,sub_self,norm_zero] at hb
    have hL : 0 < L := Fact.out
    have hd : 0 < halfWidth L/2 := by unfold halfWidth; positivity
    linarith
  rw [represented_kernels,← transfer_eq hN]
  change transfer L κ (eps N) N z (basis hκ (eps_pos hN) hN m) -
    (1+Complex.exp (I*z*L)) • basis hκ (eps_pos hN) hN m = _
  rw [transfer_eigen hκ (eps_pos hN) hN m hn,← sub_smul]
  congr 2
  simp [spectralMap]

/-- The radius-8 inverse-series kernels represent the CFC with the larger
inverse branch. Every spectral and summability hypothesis is discharged. -/
theorem represented_large_cfc (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    {N : ℕ} (hN : 0 < N) (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) :
    RadiusBound.represented (inverseKernels (L := L) κ z N) =
      normalCalc (spectralInverse κ L (W κ) z) (transfer L κ (eps N) N z) := by
  let b := basis (L := L) hκ (eps_pos hN) hN
  let s := fun m : BetheLabels.MArr N =>
    TransferProductCorrection.transferS (κ*eps N) L (BetheLabels.arrRoots L (κ*eps N) m) z
  let s0 := spectralMap κ L z 0
  let Y := RadiusBound.represented (kernels (L := L) κ z N)
  have hy : ∀ m, Y (b m) = (s m-s0) • b m := perturbation_eigen hκ hN hs n hz
  have hY : ‖Y‖ ≤ 256*(κ*L) := perturbation_norm hκ hs n hz N
  have hval : ∀ m, ‖s m-s0‖ ≤ 256*(κ*L) := fun m =>
    (LOCAL009R23OperatorContour.norm_eigen_le b Y _ m (hy m)).trans hY
  have he : ∀ m, transfer L κ (eps N) N z (b m) = s m • b m := by
    intro m
    have hh := hy m
    dsimp [Y] at hh
    rw [represented_kernels,← transfer_eq hN] at hh
    have hzero : spectralMap κ L z 0 = 1+Complex.exp (I*z*L) := by simp [spectralMap]
    change transfer L κ (eps N) N z (b m) - (1+Complex.exp (I*z*L)) • b m =
      (s m-s0) • b m at hh
    dsimp [s0] at hh
    rw [hzero,sub_smul] at hh
    exact sub_left_inj.mp hh
  have hc := Local013PowerSeries.summable_majorant
    (show 0 ≤ 256*(κ*L) by have hL : 0 < L := Fact.out; positivity)
    (show 256*(κ*L) < rstar/4 by norm_num [rstar] at *; linarith)
    (coefficient_summable hκ n hz)
  have hD : κ/2 ≤ ‖spectralLinear κ L z‖ := by
    rw [spectralLinear_norm,abs_of_pos hκ]
    have hg := source_gap_bound (Fact.out : 0 < L) n hz
    nlinarith
  have hmargin : ∀ m, ‖s m-spectralMap κ L z 0‖ ≤
      7/10*‖spectralLinear κ L z‖*W κ := by
    intro m
    have hw := W_pos hκ
    calc
      _ ≤ 256*(κ*L) := hval m
      _ ≤ 7/10*(κ/2)*W κ := by
        have heq : 7/10*(κ/2)*W κ = 7/20000 := by rw [show 7/10*(κ/2)*W κ = 7/20*(κ*W κ) by ring,W_small hκ]; norm_num
        rw [heq]; linarith
      _ ≤ _ := by gcongr
  apply NormalityBridge.clm_ext_basis b
  intro m
  rw [(inverse_series_converges hκ hs n hz).2.1 N]
  have hsval := scalar_series hκ n hz
    (show ‖s m-s0‖ < rstar/2 by have := hval m; norm_num [rstar] at *; linarith)
  have hseries := series_eigen Y (b m) (s m-s0) (hy m) (coeff (L := L) κ z)
    (show 0 ≤ 256*(κ*L) by have hL : 0 < L := Fact.out; positivity) hY hc hsval
  change (∑' k, coeff (L := L) κ z k • Y^k) (b m) = _
  rw [hseries]
  have hcfc := inverse_cfc_eigen b (transfer L κ (eps N) N z) s he hκ
    (W_pos hκ) (W_small hκ).le (band_open _ _)
    (fun a ha => source_phase_bound (Fact.out : 0 < L) n ha)
    (fun a ha => source_gap_bound (Fact.out : 0 < L) n ha) hz hmargin m
  calc
    _ = spectralInverse κ L (W κ) z (s m) • b m := by
      congr 1
      unfold centered
      dsimp [s0]
      rw [add_sub_cancel]
    _ = _ := hcfc.symm


/-- The larger inverse agrees with the original LOCAL-009 branch on every
actual spectral entry; the original branch is proved to lie in the larger disk. -/
theorem actual_scalar_branch (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    {N : ℕ} (hN : 0 < N) (n : ℤ) {z : ℂ} (hz : z ∈ tube L n)
    (m : BetheLabels.MArr N) :
    spectralInverse κ L (W κ) z
        (TransferProductCorrection.transferS (κ*eps N) L (BetheLabels.arrRoots L (κ*eps N) m) z) =
      inverseTransfer κ L (radius L 1) (eps N) (BetheLabels.arrRoots L (κ*eps N) m) z := by
  let d := halfWidth L/2
  let R := radius L 1
  let v := TransferProductCorrection.transferS (κ*eps N) L (BetheLabels.arrRoots L (κ*eps N) m) z
  have hL : 0 < L := Fact.out
  have hd : 0 < d := by dsimp [d,halfWidth]; positivity
  have hR : 0 < R := by dsimp [R,radius,halfWidth]; positivity
  have hsmall : κ*L*1 ≤ 1/1000000 := by nlinarith
  have hkr : κ*R ≤ 1/1000 := by
    have hh := source_small hsmall
    change κ*(2*1/d) ≤ 1/1000
    change κ*1/d ≤ 1/10000 at hh
    calc
      κ*(2*1/d) = 2*(κ*1/d) := by ring
      _ ≤ 1/1000 := by linarith
  have hRW : R ≤ W κ := by
    apply (mul_le_mul_iff_right₀ hκ).mp
    rw [W_small hκ]
    exact hkr
  have hsep : ∀ j, d ≤ ‖z-(BetheLabels.arrRoots L (κ*eps N) m j : ℂ)‖ :=
    actual_band_separation hκ (eps_pos hN) hN hsmall
      (by rw [eps_budget hN]) n m hz
  have ht : ‖v-spectralMap κ L z 0‖ < 3/4*‖spectralLinear κ L z‖*R := by
    exact LOCAL009R22Margin.transfer_target_margin hκ (by norm_num : (0 : ℝ) < 1)
      hd (source_small hsmall) hN (eps_pos hN).le (eps_le_one hN)
      (by rw [eps_budget hN]) _ hsep (source_phase_bound hL n hz) (source_gap_bound hL n hz)
  have small := local009_application κ L hκ hR hkr (band_open _ _)
    (fun a ha => source_phase_bound hL n ha)
    (fun a ha => source_gap_bound hL n ha) hz ht
  have hv : ‖v-spectralMap κ L z 0‖ < rstar := by
    have he := perturbation_eigen hκ hN hs n hz m
    have hb := (LOCAL009R23OperatorContour.norm_eigen_le (basis hκ (eps_pos hN) hN)
      _ _ m he).trans (perturbation_norm hκ hs n hz N)
    change ‖v-spectralMap κ L z 0‖ ≤ 256*(κ*L) at hb
    norm_num [rstar]
    linarith
  apply ((inverse_disk hκ n hz hv).2.2.1 _ _ small.2.1).symm
  exact mem_closedBall_zero_iff.mpr ((mem_ball_zero_iff.mp small.1).le.trans hRW)

/-- The actual LOCAL-009 CFC inverse has the constructed radius-8 expansion.
No CFC equality or inverse-branch agreement is assumed. -/
theorem represented_actual_cfc (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    {N : ℕ} (hN : 0 < N) (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) :
    RadiusBound.represented (inverseKernels (L := L) κ z N) =
      inverseOp L κ 1 (eps N) N z := by
  let b := basis (L := L) hκ (eps_pos hN) hN
  let s := fun m : BetheLabels.MArr N =>
    TransferProductCorrection.transferS (κ*eps N) L (BetheLabels.arrRoots L (κ*eps N) m) z
  let s0 := spectralMap κ L z 0
  let Y := RadiusBound.represented (kernels (L := L) κ z N)
  have hM : 0 ≤ 256*(κ*L) := by have hL : 0 < L := Fact.out; positivity
  have hρ : 256*(κ*L) < rstar/4 := by norm_num [rstar]; linarith
  have hY := perturbation_norm hκ hs n hz N
  have hc := Local013PowerSeries.summable_majorant hM hρ (coefficient_summable hκ n hz)
  apply NormalityBridge.clm_ext_basis b
  intro m
  have he := perturbation_eigen hκ hN hs n hz m
  have hv : ‖s m-s0‖ ≤ 256*(κ*L) :=
    (LOCAL009R23OperatorContour.norm_eigen_le b Y _ m he).trans hY
  have hx : ‖s m-s0‖ < rstar/2 := by norm_num [rstar]; linarith
  have ht := series_eigen Y (b m) (s m-s0) he (coeff (L := L) κ z) hM hY hc
    (scalar_series hκ n hz hx)
  rw [(inverse_series_converges hκ hs n hz).2.1 N]
  change (∑' k, coeff (L := L) κ z k • Y^k) (b m) = _
  rw [ht]
  have ho := (inverseOp_spec hκ (by norm_num : (0 : ℝ) < 1)
    (show κ*L*1 ≤ 1/1000000 by nlinarith) hN (eps_pos hN) (eps_le_one hN)
    (by rw [eps_budget hN]) n hz).1 m
  rw [show inverseOp L κ 1 (eps N) N z (b m) = _ from ho]
  congr 1
  calc
    _ = spectralInverse κ L (W κ) z (s m) := by unfold centered; dsimp [s0]; rw [add_sub_cancel]
    _ = _ := actual_scalar_branch hκ hs hN n hz m

/-- Operator-norm holomorphy on the whole open tube, after actual binding. -/
theorem analytic_actual_inverse (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    {N : ℕ} (hN : 0 < N) (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) :
    AnalyticAt ℂ (fun w => RadiusBound.represented (inverseKernels (L := L) κ w N)) z := by
  have hd : DifferentiableOn ℂ (inverseOp L κ 1 (eps N) N) (tube L n) := by
    intro w hw
    exact (inverseOp_spec hκ (by norm_num : (0 : ℝ) < 1)
      (show κ*L*1 ≤ 1/1000000 by nlinarith) hN (eps_pos hN) (eps_le_one hN)
      (by rw [eps_budget hN]) n hw).2.1.differentiableWithinAt
  exact (hd.analyticOnNhd (band_open _ _) z hz).congr
    (Filter.eventuallyEq_iff_exists_mem.mpr ⟨tube L n,(band_open _ _).mem_nhds hz,
      fun w hw => (represented_actual_cfc hκ hs hN n hw).symm⟩)

theorem deriv_actual_inverse (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    {N : ℕ} (hN : 0 < N) (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) :
    deriv (fun w => RadiusBound.represented (inverseKernels (L := L) κ w N)) z =
      deriv (inverseOp L κ 1 (eps N) N) z := by
  have he : (fun w => RadiusBound.represented (inverseKernels (L := L) κ w N)) =ᶠ[𝓝 z]
      inverseOp L κ 1 (eps N) N :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨tube L n,(band_open _ _).mem_nhds hz,
      fun w hw => represented_actual_cfc hκ hs hN n hw⟩
  exact he.deriv_eq

end QuantumNLS.IndexedCFCBindingR29b
#print axioms QuantumNLS.IndexedCFCBindingR29b.represented_large_cfc
#print axioms QuantumNLS.IndexedCFCBindingR29b.actual_scalar_branch
#print axioms QuantumNLS.IndexedCFCBindingR29b.represented_actual_cfc
#print axioms QuantumNLS.IndexedCFCBindingR29b.analytic_actual_inverse
#print axioms QuantumNLS.IndexedCFCBindingR29b.deriv_actual_inverse
