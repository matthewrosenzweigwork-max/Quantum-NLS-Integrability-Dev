import QuantumNLS.RootMassInvolutionBatchR9
import QuantumNLS.RootScalarPeriodR8
import QuantumNLS.RootIndexedMassesCollapsed
import QuantumNLS.HilbertDiagOp
import QuantumNLS.Prop026Bound
import QuantumNLS.Prop009Branch

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Topology Complex
namespace QuantumNLS.ScalarLogBranchR10

def transfer (e g : ℂ) : ℂ := exp g + e / exp g
def difference (e g : ℂ) : ℂ := exp g - e / exp g
/-- Literal Taylor quadratic root in eq:B4-local-functions. -/
def root (e g w : ℂ) : ℂ :=
  (w + difference e g * (1 + (w^2 - (transfer e g)^2) / (difference e g)^2)^((2:ℂ)⁻¹))/2
/-- Literal normalized local logarithm; it is not defined by the desired Cauchy value. -/
def localLog (e g w : ℂ) : ℂ := g + log (root e g w / exp g)

lemma root_at (e g : ℂ) : root e g (transfer e g) = exp g := by
  simp only [root,sub_self,zero_div,add_zero,one_cpow,mul_one,transfer,difference]
  ring

lemma root_quadratic (e g w : ℂ) (hD : difference e g ≠ 0) :
    root e g w ^ 2 - w * root e g w + e = 0 := by
  have hA := exp_ne_zero g
  have hsq : (difference e g * (1+(w^2-transfer e g^2)/difference e g^2)^((2:ℂ)⁻¹))^2 = w^2-4*e := by
    rw [mul_pow,Complex.cpow_ofNat_inv_pow]
    have h : transfer e g ^ 2 - difference e g ^ 2 = 4*e := by
      unfold transfer difference
      field_simp
      ring
    rw [mul_add,mul_one,mul_div_cancel₀ _ (pow_ne_zero 2 hD)]
    linear_combination -h
  unfold root
  linear_combination hsq/4

lemma continuousAt_root {X : Type*} [TopologicalSpace X] {e g w : X → ℂ} {x : X}
    (he : ContinuousAt e x) (hg : ContinuousAt g x) (hw : ContinuousAt w x)
    (hD : difference (e x) (g x) ≠ 0) (hbase : w x = transfer (e x) (g x)) :
    ContinuousAt (fun y => root (e y) (g y) (w y)) x := by
  have hA := hg.cexp
  have ht := hA.add (he.div hA (exp_ne_zero _))
  have hd := hA.sub (he.div hA (exp_ne_zero _))
  change ContinuousAt (fun y => (w y + difference (e y) (g y) *
    (1 + (w y^2-transfer (e y) (g y)^2)/difference (e y) (g y)^2)^((2:ℂ)⁻¹))/2) x
  have hb : 1 + (w x^2-transfer (e x) (g x)^2)/difference (e x) (g x)^2 ∈ slitPlane := by
    simp [hbase,Complex.slitPlane]
  have harg : ContinuousAt (fun y => 1+(w y^2-transfer (e y) (g y)^2)/difference (e y) (g y)^2) x :=
    continuousAt_const.add (((hw.pow 2).sub (ht.pow 2)).div (hd.pow 2) (pow_ne_zero 2 hD))
  exact (hw.add (hd.mul ((continuousAt_cpow_const hb).comp (f := fun y : X => 1+(w y^2-transfer (e y) (g y)^2)/difference (e y) (g y)^2) harg))).div_const 2

/-- Actual branch selection, with varying spectral background, proved from
quadratic factorization and the normalized logarithm near zero. -/
theorem eventually_localLog {X : Type*} [TopologicalSpace X] {e g v : X → ℂ} {x : X}
    (he : ContinuousAt e x) (hg : ContinuousAt g x) (hv : ContinuousAt v x)
    (hbase : v x = g x) (hD : difference (e x) (g x) ≠ 0) :
    ∀ᶠ y in 𝓝 x, localLog (e y) (g y) (transfer (e y) (v y)) = v y := by
  have ht : ContinuousAt (fun y => transfer (e y) (v y)) x :=
    hv.cexp.add (he.div hv.cexp (exp_ne_zero _))
  have hr := continuousAt_root he hg ht hD (by rw [hbase])
  have hd : ContinuousAt (fun y => difference (e y) (g y)) x :=
    hg.cexp.sub (he.div hg.cexp (exp_ne_zero _))
  have hne : root (e x) (g x) (transfer (e x) (v x)) ≠ e x / exp (v x) := by
    rw [hbase,root_at]
    exact sub_ne_zero.mp hD
  have hn := (hr.sub (he.div hv.cexp (exp_ne_zero _))).eventually_ne (sub_ne_zero.mpr hne)
  have hdne := hd.eventually_ne hD
  have hsmall : ∀ᶠ y in 𝓝 x, -Real.pi < (v y-g y).im ∧ (v y-g y).im < Real.pi := by
    have hc : ContinuousAt (fun y => (v y-g y).im) x :=
      Complex.continuous_im.continuousAt.comp (hv.sub hg)
    have h0 : (v x-g x).im = 0 := by rw [hbase,sub_self]; rfl
    exact hc.eventually (Ioo_mem_nhds (by change -Real.pi < (v x-g x).im; rw [h0]; linarith [Real.pi_pos])
      (by change (v x-g x).im < Real.pi; rw [h0]; exact Real.pi_pos))
  filter_upwards [hn,hdne,hsmall] with y hy hdy hsy
  have hA := exp_ne_zero (v y)
  have hq := root_quadratic (e y) (g y) (transfer (e y) (v y)) hdy
  have hf : (root (e y) (g y) (transfer (e y) (v y))-exp (v y)) *
      (root (e y) (g y) (transfer (e y) (v y))-e y/exp (v y)) = 0 := by
    rw [← hq]
    unfold transfer
    field_simp
    ring
  have ha : root (e y) (g y) (transfer (e y) (v y)) = exp (v y) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hy)
  rw [localLog,ha,← exp_sub,log_exp hsy.1 hsy.2.le]
  ring
theorem hasDerivAt_localLog (e g : ℂ) (hD : difference e g ≠ 0) :
    HasDerivAt (localLog e g) (difference e g)⁻¹ (transfer e g) := by
  let s := transfer e g
  let d := difference e g
  have hd : d ≠ 0 := hD
  have hA := exp_ne_zero g
  have hw : HasDerivAt (fun w : ℂ => 1+(w^2-s^2)/d^2) ((2*s)/d^2) s := by
    simpa using (((hasDerivAt_id s).pow 2).sub_const (s^2) |>.div_const (d^2)).const_add 1
  have hp := hw.cpow_const (c := (2:ℂ)⁻¹) (by simp [Complex.slitPlane])
  have hr := ((hasDerivAt_id s).add (hp.const_mul d)).div_const 2
  have hs : root e g s / exp g ∈ slitPlane := by simp [s,root_at,Complex.slitPlane]
  have hratio : HasDerivAt (fun w => root e g w/exp g)
      ((1+d*((2:ℂ)⁻¹ * (1+(s^2-s^2)/d^2)^((2:ℂ)⁻¹-1) * ((2*s)/d^2)))/2/exp g) s :=
    hr.div_const (exp g)
  have hl := (hratio.clog hs).const_add g
  apply hl.congr_deriv
  rw [show root e g s = exp g from root_at e g]
  simp only [sub_self,zero_div,add_zero,one_cpow,mul_one,div_self hA,div_one]
  field_simp [hd,hA]
  dsimp [s,d,transfer,difference]
  field_simp
  ring
end QuantumNLS.ScalarLogBranchR10
#print axioms QuantumNLS.ScalarLogBranchR10.eventually_localLog

/-! R-620D5517: literal local quadratic/logarithmic period on fixed
full-Hilbert neighborhoods, including vacuum and collapsed actions. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Topology Complex
namespace QuantumNLS.RootScalarPeriodR10
open PhysicalTensor (L2T)
open RootCauchyFullBracketR8 (G)
open RootCauchyJointR9 (Regular)
open RootMassInvolutionR8 (mass)
open RootScalarPeriodR8 (cut center radius)
variable {L κ : ℝ} [Fact (0 < L)]

def exponent (hκ : 0 < κ) (u : L2T L) (z : ℂ) : ℂ := I * κ * G hκ z u
def exponential (L : ℝ) (z : ℂ) : ℂ := exp (I * z * L)
/-- The actual transfer series, normalized as in the source. -/
def symbol (κ : ℝ) (u : L2T L) (z : ℂ) : ℂ := NormalizedTransfer.productSymbol L κ u z
/-- The normalized local logarithm in eq:B4-local-functions. -/
def lambda (hκ : 0 < κ) (u : L2T L) (z w : ℂ) : ℂ :=
  ScalarLogBranchR10.localLog (exponential L z) (exponent hκ u z) w
/-- The literal leading quantum period, with the background contour frozen at u. -/
def leadingPeriod (hκ : 0 < κ) (u : L2T L) (n : ℤ) (v : L2T L) : ℝ :=
  -(2 * Real.pi * κ)⁻¹ *
    (∮ z in C((center hκ u n : ℂ),radius hκ u n), lambda hκ u z (symbol κ v z)).re

lemma radius_pos (hκ : 0 < κ) (u : L2T L) (n : ℤ) : 0 < radius hκ u n := by
  have h := (DEF014Phase.facts ((⟨κ,hκ⟩,u) : DEF014Phase.Param L)).phase.separator_strictMono
    (show n-1<n by omega)
  change 0 < (cut hκ u n-cut hκ u (n-1))/2
  change cut hκ u (n-1)<cut hκ u n at h
  linarith

lemma circle_regular (hκ : 0 < κ) (u : L2T L) (n : ℤ) {z : ℂ}
    (hz : z ∈ Metric.sphere (center hκ u n : ℂ) (radius hκ u n)) : Regular κ (u,z) := by
  by_cases hi : z.im = 0
  · right
    have hez : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
    have hr := radius_pos hκ u n
    have hn : |z.re-center hκ u n| = radius hκ u n := by
      have hh : ‖z-(RootScalarPeriodR8.center hκ u n : ℂ)‖ = radius hκ u n := by simpa only [Metric.mem_sphere,dist_eq_norm] using hz
      rw [hez,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hh
      exact hh
    have he : z.re = cut hκ u (n-1) ∨ z.re = cut hκ u n := by
      rcases (abs_eq hr.le).mp hn with hh | hh
      · right; dsimp [RootScalarPeriodR8.center,radius] at hh; linarith
      · left; dsimp [RootScalarPeriodR8.center,radius] at hh; linarith
    rw [hez]
    rcases he with he | he
    · rw [he]; exact (DEF014Phase.facts ((⟨κ,hκ⟩,u) : DEF014Phase.Param L)).separator_in_band (n-1)
    · rw [he]; exact (DEF014Phase.facts ((⟨κ,hκ⟩,u) : DEF014Phase.Param L)).separator_in_band n
  · exact Or.inl hi

lemma transfer_identity (hκ : 0 < κ) (u : L2T L) (z : ℂ) (hz : Regular κ (u,z)) :
    symbol κ u z = ScalarLogBranchR10.transfer (exponential L z) (exponent hκ u z) := by
  have ht := RootTraceSymbolFinal.traceSymbol_all hκ.le u z
  have hc := RootCauchyJointR9.cosine_regular hκ (u,z) hz
  rw [← hc] at ht
  dsimp [DEF014PhaseAnalytic.selected,SpatialTransfer.boundaryPhase] at ht
  change exp (-(I*z*L/2))*symbol κ u z = _ at ht
  apply mul_left_cancel₀ (exp_ne_zero (-(I*z*L/2)))
  rw [ht]
  dsimp [ScalarLogBranchR10.transfer,exponential,exponent,Complex.cos]
  change 2*((exp (((L:ℂ)*z/2-(κ:ℂ)*G hκ z u)*I)+
    exp (-((L:ℂ)*z/2-(κ:ℂ)*G hκ z u)*I))*2⁻¹) = _
  have he : exp (I*z*L)/exp (I*(κ:ℂ)*G hκ z u) =
      exp (I*z*L-I*(κ:ℂ)*G hκ z u) := (exp_sub _ _).symm
  rw [he,mul_add,← exp_add,← exp_add]
  have h1 : -(I*z*L/2)+(I*(κ:ℂ)*G hκ z u) = -((L:ℂ)*z/2-(κ:ℂ)*G hκ z u)*I := by ring
  have h2 : -(I*z*L/2)+(I*z*L-I*(κ:ℂ)*G hκ z u) =
      ((L:ℂ)*z/2-(κ:ℂ)*G hκ z u)*I := by ring
  rw [h1,h2]
  ring

lemma difference_ne (hκ : 0 < κ) (u : L2T L) (z : ℂ) (hz : Regular κ (u,z)) :
    ScalarLogBranchR10.difference (exponential L z) (exponent hκ u z) ≠ 0 := by
  have hs := RootCauchyJointR9.sine_regular hκ (u,z) hz
  have he : ScalarLogBranchR10.difference (exponential L z) (exponent hκ u z) =
      -2*I*exp (I*z*L/2)*Complex.sin (DEF014PhaseAnalytic.selected hκ u z) := by
    change exp (I*(κ:ℂ)*G hκ z u)-exp (I*z*L)/exp (I*(κ:ℂ)*G hκ z u) =
      -2*I*exp (I*z*L/2)*Complex.sin ((L:ℂ)*z/2-(κ:ℂ)*G hκ z u)
    have h1 : I*(κ:ℂ)*G hκ z u = I*z*L/2-(((L:ℂ)*z/2-(κ:ℂ)*G hκ z u)*I) := by ring
    have h2 : I*z*L-I*(κ:ℂ)*G hκ z u = I*z*L/2+(((L:ℂ)*z/2-(κ:ℂ)*G hκ z u)*I) := by ring
    rw [← exp_sub,h2,exp_add,h1,exp_sub]
    rw [Complex.sin]
    have hexp : exp (-((L:ℂ)*z/2-(κ:ℂ)*G hκ z u)*I) =
        (exp (((L:ℂ)*z/2-(κ:ℂ)*G hκ z u)*I))⁻¹ := by rw [neg_mul,exp_neg]
    rw [hexp]
    field_simp
    simp only [Complex.I_sq]
    ring
  rw [he]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) (exp_ne_zero _)) hs

lemma eventually_lambda_circle (hκ : 0 < κ) (u : L2T L) (n : ℤ) :
    ∀ᶠ v : L2T L in 𝓝 u, ∀ z ∈ Metric.sphere (center hκ u n : ℂ) (radius hκ u n),
      lambda hκ u z (symbol κ v z) = exponent hκ v z := by
  apply (isCompact_sphere (center hκ u n : ℂ) (radius hκ u n)).eventually_forall_of_forall_eventually
  intro z hz
  have hreg := circle_regular hκ u n hz
  have hc := (RootCauchyJointR9.continuousAt_joint_regular hκ (u,z) hreg).const_mul (I*(κ:ℂ))
  have hc0 : ContinuousAt (fun p : L2T L × ℂ => exponent hκ u p.2) (u,z) := by
    have hj : ContinuousAt (fun p : L2T L × ℂ => (u,p.2)) (u,z) :=
      (continuous_const.prodMk continuous_snd).continuousAt
    have h := (RootCauchyJointR9.continuousAt_joint_regular hκ (u,z) hreg).comp (f := fun p : L2T L × ℂ => (u,p.2)) hj
    exact h.const_mul (I*(κ:ℂ))
  have he : ContinuousAt (fun p : L2T L × ℂ => exponential L p.2) (u,z) := by
    unfold exponential; fun_prop
  have hl := ScalarLogBranchR10.eventually_localLog he hc0 hc rfl (difference_ne hκ u z hreg)
  filter_upwards [hl,(RootCauchyJointR9.isOpen_regular κ).mem_nhds hreg] with p hp hpr
  change ScalarLogBranchR10.localLog _ _ _ = _
  rw [transfer_identity hκ p.1 p.2 hpr]
  exact hp

lemma eventually_leadingPeriod (hκ : 0 < κ) (u : L2T L) (n : ℤ) :
    ∀ᶠ v : L2T L in 𝓝 u, leadingPeriod hκ u n v = mass hκ n v := by
  filter_upwards [eventually_lambda_circle hκ u n,
    RootScalarPeriodR8.eventually_mass_eq_cauchyPeriod hκ u n] with v hv hm
  have he : (∮ z in C((center hκ u n : ℂ),radius hκ u n),lambda hκ u z (symbol κ v z)) =
      (I*(κ:ℂ)) * (∮ z in C((center hκ u n : ℂ),radius hκ u n),G hκ z v) := by
    rw [← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr (radius_pos hκ u n).le
    intro z hz
    exact hv z (by simpa [abs_of_pos (radius_pos hκ u n)] using hz)
  change (mass hκ n v : ℂ) = (2*(Real.pi:ℂ)*I)⁻¹ *
    (∮ z in C((center hκ u n : ℂ),radius hκ u n),G hκ z v) at hm
  have hp : (2*(Real.pi:ℂ)*I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hi : (∮ z in C((center hκ u n : ℂ),radius hκ u n),G hκ z v) =
      (2*(Real.pi:ℂ)*I)*(mass hκ n v : ℂ) := by
    rw [hm]; field_simp
  rw [leadingPeriod,he,hi]
  simp only [mul_re,mul_im,I_re,I_im,ofReal_re,ofReal_im]
  norm_num
  field_simp

/-- R-620D5517, one named theorem: fixed literal logarithmic periods on a
common full open Hilbert neighborhood, with full differentials at every
point and on every tangent vector. No action-positivity premise is used. -/
theorem audit_scalar_period (hκ : 0 < κ) (u : L2T L) (F : Finset ℤ) :
    ∃ U : Set (L2T L), IsOpen U ∧ u ∈ U ∧ ∀ n ∈ F,
      0 < radius hκ u n ∧
      (∀ v ∈ U, ∀ z ∈ Metric.sphere (center hκ u n : ℂ) (radius hκ u n),
        lambda hκ u z (symbol κ v z) = exponent hκ v z) ∧
      (∀ v ∈ U, leadingPeriod hκ u n v = mass hκ n v) ∧
      (∀ v ∈ U, AnalyticAt ℝ (leadingPeriod hκ u n) v) ∧
      (∀ v ∈ U, fderiv ℝ (leadingPeriod hκ u n) v = fderiv ℝ (mass hκ n) v) ∧
      (∀ v ∈ U, ∀ h : L2T L, fderiv ℝ (leadingPeriod hκ u n) v h =
        fderiv ℝ (mass hκ n) v h) := by
  have he : ∀ᶠ v : L2T L in 𝓝 u, ∀ n ∈ F,
      (∀ z ∈ Metric.sphere (center hκ u n : ℂ) (radius hκ u n),
        lambda hκ u z (symbol κ v z) = exponent hκ v z) ∧
      leadingPeriod hκ u n v = mass hκ n v := by
    rw [Filter.eventually_all_finset]
    intro n hn
    exact (eventually_lambda_circle hκ u n).and (eventually_leadingPeriod hκ u n)
  obtain ⟨U,hsub,hU,hu⟩ := mem_nhds_iff.mp he
  refine ⟨U,hU,hu,fun n hn => ⟨radius_pos hκ u n,fun v hv => (hsub hv n hn).1,
    fun v hv => (hsub hv n hn).2,?_,?_,?_⟩⟩
  · intro v hv
    apply (DEF014MassAnalytic.analyticAt_physical_coordinate hκ n v).congr
    filter_upwards [hU.mem_nhds hv] with w hw
    exact (hsub hw n hn).2.symm
  · intro v hv
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hU.mem_nhds hv] with w hw
    exact (hsub hw n hn).2
  · intro v hv h
    apply DFunLike.congr_fun _ h
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hU.mem_nhds hv] with w hw
    exact (hsub hw n hn).2
end QuantumNLS.RootScalarPeriodR10
#print axioms QuantumNLS.RootScalarPeriodR10.audit_scalar_period
#check @QuantumNLS.RootScalarPeriodR10.audit_scalar_period

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Topology MeasureTheory Complex
namespace QuantumNLS.RootScalarDifferentialR10
open scoped NNReal
open PhysicalTensor (L2T)
open RootCauchyFullBracketR8 (G)
open RootCauchyJointR9 (Regular)
open RootMassInvolutionR8 (mass)
open RootScalarPeriodR8 (cut center radius)
open RootScalarPeriodR10
variable {L κ : ℝ} [Fact (0 < L)]

/-- A uniform analytic Cauchy germ on any compact regular path, including
both half-planes and its real band crossings. -/
theorem exists_analytic_regular_path (hκ : 0 < κ)
    {K : Type*} [PseudoMetricSpace K] [CompactSpace K]
    (Z : C(K,ℂ)) {B : ℝ≥0} (hZ : LipschitzWith B Z) (u : L2T L)
    {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hgap : ∀ᶠ v : L2T L in 𝓝 u,
      ∀ᵐ (t : ℝ) ∂(PhysicalQuantumMeasure.measure hκ v), ∀ k, δ ≤ ‖Z k-(t : ℂ)‖)
    (hmass : ∀ᶠ v : L2T L in 𝓝 u,
      (PhysicalQuantumMeasure.measure hκ v univ).toReal ≤ M)
    (hreg : ∀ᶠ v : L2T L in 𝓝 u, ∀ k, Regular κ (v,Z k)) :
    ∃ H : L2T L → C(K,ℂ), AnalyticAt ℝ H u ∧
      ∀ᶠ v : L2T L in 𝓝 u, ∀ k, H v k = G hκ (Z k) v := by
  have hpoint : ∀ k, ContinuousAt (fun v : L2T L => G hκ (Z k) v) u := by
    intro k
    exact (RootCauchyJointR9.continuousAt_joint_regular hκ (u,Z k)
      (hreg.self_of_nhds k)).comp (f := fun v : L2T L => (v,Z k))
      (continuous_id.prodMk continuous_const).continuousAt
  obtain ⟨C,hC,hCe⟩ := DEF014UniformCauchy.exists_continuousAt_path
    (fun v : L2T L => PhysicalQuantumMeasure.measure hκ v) Z hZ hδ hM hgap hmass hpoint
  obtain ⟨D,hD,hDe⟩ := DEF014UniformDiscriminant.analyticAt_discriminant_contour κ Z u
  let lin : C(K,ℂ) := ((L : ℂ)/2) • Z
  let P : L2T L → C(K,ℂ) := fun v => lin-(κ : ℂ) • C v
  have hP : ContinuousAt P u := continuousAt_const.sub (hC.const_smul (κ : ℂ))
  have hPe : ∀ᶠ v : L2T L in 𝓝 u, ∀ k,
      P v k = DEF014PhaseAnalytic.selected hκ v (Z k) := by
    filter_upwards [hCe] with v hv k
    change ((L : ℂ)/2) * Z k-(κ : ℂ)*C v k = _
    rw [hv k]
    dsimp [DEF014PhaseAnalytic.selected,SpatialTransfer.boundaryPhase]
    ring
  have he : ∀ᶠ v : L2T L in 𝓝 u, ∀ k, 2*cos (P v k) = D v k := by
    filter_upwards [hPe,hreg] with v hv hr k
    rw [hv k,hDe]
    exact RootCauchyJointR9.cosine_regular hκ (v,Z k) (hr k)
  have hs : ∀ k, sin (P u k) ≠ 0 := by
    intro k
    rw [hPe.self_of_nhds k]
    exact RootCauchyJointR9.sine_regular hκ (u,Z k) (hreg.self_of_nhds k)
  have ha : AnalyticAt ℝ P u := DEF014UniformPhase.analytic_selected_cosine hD hP he hs
  let H : L2T L → C(K,ℂ) := fun v => ((κ : ℂ)⁻¹) • (lin-P v)
  refine ⟨H,(analyticAt_const.sub ha).const_smul (c := (κ : ℂ)⁻¹),?_⟩
  filter_upwards [hCe] with v hv k
  change (κ : ℂ)⁻¹ * (((L : ℂ)/2)*Z k-(((L : ℂ)/2)*Z k-(κ : ℂ)*C v k)) = _
  rw [hv k]
  unfold G
  field_simp [Complex.ofReal_ne_zero.mpr hκ.ne']
  ring

abbrev UI := DEF014AnalyticIntegration.UnitInterval

def circlePath (hκ : 0 < κ) (u : L2T L) (n : ℤ) : C(UI,ℂ) :=
  ⟨fun s => circleMap (center hκ u n : ℂ) (radius hκ u n) (2*Real.pi*s.1),by fun_prop⟩

def circleWeight (c R : ℝ) : C(UI,ℂ) :=
  ⟨fun s => deriv (circleMap (c : ℂ) R) (2*Real.pi*s.1),by
    simp only [deriv_circleMap]; fun_prop⟩

lemma circle_reparam (c R : ℝ) (F : C(UI,ℂ)) (f : ℂ → ℂ)
    (he : ∀ s : UI, F s = deriv (circleMap (c : ℂ) R) (2*Real.pi*s.1) *
      f (circleMap (c : ℂ) R (2*Real.pi*s.1))) :
    (2*(Real.pi : ℂ))*DEF014AnalyticIntegration.integrateCLM F = ∮ z in C((c : ℂ),R), f z := by
  have hi : (∫ t in (0:ℝ)..1,DEF014AnalyticIntegration.extend F t) =
      ∫ t in (0:ℝ)..1,deriv (circleMap (c : ℂ) R) (2*Real.pi*t) *
        f (circleMap (c : ℂ) R (2*Real.pi*t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    change F (projIcc 0 1 (by norm_num) t) = _
    rw [projIcc_of_mem (by norm_num) ht]
    exact he ⟨t,ht⟩
  change (2*(Real.pi : ℂ))*(∫ t in (0:ℝ)..1,DEF014AnalyticIntegration.extend F t) = _
  rw [hi]
  have hh := intervalIntegral.smul_integral_comp_mul_add (a := (0:ℝ)) (b := 1)
    (fun θ => deriv (circleMap (c : ℂ) R) θ * f (circleMap (c : ℂ) R θ)) (2*Real.pi) 0
  rw [RCLike.real_smul_eq_coe_mul] at hh
  push_cast at hh
  convert! hh using 1 <;> simp [circleIntegral,smul_eq_mul]

lemma circle_analytic_path (hκ : 0 < κ) (u : L2T L) (n : ℤ) :
    ∃ H : L2T L → C(UI,ℂ), AnalyticAt ℝ H u ∧
      ∀ᶠ v : L2T L in 𝓝 u, ∀ s, H v s = G hκ (circlePath hκ u n s) v := by
  let Z := circlePath hκ u n
  have hR := radius_pos hκ u n
  have hZ : LipschitzWith (Real.nnabs (radius hκ u n)*Real.nnabs (2*Real.pi)) Z := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    have hh := (lipschitzWith_circleMap (center hκ u n : ℂ) (radius hκ u n)).dist_le_mul
      (2*Real.pi*s.1) (2*Real.pi*t.1)
    simpa only [Z,circlePath,ContinuousMap.coe_mk,Real.dist_eq,← mul_sub,
      abs_mul,NNReal.coe_mul,Real.coe_nnabs,mul_assoc,Subtype.dist_eq] using hh
  let p : DEF014Phase.Param L := (⟨κ,hκ⟩,u)
  have hj : Continuous (fun v : L2T L => ((⟨κ,hκ⟩,v) : DEF014Phase.Param L)) :=
    continuous_const.prodMk continuous_id
  obtain ⟨δ,hδ,hgapP⟩ := DEF014Contour.common_contour_gap p n
  have hgap : ∀ᶠ v : L2T L in 𝓝 u,
      ∀ᵐ (t : ℝ) ∂(PhysicalQuantumMeasure.measure hκ v), ∀ s, δ ≤ ‖Z s-(t : ℂ)‖ := by
    filter_upwards [hj.continuousAt.eventually hgapP] with v hv
    filter_upwards [hv] with t ht s
    exact DEF014ContourReflection.circle_support_distance (center hκ u n) hR ht (2*Real.pi*s.1)
  have hm : ∀ᶠ v : L2T L in 𝓝 u,
      (PhysicalQuantumMeasure.measure hκ v univ).toReal ≤ (‖u‖+1)^2 := by
    have hn : ∀ᶠ v : L2T L in 𝓝 u, ‖v‖ < ‖u‖+1 :=
      continuous_norm.continuousAt.eventually (gt_mem_nhds (by linarith))
    filter_upwards [hn] with v hv
    rw [PhysicalQuantumMeasure.measure_univ,ENNReal.toReal_ofReal (sq_nonneg _)]
    nlinarith [norm_nonneg v,norm_nonneg u]
  have hr : ∀ᶠ v : L2T L in 𝓝 u, ∀ s, Regular κ (v,Z s) := by
    have hh : ∀ᶠ v : L2T L in 𝓝 u, ∀ z ∈ Metric.sphere (center hκ u n : ℂ) (radius hκ u n),
        Regular κ (v,z) := by
      apply (isCompact_sphere (center hκ u n : ℂ) (radius hκ u n)).eventually_forall_of_forall_eventually
      intro z hz
      exact (RootCauchyJointR9.isOpen_regular κ).mem_nhds (circle_regular hκ u n hz)
    filter_upwards [hh] with v hv s
    exact hv _ (circleMap_mem_sphere _ hR.le _)
  exact exists_analytic_regular_path hκ Z hZ u hδ (sq_nonneg _) hgap hm hr

/-- Differentiation of the actual full fixed Cauchy contour in the full
Hilbert space. Parameter integration is a bounded linear map. -/
theorem mass_differential_contour (hκ : 0 < κ) (u h : L2T L) (n : ℤ) :
    (fderiv ℝ (mass hκ n) u h : ℂ) = (2*(Real.pi : ℂ)*I)⁻¹ *
      (∮ z in C((center hκ u n : ℂ),radius hκ u n),fderiv ℝ (G hκ z) u h) := by
  obtain ⟨H,hH,hHe⟩ := circle_analytic_path hκ u n
  let d := circleWeight (center hκ u n) (radius hκ u n)
  let F : L2T L → C(UI,ℂ) := fun v => d * H v
  have hF : AnalyticAt ℝ F u := analyticAt_const.mul hH
  let J : L2T L → ℂ := fun v => (2*(Real.pi : ℂ))*DEF014AnalyticIntegration.integrateCLM (F v)
  have hJ := (DEF014AnalyticIntegration.integrateCLM.hasFDerivAt.comp u
    hF.differentiableAt.hasFDerivAt).const_mul (2*(Real.pi : ℂ))
  change HasFDerivAt J _ u at hJ
  have hDF : fderiv ℝ F u h = d * (fderiv ℝ H u h) := by
    have hh := (hasFDerivAt_const d u).mul hH.differentiableAt.hasFDerivAt
    change HasFDerivAt F _ u at hh
    rw [hh.fderiv]
    simp
  have hDH : ∀ s : UI, fderiv ℝ H u h s = fderiv ℝ (G hκ (circlePath hκ u n s)) u h := by
    intro s
    have hd := (ContinuousMap.evalCLM ℝ s).hasFDerivAt.comp u hH.differentiableAt.hasFDerivAt
    have heq : (fun v => H v s) =ᶠ[𝓝 u] G hκ (circlePath hκ u n s) := hHe.mono fun v hv => hv s
    have hg := hd.congr_of_eventuallyEq heq.symm
    have hh := congrArg (fun A : L2T L →L[ℝ] ℂ => A h) hg.fderiv
    simpa using hh.symm
  have hder : fderiv ℝ J u h = ∮ z in C((center hκ u n : ℂ),radius hκ u n),fderiv ℝ (G hκ z) u h := by
    rw [hJ.fderiv]
    change (2*(Real.pi : ℂ))*DEF014AnalyticIntegration.integrateCLM (fderiv ℝ F u h) = _
    rw [hDF]
    apply circle_reparam
    intro s
    change deriv (circleMap (center hκ u n : ℂ) (radius hκ u n)) (2*Real.pi*s.1) *
      fderiv ℝ H u h s = _
    rw [hDH]
    rfl
  have hJeq : J =ᶠ[𝓝 u] (fun v : L2T L => ∮ z in C((center hκ u n : ℂ),radius hκ u n),G hκ z v) := by
    filter_upwards [hHe] with v hv
    apply circle_reparam
    intro s
    change deriv (circleMap (center hκ u n : ℂ) (radius hκ u n)) (2*Real.pi*s.1) * H v s = _
    rw [hv]
    rfl
  have heq : (fun v => (mass hκ n v : ℂ)) =ᶠ[𝓝 u] (fun v => (2*(Real.pi : ℂ)*I)⁻¹*J v) := by
    filter_upwards [RootScalarPeriodR8.eventually_mass_eq_cauchyPeriod hκ u n,hJeq] with v hv hjv
    rw [hjv]
    exact hv
  have hdM := Complex.ofRealCLM.hasFDerivAt.comp u
    (DEF014MassAnalytic.analyticAt_physical_coordinate hκ n u).differentiableAt.hasFDerivAt
  have hh := (hdM.congr_of_eventuallyEq heq.symm).fderiv
  have hdJ := (hJ.const_mul (2*(Real.pi : ℂ)*I)⁻¹).fderiv
  have he := congrArg (fun A : L2T L →L[ℝ] ℂ => A h) (hh.symm.trans hdJ)
  have hjval : (2*(Real.pi:ℂ))*DEF014AnalyticIntegration.integrateCLM (fderiv ℝ F u h) =
      ∮ z in C((center hκ u n : ℂ),radius hκ u n),fderiv ℝ (G hκ z) u h := by
    simpa only [hJ.fderiv,smul_apply,ContinuousLinearMap.comp_apply,smul_eq_mul] using hder
  change (fderiv ℝ (mass hκ n) u h : ℂ) =
    (2*(Real.pi:ℂ)*I)⁻¹*((2*(Real.pi:ℂ))*DEF014AnalyticIntegration.integrateCLM (fderiv ℝ F u h)) at he
  rw [hjval] at he
  exact he
end QuantumNLS.RootScalarDifferentialR10
#print axioms QuantumNLS.RootScalarDifferentialR10.mass_differential_contour

#print axioms QuantumNLS.ScalarLogBranchR10.hasDerivAt_localLog
#check @QuantumNLS.RootScalarDifferentialR10.mass_differential_contour

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Topology MeasureTheory
namespace QuantumNLS.RootScalarLevelR10
open PhysicalTensor (L2T)
open RootCauchyFullBracketR8 (G)
open RootMassInvolutionR8 (mass)
open RootScalarPeriodR8 (cut center radius)
open RootScalarPeriodR10
variable {L κ : ℝ} [Fact (0 < L)]

def SameDiscriminant (u v : L2T L) : Prop :=
  ∀ z : ℂ, L2SpatialTransfer.discriminant κ u z = L2SpatialTransfer.discriminant κ v z

lemma density_measure (hκ : 0 < κ) (u : L2T L) :
    PhysicalQuantumMeasure.measure hκ u = MeasureTheory.volume.withDensity
      (fun t => ENNReal.ofReal (RootDensityIdentification.dens κ u t)) := by
  by_cases hu : u = 0
  · subst u
    have h0 : ∀ t, RootDensityIdentification.dens κ (0 : L2T L) t = 0 := by
      intro t
      have hi := PhysicalContinuousBoundary.boundary_im hκ (0 : L2T L) t
      rw [PhysicalContinuousBoundary.boundary_zero hκ t] at hi
      have hh : RootDensity.hfun |(L2SpatialTransfer.discriminant κ (0 : L2T L) (t : ℂ)).re| = 0 := by
        rw [← hi]; simp
      unfold RootDensityIdentification.dens
      rw [hh,mul_zero]
    rw [PhysicalQuantumMeasure.measure_zero]
    simp [h0]
  · exact RootDensityIdentification.root_density hκ hu

lemma measure_eq (hκ : 0 < κ) {u v : L2T L} (h : SameDiscriminant (κ := κ) u v) :
    PhysicalQuantumMeasure.measure hκ u = PhysicalQuantumMeasure.measure hκ v := by
  rw [density_measure hκ u,density_measure hκ v]
  congr 1
  funext t
  simp only [RootDensityIdentification.dens,h (t:ℂ)]

lemma boundary_eq (hκ : 0 < κ) {u v : L2T L} (h : SameDiscriminant (κ := κ) u v) :
    PhysicalContinuousBoundary.boundary hκ u = PhysicalContinuousBoundary.boundary hκ v := by
  funext x
  have hu : Tendsto (fun ε : ℝ => SpatialTransfer.boundaryPhase L κ
      (PhysicalQuantumMeasure.measure hκ u) ((x:ℂ)+(ε:ℂ)*Complex.I)) (𝓝[>] 0)
      (𝓝 (PhysicalContinuousBoundary.boundary hκ u x)) := (PhysicalSourceFinal.sourceFacts hκ u).boundary x
  have hv : Tendsto (fun ε : ℝ => SpatialTransfer.boundaryPhase L κ
      (PhysicalQuantumMeasure.measure hκ v) ((x:ℂ)+(ε:ℂ)*Complex.I)) (𝓝[>] 0)
      (𝓝 (PhysicalContinuousBoundary.boundary hκ v x)) := (PhysicalSourceFinal.sourceFacts hκ v).boundary x
  rw [measure_eq hκ h] at hu
  exact tendsto_nhds_unique hu hv

lemma cut_eq (hκ : 0 < κ) {u v : L2T L} (h : SameDiscriminant (κ := κ) u v) (n : ℤ) :
    cut hκ u n = cut hκ v n := by
  have hu := (PhysicalSourceFinal.sourceFacts hκ u).phase.separator_spec n
  have hv := (PhysicalSourceFinal.sourceFacts hκ v).phase.separator_spec n
  change (PhysicalContinuousBoundary.boundary hκ u (cut hκ u n)).re = _ at hu
  change (PhysicalContinuousBoundary.boundary hκ v (cut hκ v n)).re = _ at hv
  rw [← boundary_eq hκ h] at hv
  exact ((PhysicalSourceFinal.sourceFacts hκ u).phase.exists_unique_separator n).unique hu hv

lemma period_eq (hκ : 0 < κ) {u v : L2T L} (h : SameDiscriminant (κ := κ) u v) (n : ℤ) :
    leadingPeriod hκ u n = leadingPeriod hκ v n := by
  have hc : center hκ u n = center hκ v n := by simp only [RootScalarPeriodR8.center,cut_eq hκ h]
  have hr : radius hκ u n = radius hκ v n := by simp only [radius,cut_eq hκ h]
  have hlog : lambda hκ u = lambda hκ v := by
    funext z w
    simp only [lambda,exponent,G,measure_eq hκ h]
  funext w
  simp only [leadingPeriod,hc,hr,hlog]

/-- The same fixed logarithmic contour works locally at every point of
the entire equal-discriminant level; no uniform neighborhood of that
whole level is asserted or assumed. -/
theorem equal_discriminant_neighborhood (hκ : 0 < κ) (u v : L2T L) (F : Finset ℤ)
    (h : SameDiscriminant (κ := κ) u v) :
    ∃ U : Set (L2T L), IsOpen U ∧ v ∈ U ∧ ∀ n ∈ F,
      (∀ w ∈ U, leadingPeriod hκ u n w = mass hκ n w) ∧
      (∀ w ∈ U, fderiv ℝ (leadingPeriod hκ u n) w = fderiv ℝ (mass hκ n) w) := by
  obtain ⟨U,hU,hv,hp⟩ := audit_scalar_period hκ v F
  refine ⟨U,hU,hv,fun n hn => ?_⟩
  rw [period_eq hκ h n]
  exact ⟨(hp n hn).2.2.1,(hp n hn).2.2.2.2.1⟩
end QuantumNLS.RootScalarLevelR10
#print axioms QuantumNLS.RootScalarLevelR10.equal_discriminant_neighborhood

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Topology Complex
namespace QuantumNLS.Prop010ClassicalR10
open PhysicalTensor (L2T)
open RootCauchyFullBracketR8 (G)
open RootCauchyJointR9 (Regular)
open RootMassInvolutionR8 (mass)
open RootScalarPeriodR8 (cut center radius)
open RootScalarPeriodR10
variable {L κ : ℝ} [Fact (0 < L)]

lemma symbol_eq_trace (hκ : 0 < κ) (u : L2T L) (z : ℂ) :
    symbol κ u z = exp (I*z*L/2)*L2SpatialTransfer.discriminant κ u z := by
  have ht := RootTraceSymbolFinal.traceSymbol_all hκ.le u z
  change exp (-(I*z*L/2))*symbol κ u z = _ at ht
  rw [← ht,← mul_assoc,← exp_add,add_neg_cancel,exp_zero,one_mul]

lemma analyticAt_symbol (hκ : 0 < κ) (u : L2T L) (z : ℂ) :
    AnalyticAt ℝ (fun v : L2T L => symbol κ v z) u := by
  simp_rw [symbol_eq_trace hκ]
  exact analyticAt_const.mul (DEF014DiscriminantAnalytic.analyticAt_discriminant κ z u)

lemma exponent_differential (hκ : 0 < κ) (u h : L2T L) (z : ℂ) (hz : Regular κ (u,z)) :
    (I*(κ:ℂ))*fderiv ℝ (G hκ z) u h =
      fderiv ℝ (fun v : L2T L => symbol κ v z) u h /
        ScalarLogBranchR10.difference (exponential L z) (exponent hκ u z) := by
  have hGa := (RootCauchyJointR9.analyticAt_joint_regular hκ (u,z) hz).comp
    (f := fun v : L2T L => (v,z)) (analyticAt_id.prod analyticAt_const)
  have hGe := hGa.differentiableAt.hasFDerivAt.const_mul (I*(κ:ℂ))
  have hreg : ∀ᶠ v : L2T L in 𝓝 u, Regular κ (v,z) :=
    (continuous_id.prodMk continuous_const).continuousAt.eventually
      ((RootCauchyJointR9.isOpen_regular κ).mem_nhds hz)
  have he := ScalarLogBranchR10.eventually_localLog continuousAt_const continuousAt_const
    (hGa.continuousAt.const_mul (I*(κ:ℂ))) rfl (difference_ne hκ u z hz)
  have heq : (fun v : L2T L => lambda hκ u z (symbol κ v z)) =ᶠ[𝓝 u]
      (fun v => exponent hκ v z) := by
    filter_upwards [he,hreg] with v hv hr
    change ScalarLogBranchR10.localLog _ _ _ = _
    rw [transfer_identity hκ v z hr]
    exact hv
  have hlog := ScalarLogBranchR10.hasDerivAt_localLog (exponential L z) (exponent hκ u z)
    (difference_ne hκ u z hz)
  rw [← transfer_identity hκ u z hz] at hlog
  have hd := (hlog.hasFDerivAt.restrictScalars ℝ).comp u (analyticAt_symbol hκ u z).differentiableAt.hasFDerivAt
  have hh := (hd.congr_of_eventuallyEq heq.symm).unique hGe
  have hv := congrArg (fun A : L2T L →L[ℝ] ℂ => A h) hh
  have heval := hv.symm
  change (I*(κ:ℂ))*fderiv ℝ (G hκ z) u h =
    fderiv ℝ (fun v : L2T L => symbol κ v z) u h *
      (ScalarLogBranchR10.difference (exponential L z) (exponent hκ u z))⁻¹ at heval
  simpa only [div_eq_mul_inv] using heval

/-- The source's full-Hilbert 1/D differential formula, proved for the
actual indexed mass and actual transfer series. -/
theorem action_differential (hκ : 0 < κ) (u h : L2T L) (n : ℤ) :
    fderiv ℝ (mass hκ n) u h = -(2*Real.pi*κ)⁻¹ *
      (∮ z in C((center hκ u n : ℂ),radius hκ u n),
        fderiv ℝ (fun v : L2T L => symbol κ v z) u h /
          ScalarLogBranchR10.difference (exponential L z) (exponent hκ u z)).re := by
  let J := ∮ z in C((center hκ u n : ℂ),radius hκ u n),fderiv ℝ (G hκ z) u h
  have hm := RootScalarDifferentialR10.mass_differential_contour hκ u h n
  have hp : 2*(Real.pi:ℂ)*I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hj : J = (2*(Real.pi:ℂ)*I)*(fderiv ℝ (mass hκ n) u h : ℂ) := by
    change (fderiv ℝ (mass hκ n) u h : ℂ) = (2*(Real.pi:ℂ)*I)⁻¹*J at hm
    rw [hm]
    field_simp
  have he : (∮ z in C((center hκ u n : ℂ),radius hκ u n),
      fderiv ℝ (fun v : L2T L => symbol κ v z) u h /
        ScalarLogBranchR10.difference (exponential L z) (exponent hκ u z)) = (I*(κ:ℂ))*J := by
    rw [← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr (radius_pos hκ u n).le
    intro z hz
    exact (exponent_differential hκ u h z (circle_regular hκ u n hz)).symm
  rw [he,hj]
  simp only [mul_re,mul_im,I_re,I_im,ofReal_re,ofReal_im]
  norm_num
  field_simp

/-- The classical-symbol and differential clauses of PROP-010, under
exactly the physical hypotheses (in fact no unit norm is needed).
The operator reconstruction clause is not part of this partial theorem. -/
theorem condensate_reconstruction_classical (hκ : 0 < κ) (u : L2T L) (n : ℤ) :
    (∃ U : Set (L2T L), IsOpen U ∧ u ∈ U ∧
      (∀ v ∈ U, leadingPeriod hκ u n v = mass hκ n v) ∧
      (∀ v ∈ U, fderiv ℝ (leadingPeriod hκ u n) v = fderiv ℝ (mass hκ n) v)) ∧
    (∀ h : L2T L, fderiv ℝ (mass hκ n) u h = -(2*Real.pi*κ)⁻¹ *
      (∮ z in C((center hκ u n : ℂ),radius hκ u n),
        fderiv ℝ (fun v : L2T L => symbol κ v z) u h /
          ScalarLogBranchR10.difference (exponential L z) (exponent hκ u z)).re) := by
  obtain ⟨U,hU,hu,h⟩ := audit_scalar_period hκ u {n}
  have hn := h n (Finset.mem_singleton_self n)
  exact ⟨⟨U,hU,hu,hn.2.2.1,hn.2.2.2.2.1⟩,fun h => action_differential hκ u h n⟩

/-- The leading symbol for the actual chosen scalar extension f_z. -/
def cutoffSymbol (hκ : 0 < κ) (u : L2T L) (n : ℤ) (f : ℂ → ℂ → ℂ) (v : L2T L) : ℝ :=
  -(2*Real.pi*κ)⁻¹*(∮ z in C((center hκ u n : ℂ),radius hκ u n),f z (symbol κ v z)).re

/-- Every extension equal to the literal logarithm on the source's fixed
positive-radius tube has exactly the same full-neighborhood symbol and
full differential. The explicit extension premise is the cutoff's
construction property; it is not an assumed period identity. -/
theorem cutoff_symbol_identification (hκ : 0 < κ) (u : L2T L) (n : ℤ)
    (f : ℂ → ℂ → ℂ) {r : ℝ} (hr : 0 < r)
    (hf : ∀ z ∈ Metric.sphere (center hκ u n : ℂ) (radius hκ u n),
      ∀ w : ℂ, ‖w-symbol κ u z‖ < r → f z w = lambda hκ u z w) :
    ∃ U : Set (L2T L), IsOpen U ∧ u ∈ U ∧
      (∀ v ∈ U, cutoffSymbol hκ u n f v = mass hκ n v) ∧
      (∀ v ∈ U, AnalyticAt ℝ (cutoffSymbol hκ u n f) v) ∧
      (∀ v ∈ U, fderiv ℝ (cutoffSymbol hκ u n f) v = fderiv ℝ (mass hκ n) v) := by
  have hc : Continuous (fun p : L2T L × ℂ => symbol κ p.1 p.2) := by
    simp_rw [symbol_eq_trace hκ]
    have hd : Continuous (fun p : L2T L × ℂ => L2SpatialTransfer.discriminant κ p.1 p.2) :=
      continuous_iff_continuousAt.mpr fun p =>
        (DEF014DiscriminantAnalytic.analyticAt_discriminant_joint κ p).continuousAt
    exact (by fun_prop : Continuous (fun p : L2T L × ℂ => exp (I*p.2*L/2))).mul hd
  have hc0 : Continuous (fun p : L2T L × ℂ => symbol κ u p.2) :=
    hc.comp (continuous_const.prodMk continuous_snd)
  have hev : ∀ᶠ v : L2T L in 𝓝 u, ∀ z ∈ Metric.sphere (center hκ u n : ℂ) (radius hκ u n),
      ‖symbol κ v z-symbol κ u z‖ < r := by
    apply (isCompact_sphere (center hκ u n : ℂ) (radius hκ u n)).eventually_forall_of_forall_eventually
    intro z _
    exact (hc.sub hc0).norm.continuousAt.eventually (gt_mem_nhds (by simpa using hr))
  have heq : ∀ᶠ v : L2T L in 𝓝 u, cutoffSymbol hκ u n f v = mass hκ n v := by
    filter_upwards [hev,eventually_leadingPeriod hκ u n] with v hv hm
    rw [← hm]
    unfold cutoffSymbol leadingPeriod
    congr 2
    apply circleIntegral.integral_congr (radius_pos hκ u n).le
    intro z hz
    exact hf z hz _ (hv z hz)
  obtain ⟨U,hsub,hU,hu⟩ := mem_nhds_iff.mp heq
  refine ⟨U,hU,hu,hsub,?_,?_⟩
  · intro v hv
    apply (DEF014MassAnalytic.analyticAt_physical_coordinate hκ n v).congr
    filter_upwards [hU.mem_nhds hv] with w hw
    exact (hsub hw).symm
  · intro v hv
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hU.mem_nhds hv] with w hw
    exact hsub hw

#print axioms cutoff_symbol_identification
#check @cutoff_symbol_identification
end QuantumNLS.Prop010ClassicalR10
#print axioms QuantumNLS.Prop010ClassicalR10.condensate_reconstruction_classical
#check @QuantumNLS.Prop010ClassicalR10.condensate_reconstruction_classical

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Topology
open scoped InnerProductSpace BigOperators
namespace QuantumNLS.CondensateLocalizationR10
open HilbertDiagOp
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The source localization argument as a coefficient inequality. No
probability estimate or condensate reconstruction conclusion is assumed. -/
theorem spectral_error_sq_bound (b : HilbertBasis ι ℂ E) (ψ : E) {m : ℕ}
    (T : Fin m → E →L[ℂ] E) (t : Fin m → ι → ℂ)
    (hT : ∀ j i, T j (b i) = t j i • b i)
    (R : E →L[ℂ] E) (r : ι → ℂ) (hR : ∀ i, R (b i) = r i • b i)
    {ε A K : ℝ} (hε : 0 < ε)
    (hbound : ∀ i, ‖r i‖ ≤ K)
    (hgood : ∀ i, (∀ j, ‖t j i‖ < ε) → ‖r i‖ ≤ A) :
    ‖R ψ‖^2 ≤ A^2*‖ψ‖^2+K^2*ε⁻¹^8*∑ j, ‖((T j)^4) ψ‖^2 := by
  classical
  have heig : ∀ j k i, ((T j)^k) (b i) = (t j i)^k • b i := by
    intro j k i
    induction k with
    | zero => simp
    | succ k hk => simp [pow_succ,mul_apply_eq_comp,hT,hk,smul_smul,mul_comm]
  have hcoeff : ∀ j i, ⟪b i,((T j)^4) ψ⟫_ℂ = (t j i)^4*⟪b i,ψ⟫_ℂ :=
    fun j i => eig_coeff b _ _ (heig j 4) i ψ
  have hpow : ∀ j, HasSum (fun i => ‖t j i‖^8*‖⟪b i,ψ⟫_ℂ‖^2) (‖((T j)^4) ψ‖^2) := by
    intro j
    have hh := parseval_hasSum b (((T j)^4) ψ)
    convert hh using 1
    funext i
    rw [hcoeff,norm_mul,norm_pow,mul_pow,← pow_mul]
  have hr : HasSum (fun i => ‖r i‖^2*‖⟪b i,ψ⟫_ℂ‖^2) (‖R ψ‖^2) := by
    have hh := parseval_hasSum b (R ψ)
    convert hh using 1
    funext i
    rw [eig_coeff b R r hR,norm_mul,mul_pow]
  have hsum : HasSum (fun i => A^2*‖⟪b i,ψ⟫_ℂ‖^2 +
      K^2*ε⁻¹^8*∑ j, ‖t j i‖^8*‖⟪b i,ψ⟫_ℂ‖^2)
      (A^2*‖ψ‖^2+K^2*ε⁻¹^8*∑ j, ‖((T j)^4) ψ‖^2) :=
    ((parseval_hasSum b ψ).mul_left _).add ((hasSum_sum fun j _ => hpow j).mul_left _)
  apply hasSum_le _ hr hsum
  intro i
  have hpt : ‖r i‖^2 ≤ A^2+K^2*ε⁻¹^8*∑ j, ‖t j i‖^8 := by
    by_cases hg : ∀ j, ‖t j i‖ < ε
    · have hh := pow_le_pow_left₀ (norm_nonneg _) (hgood i hg) 2
      have hnn : 0 ≤ K^2*ε⁻¹^8*∑ j, ‖t j i‖^8 := by positivity
      linarith
    · push Not at hg
      obtain ⟨j,hj⟩ := hg
      have hs : ε^8 ≤ ∑ k, ‖t k i‖^8 :=
        (pow_le_pow_left₀ hε.le hj 8).trans (Finset.single_le_sum (f := fun k : Fin m => ‖t k i‖^8) (fun k _ => by positivity) (Finset.mem_univ j))
      have hi : (1:ℝ) ≤ ε⁻¹^8*∑ k, ‖t k i‖^8 := by
        rw [inv_pow,← div_eq_inv_mul,le_div_iff₀ (pow_pos hε 8)]
        simpa using hs
      have hb := pow_le_pow_left₀ (norm_nonneg _) (hbound i) 2
      have hh := mul_le_mul_of_nonneg_left hi (sq_nonneg K)
      nlinarith [sq_nonneg A]
  have hh := mul_le_mul_of_nonneg_right hpt (sq_nonneg ‖⟪b i,ψ⟫_ℂ‖)
  simpa only [add_mul,mul_assoc,Finset.sum_mul] using hh

/-- Squared source localization bounds yield exactly an N^-2 vector
bound when the fourth powers have N^-4 squared norms. -/
theorem rate_from_eighth_moments (b : HilbertBasis ι ℂ E) (ψ : E) (hψ : ‖ψ‖=1) {m : ℕ}
    (T : Fin m → E →L[ℂ] E) (t : Fin m → ι → ℂ)
    (hT : ∀ j i, T j (b i) = t j i • b i)
    (R : E →L[ℂ] E) (r : ι → ℂ) (hR : ∀ i, R (b i) = r i • b i)
    {ε C K x : ℝ} (hε : 0 < ε)
    (D : Fin m → ℝ) (hD : ∀ j, 0 ≤ D j)
    (hmoment : ∀ j, ‖((T j)^4) ψ‖^2 ≤ D j*x^4)
    (hbound : ∀ i, ‖r i‖ ≤ K)
    (hgood : ∀ i, (∀ j, ‖t j i‖ < ε) → ‖r i‖ ≤ C*x^2) :
    ‖R ψ‖ ≤ Real.sqrt (C^2+K^2*ε⁻¹^8*∑ j,D j)*x^2 := by
  have hh := spectral_error_sq_bound b ψ T t hT R r hR hε hbound hgood
  have hs : (∑ j, ‖((T j)^4) ψ‖^2) ≤ (∑ j,D j)*x^4 := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => hmoment j
  have hsD : 0 ≤ ∑ j,D j := Finset.sum_nonneg (fun j _ => hD j)
  have hnn : 0 ≤ C^2+K^2*ε⁻¹^8*∑ j,D j := by positivity
  have hb : ‖R ψ‖^2 ≤ (C^2+K^2*ε⁻¹^8*∑ j,D j)*x^4 := by
    rw [hψ,one_pow,mul_one] at hh
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ K^2*ε⁻¹^8 by positivity)
    nlinarith
  apply le_of_sq_le_sq_nonneg (by positivity)
  rw [mul_pow,Real.sq_sqrt hnn]
  simpa [← pow_mul] using hb

/-- The localization mechanism bound to the actual Bethe basis, the actual
condensate, and the unconditional PROP-008 eighth-moment estimate. This
is an explicit implication for a diagonal error operator, not an assertion
that a chosen C_N has the required scalar eigenvalue bounds. -/
theorem physical_error_rate {L κ : ℝ} [Fact (0<L)] (hκ : 0<κ)
    (u : PhysicalTensor.L2T L) (hu : ‖u‖=1) {N : ℕ} (hN : 0<N)
    {m : ℕ} (z : Fin m → ℂ) (hz : ∀ j,RootMeasureComplex.HighHalf L κ (z j))
    (R : KernelDefinition.BoundedSymmetricKernel (PhysicalTensor.L2T L) N)
    (r : BetheLabels.MArr N → ℂ)
    (hR : ∀ i,R (UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ i) =
      r i • UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ i)
    {ε C K : ℝ} (hε : 0<ε) (hbound : ∀ i,‖r i‖≤K)
    (hgood : ∀ i,(∀ j,‖NormalityBridge.eigen (L := L) κ hκ hN i (z j)-
      NormalizedTransfer.productSymbol L κ u (z j)‖<ε) → ‖r i‖≤C*((N:ℝ)⁻¹)^2) :
    ‖R (HighMomentsOps.wvec N u)‖ ≤ Real.sqrt (C^2+K^2*ε⁻¹^8*
      ∑ _j : Fin m,max 0 (HighMomentsTransfer.Cunif L κ 0 4))*((N:ℝ)⁻¹)^2 := by
  let b := UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ
  let T : Fin m → KernelDefinition.BoundedSymmetricKernel (PhysicalTensor.L2T L) N :=
    fun j => NormalizedTransfer.normalizedTransfer L κ N (z j)-
      NormalizedTransfer.productSymbol L κ u (z j) • 1
  let t : Fin m → BetheLabels.MArr N → ℂ := fun j i =>
    NormalityBridge.eigen (L := L) κ hκ hN i (z j)-NormalizedTransfer.productSymbol L κ u (z j)
  have hT : ∀ j i,T j (b i)=t j i • b i := by
    intro j i
    dsimp [T,t,b]
    rw [sub_apply,UnconditionalBetheBasis.transfer_physicalBasis hκ hN]
    simp only [smul_apply,one_apply_eq_self]
    exact (sub_smul _ _ _).symm
  let D : Fin m → ℝ := fun _ => max 0 (HighMomentsTransfer.Cunif L κ 0 4)
  have hm : ∀ j,‖((T j)^4) (HighMomentsOps.wvec N u)‖^2≤D j*((N:ℝ)⁻¹)^4 := by
    intro j
    have hj : -(0:ℝ)≤(z j).im := by have hh := (hz j).1; linarith
    have hh := (UnconditionalBetheBasis.transfer_moments_physical hκ hN
      (b' := 0) (by norm_num) u hu (z j) hj (p := 4) (by norm_num)).2
    have hC : HighMomentsTransfer.Cunif L κ 0 4≤D j := le_max_right _ _
    exact hh.trans (by dsimp [D]; rw [div_eq_mul_inv,inv_pow]; gcongr)
  exact rate_from_eighth_moments b (HighMomentsOps.wvec N u)
    (HighMomentsFinal.norm_wvec u hu N) T t hT R r hR hε D
    (fun _ => le_max_left _ _) hm hbound hgood

#print axioms physical_error_rate
#check @physical_error_rate
end QuantumNLS.CondensateLocalizationR10
#print axioms QuantumNLS.CondensateLocalizationR10.rate_from_eighth_moments

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Topology MeasureTheory
namespace QuantumNLS.CondensateProbesR10
open IndexedScalarMeasure IndexedScalarMeasureCuts
open LabelJointLimit LabelJointWeak LabelBlock
open PeriodReconstructionCore PeriodReconstruction PeriodTwoTerm
open RootMeasureComplex (HighHalf)
open PhysicalTensor (L2T)

/-- The fixed finite-probe version of the accepted two-term quantum
period estimate, rather than only a sequential asymptotic statement. -/
theorem finite_probes_two_term {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ)
    {n : ℤ} {a b h : ℝ} (ha : a ∈ S.cuts) (hb : b ∈ S.cuts) (hab : a < b) (hh : 0 < h)
    (h1 : 2*Real.pi*(n-1) < exteriorForce L κ S.μ a)
    (h2 : exteriorForce L κ S.μ a < 2*Real.pi*n)
    (h3 : 2*Real.pi*n < exteriorForce L κ S.μ b)
    (h4 : exteriorForce L κ S.μ b < 2*Real.pi*(n+1)) :
    ∃ m : ℕ, ∃ z : Fin m → ℂ, (∀ j, HighHalf L κ (z j)) ∧ ∃ ε > 0, ∃ N₀ : ℕ, ∃ C ≥ 0,
      ∀ (N : ℕ) (_hN : 0 < N), N₀ ≤ N → ∀ B : OnShellBethe L κ N,
        (∀ j, ‖sNf L (κ/N) B.q (z j)-sf L κ (EmpiricalRapidity.cauchyTransform S.μ) (z j)‖ < ε) →
        ‖twoTermErr L κ (EmpiricalRapidity.cauchyTransform S.μ) B n a b h‖ ≤ C*((N:ℝ)⁻¹)^2 := by
  let P : ℕ → ∀ N : ℕ, OnShellBethe L κ N → Prop := fun t N B =>
    ‖twoTermErr L κ (EmpiricalRapidity.cauchyTransform S.μ) B n a b h‖ ≤ (t:ℝ)*((N:ℝ)⁻¹)^2
  have hmono : ∀ t t' N (B : OnShellBethe L κ N), t ≤ t' → P t N B → P t' N B := by
    intro t t' N B htt hp
    exact hp.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast htt) (sq_nonneg _))
  have hseq : ∀ (N : ℕ → ℕ) (hN : ∀ k,0<N k) (B : ∀ k,OnShellBethe L κ (N k)),
      Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 (⟨S.μ,S.isProb⟩ : ProbabilityMeasure ℝ)) →
      Tendsto N atTop atTop → ∃ t, ∀ᶠ k in atTop,P t (N k) (B k) := by
    intro N _hN B hc hNt
    obtain ⟨C,hC⟩ := two_term_period S (μ := ⟨S.μ,S.isProb⟩) rfl hc hNt ha hb hab hh h1 h2 h3 h4
    refine ⟨⌈C⌉₊,hC.mono fun k hk => hk.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (Nat.le_ceil C) (sq_nonneg _)
  obtain ⟨m,z,hz,ε,hε,N₀,t,ht⟩ := Prop009ProbeDev.probes_generic S P hmono hseq
  exact ⟨m,z,hz,ε,hε,N₀,(t:ℝ),Nat.cast_nonneg t,ht⟩

variable {L κ : ℝ} [Fact (0 < L)]

/-- Physical fixed-unit-profile binding: the scalar target and cutpoints
are the actual quantum measure and its indexed phase separators. -/
theorem physical_two_term_probes (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖=1) (n : ℤ) {h : ℝ} (hh : 0<h) :
    ∃ m : ℕ, ∃ z : Fin m → ℂ, (∀ j, HighHalf L κ (z j)) ∧ ∃ ε > 0, ∃ N₀ : ℕ, ∃ C ≥ 0,
      ∀ (N : ℕ) (_hN : 0<N), N₀ ≤ N → ∀ B : OnShellBethe L κ N,
        (∀ j, ‖sNf L (κ/N) B.q (z j)-sf L κ (EmpiricalRapidity.cauchyTransform
          (PhysicalQuantumMeasure.measure hκ u)) (z j)‖ < ε) →
        ‖twoTermErr L κ (EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)) B n
          (RootScalarPeriodR8.cut hκ u (n-1)) (RootScalarPeriodR8.cut hκ u n) h‖ ≤ C*((N:ℝ)⁻¹)^2 := by
  let S := Prop026Bound.scalarCuts hκ u hu
  have hne : u ≠ 0 := by intro he; rw [he,norm_zero] at hu; norm_num at hu
  have hcut (k : ℤ) : RootScalarPeriodR8.cut hκ u k ∈ S.cuts :=
    (DEF014Phase.facts ((⟨κ,hκ⟩,u) : DEF014Phase.Param L)).separator_in_band k
  have hf (k : ℤ) : exteriorForce L κ S.μ (RootScalarPeriodR8.cut hκ u k) =
      2*((k:ℝ)+1/2)*Real.pi := by
    change exteriorForce L κ (Prop026Bound.M hκ u) _ = _
    rw [Prop026Bound.force_eq hκ hne (hcut k)]
    have hp := (PhysicalSourceFinal.sourceFacts hκ u).phase.separator_spec k
    change Prop026Bound.theta hκ u (RootScalarPeriodR8.cut hκ u k) = ((k:ℝ)+1/2)*Real.pi at hp
    rw [hp]
    ring
  apply finite_probes_two_term S (hcut (n-1)) (hcut n)
    ((DEF014Phase.facts ((⟨κ,hκ⟩,u) : DEF014Phase.Param L)).phase.separator_strictMono (by omega)) hh
  all_goals rw [hf]; push_cast; nlinarith [Real.pi_pos]
end QuantumNLS.CondensateProbesR10
#print axioms QuantumNLS.CondensateProbesR10.physical_two_term_probes

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex
namespace QuantumNLS.Round10
open PhysicalTensor (L2T)
open RootMassInvolutionR8 (mass)
open RootScalarPeriodR8 (cut center radius)
open RootScalarPeriodR10
variable {L κ : ℝ} [Fact (0 < L)]

/-- R-620D5517, assembled with the source's exact scalar inverse and
logarithm, the full 1/D differential, and local continuation at every
point of the full equal-discriminant level. -/
theorem audit_scalar_period (hκ : 0 < κ) (u : L2T L) (F : Finset ℤ) :
    (∃ U : Set (L2T L), IsOpen U ∧ u ∈ U ∧ ∀ n ∈ F,
      0 < radius hκ u n ∧
      (∀ v ∈ U, ∀ z ∈ Metric.sphere (center hκ u n : ℂ) (radius hκ u n),
        lambda hκ u z (symbol κ v z) = exponent hκ v z) ∧
      (∀ v ∈ U, leadingPeriod hκ u n v = mass hκ n v) ∧
      (∀ v ∈ U, AnalyticAt ℝ (leadingPeriod hκ u n) v) ∧
      (∀ v ∈ U, fderiv ℝ (leadingPeriod hκ u n) v = fderiv ℝ (mass hκ n) v) ∧
      (∀ h : L2T L, fderiv ℝ (mass hκ n) u h = -(2*Real.pi*κ)⁻¹ *
        (∮ z in C((center hκ u n : ℂ),radius hκ u n),
          fderiv ℝ (fun v : L2T L => symbol κ v z) u h /
            ScalarLogBranchR10.difference (exponential L z) (exponent hκ u z)).re)) ∧
    (∀ v : L2T L, RootScalarLevelR10.SameDiscriminant (κ := κ) u v →
      ∃ V : Set (L2T L), IsOpen V ∧ v ∈ V ∧ ∀ n ∈ F,
        (∀ w ∈ V, leadingPeriod hκ u n w = mass hκ n w) ∧
        (∀ w ∈ V, fderiv ℝ (leadingPeriod hκ u n) w = fderiv ℝ (mass hκ n) w)) := by
  obtain ⟨U,hU,hu,hp⟩ := RootScalarPeriodR10.audit_scalar_period hκ u F
  refine ⟨⟨U,hU,hu,fun n hn => ?_⟩,fun v hv =>
    RootScalarLevelR10.equal_discriminant_neighborhood hκ u v F hv⟩
  have h := hp n hn
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,
    fun h => Prop010ClassicalR10.action_differential hκ u h n⟩
end QuantumNLS.Round10
#print axioms QuantumNLS.Round10.audit_scalar_period
#check @QuantumNLS.Round10.audit_scalar_period
#check @QuantumNLS.CondensateProbesR10.physical_two_term_probes
#check @QuantumNLS.CondensateLocalizationR10.rate_from_eighth_moments

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootScalarLevelR10." ||
        n.toString.startsWith "QuantumNLS.Prop010ClassicalR10." ||
        n.toString.startsWith "QuantumNLS.CondensateLocalizationR10." ||
        n.toString.startsWith "QuantumNLS.CondensateProbesR10." ||
        n.toString.startsWith "QuantumNLS.Round10." ||
        n.toString.startsWith "QuantumNLS.ScalarLogBranchR10." ||
        n.toString.startsWith "QuantumNLS.RootScalarPeriodR10." ||
        n.toString.startsWith "QuantumNLS.RootScalarDifferentialR10." ||
        n.toString.startsWith "_private.QuantumNLS.Round10ScalarReconstructionBatch." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Round10ScalarReconstructionBatch audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
