import Armstrong.Work.CartesianContinuationSpec
import Armstrong.Work.CartesianTerminalRootSpec
import Armstrong.Work.RawBetaRootDerivative
import Armstrong.Work.RawBetaCompactIntegrability
import Armstrong.Work.RawBetaRootedPath
import Armstrong.Work.RawBetaEndpointZero
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Actual diagonal rooted-path exponential bridge

The actual continuous path sheet is normalized by the nonvanishing omitted
root. No canonical sheet value on the own cut is used. The positive eta
exponential uses sign -1 in this normalized-sheet model. The genuine additive
improper-integral limit is earned from local endpoint logarithms and compact
FTC, then combined with signed exponential transport. This remains ordinary
speculative infrastructure, without a claim of Cartesian source-node closure.
-/
set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
namespace NlsGge.GK38
noncomputable section

/-- The exact nonvanishing factor removed from the actual full sheet. -/
def gk16OwnSheetDenominator38 (phi : PotPair) (n : ℤ) (z : ℂ) : ℂ :=
  ((2*Complex.I)/(Lib.piN n : ℂ))*a5OmittedRootProduct38 n (phi,z)

/-- Literal normalization of the actual path sheet. -/
def gk16ArcNormalizedSheet38 (phi : GKPotential38) (n : ℤ)
    (arc : GKRootedC1Arc38 phi n) (t : ℝ) : ℂ :=
  GKArcSheet38 arc t / gk16OwnSheetDenominator38 phi.1 n (GKArcCurve38 arc t)

/-- Literal signed quadratic exponential along the actual rooted arc. -/
def gk16ArcExponentialModel38 (phi : GKPotential38) (n : ℤ)
    (eps : ℂ) (R : ℂ → ℂ) (arc : GKRootedC1Arc38 phi n) (t : ℝ) : ℂ :=
  (2*((lamMinus phi.1 n+lamPlus phi.1 n)/2-GKArcCurve38 arc t)-
      2*eps*gk16ArcNormalizedSheet38 phi n arc t) *
    Complex.exp (eps*gk16ArcNormalizedSheet38 phi n arc t*R (GKArcCurve38 arc t))

theorem gk16_own_sheet_denominator38 (phi : GKPotential38) (n : ℤ) :
    AnalyticOnNhd ℂ (gk16OwnSheetDenominator38 phi.1 n)
      (ball (discC phi.1 n) (discR phi.1 n)) ∧
    ∀ z ∈ ball (discC phi.1 n) (discR phi.1 n),
      gk16OwnSheetDenominator38 phi.1 n z ≠ 0 := by
  have hfam := isolating_family38 phi.1 phi.2
  have hK : ((2*Complex.I)/(Lib.piN n : ℂ)) ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero n))
  constructor
  · intro z hz
    have hdom := a5OwnClosedBall_omittedDomain38 phi.1 phi.2
      (discC phi.1) (discR phi.1) hfam n z (ball_subset_closedBall hz)
    exact analyticAt_const.mul ((a5OmittedRoot_analytic38 n (phi.1,z) hdom).comp
      (analyticAt_const.prod analyticAt_id))
  · intro z hz
    exact mul_ne_zero hK (a5OmittedRoot_ne_zero38 n (phi.1,z)
      (a5OwnClosedBall_omittedDomain38 phi.1 phi.2
        (discC phi.1) (discR phi.1) hfam n z (ball_subset_closedBall hz)))

theorem gk16_arc_normalized_sheet_continuous38
    (phi : GKPotential38) (n : ℤ) (arc : GKRootedC1Arc38 phi n) :
    ContinuousOn (gk16ArcNormalizedSheet38 phi n arc) (Icc (0 : ℝ) 1) := by
  have hD := gk16_own_sheet_denominator38 phi n
  exact arc.2.2.2.1.div₀
    (hD.1.continuousOn.comp arc.2.1 (fun t ht => arc.2.2.2.2.2.1 t ht))
    (fun t ht => hD.2 _ (arc.2.2.2.2.2.1 t ht))

theorem gk16_arc_normalized_sheet_sq38
    (phi : GKPotential38) (n : ℤ) (arc : GKRootedC1Arc38 phi n)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (gk16ArcNormalizedSheet38 phi n arc t)^2 =
      (GKArcCurve38 arc t-lamMinus phi.1 n)*(GKArcCurve38 arc t-lamPlus phi.1 n) := by
  have hz := arc.2.2.2.2.2.1 t ht
  have hden : gk16OwnSheetDenominator38 phi.1 n (GKArcCurve38 arc t) ≠ 0 :=
    (gk16_own_sheet_denominator38 phi n).2 _ hz
  have hsheetSquare : GKArcSheet38 arc t ^ 2 =
      perChar phi.1 (GKArcCurve38 arc t) := arc.2.2.2.2.1 t ht
  have hsquare := hsheetSquare.trans
    (rawBetaFixedFilledFactorization38 phi.1 phi.2 (discC phi.1) (discR phi.1)
      (isolating_family38 phi.1 phi.2) n (GKArcCurve38 arc t) (ball_subset_closedBall hz))
  unfold gk16ArcNormalizedSheet38
  rw [div_pow,hsquare]
  apply (div_eq_iff (pow_ne_zero 2 hden)).2
  unfold gk16OwnSheetDenominator38
  ring

theorem gk16_arc_normalized_sheet_ne_zero38
    (phi : GKPotential38) (n : ℤ) (arc : GKRootedC1Arc38 phi n)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    gk16ArcNormalizedSheet38 phi n arc t ≠ 0 := by
  have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
  have hsheet : GKArcSheet38 arc t ≠ 0 := by
    intro hzero
    apply rawBetaPerCharNonzeroOnSlit38 phi n (GKArcCurve38 arc t)
      (arc.2.2.2.2.2.2 t ht)
    have hsq : GKArcSheet38 arc t ^ 2 =
        perChar phi.1 (GKArcCurve38 arc t) := arc.2.2.2.2.1 t htcc
    simpa only [hzero,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hsq.symm
  exact div_ne_zero hsheet
    ((gk16_own_sheet_denominator38 phi n).2 _ (arc.2.2.2.2.2.1 t htcc))

/-- A continuous normalized sheet inherits its real parameter derivative from
its actual quadratic square; endpoint derivatives are not required. -/
theorem gk16_arc_normalized_sheet_hasDerivAt38
    (phi : GKPotential38) (n : ℤ) (arc : GKRootedC1Arc38 phi n)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (gk16ArcNormalizedSheet38 phi n arc)
      (((GKArcCurve38 arc t-(lamMinus phi.1 n+lamPlus phi.1 n)/2)*
        deriv (GKArcCurve38 arc) t) / gk16ArcNormalizedSheet38 phi n arc t) t := by
  have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
  have htn : Icc (0 : ℝ) 1 ∈ nhds t := Icc_mem_nhds ht.1 ht.2
  have hgamma : DifferentiableAt ℝ (GKArcCurve38 arc) t :=
    (arc.2.2.1.differentiableOn (by norm_num) t htcc).differentiableAt htn
  let Q : ℂ → ℂ := fun z => (z-lamMinus phi.1 n)*(z-lamPlus phi.1 n)
  have hQ : HasDerivAt Q
      (2*(GKArcCurve38 arc t-(lamMinus phi.1 n+lamPlus phi.1 n)/2))
      (GKArcCurve38 arc t) := by
    apply (((hasDerivAt_id (GKArcCurve38 arc t)).sub_const (lamMinus phi.1 n)).mul
      ((hasDerivAt_id (GKArcCurve38 arc t)).sub_const (lamPlus phi.1 n))).congr_deriv
    simp only [id_eq]
    ring
  have he : (fun u => (gk16ArcNormalizedSheet38 phi n arc u)^2) =ᶠ[nhds t]
      Q ∘ GKArcCurve38 arc := by
    filter_upwards [htn] with u hu
    exact gk16_arc_normalized_sheet_sq38 phi n arc u hu
  have hne := gk16_arc_normalized_sheet_ne_zero38 phi n arc t ht
  have hd := rawBetaContinuousRootHasDerivAtOfEq38 hgamma.hasDerivAt hQ
    ((gk16_arc_normalized_sheet_continuous38 phi n arc).continuousAt htn) hne he
  apply hd.congr_deriv
  field_simp [hne]

/-- The real-parameter version of the signed quadratic exponential ODE.
The sheet need not be an analytic function of the spectral variable. -/
theorem gk16_correction_real_hasDerivAt38
    (a b eps q : ℂ) (gamma v : ℝ → ℂ) (R : ℂ → ℂ)
    (t : ℝ) (gd vd Rd : ℂ) (heps : eps^2 = 1) (hvn : v t ≠ 0)
    (hgamma : HasDerivAt gamma gd t) (hv : HasDerivAt v vd t)
    (hR : HasDerivAt R Rd (gamma t))
    (hroot : (v t)^2 = (gamma t-a)*(gamma t-b))
    (hrootder : v t*vd = (gamma t-(a+b)/2)*gd)
    (hode : (gamma t-a)*(gamma t-b)*Rd+(gamma t-(a+b)/2)*R (gamma t) = q-1) :
    HasDerivAt
      (fun u => (2*((a+b)/2-gamma u)-2*eps*v u)*
        Complex.exp (eps*v u*R (gamma u)))
      ((eps*q/v t)*gd*((2*((a+b)/2-gamma t)-2*eps*v t)*
        Complex.exp (eps*v t*R (gamma t)))) t := by
  have hvd : vd = ((gamma t-(a+b)/2)*gd)/v t := by
    apply (eq_div_iff hvn).2
    simpa only [mul_comm] using hrootder
  have hc : vd*R (gamma t)+v t*(Rd*gd) = ((q-1)/v t)*gd := by
    calc
      _ = ((q-1)*gd)/v t := by
        apply (eq_div_iff hvn).2
        calc
          (vd*R (gamma t)+v t*(Rd*gd))*v t =
              ((v t*vd)*R (gamma t)+(v t)^2*Rd*gd) := by ring
          _ = (q-1)*gd := by
            rw [hrootder,hroot]
            linear_combination gd * hode
      _ = ((q-1)/v t)*gd := by ring
  have hp : -2*gd-2*eps*vd =
      (eps/v t)*gd*(2*((a+b)/2-gamma t)-2*eps*v t) := by
    rw [hvd]
    field_simp [hvn]
    linear_combination 2*v t*gd * heps
  have hdP : HasDerivAt
      (fun u => 2*((a+b)/2-gamma u)-2*eps*v u) (-2*gd-2*eps*vd) t := by
    apply (((hgamma.const_sub ((a+b)/2)).const_mul 2).sub
      (hv.const_mul (2*eps))).congr_deriv
    ring
  have hdF : HasDerivAt (fun u : ℝ => eps*v u*R (gamma u))
      (eps*(vd*R (gamma t)+v t*(Rd*gd))) t := by
    simpa only [Pi.mul_apply,Function.comp_apply,mul_assoc] using
      (hv.mul (hR.comp t hgamma)).const_mul eps
  apply (hdP.mul hdF.cexp).congr_deriv
  rw [hp,hc]
  field_simp [hvn]
  ring

/-- The actual own numerator divided by the omitted sheet factor is i*q.
This identity is valid on the filled disc, including the own cut. -/
theorem gk16_own_numerator_div_sheet_factor38
    (phi : GKPotential38) (n : ℤ) (s : Lib.L2Seq)
    (z : ℂ) (hz : z ∈ ball (discC phi.1 n) (discR phi.1 n)) :
    p2FullNumerator38 n s z / gk16OwnSheetDenominator38 phi.1 n z =
      Complex.I*p2OmittedRatio38 n ((phi.1,s),z) := by
  have hD := a5OmittedRoot_ne_zero38 n (phi.1,z)
    (a5OwnClosedBall_omittedDomain38 phi.1 phi.2 (discC phi.1) (discR phi.1)
      (isolating_family38 phi.1 phi.2) n z (ball_subset_closedBall hz))
  unfold p2FullNumerator38 gk16OwnSheetDenominator38 p2OmittedRatio38
  field_simp [hD,Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero n),Complex.I_ne_zero]
  simp only [Complex.I_sq]
  ring

/-- Exact diagonal integrand on the supplied actual sheet. -/
theorem gk16_diagonal_arc_integrand38
    (n : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (phi : GKPotential38) (s : Lib.L2Seq)
    (hnum : p6PsiNumerator38 n (F n) phi.1 = p2FullNumerator38 n s)
    (arc : GKRootedC1Arc38 phi n) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    GKRootedArcIntegrand38 n n F phi arc t =
      (Complex.I*p2OmittedRatio38 n ((phi.1,s),GKArcCurve38 arc t) /
        gk16ArcNormalizedSheet38 phi n arc t)*deriv (GKArcCurve38 arc) t := by
  have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
  have hz := arc.2.2.2.2.2.1 t htcc
  have hden : gk16OwnSheetDenominator38 phi.1 n (GKArcCurve38 arc t) ≠ 0 :=
    (gk16_own_sheet_denominator38 phi n).2 _ hz
  have hratio := gk16_own_numerator_div_sheet_factor38 phi n s (GKArcCurve38 arc t) hz
  have hnumEq := (div_eq_iff hden).mp hratio
  have hsheet : GKArcSheet38 arc t ≠ 0 := by
    intro hzero
    apply gk16_arc_normalized_sheet_ne_zero38 phi n arc t ht
    simp only [gk16ArcNormalizedSheet38,hzero,zero_div]
  unfold GKRootedArcIntegrand38 gk16ArcNormalizedSheet38
  rw [hnum,hnumEq]
  field_simp [hden,hsheet] <;> ring

/-- The actual density is continuous in the open parameter interval. Values
of the ordinary curve derivative at the two endpoints are not used. -/
theorem gk16_arc_integrand_continuous38
    (n : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (phi : GKPotential38) (arc : GKRootedC1Arc38 phi n) :
    ContinuousOn (GKRootedArcIntegrand38 n n F phi arc) (Ioo (0 : ℝ) 1) := by
  have hnumerator : Continuous (p6PsiNumerator38 n (F n) phi.1) :=
    continuousOn_univ.mp (p6PsiNumerator_entire38 n (F n) phi.1).continuousOn
  have hsheet : ∀ t ∈ Ioo (0 : ℝ) 1, GKArcSheet38 arc t ≠ 0 := by
    intro t ht hzero
    apply gk16_arc_normalized_sheet_ne_zero38 phi n arc t ht
    simp only [gk16ArcNormalizedSheet38,hzero,zero_div]
  have hquotient := ((hnumerator.comp_continuousOn arc.2.1).mono
    Ioo_subset_Icc_self).div₀ (arc.2.2.2.1.mono Ioo_subset_Icc_self) hsheet
  exact hquotient.mul
    ((arc.2.2.1.mono Ioo_subset_Icc_self).continuousOn_deriv_of_isOpen
      isOpen_Ioo (by norm_num))

/-- The model is continuous even at either branch point. -/
theorem gk16_arc_model_continuous38
    (phi : GKPotential38) (n : ℤ) (eps : ℂ) (R : ℂ → ℂ)
    (hR : AnalyticOnNhd ℂ R (ball (discC phi.1 n) (discR phi.1 n)))
    (arc : GKRootedC1Arc38 phi n) :
    ContinuousOn (gk16ArcExponentialModel38 phi n eps R arc) (Icc (0 : ℝ) 1) := by
  have hv := gk16_arc_normalized_sheet_continuous38 phi n arc
  have hRc := hR.continuousOn.comp arc.2.1
    (fun t ht => arc.2.2.2.2.2.1 t ht)
  exact ((continuousOn_const.mul (continuousOn_const.sub arc.2.1)).sub
    (continuousOn_const.mul hv)).mul
      (((continuousOn_const.mul hv).mul hRc).cexp)

/-- The two signed models have the exact gap-square product, including at
branch points; exponentials do not obscure a possible zero. -/
theorem gk16_arc_model_product38
    (phi : GKPotential38) (n : ℤ) (R : ℂ → ℂ)
    (arc : GKRootedC1Arc38 phi n) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    gk16ArcExponentialModel38 phi n (-1) R arc t *
      gk16ArcExponentialModel38 phi n 1 R arc t =
        (lamPlus phi.1 n-lamMinus phi.1 n)^2 := by
  have hsquare := gk16_arc_normalized_sheet_sq38 phi n arc t ht
  unfold gk16ArcExponentialModel38
  rw [mul_mul_mul_comm, ← Complex.exp_add]
  have he : (-1 : ℂ)*gk16ArcNormalizedSheet38 phi n arc t*R (GKArcCurve38 arc t)+
      1*gk16ArcNormalizedSheet38 phi n arc t*R (GKArcCurve38 arc t) = 0 := by ring
  rw [he,Complex.exp_zero,mul_one]
  linear_combination -4 * hsquare

/-- Noncollapse alone guarantees both actual models are nonzero on the whole
closed parameter interval, including a Dirichlet terminal at either tip. -/
theorem gk16_arc_model_ne_zero38
    (phi : GKPotential38) (n : ℤ) (R : ℂ → ℂ)
    (hgap : lamMinus phi.1 n ≠ lamPlus phi.1 n)
    (arc : GKRootedC1Arc38 phi n) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    gk16ArcExponentialModel38 phi n (-1) R arc t ≠ 0 ∧
      gk16ArcExponentialModel38 phi n 1 R arc t ≠ 0 := by
  apply mul_ne_zero_iff.mp
  rw [gk16_arc_model_product38 phi n R arc t ht]
  exact pow_ne_zero 2 (sub_ne_zero.mpr hgap.symm)

/-- Signed model ODE on the actual rooted arc, using the coefficient produced
from this same numerator's exact own period. In particular eps=-1 gives +i
 times the actual diagonal density, and eps=1 gives -i times that density. -/
theorem gk16_diagonal_arc_model_hasDerivAt38
    (n : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (phi : GKPotential38) (s : Lib.L2Seq)
    (hnum : p6PsiNumerator38 n (F n) phi.1 = p2FullNumerator38 n s)
    (hperiod : abelianPeriod38 n phi.1
      (p6PsiNumerator38 n (F n) phi.1) = 2*(Real.pi : ℂ))
    (eps : ℂ) (heps : eps^2 = 1) (arc : GKRootedC1Arc38 phi n)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    let R := gk16OwnCorrectionCoefficient38 phi.1 n s
      (discC phi.1 n) (discR phi.1 n)
    HasDerivAt (gk16ArcExponentialModel38 phi n eps R arc)
      ((-eps*Complex.I)*GKRootedArcIntegrand38 n n F phi arc t *
        gk16ArcExponentialModel38 phi n eps R arc t) t := by
  let R := gk16OwnCorrectionCoefficient38 phi.1 n s
    (discC phi.1 n) (discR phi.1 n)
  have hR := gk16_own_correction_coefficient38 phi.1 phi.2
    (discC phi.1) (discR phi.1) (isolating_family38 phi.1 phi.2) n s
    (by simpa only [hnum] using hperiod)
  have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
  have hgamma : DifferentiableAt ℝ (GKArcCurve38 arc) t :=
    (arc.2.2.1.differentiableOn (by norm_num) t htcc).differentiableAt
      (Icc_mem_nhds ht.1 ht.2)
  have hvn := gk16_arc_normalized_sheet_ne_zero38 phi n arc t ht
  have hv := gk16_arc_normalized_sheet_hasDerivAt38 phi n arc t ht
  have hvd : gk16ArcNormalizedSheet38 phi n arc t *
      (((GKArcCurve38 arc t-(lamMinus phi.1 n+lamPlus phi.1 n)/2)*
        deriv (GKArcCurve38 arc) t)/gk16ArcNormalizedSheet38 phi n arc t) =
      (GKArcCurve38 arc t-(lamMinus phi.1 n+lamPlus phi.1 n)/2)*
        deriv (GKArcCurve38 arc) t := by field_simp [hvn]
  have hd := gk16_correction_real_hasDerivAt38
    (lamMinus phi.1 n) (lamPlus phi.1 n) eps
    (p2OmittedRatio38 n ((phi.1,s),GKArcCurve38 arc t))
    (GKArcCurve38 arc) (gk16ArcNormalizedSheet38 phi n arc) R t
    (deriv (GKArcCurve38 arc) t) _ (deriv R (GKArcCurve38 arc t)) heps hvn
    hgamma.hasDerivAt hv
    ((hR.1 _ (arc.2.2.2.2.2.1 t htcc)).differentiableAt.hasDerivAt)
    (gk16_arc_normalized_sheet_sq38 phi n arc t htcc) hvd
    (hR.2 _ (arc.2.2.2.2.2.1 t htcc))
  apply hd.congr_deriv
  rw [gk16_diagonal_arc_integrand38 n F phi s hnum arc t ht]
  unfold gk16ArcExponentialModel38
  field_simp [hvn]
  ring_nf <;> simp only [Complex.I_sq] <;> ring

/-- Both the curve and the actual sheet agree at a supplied rooted join. -/
theorem gk16_arc_model_join38
    (phi : GKPotential38) (n : ℤ) (eps : ℂ) (R : ℂ → ℂ)
    (a b : GKRootedC1Arc38 phi n) (h : GKRootedArcJoin38 phi n a b) :
    gk16ArcExponentialModel38 phi n eps R a 1 =
      gk16ArcExponentialModel38 phi n eps R b 0 := by
  simp only [gk16ArcExponentialModel38,gk16ArcNormalizedSheet38,h.1,h.2.1]

/-- Literal endpoint values of the normalized actual sheet. The terminal
identity includes mu at either periodic tip, where both raw sheets vanish. -/
theorem gk16_path_normalized_sheet_endpoints38
    (phi : GKPotential38) (n : ℤ) (p : GKRootedPiecewisePath38 phi n) :
    gk16ArcNormalizedSheet38 phi n (GKPathFirst38 p) 0 = 0 ∧
      gk16ArcNormalizedSheet38 phi n (GKPathLast38 p) 1 =
        gk16TerminalRoot38 n phi.1 := by
  have hfirst : GKArcSheet38 (GKPathFirst38 p) 0 = 0 := by
    have hsq : GKArcSheet38 (GKPathFirst38 p) 0 ^ 2 =
        perChar phi.1 (GKArcCurve38 (GKPathFirst38 p) 0) :=
      (GKPathFirst38 p).2.2.2.2.1 0 ⟨le_rfl,zero_le_one⟩
    have hcurve : GKArcCurve38 (GKPathFirst38 p) 0 = lamMinus phi.1 n := p.2.2.2.1
    apply sq_eq_zero_iff.mp
    rw [hsq,hcurve]
    exact rawBetaPerCharLowerTipZero38 phi n
  have hlastCurve : GKArcCurve38 (GKPathLast38 p) 1 = muSeq phi.1 n := p.2.2.2.2.1
  have hlast : GKArcSheet38 (GKPathLast38 p) 1 = antiDiscrim phi.1 (muSeq phi.1 n) := by
    by_cases ht : muSeq phi.1 n = lamMinus phi.1 n ∨ muSeq phi.1 n = lamPlus phi.1 n
    · have hball : muSeq phi.1 n ∈ ball (discC phi.1 n) (discR phi.1 n) := by
        rw [← hlastCurve]
        exact (GKPathLast38 p).2.2.2.2.2.1 1 ⟨zero_le_one,le_rfl⟩
      have hPzero := (rawBetaPerCharZeroInDiscIff38 phi n (muSeq phi.1 n) hball).mpr ht
      have hs0 : GKArcSheet38 (GKPathLast38 p) 1 = 0 := by
        have hsq : GKArcSheet38 (GKPathLast38 p) 1 ^ 2 =
            perChar phi.1 (GKArcCurve38 (GKPathLast38 p) 1) :=
          (GKPathLast38 p).2.2.2.2.1 1 ⟨zero_le_one,le_rfl⟩
        apply sq_eq_zero_iff.mp
        rw [hsq,hlastCurve,hPzero]
      have ha0 : antiDiscrim phi.1 (muSeq phi.1 n) = 0 :=
        sq_eq_zero_iff.mp ((rawBetaDirichletTerminalSquare38 phi n).trans hPzero)
      rw [hs0,ha0]
    · exact p.2.2.2.2.2 (fun h => ht (Or.inl h)) (fun h => ht (Or.inr h))
  constructor
  · simp only [gk16ArcNormalizedSheet38,hfirst,zero_div]
  · simp only [gk16ArcNormalizedSheet38,gk16OwnSheetDenominator38,
      gk16TerminalRoot38,hlast,hlastCurve]

/-- Exact source endpoints of the signed path model, without a terminal
canonical-root convention and without excluding either Dirichlet tip. -/
theorem gk16_path_model_endpoints38
    (phi : GKPotential38) (n : ℤ) (eps : ℂ) (R : ℂ → ℂ)
    (p : GKRootedPiecewisePath38 phi n) :
    gk16ArcExponentialModel38 phi n eps R (GKPathFirst38 p) 0 =
        lamPlus phi.1 n-lamMinus phi.1 n ∧
      gk16ArcExponentialModel38 phi n eps R (GKPathLast38 p) 1 =
        (2*((lamMinus phi.1 n+lamPlus phi.1 n)/2-muSeq phi.1 n)-
          2*eps*gk16TerminalRoot38 n phi.1) *
        Complex.exp (eps*gk16TerminalRoot38 n phi.1*R (muSeq phi.1 n)) := by
  have hend := gk16_path_normalized_sheet_endpoints38 phi n p
  have hfirstCurve : GKArcCurve38 (GKPathFirst38 p) 0 = lamMinus phi.1 n := p.2.2.2.1
  have hlastCurve : GKArcCurve38 (GKPathLast38 p) 1 = muSeq phi.1 n := p.2.2.2.2.1
  constructor
  · simp only [gk16ArcExponentialModel38,hend.1,hfirstCurve,mul_zero,zero_mul,
      Complex.exp_zero,sub_zero,mul_one]
    ring
  · simp only [gk16ArcExponentialModel38,hend.2,hlastCurve]

/-- Compact scalar ODE transport, with no endpoint derivative or nonzero
solution hypothesis. The density may have arbitrary values at the endpoints. -/
theorem gk16_compact_exponential_transport38
    (u v : ℝ) (huv : u ≤ v) (c : ℂ) (f G : ℝ → ℂ)
    (hG : ContinuousOn G (Icc u v))
    (hf : IntervalIntegrable f volume u v)
    (hfc : ContinuousOn f (Ioo u v))
    (hGd : ∀ t ∈ Ioo u v, HasDerivAt G (c*f t*G t) t) :
    G v = G u * Complex.exp (c*(∫ t in u..v, f t)) := by
  let J : ℝ → ℂ := fun x => ∫ t in u..x, f t
  have hJc : ContinuousOn J (Icc u v) := by
    simpa only [uIcc_of_le huv] using
      (intervalIntegral.continuousOn_primitive_interval' hf (a := u) left_mem_uIcc)
  have hJd : ∀ t ∈ Ioo u v, HasDerivAt J (f t) t := by
    intro t ht
    have htcc : t ∈ uIcc u v := by
      rw [uIcc_of_le huv]
      exact ⟨ht.1.le,ht.2.le⟩
    have hfit : IntervalIntegrable f volume u t :=
      hf.mono_set (uIcc_subset_uIcc_left htcc)
    exact intervalIntegral.integral_hasDerivAt_right hfit
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hfc t ht)
      ((hfc t ht).continuousAt (isOpen_Ioo.mem_nhds ht))
  let H : ℝ → ℂ := fun t => G t * Complex.exp ((-c)*J t)
  have hHc : ContinuousOn H (Icc u v) :=
    hG.mul ((continuousOn_const.mul hJc).cexp)
  have hHd : ∀ t ∈ Ioo u v, HasDerivAt H (0 : ℂ) t := by
    intro t ht
    apply ((hGd t ht).mul (((hJd t ht).const_mul (-c)).cexp)).congr_deriv
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    huv hHc hHd (intervalIntegrable_const (a := u) (b := v) (c := (0 : ℂ)))
  have hHu : H u = G u := by
    simp only [H,J,intervalIntegral.integral_same,mul_zero,Complex.exp_zero,mul_one]
  have hHv : H v = G u := by
    rw [← hHu]
    apply sub_eq_zero.mp
    simpa only [intervalIntegral.integral_zero] using hFTC.symm
  have hcancel : Complex.exp ((-c)*J v)*Complex.exp (c*J v) = 1 := by
    rw [← Complex.exp_add]
    have hz : (-c)*J v+c*J v = 0 := by ring
    rw [hz,Complex.exp_zero]
  calc
    G v = (G v*Complex.exp ((-c)*J v))*Complex.exp (c*J v) := by
      rw [mul_assoc,hcancel,mul_one]
    _ = G u*Complex.exp (c*J v) := by
      change H v*Complex.exp (c*J v) = _
      rw [hHv]

/-- A nonzero continuous endpoint of a logarithmic ODE admits a genuine local
additive primitive. This is not an inference from convergence of exponentials. -/
theorem gk16_local_log_left_primitive38
    (G f : ℝ → ℂ)
    (hG : ContinuousOn G (Icc (0 : ℝ) 1))
    (hG0 : G 0 ≠ 0)
    (hder : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt G (Complex.I*f t*G t) t) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      (∀ t ∈ Icc (0 : ℝ) delta, G t/G 0 ∈ Complex.slitPlane) ∧
      let L : ℝ → ℂ := fun t => -Complex.I * Complex.log (G t/G 0)
      ContinuousOn L (Icc (0 : ℝ) delta) ∧ L 0 = 0 ∧
        ∀ t ∈ Ioo (0 : ℝ) delta, HasDerivAt L (f t) t := by
  let H : ℝ → ℂ := fun t => G t/G 0
  have hH : ContinuousOn H (Icc (0 : ℝ) 1) := hG.div_const (G 0)
  have hH0 : H 0 = 1 := div_self hG0
  obtain ⟨r,hr,hclose⟩ := Metric.continuousWithinAt_iff.mp
    (hH 0 (by norm_num)) 1 (by norm_num)
  let delta : ℝ := min (r/2) 1
  have hdelta : 0 < delta := lt_min (half_pos hr) (by norm_num)
  have hdle : delta ≤ 1 := min_le_right _ _
  have hsub : Icc (0 : ℝ) delta ⊆ Icc (0 : ℝ) 1 :=
    fun t ht => ⟨ht.1,ht.2.trans hdle⟩
  have hslit : ∀ t ∈ Icc (0 : ℝ) delta, H t ∈ Complex.slitPlane := by
    intro t ht
    have hdist : dist t (0 : ℝ) < r := by
      rw [Real.dist_eq,sub_zero,abs_of_nonneg ht.1]
      exact (ht.2.trans (min_le_left (r/2) 1)).trans_lt (half_lt_self hr)
    have hnear : ‖H t-1‖ < 1 := by
      simpa only [dist_eq_norm,hH0] using hclose (hsub ht) hdist
    have hs := Complex.mem_slitPlane_of_norm_lt_one hnear
    have he : (1 : ℂ)+(H t-1) = H t := by ring
    rw [he] at hs
    exact hs
  refine ⟨delta,hdelta,hdle,hslit,?_,?_,?_⟩
  · exact continuousOn_const.mul ((hH.mono hsub).clog hslit)
  · simp only [div_self hG0,Complex.log_one,mul_zero]
  · intro t ht
    have ht01 : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1,ht.2.trans_le hdle⟩
    have htcc : t ∈ Icc (0 : ℝ) delta := ⟨ht.1.le,ht.2.le⟩
    have hHne : H t ≠ 0 := Complex.slitPlane_ne_zero (hslit t htcc)
    have hGt : G t ≠ 0 := by
      intro hzero
      apply hHne
      change G t/G 0 = 0
      rw [hzero,zero_div]
    have hdH : HasDerivAt H ((Complex.I*f t*G t)/G 0) t :=
      (hder t ht01).div_const (G 0)
    apply ((hdH.clog_real (hslit t htcc)).const_mul (-Complex.I)).congr_deriv
    change -Complex.I * (((Complex.I*f t*G t)/G 0)/(G t/G 0)) = f t
    have hI : (-Complex.I)*Complex.I = (1 : ℂ) := by
      rw [neg_mul,Complex.I_mul_I]
      ring
    calc
      _ = ((-Complex.I)*Complex.I)*f t := by
        field_simp [hG0,hGt]
      _ = f t := by rw [hI,one_mul]


/-- The compact FTC identity used for the additive endpoint limit. Integrability
is supplied only on compact truncations ending at `1`; none at `0` is assumed. -/
theorem gk16_local_primitive_tail_identity38
    (L f : ℝ → ℂ) (delta rho eps : ℝ)
    (hdelta : delta ≤ 1)
    (hrho : 0 < rho) (hrhodelta : rho < delta)
    (heps : 0 < eps) (hepsrho : eps < rho)
    (hL : ContinuousOn L (Icc (0 : ℝ) delta))
    (hder : ∀ t ∈ Ioo (0 : ℝ) delta, HasDerivAt L (f t) t)
    (hint : ∀ e : ℝ, 0 < e → e < 1 → IntervalIntegrable f volume e 1) :
    (∫ t in eps..1, f t) =
      (L rho + ∫ t in rho..1, f t) - L eps := by
  have hrho1 : rho < 1 := hrhodelta.trans_le hdelta
  have heps1 : eps < 1 := hepsrho.trans hrho1
  have hrhoint : IntervalIntegrable f volume rho 1 := hint rho hrho hrho1
  have hepsint : IntervalIntegrable f volume eps 1 := hint eps heps heps1
  have hepsrhoInt : IntervalIntegrable f volume eps rho :=
    hepsint.trans hrhoint.symm
  have hcompact : (∫ t in eps..rho, f t) = L rho - L eps := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hepsrho.le
    · exact hL.mono (fun t ht =>
        ⟨heps.le.trans ht.1, ht.2.trans hrhodelta.le⟩)
    · intro t ht
      exact hder t ⟨heps.trans ht.1, ht.2.trans hrhodelta⟩
    · exact hepsrhoInt
  calc
    (∫ t in eps..1, f t) =
        (∫ t in eps..rho, f t) + ∫ t in rho..1, f t :=
      (intervalIntegral.integral_add_adjacent_intervals hepsrhoInt hrhoint).symm
    _ = (L rho + ∫ t in rho..1, f t) - L eps := by
      rw [hcompact]
      ring

/-- A continuous local additive primitive, with no derivative assumed at the
singular endpoint, gives the genuine one-sided additive improper tail limit. -/
theorem gk16_local_primitive_left_tail38
    (L f : ℝ → ℂ) (delta : ℝ)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hL : ContinuousOn L (Icc (0 : ℝ) delta)) (hL0 : L 0 = 0)
    (hder : ∀ t ∈ Ioo (0 : ℝ) delta, HasDerivAt L (f t) t)
    (hint : ∀ e : ℝ, 0 < e → e < 1 → IntervalIntegrable f volume e 1) :
    Tendsto (fun eps : ℝ => ∫ t in eps..1, f t)
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds (L (delta/2) + ∫ t in (delta/2)..1, f t)) := by
  let rho : ℝ := delta/2
  have hrho : 0 < rho := half_pos hdelta
  have hrhodelta : rho < delta := half_lt_self hdelta
  have hinput : Tendsto (fun eps : ℝ => eps)
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhdsWithin 0 (Icc (0 : ℝ) delta)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT hrho] with eps heps
      exact ⟨heps.1.le, heps.2.le.trans hrhodelta.le⟩
  have hLlim : Tendsto L (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds (0 : ℂ)) := by
    have h := (hL 0 ⟨le_rfl, hdelta.le⟩).tendsto.comp hinput
    simpa only [hL0, Function.comp_def] using h
  have hlim : Tendsto
      (fun eps : ℝ => (L rho + ∫ t in rho..1, f t) - L eps)
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds (L rho + ∫ t in rho..1, f t)) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub hLlim : Tendsto
        (fun eps : ℝ => (L rho + ∫ t in rho..1, f t) - L eps)
        (nhdsWithin 0 (Ioi (0 : ℝ)))
        (nhds ((L rho + ∫ t in rho..1, f t) - 0)))
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT hrho] with eps heps
  exact (gk16_local_primitive_tail_identity38 L f delta rho eps
    hdelta1 hrho hrhodelta heps.1 heps.2 hL hder hint).symm

/-- A nonzero continuous endpoint of the actual scalar ODE model earns a finite
additive improper tail limit. This is stronger than convergence of its exponential. -/
theorem gk16_local_log_left_tail38
    (G f : ℝ → ℂ)
    (hG : ContinuousOn G (Icc (0 : ℝ) 1))
    (hG0 : G 0 ≠ 0)
    (hder : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt G (Complex.I*f t*G t) t)
    (hint : ∀ e : ℝ, 0 < e → e < 1 → IntervalIntegrable f volume e 1) :
    ∃ eta : ℂ, Tendsto (fun eps : ℝ => ∫ t in eps..1, f t)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds eta) := by
  obtain ⟨delta, hdelta, hdelta1, _hslit, hL, hL0, hdL⟩ :=
    gk16_local_log_left_primitive38 G f hG hG0 hder
  let L : ℝ → ℂ := fun t => -Complex.I * Complex.log (G t/G 0)
  exact ⟨L (delta/2) + ∫ t in (delta/2)..1, f t,
    gk16_local_primitive_left_tail38 L f delta hdelta hdelta1 hL hL0 hdL hint⟩

/-- Reversing the unit parameter reverses the density in the actual scalar ODE.
Only ordinary derivatives at interior parameters are used. -/
theorem gk16_logarithmic_ode_reverse38
    (G f : ℝ → ℂ)
    (hG : ContinuousOn G (Icc (0 : ℝ) 1))
    (hG1 : G 1 ≠ 0)
    (hder : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt G (Complex.I * f t * G t) t) :
    ContinuousOn (fun t : ℝ => G (1 - t)) (Icc (0 : ℝ) 1) ∧
      G (1 - (0 : ℝ)) ≠ 0 ∧
      ∀ t ∈ Ioo (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => G (1 - t))
          (Complex.I * (-f (1 - t)) * G (1 - t)) t := by
  refine ⟨?_, ?_, ?_⟩
  · apply hG.comp (continuous_const.sub continuous_id).continuousOn
    intro t ht
    change 1-t ∈ Icc (0 : ℝ) 1
    constructor <;> linarith [ht.1, ht.2]
  · simpa only [sub_zero] using hG1
  · intro t ht
    have ht' : 1 - t ∈ Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2]
    simpa only [mul_neg, neg_mul] using
      (HasDerivAt.comp_const_sub (1 : ℝ) t (hder (1 - t) ht'))

/-- Reflection exactly preserves compact interval integrability, including the
sign of the reversed ODE density. -/
theorem gk16_reversed_density_intervalIntegrable38 (f : ℝ → ℂ) (eps : ℝ) :
    IntervalIntegrable (fun u : ℝ => -f (1 - u)) volume eps 1 ↔
      IntervalIntegrable f volume 0 (1 - eps) := by
  have hflip (t : ℝ) : 1 - (1 - t) = t := by ring
  constructor
  · intro h
    have hpos : IntervalIntegrable (fun u : ℝ => f (1 - u)) volume eps 1 := by
      have hneg : IntervalIntegrable (fun u : ℝ => -(-f (1-u))) volume eps 1 := h.neg
      simpa only [neg_neg] using hneg
    have hback : IntervalIntegrable f volume (1 - eps) 0 := by
      simpa only [hflip, sub_self] using hpos.comp_sub_left (1 : ℝ)
    exact hback.symm
  · intro h
    have hpos : IntervalIntegrable (fun u : ℝ => f (1 - u)) volume 1 eps := by
      simpa only [sub_zero, hflip] using h.comp_sub_left (1 : ℝ)
    exact hpos.symm.neg

/-- This exact change of variables concerns the actual additive integrals.
It requires no exponential limit and is valid for every real truncation. -/
theorem gk16_reversed_density_integral38 (f : ℝ → ℂ) (eps : ℝ) :
    (∫ u in eps..1, -f (1 - u)) = -(∫ t in 0..(1 - eps), f t) := by
  have hreflect : (∫ u in eps..1, f (1 - u)) = ∫ t in 0..(1 - eps), f t := by
    simpa only [sub_self] using
      (intervalIntegral.integral_comp_sub_left (a := eps) (b := 1) f (1 : ℝ))
  rw [intervalIntegral.integral_neg, hreflect]

/-- A genuine additive left-tail limit of the reversed density gives the
right-tail limit of the original density, with the required sign. -/
theorem gk16_reversed_density_tendsto38 (f : ℝ → ℂ) (eta : ℂ)
    (h : Tendsto (fun eps : ℝ => ∫ u in eps..1, -f (1 - u))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds eta)) :
    Tendsto (fun eps : ℝ => ∫ t in 0..(1 - eps), f t)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds (-eta)) := by
  simpa only [gk16_reversed_density_integral38, neg_neg] using h.neg

/-- A continuous nonzero endpoint model, its actual interior logarithmic ODE,
and compact integrability earn the additive improper right-tail limit.
No derivative or integrand continuity is demanded at either endpoint. -/
theorem gk16_local_log_right_tail38
    (G f : ℝ → ℂ)
    (hG : ContinuousOn G (Icc (0 : ℝ) 1))
    (hG1 : G 1 ≠ 0)
    (hder : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt G (Complex.I * f t * G t) t)
    (hint : ∀ e : ℝ, 0 < e → e < 1 →
      IntervalIntegrable f volume 0 (1 - e)) :
    ∃ eta : ℂ, Tendsto (fun eps : ℝ => ∫ t in 0..(1 - eps), f t)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds eta) := by
  rcases gk16_logarithmic_ode_reverse38 G f hG hG1 hder with
    ⟨hGr, hGr0, hGrd⟩
  have hintR : ∀ e : ℝ, 0 < e → e < 1 →
      IntervalIntegrable (fun u : ℝ => -f (1 - u)) volume e 1 := by
    intro e he he1
    exact (gk16_reversed_density_intervalIntegrable38 f e).2 (hint e he he1)
  obtain ⟨eta, heta⟩ := gk16_local_log_left_tail38
    (fun t : ℝ => G (1 - t)) (fun t : ℝ => -f (1 - t)) hGr hGr0 hGrd hintR
  exact ⟨-eta, gk16_reversed_density_tendsto38 f eta heta⟩

/-- Compact transport along an actual arc; ordinary derivatives are used only
inside the chosen interval. -/
theorem gk16_diagonal_arc_transport38
    (n : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (phi : GKPotential38) (s : Lib.L2Seq)
    (hnum : p6PsiNumerator38 n (F n) phi.1 = p2FullNumerator38 n s)
    (hperiod : abelianPeriod38 n phi.1
      (p6PsiNumerator38 n (F n) phi.1) = 2*(Real.pi : ℂ))
    (eps : ℂ) (heps : eps^2 = 1) (arc : GKRootedC1Arc38 phi n)
    (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1)
    (hi : IntervalIntegrable (GKRootedArcIntegrand38 n n F phi arc) volume u v) :
    let R := gk16OwnCorrectionCoefficient38 phi.1 n s
      (discC phi.1 n) (discR phi.1 n)
    gk16ArcExponentialModel38 phi n eps R arc v =
      gk16ArcExponentialModel38 phi n eps R arc u *
        Complex.exp ((-eps*Complex.I)*
          (∫ t in u..v, GKRootedArcIntegrand38 n n F phi arc t)) := by
  let R := gk16OwnCorrectionCoefficient38 phi.1 n s
    (discC phi.1 n) (discR phi.1 n)
  have hR := gk16_own_correction_coefficient38 phi.1 phi.2
    (discC phi.1) (discR phi.1) (isolating_family38 phi.1 phi.2) n s
    (by simpa only [hnum] using hperiod)
  exact gk16_compact_exponential_transport38 u v huv (-eps*Complex.I)
    (GKRootedArcIntegrand38 n n F phi arc)
    (gk16ArcExponentialModel38 phi n eps R arc)
    ((gk16_arc_model_continuous38 phi n eps R hR.1 arc).mono
      (fun t ht => ⟨hu.trans ht.1,ht.2.trans hv⟩)) hi
    ((gk16_arc_integrand_continuous38 n F phi arc).mono
      (fun t ht => ⟨hu.trans_lt ht.1,ht.2.trans_le hv⟩))
    (fun t ht => gk16_diagonal_arc_model_hasDerivAt38 n F phi s hnum hperiod
      eps heps arc t ⟨hu.trans_lt ht.1,ht.2.trans_le hv⟩)

private theorem gk16_middle_model_transport38
    (n : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (phi : GKPotential38) (eps : ℂ) (R : ℂ → ℂ)
    (arcs : List (GKRootedC1Arc38 phi n)) :
    ∀ (a b : GKRootedC1Arc38 phi n),
      GKRootedArcChain38 phi n (a :: (arcs ++ [b])) →
      (∀ d ∈ arcs, gk16ArcExponentialModel38 phi n eps R d 1 =
        gk16ArcExponentialModel38 phi n eps R d 0 *
          Complex.exp ((-eps*Complex.I)*
            (∫ t in (0 : ℝ)..1, GKRootedArcIntegrand38 n n F phi d t))) →
      gk16ArcExponentialModel38 phi n eps R b 0 =
        gk16ArcExponentialModel38 phi n eps R a 1 *
          Complex.exp ((-eps*Complex.I)*GKPathMiddleIntegral38 n n F phi arcs) := by
  induction arcs with
  | nil =>
      intro a b hc hi
      simpa only [GKPathMiddleIntegral38,mul_zero,Complex.exp_zero,mul_one] using
        (gk16_arc_model_join38 phi n eps R a b hc.1).symm
  | cons d tail ih =>
      intro a b hc hi
      have hjoin := gk16_arc_model_join38 phi n eps R a d hc.1
      have hd := hi d List.mem_cons_self
      have htail := ih d b hc.2 (fun e he => hi e (List.mem_cons_of_mem _ he))
      rw [htail,hd,← hjoin,GKPathMiddleIntegral38,mul_assoc,← Complex.exp_add]
      congr 2
      ring

/-- Exact transport for the literal first/middle/last truncation, before
any endpoint limit is taken. -/
theorem gk16_diagonal_truncated_transport38
    (n : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (phi : GKPotential38) (s : Lib.L2Seq)
    (hnum : p6PsiNumerator38 n (F n) phi.1 = p2FullNumerator38 n s)
    (hperiod : abelianPeriod38 n phi.1
      (p6PsiNumerator38 n (F n) phi.1) = 2*(Real.pi : ℂ))
    (eps : ℂ) (heps : eps^2 = 1) (p : GKRootedPiecewisePath38 phi n)
    (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (hsum : u+v < 1) :
    let R := gk16OwnCorrectionCoefficient38 phi.1 n s
      (discC phi.1 n) (discR phi.1 n)
    gk16ArcExponentialModel38 phi n eps R (GKPathLast38 p) (1-v) =
      gk16ArcExponentialModel38 phi n eps R (GKPathFirst38 p) u *
        Complex.exp ((-eps*Complex.I)*GKPathTruncatedIntegral38 n n F phi p u v) := by
  let R := gk16OwnCorrectionCoefficient38 phi.1 n s
    (discC phi.1 n) (discR phi.1 n)
  obtain ⟨hif,him,hil⟩ := rawBetaPathCompactIntegrable38 n n F phi p u v hu hv hsum
  have hf := gk16_diagonal_arc_transport38 n F phi s hnum hperiod eps heps
    (GKPathFirst38 p) u 1 hu.le (by linarith) le_rfl hif
  have hl := gk16_diagonal_arc_transport38 n F phi s hnum hperiod eps heps
    (GKPathLast38 p) 0 (1-v) le_rfl (by linarith) (by linarith) hil
  have hm := gk16_middle_model_transport38 n F phi eps R (GKPathMiddle38 p)
    (GKPathFirst38 p) (GKPathLast38 p) p.2.2.1
    (fun d hd => gk16_diagonal_arc_transport38 n F phi s hnum hperiod eps heps
      d 0 1 le_rfl zero_le_one le_rfl (him d hd))
  change gk16ArcExponentialModel38 phi n eps R (GKPathLast38 p) (1-v) = _
  rw [hl,hm,hf,GKPathTruncatedIntegral38,mul_assoc,mul_assoc,
    ← Complex.exp_add,← Complex.exp_add]
  congr 2
  ring

/-- Every supplied actual noncollapsed diagonal rooted path has a genuine
additive joint improper integral and both signed gap-scaled exponentials. -/
theorem gk16_diagonal_original_path_exponential38
    (n : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (phi : GKPotential38) (s : Lib.L2Seq)
    (hnum : p6PsiNumerator38 n (F n) phi.1 = p2FullNumerator38 n s)
    (hperiod : abelianPeriod38 n phi.1
      (p6PsiNumerator38 n (F n) phi.1) = 2*(Real.pi : ℂ))
    (hgap : lamMinus phi.1 n ≠ lamPlus phi.1 n) :
    let a := lamMinus phi.1 n
    let b := lamPlus phi.1 n
    let mu := muSeq phi.1 n
    let R := gk16OwnCorrectionCoefficient38 phi.1 n s
      (discC phi.1 n) (discR phi.1 n)
    let H := gk16TerminalRoot38 n phi.1
    ∀ p : GKRootedPiecewisePath38 phi n, ∃ eta : ℂ,
      HasGKImproperPathIntegral38 n n F phi p eta ∧
      (2*((a+b)/2-mu)+2*H)*Complex.exp (-H*R mu) =
        (b-a)*Complex.exp (Complex.I*eta) ∧
      (2*((a+b)/2-mu)-2*H)*Complex.exp (H*R mu) =
        (b-a)*Complex.exp (-Complex.I*eta) := by
  dsimp only
  intro p
  let R := gk16OwnCorrectionCoefficient38 phi.1 n s
    (discC phi.1 n) (discR phi.1 n)
  have hR := gk16_own_correction_coefficient38 phi.1 phi.2
    (discC phi.1) (discR phi.1) (isolating_family38 phi.1 phi.2) n s
    (by simpa only [hnum] using hperiod)
  have hode : ∀ (arc : GKRootedC1Arc38 phi n) (t : ℝ), t ∈ Ioo (0 : ℝ) 1 →
      HasDerivAt (gk16ArcExponentialModel38 phi n (-1) R arc)
        (Complex.I*GKRootedArcIntegrand38 n n F phi arc t *
          gk16ArcExponentialModel38 phi n (-1) R arc t) t := by
    intro arc t ht
    simpa only [neg_neg,one_mul] using
      gk16_diagonal_arc_model_hasDerivAt38 n F phi s hnum hperiod
        (-1) (by norm_num) arc t ht
  have hfirstInt : ∀ e : ℝ, 0 < e → e < 1 →
      IntervalIntegrable (GKRootedArcIntegrand38 n n F phi (GKPathFirst38 p))
        volume e 1 := by
    intro e he he1
    exact (rawBetaPathCompactIntegrable38 n n F phi p e ((1-e)/2)
      he (by linarith) (by linarith)).1
  have hlastInt : ∀ e : ℝ, 0 < e → e < 1 →
      IntervalIntegrable (GKRootedArcIntegrand38 n n F phi (GKPathLast38 p))
        volume 0 (1-e) := by
    intro e he he1
    exact (rawBetaPathCompactIntegrable38 n n F phi p ((1-e)/2) e
      (by linarith) he (by linarith)).2.2
  obtain ⟨etaFirst,hlimFirst⟩ := gk16_local_log_left_tail38
    (gk16ArcExponentialModel38 phi n (-1) R (GKPathFirst38 p))
    (GKRootedArcIntegrand38 n n F phi (GKPathFirst38 p))
    (gk16_arc_model_continuous38 phi n (-1) R hR.1 (GKPathFirst38 p))
    (gk16_arc_model_ne_zero38 phi n R hgap (GKPathFirst38 p) 0
      ⟨le_rfl,zero_le_one⟩).1
    (hode (GKPathFirst38 p)) hfirstInt
  obtain ⟨etaLast,hlimLast⟩ := gk16_local_log_right_tail38
    (gk16ArcExponentialModel38 phi n (-1) R (GKPathLast38 p))
    (GKRootedArcIntegrand38 n n F phi (GKPathLast38 p))
    (gk16_arc_model_continuous38 phi n (-1) R hR.1 (GKPathLast38 p))
    (gk16_arc_model_ne_zero38 phi n R hgap (GKPathLast38 p) 1
      ⟨zero_le_one,le_rfl⟩).1
    (hode (GKPathLast38 p)) hlastInt
  let eta := etaFirst+GKPathMiddleIntegral38 n n F phi (GKPathMiddle38 p)+etaLast
  let L := nhdsWithin ((0 : ℝ),(0 : ℝ))
    {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1+q.2 < 1}
  have hfst : Tendsto (fun q : ℝ × ℝ => q.1) L (nhdsWithin 0 (Ioi (0 : ℝ))) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact hq.1
  have hsnd : Tendsto (fun q : ℝ × ℝ => q.2) L (nhdsWithin 0 (Ioi (0 : ℝ))) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact hq.2.1
  have hIntegral : HasGKImproperPathIntegral38 n n F phi p eta := by
    refine ⟨rawBetaPathCompactIntegrable38 n n F phi p,?_⟩
    exact ((hlimFirst.comp hfst).add tendsto_const_nhds).add (hlimLast.comp hsnd)
  have hfstcc : Tendsto (fun q : ℝ × ℝ => q.1) L
      (nhdsWithin 0 (Icc (0 : ℝ) 1)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact ⟨hq.1.le,by linarith [hq.2.1,hq.2.2]⟩
  have hlastcc : Tendsto (fun q : ℝ × ℝ => 1-q.2) L
      (nhdsWithin 1 (Icc (0 : ℝ) 1)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hq : Tendsto (fun q : ℝ × ℝ => q.2) L (nhds (0 : ℝ)) :=
        continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      simpa only [sub_zero] using (tendsto_const_nhds.sub hq :
        Tendsto (fun q : ℝ × ℝ => (1 : ℝ)-q.2) L (nhds (1-0)))
    · filter_upwards [self_mem_nhdsWithin] with q hq
      constructor <;> linarith [hq.1,hq.2.1,hq.2.2]
  have hmodel : ∀ eps : ℂ, eps^2 = 1 →
      gk16ArcExponentialModel38 phi n eps R (GKPathLast38 p) 1 =
        (lamPlus phi.1 n-lamMinus phi.1 n)*Complex.exp ((-eps*Complex.I)*eta) := by
    intro eps heps
    letI : NeBot L := rawBetaImproperApproachNeBot38
    have hgfirst := (gk16_arc_model_continuous38 phi n eps R hR.1 (GKPathFirst38 p)
      0 ⟨le_rfl,zero_le_one⟩).tendsto.comp hfstcc
    have hglast := (gk16_arc_model_continuous38 phi n eps R hR.1 (GKPathLast38 p)
      1 ⟨zero_le_one,le_rfl⟩).tendsto.comp hlastcc
    rw [(gk16_path_model_endpoints38 phi n eps R p).1] at hgfirst
    have hscaled : Tendsto
        (fun q : ℝ × ℝ => (-eps*Complex.I)*GKPathTruncatedIntegral38 n n F phi p q.1 q.2)
        L (nhds ((-eps*Complex.I)*eta)) := tendsto_const_nhds.mul hIntegral.2
    have hexp := hgfirst.mul hscaled.cexp
    apply tendsto_nhds_unique hglast
    apply hexp.congr'
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact (gk16_diagonal_truncated_transport38 n F phi s hnum hperiod
      eps heps p q.1 q.2 hq.1 hq.2.1 hq.2.2).symm
  refine ⟨eta,hIntegral,?_,?_⟩
  · have hplus := hmodel (-1) (by norm_num)
    rw [(gk16_path_model_endpoints38 phi n (-1) R p).2] at hplus
    simpa only [neg_neg,one_mul,mul_neg_one,neg_mul,sub_neg_eq_add,neg_one_mul] using hplus
  · have hminus := hmodel 1 (by norm_num)
    rw [(gk16_path_model_endpoints38 phi n 1 R p).2] at hminus
    simpa only [one_mul,mul_one,neg_one_mul] using hminus

end
end NlsGge.GK38
