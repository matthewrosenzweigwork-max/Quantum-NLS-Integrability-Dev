import NlsGge.Atomic.LIB.LIB026
import NlsGge.Atomic.IntervalZS
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.ContinuousMap.Compact

/-!
# LIB-031: the epsilon H1-to-sup bound on the actual interval pair

The scalar squared estimate applies the proved AC averaging inequality to
`conj(F) * F`, then uses genuine L2 Holder bounds. Summing the two components
and applying Euclidean Cauchy--Schwarz gives the actual paired estimate.
An elementary Young inequality yields the explicit uniform constant
`Cε = 1 + ε⁻¹`. The supremum is the continuous-map norm of the canonical
representative with its Euclidean pair norm. No boundary condition is imposed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff
namespace NlsGge.Atomic.LIB031
open NlsGge.Schur NlsGge.Atomic.Interval NlsGge.Atomic.LIB026

abbrev unitMeasure : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)

def normLp (f : SourceIntervalL2) : Lp ℝ 2 unitMeasure :=
  (Lp.memLp f).norm.toLp (fun x => ‖f x‖)

lemma normLp_norm (f : SourceIntervalL2) : ‖normLp f‖ = ‖f‖ := by
  rw [normLp, Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable f), Lp.norm_def]

lemma normLp_ae (f : SourceIntervalL2) :
    (normLp f : ℝ → ℝ) =ᵐ[unitMeasure] fun x => ‖f x‖ :=
  (Lp.memLp f).norm.coeFn_toLp

lemma integral_norm_mul_norm (f g : SourceIntervalL2) :
    (∫ x in (0 : ℝ)..1, ‖f x‖ * ‖g x‖) = inner ℝ (normLp f) (normLp g) := by
  rw [intervalIntegral.integral_of_le zero_le_one, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [normLp_ae f, normLp_ae g] with x hx hy
  simp only [RCLike.inner_apply, conj_trivial]
  rw [hx, hy]
  ring

lemma integral_norm_mul_norm_le (f g : SourceIntervalL2) :
    (∫ x in (0 : ℝ)..1, ‖f x‖ * ‖g x‖) ≤ ‖f‖ * ‖g‖ := by
  rw [integral_norm_mul_norm, ← normLp_norm f, ← normLp_norm g]
  exact real_inner_le_norm _ _

lemma integral_norm_sq (f : SourceIntervalL2) :
    (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) = ‖f‖ ^ 2 := by
  simpa only [pow_two, real_inner_self_eq_norm_sq, normLp_norm] using
    integral_norm_mul_norm f f


set_option backward.isDefEq.respectTransparency false in
/-- The source averaging estimate applied to the squared absolute value. -/
theorem representative_norm_sq_le (f : H1) (x : Icc (0 : ℝ) 1) :
    ‖representative f x‖ ^ 2 ≤ ‖f.value‖ ^ 2 + 2 * ‖f.value‖ * ‖f.derivative‖ := by
  let F : ℝ → ℂ := IccExtend zero_le_one (representative f)
  let D : ℝ → ℂ := fun t => star (f.derivative t) * F t + star (F t) * f.derivative t
  have hF := (representative_spec f).1
  have hstar : AbsolutelyContinuousOnInterval (fun t => star (F t)) 0 1 := by
    simpa only [Function.comp_def] using!
      Complex.conjLIE.lipschitz.comp_absolutelyContinuousOnInterval hF
  have hprod : AbsolutelyContinuousOnInterval (fun t => star (F t) * F t) 0 1 := by
    simpa only [Pi.smul_apply, smul_eq_mul] using! hstar.smul hF
  have hi1 : IntervalIntegrable (fun t => star (f.derivative t) * F t) volume 0 1 :=
    (intervalIntegrable_iff.mpr
      (Complex.conjCLE.toContinuousLinearMap.integrable_comp
        (intervalIntegrable_L2 f.derivative).def')).mul_continuousOn hF.continuousOn
  have hi2 : IntervalIntegrable (fun t => star (F t) * f.derivative t) volume 0 1 :=
    (intervalIntegrable_L2 f.derivative).continuousOn_mul hstar.continuousOn
  have hD : IntervalIntegrable D volume 0 1 := hi1.add hi2
  have hd : ∀ᵐ t ∂volume, t ∈ uIcc (0 : ℝ) 1 →
      HasDerivAt (fun s => star (F s) * F s) (D t) t := by
    filter_upwards [(representative_spec f).2] with t ht hmem
    exact (ht hmem).star.mul (ht hmem)
  have hbound := ac_norm_le_integral_norm_add_derivative hprod hD hd x.property
  have heq : (∫ t in (0 : ℝ)..1, ‖star (F t) * F t‖) = ‖f.value‖ ^ 2 := by
    rw [← integral_norm_sq f.value]
    apply intervalIntegral.integral_congr_ae_restrict
    have hae := representative_ae f
    simp only [uIoc_of_le zero_le_one]
    filter_upwards [hae] with t ht
    rw [norm_mul, norm_star, show F t = f.value t from ht]
    ring
  have hip : IntervalIntegrable (fun t => ‖f.derivative t‖ * ‖f.value t‖) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      ((Lp.memLp f.derivative).norm.integrable_mul (Lp.memLp f.value).norm)
  have hDle : (∫ t in (0 : ℝ)..1, ‖D t‖) ≤
      ∫ t in (0 : ℝ)..1, 2 * (‖f.derivative t‖ * ‖f.value t‖) := by
    rw [intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_of_le zero_le_one]
    apply integral_mono_ae
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hD.norm)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp (hip.const_mul 2))
    filter_upwards [representative_ae f] with t ht
    change ‖star (f.derivative t) * F t + star (F t) * f.derivative t‖ ≤ _
    calc
      _ ≤ ‖star (f.derivative t) * F t‖ + ‖star (F t) * f.derivative t‖ := norm_add_le _ _
      _ = 2 * (‖f.derivative t‖ * ‖f.value t‖) := by
        rw [norm_mul, norm_mul, norm_star, norm_star, show F t = f.value t from ht]
        ring
  have hHolder := integral_norm_mul_norm_le f.derivative f.value
  rw [intervalIntegral.integral_const_mul] at hDle
  have hleft : ‖star (F x) * F x‖ = ‖representative f x‖ ^ 2 := by
    rw [norm_mul, norm_star]
    simp only [F, IccExtend_val]
    ring
  rw [hleft, heq] at hbound
  nlinarith


abbrev PointPair := PiLp 2 (fun _ : Bool => ℂ)

/-- Canonical continuous representative with the source Euclidean pair norm. -/
def pairRepresentative (f : H1Pair) : C(Icc (0 : ℝ) 1, PointPair) :=
  ⟨fun x => WithLp.toLp 2 (fun b => representative (f b) x),
    (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun b => (representative (f b)).continuous))⟩

/-- The actual paired L2 weak derivative. -/
def pairDerivative (f : H1Pair) : SourcePairL2 :=
  WithLp.toLp 2 (fun b => (f b).derivative)

lemma pairRepresentative_norm_sq (f : H1Pair) (x : Icc (0 : ℝ) 1) :
    ‖pairRepresentative f x‖ ^ 2 =
      ‖representative (f true) x‖ ^ 2 + ‖representative (f false) x‖ ^ 2 := by
  simpa only [Fintype.sum_bool, pairRepresentative, h1PairValue, pairDerivative] using! PiLp.norm_sq_eq_of_L2 _ (pairRepresentative f x)

lemma pairValue_norm_sq (f : H1Pair) :
    ‖h1PairValue f‖ ^ 2 = ‖(f true).value‖ ^ 2 + ‖(f false).value‖ ^ 2 := by
  simpa only [Fintype.sum_bool, pairRepresentative, h1PairValue, pairDerivative] using! PiLp.norm_sq_eq_of_L2 _ (h1PairValue f)

lemma pairDerivative_norm_sq (f : H1Pair) :
    ‖pairDerivative f‖ ^ 2 = ‖(f true).derivative‖ ^ 2 + ‖(f false).derivative‖ ^ 2 := by
  simpa only [Fintype.sum_bool, pairRepresentative, h1PairValue, pairDerivative] using! PiLp.norm_sq_eq_of_L2 _ (pairDerivative f)

lemma pair_component_norm_products_le (f : H1Pair) :
    ‖(f true).value‖ * ‖(f true).derivative‖ +
      ‖(f false).value‖ * ‖(f false).derivative‖ ≤ ‖h1PairValue f‖ * ‖pairDerivative f‖ := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  have hprod : (‖h1PairValue f‖ * ‖pairDerivative f‖) ^ 2 =
      (‖(f true).value‖ ^ 2 + ‖(f false).value‖ ^ 2) *
      (‖(f true).derivative‖ ^ 2 + ‖(f false).derivative‖ ^ 2) := by
    rw [mul_pow, pairValue_norm_sq, pairDerivative_norm_sq]
  nlinarith only [hprod, sq_nonneg
    (‖(f true).value‖ * ‖(f false).derivative‖ -
      ‖(f false).value‖ * ‖(f true).derivative‖)]

/-- The source squared-norm estimate on the actual paired representative. -/
theorem pairRepresentative_norm_sq_le (f : H1Pair) (x : Icc (0 : ℝ) 1) :
    ‖pairRepresentative f x‖ ^ 2 ≤
      ‖h1PairValue f‖ ^ 2 + 2 * ‖h1PairValue f‖ * ‖pairDerivative f‖ := by
  rw [pairRepresentative_norm_sq, pairValue_norm_sq]
  have ht := representative_norm_sq_le (f true) x
  have hf := representative_norm_sq_le (f false) x
  have hc := pair_component_norm_products_le f
  nlinarith

lemma epsilon_of_sq_bound {a b d ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hε : 0 < ε) (hsq : a ^ 2 ≤ b ^ 2 + 2 * b * d) :
    a ≤ ε * d + (1 + ε⁻¹) * b := by
  let C := 1 + ε⁻¹
  have hC : 1 ≤ C := by dsimp [C]; linarith [inv_nonneg.mpr hε.le]
  have hεC : 1 ≤ ε * C := by
    dsimp [C]
    rw [mul_add, mul_inv_cancel₀ hε.ne']
    linarith
  have hbC : b ≤ C * b := by nlinarith [mul_nonneg (sub_nonneg.mpr hC) hb]
  have hbb : b ^ 2 ≤ (C * b) ^ 2 := (sq_le_sq₀ hb (by positivity)).mpr hbC
  have hcross : 2 * b * d ≤ 2 * (ε * d) * (C * b) := by
    have h := mul_le_mul_of_nonneg_left hεC (show 0 ≤ 2 * (b * d) by positivity)
    nlinarith only [h]
  have hfinal : a ^ 2 ≤ (ε * d + C * b) ^ 2 := by
    nlinarith [sq_nonneg (ε * d)]
  exact (sq_le_sq₀ ha (by positivity)).mp hfinal

/-- Boundary-independent epsilon H1-to-sup estimate with an explicit valid constant. -/
theorem pair_sup_le_epsilon_deriv {ε : ℝ} (hε : 0 < ε) (f : H1Pair) :
    ‖pairRepresentative f‖ ≤ ε * ‖pairDerivative f‖ + (1 + ε⁻¹) * ‖h1PairValue f‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  exact epsilon_of_sq_bound (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hε
    (pairRepresentative_norm_sq_le f x)

/-- The requested quantifier order, uniform over all actual interval H1 pairs. -/
theorem interval_sup_le_epsilon_deriv {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : H1Pair,
      ‖pairRepresentative f‖ ≤ ε * ‖pairDerivative f‖ + C * ‖h1PairValue f‖ :=
  ⟨1 + ε⁻¹, by positivity, fun f => pair_sup_le_epsilon_deriv hε f⟩

end NlsGge.Atomic.LIB031
