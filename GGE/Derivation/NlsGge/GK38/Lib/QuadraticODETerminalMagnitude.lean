import NlsGge.GK38.AngleSegmentNumerator
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Ordinary scalar quadratic-ODE magnitude estimate on a filled convex domain.
There is no source-beta value or spectral family in this module. -/

set_option autoImplicit false
open Set Metric MeasureTheory
namespace NlsGge.GK38.Lib
noncomputable section

private def magnitudePath38 (a μ : ℂ) (t : ℝ) : ℂ := a + (t : ℂ) * (μ - a)

private def magnitudeFarRoot38 (a b μ : ℂ) (t : ℝ) : ℂ :=
  Complex.sqrt ((magnitudePath38 a μ t - b) / (a - b))

private def magnitudePrimitive38 (a b μ : ℂ) (T : ℂ → ℂ) (t : ℝ) : ℂ :=
  (Real.sqrt t : ℂ) * magnitudeFarRoot38 a b μ t * T (magnitudePath38 a μ t)

private def magnitudeDensity38 (a b μ σ : ℂ) (ζ : ℂ → ℂ) (t : ℝ) : ℂ :=
  (σ - magnitudePath38 a μ t) * ζ (magnitudePath38 a μ t) /
    ((a - b) * magnitudeFarRoot38 a b μ t * (Real.sqrt t : ℂ))

private theorem magnitudePath_mem38 (U : Set ℂ) (hconv : Convex ℝ U)
    (a μ : ℂ) (ha : a ∈ U) (hμ : μ ∈ U) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    magnitudePath38 a μ t ∈ U := by
  apply (hconv.segment_subset ha hμ)
  exact ⟨1-t, t, by linarith [ht.2], ht.1, by ring,
    by simp only [magnitudePath38, Complex.real_smul]; push_cast; ring⟩

private theorem magnitudeSqrt_sq38 (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  unfold Complex.sqrt
  exact Complex.cpow_nat_inv_pow z (n := 2) (by norm_num)

private theorem magnitudeFarRoot_sq38 (a b μ : ℂ) (t : ℝ) :
    magnitudeFarRoot38 a b μ t ^ 2 = (magnitudePath38 a μ t - b) / (a - b) :=
  magnitudeSqrt_sq38 _

private theorem magnitudeFar_re38 (a b μ : ℂ) (hab : a ≠ b)
    (hnear : ‖μ-a‖ ≤ ‖μ-b‖) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 : ℝ)/2 ≤ ((magnitudePath38 a μ t-b)/(a-b)).re := by
  have hg : a-b ≠ 0 := sub_ne_zero.mpr hab
  have hgpos : 0 < ‖a-b‖ := norm_pos_iff.mpr hg
  let v : ℂ := (μ-a)/(a-b)
  have hμ : μ-b = (1+v)*(a-b) := by dsimp [v]; field_simp [hg]; ring
  have hn : ‖v‖ ≤ ‖1+v‖ := by
    rw [show ‖v‖ = ‖μ-a‖/‖a-b‖ by simp only [v,norm_div]]
    apply (div_le_iff₀ hgpos).mpr
    exact hnear.trans_eq (by rw [hμ,norm_mul])
  have hn2 : ‖v‖^2 ≤ ‖1+v‖^2 := by nlinarith [norm_nonneg v,norm_nonneg (1+v)]
  have hv : -(1:ℝ)/2 ≤ v.re := by
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.one_re,
      Complex.add_im,Complex.one_im,zero_add] at hn2
    nlinarith
  have he : (magnitudePath38 a μ t-b)/(a-b) = 1+(t:ℂ)*v := by
    dsimp only [magnitudePath38,v]
    field_simp [hg] <;> ring
  rw [he]
  simp only [Complex.add_re,Complex.one_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  nlinarith [ht.1,ht.2]

private theorem magnitudeFar_slit38 (a b μ : ℂ) (hab : a ≠ b)
    (hnear : ‖μ-a‖ ≤ ‖μ-b‖) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (magnitudePath38 a μ t-b)/(a-b) ∈ Complex.slitPlane :=
  Or.inl (lt_of_lt_of_le (by norm_num) (magnitudeFar_re38 a b μ hab hnear t ht))

private theorem magnitudeFar_ne_zero38 (a b μ : ℂ) (hab : a ≠ b)
    (hnear : ‖μ-a‖ ≤ ‖μ-b‖) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    magnitudeFarRoot38 a b μ t ≠ 0 := by
  intro h
  have hs := magnitudeFarRoot_sq38 a b μ t
  rw [h,zero_pow (by norm_num)] at hs
  exact (Complex.slitPlane_ne_zero (magnitudeFar_slit38 a b μ hab hnear t ht)) hs.symm

private theorem magnitudeFar_continuousAt38 (a b μ : ℂ) (hab : a ≠ b)
    (hnear : ‖μ-a‖ ≤ ‖μ-b‖) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (magnitudeFarRoot38 a b μ) t := by
  have hre := magnitudeFar_re38 a b μ hab hnear t ht
  have hg : a-b ≠ 0 := sub_ne_zero.mpr hab
  have hinner : ContinuousAt (fun u : ℝ => (magnitudePath38 a μ u-b)/(a-b)) t := by
    dsimp only [magnitudePath38]
    fun_prop
  have houter : ContinuousAt Complex.sqrt ((magnitudePath38 a μ t-b)/(a-b)) :=
    Complex.continuousAt_sqrt (Or.inl (by linarith :
      0 ≤ ((magnitudePath38 a μ t-b)/(a-b)).re))
  exact ContinuousAt.comp' (f := fun u : ℝ => (magnitudePath38 a μ u-b)/(a-b))
    (g := Complex.sqrt) (x := t) houter hinner

private theorem magnitudeAffine_deriv38 (a μ : ℂ) (t : ℝ) :
    HasDerivAt (fun w : ℂ => a+w*(μ-a)) (μ-a) (t:ℂ) := by
  convert (hasDerivAt_const (t:ℂ) a).add
    ((hasDerivAt_id (t:ℂ)).mul_const (μ-a)) using 1 <;> simp <;> rfl

private theorem magnitudePrimitive_deriv38
    (U : Set ℂ) (hconv : Convex ℝ U) (a b μ σ : ℂ) (ha : a∈U) (hμ : μ∈U)
    (T ζ : ℂ → ℂ) (hT : AnalyticOnNhd ℂ T U)
    (hode : ∀ z∈U, (z-a)*(z-b)*deriv T z + (z-(a+b)/2)*T z = (σ-z)*ζ z)
    (hab : a ≠ b) (hμa : μ ≠ a) (hnear : ‖μ-a‖ ≤ ‖μ-b‖)
    (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (magnitudePrimitive38 a b μ T) (magnitudeDensity38 a b μ σ ζ t) t := by
  have htcc : t ∈ Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
  have hzt := magnitudePath_mem38 U hconv a μ ha hμ t htcc
  have hg : a-b ≠ 0 := sub_ne_zero.mpr hab
  have hω : μ-a ≠ 0 := sub_ne_zero.mpr hμa
  have htc : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
  have hr : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht.1).ne'
  have hrc : (Real.sqrt t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hH := magnitudeFar_ne_zero38 a b μ hab hnear t htcc
  have hfar : magnitudePath38 a μ t-b ≠ 0 := by
    have hs := magnitudeFarRoot_sq38 a b μ t
    intro h
    rw [h,zero_div] at hs
    exact hH (sq_eq_zero_iff.mp hs)
  have hzC := magnitudeAffine_deriv38 a μ t
  have huC := (hzC.sub_const b).div_const (a-b)
  have hHC := (Complex.hasDerivAt_sqrt
    (magnitudeFar_slit38 a b μ hab hnear t htcc)).comp (t:ℂ) huC
  have hHd := hHC.comp_ofReal
  let e : ℂ :=
    (((magnitudePath38 a μ t-b)/(a-b)) ^ (-(1:ℂ)/2) / 2) * ((μ-a)/(a-b))
  have hHder : HasDerivAt (magnitudeFarRoot38 a b μ) e t := hHd
  have hsq : HasDerivAt (fun u : ℝ => magnitudeFarRoot38 a b μ u ^ 2)
      (2*magnitudeFarRoot38 a b μ t*e) t := by
    have hh := hHder.pow 2
    change HasDerivAt (fun u : ℝ => magnitudeFarRoot38 a b μ u ^ 2)
      ((2:ℂ)*magnitudeFarRoot38 a b μ t ^ (2-1)*e) t at hh
    simpa only [show (2:ℕ)-1 = 1 by rfl,pow_one] using hh
  have hc : 2*magnitudeFarRoot38 a b μ t*e = (μ-a)/(a-b) :=
    (hsq.congr_of_eventuallyEq (Filter.Eventually.of_forall
      (fun u => (magnitudeFarRoot_sq38 a b μ u).symm))).unique huC.comp_ofReal
  have hfe : magnitudePath38 a μ t-b = (a-b)*magnitudeFarRoot38 a b μ t ^ 2 := by
    rw [magnitudeFarRoot_sq38]
    field_simp [hg] <;> ring
  have he : e = magnitudeFarRoot38 a b μ t*(μ-a)/(2*(magnitudePath38 a μ t-b)) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hfar)).mpr
    calc
      e*(2*(magnitudePath38 a μ t-b)) =
          (a-b)*magnitudeFarRoot38 a b μ t*(2*magnitudeFarRoot38 a b μ t*e) := by rw [hfe]; ring
      _ = (a-b)*magnitudeFarRoot38 a b μ t*((μ-a)/(a-b)) := by rw [hc]
      _ = magnitudeFarRoot38 a b μ t*(μ-a) := by field_simp [hg] <;> ring
  have hRsq : (Real.sqrt t:ℂ)^2 = (t:ℂ) := by
    exact_mod_cast Real.sq_sqrt ht.1.le
  have hre : ((1/(2*Real.sqrt t):ℝ):ℂ) = (Real.sqrt t:ℂ)/(2*(t:ℂ)) := by
    push_cast
    field_simp [hrc,htc]
    linear_combination -hRsq
  have hnormode : (μ-a)*deriv T (magnitudePath38 a μ t) +
      (1/(2*(t:ℂ))+(μ-a)/(2*(magnitudePath38 a μ t-b)))*T (magnitudePath38 a μ t) =
      ((σ-magnitudePath38 a μ t)*ζ (magnitudePath38 a μ t)) /
        ((t:ℂ)*(magnitudePath38 a μ t-b)) := by
    apply (eq_div_iff (mul_ne_zero htc hfar)).mpr
    calc
      _ = (magnitudePath38 a μ t-a)*(magnitudePath38 a μ t-b)*
          deriv T (magnitudePath38 a μ t) +
          (magnitudePath38 a μ t-(a+b)/2)*T (magnitudePath38 a μ t) := by
            field_simp [htc,hfar]
            dsimp only [magnitudePath38]
            ring
      _ = _ := hode _ hzt
  have hTd := (((hT _ hzt).differentiableAt.hasDerivAt).comp (t:ℂ) hzC).comp_ofReal
  have hrd := (Real.hasDerivAt_sqrt ht.1.ne').ofReal_comp
  apply ((hrd.mul hHder).mul hTd).congr_deriv
  change (((1/(2*Real.sqrt t):ℝ):ℂ)*magnitudeFarRoot38 a b μ t +
    (Real.sqrt t:ℂ)*e)*T (magnitudePath38 a μ t) +
    ((Real.sqrt t:ℂ)*magnitudeFarRoot38 a b μ t)*
      (deriv T (magnitudePath38 a μ t)*(μ-a)) = _
  calc
    _ = (Real.sqrt t:ℂ)*magnitudeFarRoot38 a b μ t *
      ((μ-a)*deriv T (magnitudePath38 a μ t) +
        (1/(2*(t:ℂ))+(μ-a)/(2*(magnitudePath38 a μ t-b)))*T (magnitudePath38 a μ t)) := by
          rw [hre,he]
          ring
    _ = (Real.sqrt t:ℂ)*magnitudeFarRoot38 a b μ t *
      (((σ-magnitudePath38 a μ t)*ζ (magnitudePath38 a μ t)) /
        ((t:ℂ)*(magnitudePath38 a μ t-b))) := by rw [hnormode]
    _ = magnitudeDensity38 a b μ σ ζ t := by
      rw [← hRsq,hfe]
      dsimp only [magnitudeDensity38]
      field_simp [hg,hH,hrc] <;> ring

private theorem magnitudeDensity_bound38 (a b μ σ : ℂ) (ζ : ℂ → ℂ)
    (L Z : ℝ) (hL : 0 ≤ L) (hZ : 0 ≤ Z) (hab : a ≠ b)
    (hσ : ‖σ-b‖ ≤ L*‖a-b‖)
    (hζ : ∀ z ∈ segment ℝ a μ, ‖ζ z‖ ≤ Z)
    (hnear : ‖μ-a‖ ≤ ‖μ-b‖) (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) :
    ‖magnitudeDensity38 a b μ σ ζ t‖ ≤
      (Z * (Real.sqrt (1+2*L)*Real.sqrt (L+1)*Real.sqrt (‖a-b‖+‖μ-a‖)) /
        Real.sqrt ‖a-b‖) * t ^ (-(1:ℝ)/2) := by
  have hg : 0 < ‖a-b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have hfg : 0 < ‖magnitudePath38 a μ t-b‖ := by
    have h := angleSegment_far_root38 a b μ t ht.1.le ht.2 hnear
    change ‖a-b‖/2 ≤ ‖magnitudePath38 a μ t-b‖ at h
    linarith
  have hseg : magnitudePath38 a μ t ∈ segment ℝ a μ := by
    exact ⟨1-t,t,by linarith [ht.2],ht.1.le,by ring,
      by simp only [magnitudePath38,Complex.real_smul]; push_cast; ring⟩
  have hN1 := angleSegment_numerator38 a b μ σ t L ht.1.le ht.2 hL hnear hσ
  change ‖σ-magnitudePath38 a μ t‖ ≤ (1+2*L)*‖b-magnitudePath38 a μ t‖ at hN1
  rw [norm_sub_rev b (magnitudePath38 a μ t)] at hN1
  have hN2 : ‖σ-magnitudePath38 a μ t‖ ≤ (L+1)*(‖a-b‖+‖μ-a‖) := by
    have hσa : ‖σ-a‖ ≤ (L+1)*‖a-b‖ := by
      calc ‖σ-a‖ = ‖(σ-b)+(b-a)‖ := by congr 1; ring
           _ ≤ ‖σ-b‖+‖b-a‖ := norm_add_le _ _
           _ ≤ L*‖a-b‖+‖a-b‖ := by rw [norm_sub_rev b a]; exact add_le_add hσ le_rfl
           _ = _ := by ring
    have hpath : ‖magnitudePath38 a μ t-a‖ ≤ ‖μ-a‖ := by
      simp only [magnitudePath38,add_sub_cancel_left,norm_mul,Complex.norm_real,
        Real.norm_of_nonneg ht.1.le]
      calc
        t*‖μ-a‖ ≤ 1*‖μ-a‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
        _ = ‖μ-a‖ := one_mul _
    calc
      _ = ‖(σ-a)+(a-magnitudePath38 a μ t)‖ := by congr 1; ring
      _ ≤ ‖σ-a‖+‖a-magnitudePath38 a μ t‖ := norm_add_le _ _
      _ ≤ (L+1)*‖a-b‖+‖μ-a‖ := by rw [norm_sub_rev a]; exact add_le_add hσa hpath
      _ ≤ _ := by nlinarith [norm_nonneg (μ-a)]
  let A : ℝ := Real.sqrt (1+2*L)*Real.sqrt (L+1)*Real.sqrt (‖a-b‖+‖μ-a‖)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hA2 : A^2 = (1+2*L)*(L+1)*(‖a-b‖+‖μ-a‖) := by
    dsimp [A]
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
  have hNN : ‖σ-magnitudePath38 a μ t‖^2 ≤
      (A*Real.sqrt ‖magnitudePath38 a μ t-b‖)^2 := by
    have hh := mul_le_mul hN1 hN2 (norm_nonneg _) (by positivity :
      0 ≤ (1+2*L)*‖magnitudePath38 a μ t-b‖)
    calc
      _ ≤ ((1+2*L)*‖magnitudePath38 a μ t-b‖)*((L+1)*(‖a-b‖+‖μ-a‖)) := by
        simpa only [pow_two] using hh
      _ = _ := by rw [mul_pow,Real.sq_sqrt (norm_nonneg _),hA2]; ring
  have hN : ‖σ-magnitudePath38 a μ t‖ / Real.sqrt ‖magnitudePath38 a μ t-b‖ ≤ A := by
    apply (div_le_iff₀ (Real.sqrt_pos.2 hfg)).mpr
    have hh := Real.sqrt_le_sqrt hNN
    rwa [Real.sqrt_sq (norm_nonneg _),Real.sqrt_sq (mul_nonneg hA (Real.sqrt_nonneg _))] at hh
  have hH2 : ‖magnitudeFarRoot38 a b μ t‖^2 =
      ‖magnitudePath38 a μ t-b‖/‖a-b‖ := by
    have h := congrArg (fun z : ℂ => ‖z‖) (magnitudeFarRoot_sq38 a b μ t)
    simpa only [norm_pow,norm_div] using h
  have hroot : Real.sqrt ‖a-b‖ * ‖magnitudeFarRoot38 a b μ t‖ =
      Real.sqrt ‖magnitudePath38 a μ t-b‖ := by
    have hs : (Real.sqrt ‖a-b‖ * ‖magnitudeFarRoot38 a b μ t‖)^2 =
        ‖magnitudePath38 a μ t-b‖ := by
      rw [mul_pow,Real.sq_sqrt (norm_nonneg _),hH2]
      field_simp [hg.ne'] <;> ring
    have he := congrArg Real.sqrt hs
    simpa only [Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))] using he
  have hden : ‖a-b‖ * ‖magnitudeFarRoot38 a b μ t‖ =
      Real.sqrt ‖a-b‖ * Real.sqrt ‖magnitudePath38 a μ t-b‖ := by
    calc
      _ = (Real.sqrt ‖a-b‖)^2 * ‖magnitudeFarRoot38 a b μ t‖ := by
        rw [Real.sq_sqrt (norm_nonneg _)]
      _ = Real.sqrt ‖a-b‖ * (Real.sqrt ‖a-b‖ * ‖magnitudeFarRoot38 a b μ t‖) := by ring
      _ = _ := by rw [hroot]
  have hrpow : 1/Real.sqrt t = t^(-(1:ℝ)/2) := by
    rw [show (-(1:ℝ)/2) = -(1/2:ℝ) by ring,Real.rpow_neg ht.1.le,
      ← Real.sqrt_eq_rpow,one_div]
  have hgroot : Real.sqrt ‖a-b‖ ≠ 0 := (Real.sqrt_pos.2 hg).ne'
  have hfroot : Real.sqrt ‖magnitudePath38 a μ t-b‖ ≠ 0 := (Real.sqrt_pos.2 hfg).ne'
  have htroot : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht.1).ne'
  change _ ≤ (Z*A/Real.sqrt ‖a-b‖)*t^(-(1:ℝ)/2)
  calc
    ‖magnitudeDensity38 a b μ σ ζ t‖ =
        (‖σ-magnitudePath38 a μ t‖/Real.sqrt ‖magnitudePath38 a μ t-b‖)*
        (‖ζ (magnitudePath38 a μ t)‖/Real.sqrt ‖a-b‖)*(1/Real.sqrt t) := by
      simp only [magnitudeDensity38,norm_div,norm_mul,Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg t)]
      rw [hden]
      field_simp [hgroot,hfroot,htroot] <;> ring
    _ ≤ A*(Z/Real.sqrt ‖a-b‖)*(1/Real.sqrt t) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hN (div_le_div_of_nonneg_right (hζ _ hseg) (Real.sqrt_nonneg _))
          (by positivity) hA) (by positivity)
    _ = _ := by rw [← hrpow]; ring

theorem quadraticODE_terminal_magnitude_le38
    (U : Set ℂ) (hU : IsOpen U) (hconv : Convex ℝ U)
    (a b μ σ : ℂ) (ha : a ∈ U) (hμ : μ ∈ U)
    (T ζ : ℂ → ℂ)
    (hT : AnalyticOnNhd ℂ T U) (hζ : ContinuousOn ζ U)
    (hode : ∀ z ∈ U,
      (z - a) * (z - b) * deriv T z +
        (z - (a + b) / 2) * T z = (σ - z) * ζ z)
    (L Z : ℝ) (hL : 0 ≤ L) (hZ : 0 ≤ Z)
    (hσ : ‖σ - b‖ ≤ L * ‖a - b‖)
    (hζbound : ∀ z ∈ segment ℝ a μ, ‖ζ z‖ ≤ Z)
    (hnear : ‖μ - a‖ ≤ ‖μ - b‖) :
    Real.sqrt (‖(μ - a) * (μ - b)‖) * ‖T μ‖ ≤
      2 * Z * Real.sqrt (1 + 2 * L) * Real.sqrt (L + 1) *
        Real.sqrt (‖a - b‖ + ‖μ - a‖) * Real.sqrt (‖μ - a‖) := by
  by_cases hμa : μ = a
  · subst μ
    simp
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  have hzmem (t : ℝ) (ht : t∈Icc (0:ℝ) 1) := magnitudePath_mem38 U hconv a μ ha hμ t ht
  have hzcont : Continuous (magnitudePath38 a μ) := by
    change Continuous (fun t : ℝ => a+(t:ℂ)*(μ-a))
    fun_prop
  have hζcont : ContinuousOn (fun t : ℝ => ζ (magnitudePath38 a μ t)) (Icc (0:ℝ) 1) :=
    hζ.comp hzcont.continuousOn hzmem
  by_cases hab : a = b
  · subst b
    have hσa : σ = a := by
      have hn : ‖σ-a‖ ≤ 0 := by simpa using hσ
      exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))
    subst σ
    let G : ℝ → ℂ := fun t => (magnitudePath38 a μ t-a)*T (magnitudePath38 a μ t)
    let f : ℝ → ℂ := fun t => -(μ-a)*ζ (magnitudePath38 a μ t)
    have hGcont : ContinuousOn G (Icc (0:ℝ) 1) :=
      (hzcont.continuousOn.sub continuousOn_const).mul (hT.continuousOn.comp hzcont.continuousOn hzmem)
    have hfcont : ContinuousOn f (Icc (0:ℝ) 1) := continuousOn_const.mul hζcont
    have hfi : IntervalIntegrable f volume 0 1 := hfcont.intervalIntegrable_of_Icc h01
    have hGder (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) : HasDerivAt G (f t) t := by
      have hz := hzmem t ⟨ht.1.le,ht.2.le⟩
      have hza : magnitudePath38 a μ t-a ≠ 0 := by
        simp only [magnitudePath38,add_sub_cancel_left]
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr ht.1.ne') (sub_ne_zero.mpr hμa)
      have ho := hode _ hz
      have hc : (magnitudePath38 a μ t-a)*deriv T (magnitudePath38 a μ t)+
          T (magnitudePath38 a μ t) = -ζ (magnitudePath38 a μ t) := by
        have he : (magnitudePath38 a μ t-a)*
            ((magnitudePath38 a μ t-a)*deriv T (magnitudePath38 a μ t)+T (magnitudePath38 a μ t)) =
            (magnitudePath38 a μ t-a)*(-ζ (magnitudePath38 a μ t)) := by
          linear_combination ho
        exact mul_left_cancel₀ hza he
      have hd := magnitudeAffine_deriv38 a μ t
      have h1 := (hd.sub_const a).comp_ofReal
      have h2 := (((hT _ hz).differentiableAt.hasDerivAt).comp (t:ℂ) hd).comp_ofReal
      apply (h1.mul h2).congr_deriv
      change (μ-a)*T (magnitudePath38 a μ t)+
        (magnitudePath38 a μ t-a)*(deriv T (magnitudePath38 a μ t)*(μ-a)) = _
      calc _ = (μ-a)*((magnitudePath38 a μ t-a)*deriv T (magnitudePath38 a μ t)+T (magnitudePath38 a μ t)) := by ring
           _ = f t := by rw [hc]; dsimp [f]; ring
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h01 hGcont hGder hfi
    have hG : ‖(μ-a)*T μ‖ ≤ ‖μ-a‖*Z := by
      have hi : ‖∫ t : ℝ in (0:ℝ)..1, f t‖ ≤ ‖μ-a‖*Z := by
        calc _ ≤ ∫ t : ℝ in (0:ℝ)..1, ‖μ-a‖*Z := by
                    apply intervalIntegral.norm_integral_le_of_norm_le h01
                      (Filter.Eventually.of_forall (fun t ht => ?_)) intervalIntegrable_const
                    dsimp [f]
                    rw [norm_mul,norm_neg]
                    exact mul_le_mul_of_nonneg_left (hζbound _ (by
                      exact ⟨1-t,t,by linarith [ht.2],ht.1.le,by ring,
                        by simp only [magnitudePath38,Complex.real_smul]; push_cast; ring⟩)) (norm_nonneg _)
             _ = _ := by simp
      simpa [hFTC,G,magnitudePath38] using hi
    have hroot : Real.sqrt (‖μ-a‖*‖μ-a‖) = ‖μ-a‖ := by rw [← sq,Real.sqrt_sq (norm_nonneg _)]
    simp only [sub_self,norm_zero,zero_add,norm_mul]
    rw [hroot]
    have hs1 : 1 ≤ Real.sqrt (1+2*L) := by
      have := Real.sqrt_le_sqrt (by linarith : (1:ℝ) ≤ 1+2*L)
      simpa using this
    have hs2 : 1 ≤ Real.sqrt (L+1) := by
      have := Real.sqrt_le_sqrt (by linarith : (1:ℝ) ≤ L+1)
      simpa using this
    have hmul : 1 ≤ 2*Real.sqrt (1+2*L)*Real.sqrt (L+1) := by nlinarith
    have hb := mul_le_mul_of_nonneg_right hmul (mul_nonneg hZ (norm_nonneg (μ-a)))
    have hn : ‖μ-a‖*‖T μ‖ ≤ ‖μ-a‖*Z := by simpa only [norm_mul] using hG
    calc
      _ ≤ ‖μ-a‖*Z := hn
      _ ≤ (2*Real.sqrt (1+2*L)*Real.sqrt (L+1))*(Z*‖μ-a‖) := by nlinarith [hb]
      _ = (2*Real.sqrt (1+2*L)*Real.sqrt (L+1))*Z*(Real.sqrt ‖μ-a‖)^2 := by
        rw [Real.sq_sqrt (norm_nonneg _)]; ring
      _ = _ := by ring
  · have hg : 0 < ‖a-b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
    let A : ℝ := Real.sqrt (1+2*L)*Real.sqrt (L+1)*Real.sqrt (‖a-b‖+‖μ-a‖)
    let M : ℝ := Z*A/Real.sqrt ‖a-b‖
    have hM : 0 ≤ M := by dsimp [M,A]; positivity
    have hPcont : ContinuousOn (magnitudePrimitive38 a b μ T) (Icc (0:ℝ) 1) := by
      intro t ht
      have hH := magnitudeFar_continuousAt38 a b μ hab hnear t ht
      have hTc := ((hT _ (hzmem t ht)).continuousAt).comp hzcont.continuousAt
      exact (((by fun_prop : ContinuousAt (fun u : ℝ => (Real.sqrt u:ℂ)) t).mul hH).mul hTc).continuousWithinAt
    have hdcont : ContinuousOn (magnitudeDensity38 a b μ σ ζ) (Ioc (0:ℝ) 1) := by
      intro t ht
      have htcc : t∈Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2⟩
      have hH := magnitudeFar_continuousAt38 a b μ hab hnear t htcc
      have hzc := (hζ.continuousAt (hU.mem_nhds (hzmem t htcc))).comp hzcont.continuousAt
      have hnum : ContinuousAt (fun u : ℝ =>
          (σ-magnitudePath38 a μ u)*ζ (magnitudePath38 a μ u)) t :=
        ((continuous_const : Continuous (fun _ : ℝ => σ)).sub hzcont).continuousAt.mul hzc
      have hden : ContinuousAt (fun u : ℝ =>
          (a-b)*magnitudeFarRoot38 a b μ u*(Real.sqrt u:ℂ)) t :=
        ((continuousAt_const : ContinuousAt (fun _ : ℝ => a-b) t).mul hH).mul
          (by fun_prop : ContinuousAt (fun u : ℝ => (Real.sqrt u:ℂ)) t)
      exact (hnum.div hden (mul_ne_zero
        (mul_ne_zero (sub_ne_zero.mpr hab) (magnitudeFar_ne_zero38 a b μ hab hnear t htcc))
        (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 ht.1).ne'))).continuousWithinAt
    have hmeas : AEStronglyMeasurable (magnitudeDensity38 a b μ σ ζ)
        (volume.restrict (Set.uIoc (0:ℝ) 1)) := by
      simpa only [uIoc_of_le h01] using hdcont.aestronglyMeasurable measurableSet_Ioc
    have hmajor : IntervalIntegrable (fun t : ℝ => M*t^(-(1:ℝ)/2)) volume 0 1 :=
      angleSegment_majorant_integrable38.const_mul M
    have hbound (t : ℝ) (ht : t∈Ioc (0:ℝ) 1) :
        ‖magnitudeDensity38 a b μ σ ζ t‖ ≤ M*t^(-(1:ℝ)/2) :=
      magnitudeDensity_bound38 a b μ σ ζ L Z hL hZ hab hσ hζbound hnear t ht
    have hdi : IntervalIntegrable (magnitudeDensity38 a b μ σ ζ) volume 0 1 := by
      apply hmajor.mono_fun' hmeas
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      exact hbound t (by simpa only [uIoc_of_le h01] using ht)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h01 hPcont
      (fun t ht => magnitudePrimitive_deriv38 U hconv a b μ σ ha hμ T ζ hT hode hab hμa hnear t ht) hdi
    have hPbound : ‖magnitudeFarRoot38 a b μ 1*T μ‖ ≤ 2*M := by
      have hi := intervalIntegral.norm_integral_le_of_norm_le h01
        (Filter.Eventually.of_forall (fun t ht => hbound t ht)) hmajor
      rw [hFTC,intervalIntegral.integral_const_mul,angleSegment_majorant_integral38] at hi
      simpa [magnitudePrimitive38,magnitudePath38,mul_comm] using hi
    have hH2 : ‖magnitudeFarRoot38 a b μ 1‖^2 = ‖μ-b‖/‖a-b‖ := by
      have h := congrArg (fun z : ℂ => ‖z‖) (magnitudeFarRoot_sq38 a b μ 1)
      simpa [magnitudePath38,norm_pow,norm_div] using h
    have hroot : Real.sqrt ‖(μ-a)*(μ-b)‖ =
        Real.sqrt (‖μ-a‖*‖a-b‖)*‖magnitudeFarRoot38 a b μ 1‖ := by
      have hs : (Real.sqrt (‖μ-a‖*‖a-b‖)*‖magnitudeFarRoot38 a b μ 1‖)^2 =
          ‖(μ-a)*(μ-b)‖ := by
        rw [mul_pow,Real.sq_sqrt (by positivity),hH2,norm_mul]
        field_simp [hg.ne']
      have he := congrArg Real.sqrt hs
      have he' : Real.sqrt (‖μ-a‖*‖a-b‖)*‖magnitudeFarRoot38 a b μ 1‖ =
          Real.sqrt ‖(μ-a)*(μ-b)‖ := by
        simpa only [Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))] using he
      exact he'.symm
    calc
      Real.sqrt ‖(μ-a)*(μ-b)‖ * ‖T μ‖ =
          Real.sqrt (‖μ-a‖*‖a-b‖)*‖magnitudeFarRoot38 a b μ 1*T μ‖ := by
        rw [hroot,norm_mul]
        ring
      _ ≤ Real.sqrt (‖μ-a‖*‖a-b‖)*(2*M) :=
        mul_le_mul_of_nonneg_left hPbound (Real.sqrt_nonneg _)
      _ = 2*Z*Real.sqrt (1+2*L)*Real.sqrt (L+1)*
          Real.sqrt (‖a-b‖+‖μ-a‖)*Real.sqrt ‖μ-a‖ := by
        rw [Real.sqrt_mul (norm_nonneg _)]
        dsimp only [M,A]
        field_simp [(Real.sqrt_pos.2 hg).ne'] <;> ring

end
end NlsGge.GK38.Lib
