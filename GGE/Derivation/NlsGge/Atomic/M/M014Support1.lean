import Mathlib
import NlsGge.GK38.ActionRealBridge
import NlsGge.GK38.ActionUpperArc

/- M-014 SUPPORT01 (proof development, AUTHOR; not reviewed).  Level-k generalization (weight z^(m+1), k = m+1) of the landed k = 1 chain
   ActionUpperArc / ActionCircleReduction / ActionEllipseCosine / ActionRealBridge.circle_integral_eq_height:
     circleIntegral (z^(m+1) * Delta'/R) c r = 2 (m+1) int_{c-r}^{c+r} x^m v(x) dx
   for a circle whose sphere avoids the cuts.  Route: ellipse deformation (generic Analysis lemma), reflection symmetry,
   integration by parts against the quasimomentum primitive on the upper arc, continuity in the ellipse height and
   flattening to the real diameter (v = Im k(x+i0)). -/
set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
open NlsGge.Analysis.EllipseDeformation NlsGge.GK38.ActionEllipseContinuity
open scoped ComplexConjugate

namespace NlsGge.ThirdConsultation.M014Aux
noncomputable section

theorem arc_ibp_pow {γ γ' : ℝ → ℂ} {F f : ℂ → ℂ} {a b : ℝ} (m : ℕ)
    (hγ : ∀ θ, HasDerivAt γ (γ' θ) θ) (hγ' : Continuous γ')
    (hF : ContinuousOn (fun θ => F (γ θ)) (uIcc a b))
    (hf : ContinuousOn (fun θ => f (γ θ)) (uIcc a b))
    (hd : ∀ θ ∈ Ioo (min a b) (max a b), HasDerivAt F (f (γ θ)) (γ θ)) :
    IntervalIntegrable (fun θ => γ' θ * (γ θ ^ (m + 1) * f (γ θ))) volume a b ∧
      IntervalIntegrable (fun θ => γ' θ * (γ θ ^ m * F (γ θ))) volume a b ∧
      (∫ θ in a..b, γ' θ * (γ θ ^ (m + 1) * f (γ θ))) =
        γ b ^ (m + 1) * F (γ b) - γ a ^ (m + 1) * F (γ a) -
          ((m + 1 : ℕ) : ℂ) * ∫ θ in a..b, γ' θ * (γ θ ^ m * F (γ θ)) := by
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr (fun θ => (hγ θ).continuousAt)
  have hi : IntervalIntegrable (fun θ => γ' θ * f (γ θ)) volume a b :=
    (hγ'.continuousOn.mul hf).intervalIntegrable
  have hv : ∀ θ ∈ Ioo (min a b) (max a b),
      HasDerivAt (fun θ => F (γ θ)) (γ' θ * f (γ θ)) θ := by
    intro θ hθ
    have h := (hd θ hθ).scomp θ (hγ θ)
    simpa only [Function.comp_def, smul_eq_mul, mul_comm] using h
  have hu : ∀ θ, HasDerivAt (fun θ => γ θ ^ (m + 1))
      (((m + 1 : ℕ) : ℂ) * γ θ ^ m * γ' θ) θ := by
    intro θ
    have := (hγ θ).fun_pow (m + 1)
    simpa only [Nat.add_sub_cancel] using this
  have hucont : Continuous (fun θ => γ θ ^ (m + 1)) := hγc.pow _
  have hu'int : IntervalIntegrable (fun θ => ((m + 1 : ℕ) : ℂ) * γ θ ^ m * γ' θ) volume a b :=
    ((continuous_const.mul (hγc.pow m)).mul hγ').intervalIntegrable a b
  have he := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun θ => γ θ ^ (m + 1)) (v := fun θ => F (γ θ))
    hucont.continuousOn hF (fun θ _ => hu θ) hv hu'int hi
  beta_reduce at he
  refine ⟨(hγ'.continuousOn.mul (hucont.continuousOn.mul hf)).intervalIntegrable,
    (hγ'.continuousOn.mul ((hγc.pow m).continuousOn.mul hF)).intervalIntegrable, ?_⟩
  have e1 : (∫ θ in a..b, γ' θ * (γ θ ^ (m + 1) * f (γ θ))) =
      ∫ θ in a..b, γ θ ^ (m + 1) * (γ' θ * f (γ θ)) :=
    intervalIntegral.integral_congr (fun θ _ => by ring)
  have e2 : (∫ θ in a..b, ((m + 1 : ℕ) : ℂ) * γ θ ^ m * γ' θ * F (γ θ)) =
      ((m + 1 : ℕ) : ℂ) * ∫ θ in a..b, γ' θ * (γ θ ^ m * F (γ θ)) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun θ _ => by ring)
  rw [e1, he, e2]

theorem upper_arc_ibp_pow (u : PhysicalL2) (m : ℕ) (c r δ : ℝ)
    (hr : 0 < r) (hδ : 0 < δ)
    (hs : sphere (c : ℂ) r ⊆ actionCutDomain38 (realSlice u)) :
    IntervalIntegrable (fun θ => velocity r δ θ * (curve (c : ℂ) r δ θ ^ (m + 1) *
      (deriv (discrim (realSlice u)) (curve (c : ℂ) r δ θ) /
        canonRoot38 (realSlice u) (curve (c : ℂ) r δ θ)))) volume 0 Real.pi ∧
    IntervalIntegrable (fun θ => velocity r δ θ * (curve (c : ℂ) r δ θ ^ m *
      upperPrimitive u (curve (c : ℂ) r δ θ))) volume 0 Real.pi ∧
    (∫ θ in (0 : ℝ)..Real.pi, velocity r δ θ * (curve (c : ℂ) r δ θ ^ (m + 1) *
      (deriv (discrim (realSlice u)) (curve (c : ℂ) r δ θ) /
        canonRoot38 (realSlice u) (curve (c : ℂ) r δ θ)))) =
      curve (c : ℂ) r δ Real.pi ^ (m + 1) * upperPrimitive u (curve (c : ℂ) r δ Real.pi) -
      curve (c : ℂ) r δ 0 ^ (m + 1) * upperPrimitive u (curve (c : ℂ) r δ 0) -
      ((m + 1 : ℕ) : ℂ) * ∫ θ in (0 : ℝ)..Real.pi, velocity r δ θ * (curve (c : ℂ) r δ θ ^ m *
        upperPrimitive u (curve (c : ℂ) r δ θ)) := by
  have hcurve : Continuous (curve (c : ℂ) r δ) :=
    continuous_iff_continuousAt.mpr (fun θ => (curve_derivative (c : ℂ) r δ θ).continuousAt)
  have hF : ContinuousOn (fun θ => upperPrimitive u (curve (c : ℂ) r δ θ))
      (uIcc (0 : ℝ) Real.pi) := by
    rw [uIcc_of_le Real.pi_pos.le]
    exact (upperPrimitive_continuous u).comp hcurve.continuousOn
      (fun θ hθ => NlsGge.GK38.ActionUpperArc.curve_upper_closed c r δ θ hr hδ hθ)
  have hf : ContinuousOn (fun θ => deriv (discrim (realSlice u)) (curve (c : ℂ) r δ θ) /
      canonRoot38 (realSlice u) (curve (c : ℂ) r δ θ)) (uIcc (0 : ℝ) Real.pi) := by
    apply (NlsGge.GK38.ActionUpperArc.quotient_analytic u).continuousOn.comp hcurve.continuousOn
    intro θ _
    exact NlsGge.GK38.ActionEllipseDomain.ellipse_avoids_cut u (c : ℂ) r δ (by simp) hr hδ hs θ
  have hd : ∀ θ ∈ Ioo (min (0 : ℝ) Real.pi) (max (0 : ℝ) Real.pi),
      HasDerivAt (upperPrimitive u)
        (deriv (discrim (realSlice u)) (curve (c : ℂ) r δ θ) /
          canonRoot38 (realSlice u) (curve (c : ℂ) r δ θ))
        (curve (c : ℂ) r δ θ) := by
    intro θ hθ
    rw [min_eq_left Real.pi_pos.le, max_eq_right Real.pi_pos.le] at hθ
    exact NlsGge.GK38.ActionUpperArc.upperPrimitive_hasDeriv u _
      (NlsGge.GK38.ActionUpperArc.curve_upper_open c r δ θ hr hδ hθ)
  exact arc_ibp_pow (F := upperPrimitive u)
    (f := fun z : ℂ => deriv (discrim (realSlice u)) z / canonRoot38 (realSlice u) z) m
    (curve_derivative (c : ℂ) r δ) (velocity_continuous r δ) hF hf hd

theorem upperPrimitive_re_off_cut (u : PhysicalL2) (x : ℝ)
    (hx : (x : ℂ) ∉ gapSegments38 (realSlice u)) : (upperPrimitive u (x : ℂ)).re = 0 := by
  rw [NlsGge.GK38.ActionEllipseCosine.upperPrimitive_boundary_re,
    NlsGge.GK38.ActionGapLocalization.height_zero_off_cuts u x hx]

theorem real_pow_mul_re_zero (x : ℝ) (m : ℕ) (w : ℂ) (hw : w.re = 0) :
    (((x : ℂ)) ^ (m + 1) * w).re = 0 := by
  have : ((x : ℂ)) ^ (m + 1) = (((x ^ (m + 1) : ℝ)) : ℂ) := by push_cast; rfl
  rw [this, Complex.re_ofReal_mul, hw, mul_zero]

theorem endpoint_pow_re_zero (u : PhysicalL2) (m : ℕ) (c r δ : ℝ) (hr : 0 < r)
    (hs : sphere (c : ℂ) r ⊆ actionCutDomain38 (realSlice u)) :
    (curve (c : ℂ) r δ 0 ^ (m + 1) * upperPrimitive u (curve (c : ℂ) r δ 0)).re = 0 ∧
    (curve (c : ℂ) r δ Real.pi ^ (m + 1) *
      upperPrimitive u (curve (c : ℂ) r δ Real.pi)).re = 0 := by
  have hzero : curve (c : ℂ) r δ 0 ∈ sphere (c : ℂ) r := by
    have he : curve (c : ℂ) r δ 0 = curve (c : ℂ) r 1 0 := by simp [curve]
    rw [he, curve_one]
    exact circleMap_mem_sphere (c : ℂ) hr.le 0
  have hpi : curve (c : ℂ) r δ Real.pi ∈ sphere (c : ℂ) r := by
    have he : curve (c : ℂ) r δ Real.pi = curve (c : ℂ) r 1 Real.pi := by simp [curve]
    rw [he, curve_one]
    exact circleMap_mem_sphere (c : ℂ) hr.le Real.pi
  rw [NlsGge.GK38.ActionCircleReduction.curve_zero] at hzero ⊢
  rw [NlsGge.GK38.ActionCircleReduction.curve_pi] at hpi ⊢
  exact ⟨real_pow_mul_re_zero _ m _ (upperPrimitive_re_off_cut u (c + r) (hs hzero)),
    real_pow_mul_re_zero _ m _ (upperPrimitive_re_off_cut u (c - r) (hs hpi))⟩

theorem circle_integral_pow_eq (u : PhysicalL2) (m : ℕ) (c r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ)
    (hs : sphere (c : ℂ) r ⊆ actionCutDomain38 (realSlice u)) :
    circleIntegral (fun z : ℂ => z ^ (m + 1) *
      (deriv (discrim (realSlice u)) z / canonRoot38 (realSlice u) z)) (c : ℂ) r =
      -2 * (((m + 1 : ℕ) : ℂ) * (((∫ θ in (0 : ℝ)..Real.pi, velocity r δ θ *
        (curve (c : ℂ) r δ θ ^ m * upperPrimitive u (curve (c : ℂ) r δ θ))).re : ℝ) : ℂ)) := by
  set f : ℂ → ℂ := fun z : ℂ => z ^ (m + 1) *
      (deriv (discrim (realSlice u)) z / canonRoot38 (realSlice u) z) with hf_def
  have hfan : AnalyticOnNhd ℂ f (actionCutDomain38 (realSlice u)) := by
    intro z hz
    exact ((analyticAt_id (z := z)).pow (m + 1)).mul
      (NlsGge.GK38.ActionUpperArc.quotient_analytic u z hz)
  have he := NlsGge.Analysis.EllipseDeformation.ellipse_integral_eq_circle (f := f) (c : ℂ) r δ
    (isOpen_actionCutDomain38 (realSlice u) (realSlice_mem_gkW u)) hfan (by
      intro t ht θ _
      exact NlsGge.GK38.ActionEllipseDomain.ellipse_avoids_cut u (c : ℂ) r _ (by simp) hr
        (NlsGge.GK38.ActionEllipseDomain.interpolated_height_pos hδ ht) hs θ)
  have hconj : ∀ z : ℂ, z.im ≠ 0 → f (conj z) = -conj (f z) := by
    intro z hz
    simp only [hf_def]
    rw [NlsGge.GK38.ActionBranch.discrim_quotient_conj u z hz]
    simp only [map_mul, map_pow]
    ring
  have hi : IntervalIntegrable
      (NlsGge.GK38.ActionEllipseReflection.pullback f c r δ) volume 0 (2 * Real.pi) := he.1
  have hsym := NlsGge.GK38.ActionEllipseReflection.full_integral_eq_upper_add_conj c r δ hr hδ
    hconj hi
  change (∫ θ in (0 : ℝ)..2 * Real.pi, velocity r δ θ * f (curve (c : ℂ) r δ θ)) =
    (∫ θ in (0 : ℝ)..Real.pi, velocity r δ θ * f (curve (c : ℂ) r δ θ)) +
    conj (∫ θ in (0 : ℝ)..Real.pi, velocity r δ θ * f (curve (c : ℂ) r δ θ)) at hsym
  have hibp := upper_arc_ibp_pow u m c r δ hr hδ hs
  have hend := endpoint_pow_re_zero u m c r δ hr hs
  have hre := congrArg Complex.re hibp.2.2
  have hnat : ∀ w : ℂ, (((m + 1 : ℕ) : ℂ) * w).re = ((m + 1 : ℕ) : ℝ) * w.re := by
    intro w; simp [Complex.mul_re]
  simp only [Complex.sub_re, hend.1, hend.2, hnat] at hre
  rw [← he.2.2, hsym, Complex.add_conj]
  change ((2 * (∫ θ in (0 : ℝ)..Real.pi, velocity r δ θ * (curve (c : ℂ) r δ θ ^ (m + 1) *
      (deriv (discrim (realSlice u)) (curve (c : ℂ) r δ θ) /
        canonRoot38 (realSlice u) (curve (c : ℂ) r δ θ)))).re : ℝ) : ℂ) = _
  rw [hre]
  push_cast
  ring

theorem upper_integral_pow_continuity (u : PhysicalL2) (m : ℕ) (c r : ℝ) (hr : 0 ≤ r) :
    ContinuousOn (fun δ : ℝ => ∫ θ in (0 : ℝ)..Real.pi, velocity r δ θ *
      (curve (c : ℂ) r δ θ ^ m * upperPrimitive u (curve (c : ℂ) r δ θ))) (Icc (0 : ℝ) 1) := by
  apply (NlsGge.Analysis.CompactParametricIntegral.continuousOn_rectangle_integral
    (H := fun δ θ => velocity r δ θ * (curve (c : ℂ) r δ θ ^ m *
      upperPrimitive u (curve (c : ℂ) r δ θ))) zero_le_one Real.pi_pos.le ?_).2
  apply (velocity_joint_continuous r).continuousOn.mul
  apply (((curve_joint_continuous (c : ℂ) r).pow m).continuousOn).mul
  exact (upperPrimitive_continuous u).comp (curve_joint_continuous (c : ℂ) r).continuousOn
    (fun p hp => upper_rectangle (c : ℂ) r (by simp) hr hp.1 hp.2)

theorem flattened_pow_re (u : PhysicalL2) (m : ℕ) (c r : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi, velocity r 0 θ * (curve (c : ℂ) r 0 θ ^ m *
      upperPrimitive u (curve (c : ℂ) r 0 θ))).re =
      -(∫ x in (c - r)..(c + r), x ^ m * actualGapHeightE02_38 u x) := by
  set g : ℝ → ℂ := fun x => (x : ℂ) ^ m * (-Complex.I * actualQuasimomentumBoundaryE02_38 u x) with hg
  have hgc : Continuous g :=
    (Complex.continuous_ofReal.pow m).mul
      (continuous_const.mul (continuous_actualQuasimomentumBoundaryE02_38 u))
  have h := (NlsGge.GK38.ActionEllipseCosine.cosine_substitution g hgc c r).2.2
  have hflat : (∫ θ in (0 : ℝ)..Real.pi, velocity r 0 θ * (curve (c : ℂ) r 0 θ ^ m *
      upperPrimitive u (curve (c : ℂ) r 0 θ))) = ∫ x in (c + r)..(c - r), g x := by
    rw [← h]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [curve, upperPrimitive, actualQuasimomentumBoundaryE02_38, hg, zero_mul,
      Complex.ofReal_zero, mul_zero, add_zero, Complex.ofReal_add, Complex.ofReal_mul]
  rw [hflat]
  have hi : IntervalIntegrable g volume (c + r) (c - r) := hgc.intervalIntegrable _ _
  calc (∫ x in (c + r)..(c - r), g x).re
      = ∫ x in (c + r)..(c - r), (g x).re := (intervalIntegral.intervalIntegral_re hi).symm
    _ = ∫ x in (c + r)..(c - r), x ^ m * actualGapHeightE02_38 u x := by
        apply intervalIntegral.integral_congr
        intro x _
        have hp : ((x : ℂ)) ^ m = ((x ^ m : ℝ) : ℂ) := by push_cast; rfl
        have him := boundaryLimit_im_E02_38 u x _ (tendsto_actualQuasimomentumBoundaryE02_38 u x)
        simp only [hg]
        rw [hp, Complex.re_ofReal_mul]
        congr 1
        simp [Complex.mul_re, him]
    _ = _ := intervalIntegral.integral_symm _ _

theorem circle_integral_pow_eq_height (u : PhysicalL2) (m : ℕ) (c r : ℝ) (hr : 0 < r)
    (hs : sphere (c : ℂ) r ⊆ actionCutDomain38 (realSlice u)) :
    circleIntegral (fun z : ℂ => z ^ (m + 1) *
      (deriv (discrim (realSlice u)) z / canonRoot38 (realSlice u) z)) (c : ℂ) r =
      2 * ((m + 1 : ℕ) : ℂ) * (((∫ x in (c - r)..(c + r), x ^ m * actualGapHeightE02_38 u x : ℝ)) : ℂ) := by
  let P : ℝ → ℂ := fun δ => ∫ θ in (0 : ℝ)..Real.pi, velocity r δ θ *
    (curve (c : ℂ) r δ θ ^ m * upperPrimitive u (curve (c : ℂ) r δ θ))
  have hp : ContinuousOn P (Icc (0 : ℝ) 1) := upper_integral_pow_continuity u m c r hr.le
  have hG : ContinuousOn (fun δ => (-2 : ℂ) * (((m + 1 : ℕ) : ℂ) * ((P δ).re : ℂ))) (Icc (0 : ℝ) 1) :=
    continuousOn_const.mul (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn (Complex.continuous_re.comp_continuousOn hp)))
  have hz := NlsGge.Analysis.CompactParametricIntegral.closed_endpoint_of_positive_constant hG
    (K := circleIntegral (fun z : ℂ => z ^ (m + 1) *
      (deriv (discrim (realSlice u)) z / canonRoot38 (realSlice u) z)) (c : ℂ) r)
    (fun δ hδ => (circle_integral_pow_eq u m c r δ hr hδ.1 hs).symm)
  have hflat : (P 0).re = -(∫ x in (c - r)..(c + r), x ^ m * actualGapHeightE02_38 u x) :=
    flattened_pow_re u m c r
  rw [hflat, Complex.ofReal_neg] at hz
  rw [← hz]
  ring

theorem weighted_height_integral_diameter_eq_gap (u : PhysicalL2) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hf : IsolatingFamily38 (realSlice u) C R) (n : ℤ) (m : ℕ) :
    (∫ x in ((C n).re - R n)..((C n).re + R n), x ^ m * actualGapHeightE02_38 u x) =
      ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        x ^ m * actualGapHeightE02_38 u x := by
  have hb := NlsGge.GK38.ActionGapLocalization.own_gap_inside_diameter u C R hf n
  have hord : actualGapLowerAllE02_38 u n ≤ actualGapUpperAllE02_38 u n := by
    obtain ⟨x, hx⟩ := (actualGapLevelSet_eq_Icc_E02_38 u n).1
    rw [(actualGapLevelSet_eq_Icc_E02_38 u n).2] at hx
    exact hx.1.trans hx.2
  have hc : Continuous (fun x : ℝ => x ^ m * actualGapHeightE02_38 u x) :=
    (continuous_pow m).mul (continuous_actualGapHeightE02_38 u)
  have hi (a b : ℝ) : IntervalIntegrable (fun x : ℝ => x ^ m * actualGapHeightE02_38 u x) volume a b :=
    hc.intervalIntegrable a b
  have hl : (∫ x in ((C n).re - R n)..(actualGapLowerAllE02_38 u n),
      x ^ m * actualGapHeightE02_38 u x) = 0 := by
    calc
      _ = ∫ _x in ((C n).re - R n)..(actualGapLowerAllE02_38 u n), (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hb.1.le
        intro x hx
        show x ^ m * actualGapHeightE02_38 u x = 0
        rw [NlsGge.GK38.ActionGapLocalization.height_zero_on_diameter_outside_own u C R hf n x
          ⟨hx.1.le, (hx.2.le.trans hord).trans hb.2.le⟩ (fun ho => (not_lt_of_ge ho.1) hx.2), mul_zero]
      _ = 0 := by simp
  have hu : (∫ x in (actualGapUpperAllE02_38 u n)..((C n).re + R n),
      x ^ m * actualGapHeightE02_38 u x) = 0 := by
    calc
      _ = ∫ _x in (actualGapUpperAllE02_38 u n)..((C n).re + R n), (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hb.2.le
        intro x hx
        show x ^ m * actualGapHeightE02_38 u x = 0
        rw [NlsGge.GK38.ActionGapLocalization.height_zero_on_diameter_outside_own u C R hf n x
          ⟨hb.1.le.trans (hord.trans hx.1.le), hx.2.le⟩ (fun ho => (not_lt_of_ge ho.2) hx.1), mul_zero]
      _ = 0 := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hi ((C n).re - R n) (actualGapLowerAllE02_38 u n))
    (hi (actualGapLowerAllE02_38 u n) ((C n).re + R n))
  have hright := intervalIntegral.integral_add_adjacent_intervals
    (hi (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n))
    (hi (actualGapUpperAllE02_38 u n) ((C n).re + R n))
  rw [hl, zero_add] at hsplit
  rw [hu, add_zero] at hright
  exact hsplit.symm.trans hright.symm

theorem contour_pow_family_real (u : PhysicalL2) (n : ℤ) (m : ℕ) :
    circleIntegral (fun z : ℂ => z ^ (m + 1) *
      (deriv (discrim (realSlice u)) z / canonRoot38 (realSlice u) z))
      (discC (realSlice u) n) (discR (realSlice u) n) =
      2 * ((m + 1 : ℕ) : ℂ) * (((∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        x ^ m * actualGapHeightE02_38 u x : ℝ)) : ℂ) := by
  have hf := isolating_family38 (realSlice u) (realSlice_mem_gkW u)
  have hcopy := hf
  obtain ⟨κ, N, hg, _⟩ := hcopy
  have hr := (hg.1 n).1
  have hcenter : discC (realSlice u) n = ((discC (realSlice u) n).re : ℂ) :=
    Complex.ext (by simp) (by simp only [Complex.ofReal_im]; exact (hg.1 n).2)
  have hs : sphere (discC (realSlice u) n) (discR (realSlice u) n) ⊆
      actionCutDomain38 (realSlice u) := by
    simpa only [sub_zero, one_smul, zero_smul, add_zero, one_mul, zero_mul] using
      action_contour_sphere_subset38 (realSlice u) (discC (realSlice u)) (discC (realSlice u))
        (discR (realSlice u)) (discR (realSlice u)) hf hf n 0 ⟨le_rfl, zero_le_one⟩
  have hc := circle_integral_pow_eq_height u m (discC (realSlice u) n).re (discR (realSlice u) n) hr
    (by rwa [← hcenter])
  rw [← hcenter] at hc
  rw [hc, weighted_height_integral_diameter_eq_gap u (discC (realSlice u)) (discR (realSlice u)) hf n m]

end
end NlsGge.ThirdConsultation.M014Aux
