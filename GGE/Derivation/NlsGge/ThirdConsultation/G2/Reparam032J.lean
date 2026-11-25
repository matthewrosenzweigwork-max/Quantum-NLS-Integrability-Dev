import Mathlib
import NlsGge.GK38.AbelianComplexHomotopyCauchy
import NlsGge.ThirdConsultation.G2.Reparam032G
import NlsGge.ThirdConsultation.G2.Reparam032H
import NlsGge.ThirdConsultation.G2.Reparam032I
import NlsGge.ThirdConsultation.G2.Reparam032K

/- G2-032 APPLY032 = Reparam032J (proof development, AUTHOR; SUPPORTING lemmas, not a packet; not self-reviewed).
   Packages the radial homotopy homH (Reparam032G/H) between the isolating circle (angle θ from
   THETA032, Reparam032I) and the Joukowski-type ellipse as a ContinuousMap.Homotopy of closed loops on I
   (u ↦ 2πu), applies the production Cauchy identity p6Complex_homotopy_boundary38 with f analytic on the
   closed disc minus the own gap cut, and converts both loop integrals to interval integrals:
     circleIntegral f C R = ∫_0^{2π} f(τ + E_ρ(t)) · E_ρ'(t) dt   for every 1 < ρ ≤ ρ0. -/
set_option autoImplicit false

open MeasureTheory Set Metric
open scoped Real unitInterval Topology

namespace NlsGge.GKDefinitionDesign
namespace G2032Apply
noncomputable section

open NlsGge.GKDefinitionDesign.G2032Homo NlsGge.GKDefinitionDesign.G2032Homotopy
  NlsGge.GKDefinitionDesign.G2032Ellipse NlsGge.GKDefinitionDesign.G2032Theta

/-! ### A. Curve integrals of closed loops -/

/-- A loop `u ↦ k(2πu)` on `[0,1]` has curve integral `∫_0^{2π} f(k t) k'(t) dt`. -/
theorem curve_loop_eq (f : ℂ → ℂ) (k k' : ℝ → ℂ) (hk : ∀ t, HasDerivAt k (k' t) t)
    {a b : ℂ} (γ : Path a b) (hγ : ∀ u ∈ Icc (0 : ℝ) 1, γ.extend u = k (2 * π * u)) :
    (∫ᶜ z in γ, NlsGge.GK38.p6ComplexForm38 f z) = ∫ t in (0 : ℝ)..(2 * π), f (k t) * k' t := by
  have hc : (2 * π : ℝ) ≠ 0 := by positivity
  have hd : ∀ u ∈ Icc (0 : ℝ) 1,
      derivWithin (⇑γ.extend) (Icc 0 1) u = ((2 * π : ℝ) : ℂ) * k' (2 * π * u) := by
    intro u hu
    have hH : HasDerivAt (fun s : ℝ => k (2 * π * s))
        (((2 * π : ℝ) : ℂ) * k' (2 * π * u)) u := by
      have h : HasDerivAt (fun s : ℝ => k (2 * π * s)) ((2 * π * 1 : ℝ) • k' (2 * π * u)) u :=
        (hk (2 * π * u)).scomp u ((hasDerivAt_id u).const_mul (2 * π))
      convert h using 1
      rw [Complex.real_smul]
      push_cast
      ring
    rw [derivWithin_congr (f := fun s : ℝ => k (2 * π * s)) (fun x hx => hγ x hx) (hγ u hu)]
    exact hH.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc one_pos u hu)
  have h1 : ∀ u ∈ uIcc (0 : ℝ) 1, curveIntegralFun (NlsGge.GK38.p6ComplexForm38 f) γ u =
      ((2 * π : ℝ) : ℂ) * (f (k (2 * π * u)) * k' (2 * π * u)) := by
    intro u hu
    rw [uIcc_of_le zero_le_one] at hu
    rw [curveIntegralFun_def, hd u hu, hγ u hu]
    simp only [NlsGge.GK38.p6ComplexForm38, ContinuousLinearMap.mul_apply']
    ring
  have hcomp : (∫ x in (0 : ℝ)..1, f (k (2 * π * x)) * k' (2 * π * x)) =
      (2 * π)⁻¹ • ∫ x in (2 * π * 0)..(2 * π * 1), f (k x) * k' x :=
    intervalIntegral.integral_comp_mul_left (fun t => f (k t) * k' t) hc
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [curveIntegral_def, intervalIntegral.integral_congr h1, intervalIntegral.integral_const_mul,
    hcomp, mul_zero, mul_one, Complex.real_smul]
  push_cast
  field_simp

/-- The two sides `u ↦ F(s, u)` at `u = 0` and `u = 1` of a homotopy with equal values give equal
curve integrals. -/
theorem curve_sides_eq {f0 f1 : C(I, ℂ)} (F : ContinuousMap.Homotopy f0 f1)
    (ω : ℂ → ℂ →L[ℂ] ℂ) (h : ∀ s : I, F (s, 1) = F (s, 0)) :
    (∫ᶜ z in F.evalAt 1, ω z) = ∫ᶜ z in F.evalAt 0, ω z := by
  have hfun : ⇑(F.evalAt 1) = ⇑(F.evalAt 0) := funext fun s => h s
  have hext : (F.evalAt 1).extend = (F.evalAt 0).extend := by
    ext t
    show Set.IccExtend zero_le_one ⇑(F.evalAt 1) t = Set.IccExtend zero_le_one ⇑(F.evalAt 0) t
    rw [hfun]
  rw [curveIntegral_def, curveIntegral_def]
  congr 1
  funext t
  rw [curveIntegralFun_def, curveIntegralFun_def, hext]

/-! ### B. The sliced loops and their homotopy -/

/-- The loop `u ↦ Φ(s, 2πu)` as a path on `I`. -/
def sliceLoop (Φ : ℝ × ℝ → ℂ) (hΦ : Continuous Φ) (s : ℝ) : Path (Φ (s, 0)) (Φ (s, 2 * π)) where
  toContinuousMap := ⟨fun u : I => Φ (s, 2 * π * (u : ℝ)),
    hΦ.comp (continuous_const.prodMk (continuous_const.mul continuous_subtype_val))⟩
  source' := by simp
  target' := by simp

/-- The homotopy `(s,u) ↦ Φ(s, 2πu)` between the slice loops at `s = 0` and `s = 1`. -/
def sliceHomotopy (Φ : ℝ × ℝ → ℂ) (hΦ : Continuous Φ) :
    ContinuousMap.Homotopy ((sliceLoop Φ hΦ 0).toContinuousMap)
      ((sliceLoop Φ hΦ 1).toContinuousMap) where
  toContinuousMap := ⟨fun p : I × I => Φ ((p.1 : ℝ), 2 * π * (p.2 : ℝ)),
    hΦ.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_const.mul (continuous_subtype_val.comp continuous_snd)))⟩
  map_zero_left := fun _ => rfl
  map_one_left := fun _ => rfl

/-- Cauchy identity for the sliced loops: the `s = 0` and `s = 1` curve integrals agree whenever
`Φ` is `C²`, periodic in its second variable, and `f` is analytic at every value. -/
theorem slice_loop_integral_eq (Φ : ℝ × ℝ → ℂ) (hΦ : Continuous Φ) (hΦ2 : ContDiff ℝ 2 Φ)
    (hper : ∀ s t, Φ (s, t + 2 * π) = Φ (s, t)) (f : ℂ → ℂ)
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t : ℝ, AnalyticAt ℂ f (Φ (s, t))) :
    (∫ᶜ z in sliceLoop Φ hΦ 0, NlsGge.GK38.p6ComplexForm38 f z) =
      ∫ᶜ z in sliceLoop Φ hΦ 1, NlsGge.GK38.p6ComplexForm38 f z := by
  have hC2 : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one ((sliceHomotopy Φ hΦ).extend xy.1) xy.2)
      (Icc 0 1) := by
    have hG : ContDiff ℝ 2 (fun xy : ℝ × ℝ => Φ (xy.1, 2 * π * xy.2)) :=
      hΦ2.comp (contDiff_fst.prodMk (contDiff_const.mul contDiff_snd))
    refine ContDiffOn.congr hG.contDiffOn ?_
    intro xy hxy
    have h1 : xy.1 ∈ Icc (0 : ℝ) 1 := ⟨hxy.1.1, hxy.2.1⟩
    have h2 : xy.2 ∈ Icc (0 : ℝ) 1 := ⟨hxy.1.2, hxy.2.2⟩
    rw [Set.IccExtend_of_mem zero_le_one _ h2,
      ContinuousMap.Homotopy.extend_apply_of_mem_I _ h1]
    rfl
  have hanal : AnalyticOnNhd ℂ f (Set.range (sliceHomotopy Φ hΦ)) := by
    rintro _ ⟨p, rfl⟩
    exact hf (p.1 : ℝ) p.1.2 (2 * π * (p.2 : ℝ))
  have key := NlsGge.GK38.p6Complex_homotopy_boundary38 (γ₀ := sliceLoop Φ hΦ 0)
    (γ₁ := sliceLoop Φ hΦ 1) (sliceHomotopy Φ hΦ) f hanal hC2
  have hsides : (∫ᶜ z in (sliceHomotopy Φ hΦ).evalAt 1, NlsGge.GK38.p6ComplexForm38 f z) =
      ∫ᶜ z in (sliceHomotopy Φ hΦ).evalAt 0, NlsGge.GK38.p6ComplexForm38 f z := by
    refine curve_sides_eq (sliceHomotopy Φ hΦ) (NlsGge.GK38.p6ComplexForm38 f) (fun s => ?_)
    have h0 := hper (s : ℝ) 0
    rw [zero_add] at h0
    show Φ ((s : ℝ), 2 * π * ((1 : I) : ℝ)) = Φ ((s : ℝ), 2 * π * ((0 : I) : ℝ))
    have e1 : ((1 : I) : ℝ) = 1 := rfl
    have e0 : ((0 : I) : ℝ) = 0 := rfl
    rw [e1, e0, mul_one, mul_zero, h0]
  rw [hsides] at key
  exact add_right_cancel key

/-! ### C. Circle reparametrization -/

/-- Change of variables along `θ` with `θ(t+2π) = θ t + 2π` for a `2π`-periodic integrand. -/
theorem circle_reparam (g : ℝ → ℂ) (θ θ' : ℝ → ℝ) (hθ : ∀ t, HasDerivAt θ (θ' t) t)
    (hθ'c : Continuous θ') (hg : Continuous g) (hgp : Function.Periodic g (2 * π))
    (hper : ∀ t, θ (t + 2 * π) = θ t + 2 * π) :
    (∫ t in (0 : ℝ)..(2 * π), θ' t • g (θ t)) = ∫ s in (0 : ℝ)..(2 * π), g s := by
  show (∫ t in (0 : ℝ)..(2 * π), θ' t • (g ∘ θ) t) = ∫ s in (0 : ℝ)..(2 * π), g s
  rw [intervalIntegral.integral_deriv_smul_comp (fun x _ => hθ x) hθ'c.continuousOn hg]
  have h2 : θ (2 * π) = θ 0 + 2 * π := by
    have := hper 0
    rwa [zero_add] at this
  rw [h2]
  have h3 := hgp.intervalIntegral_add_eq (θ 0) 0
  rw [zero_add] at h3
  exact h3

/-- The derivative of the circle `circleMap C R`. -/
theorem hasDerivAt_circle (C : ℂ) (R : ℝ) (s : ℝ) :
    HasDerivAt (circleMap C R) ((R : ℂ) * (Complex.exp ((s : ℂ) * Complex.I) * Complex.I)) s := by
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 s := by
    simpa using (hasDerivAt_id s).ofReal_comp
  have h2 := ((h1.mul_const Complex.I).cexp.const_mul (R : ℂ)).const_add C
  unfold circleMap
  convert h2 using 1
  ring

/-! ### D. The main application -/

/-- The radial homotopy as a function on `ℝ × ℝ` (first variable `s`, second `t`). -/
def homHPair (τ C γ : ℂ) (R ρ : ℝ) : ℝ × ℝ → ℂ := fun st => homH τ C γ R ρ st.1 st.2

/-- APPLY032: for every ellipse radius `1 < ρ ≤ ρ0`, the circle integral of `f` over the isolating
circle equals the ellipse integral, for `f` analytic on the closed disc minus the own gap cut. -/
theorem apply032 (τ C γ : ℂ) (R : ℝ) (hγ : γ ≠ 0)
    (hA : ‖(τ - C) + γ / 2‖ < R) (hB : ‖(τ - C) - γ / 2‖ < R) (f : ℂ → ℂ)
    (hf : ∀ z ∈ closedBall C R, z ∉ segment ℝ (τ - γ / 2) (τ + γ / 2) → AnalyticAt ℂ f z) :
    ∃ ρ0 : ℝ, 1 < ρ0 ∧ ∀ ρ : ℝ, 1 < ρ → ρ ≤ ρ0 →
      circleIntegral f C R = ∫ t in (0 : ℝ)..(2 * π),
        f (τ + ellF (pOf γ ρ) (qOf γ ρ) t) * deriv (fun s : ℝ => ellF (pOf γ ρ) (qOf γ ρ) s) t := by
  obtain ⟨ρ0, hρ0, hbound⟩ := rho_choice (τ - C) γ R hγ hA hB
  refine ⟨ρ0, hρ0, fun ρ hρ1 hρ0' => ?_⟩
  -- Basic inequalities.
  have hw : ‖τ - C‖ < R := by
    have h := norm_add_le ((τ - C) + γ / 2) ((τ - C) - γ / 2)
    have e : (τ - C) + γ / 2 + ((τ - C) - γ / 2) = (2 : ℂ) * (τ - C) := by ring
    rw [e, norm_mul] at h
    norm_num at h
    linarith
  have hwR : (τ - C).re ^ 2 + (τ - C).im ^ 2 < R ^ 2 := by
    have h1 : (τ - C).re ^ 2 + (τ - C).im ^ 2 = ‖τ - C‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [h1]
    nlinarith [norm_nonneg (τ - C)]
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg _) hw
  have hpq : ‖qOf γ ρ‖ < ‖pOf γ ρ‖ := pq_norm_lt γ ρ hγ hρ1
  have hin : ∀ t, Complex.normSq ((τ - C) + ellF (pOf γ ρ) (qOf γ ρ) t) < R ^ 2 := by
    intro t
    have h := hbound ρ hρ1 hρ0' t
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg ((τ - C) + ellF (pOf γ ρ) (qOf γ ρ) t)]
  have hAn : Complex.normSq ((τ - C) + γ / 2) < R ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg ((τ - C) + γ / 2)]
  have hBn : Complex.normSq ((τ - C) - γ / 2) < R ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg ((τ - C) - γ / 2)]
  -- The homotopy stays in the closed disc, off the own cut.
  have hanal : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t : ℝ, AnalyticAt ℂ f (homH τ C γ R ρ s t) := by
    intro s hs t
    apply hf
    · rw [Metric.mem_closedBall, dist_eq_norm]
      have h := homH_normSq_le τ C γ R ρ s t hγ hρ1 hwR (hin t) hs.1 hs.2
      have h' : ‖homH τ C γ R ρ s t - C‖ ^ 2 ≤ R ^ 2 := by
        rw [Complex.sq_norm]; exact h
      nlinarith [norm_nonneg (homH τ C γ R ρ s t - C)]
    · exact homH_not_mem_cut τ C γ R ρ s t hγ hρ1 hwR hAn hBn hs.1 hs.2
  -- Continuity and C² of the homotopy on ℝ × ℝ.
  have hΦ2 : ContDiff ℝ 2 (homHPair τ C γ R ρ) := homH_contDiff τ C γ R ρ hγ hρ1 hwR
  have hΦ : Continuous (homHPair τ C γ R ρ) := hΦ2.continuous
  have hper : ∀ s t, homHPair τ C γ R ρ (s, t + 2 * π) = homHPair τ C γ R ρ (s, t) :=
    fun s t => homH_periodic τ C γ R ρ hγ hρ1 s t
  have hmain := slice_loop_integral_eq (homHPair τ C γ R ρ) hΦ hΦ2 hper f
    (fun s hs t => hanal s hs t)
  -- The circle angle θ lifting the ellipse ray angle.
  have hβC1 : ContDiff ℝ 1 (ellArg (pOf γ ρ) (qOf γ ρ)) :=
    (ellArg_contDiff _ _ hpq).of_le (by norm_num)
  obtain ⟨θ, hθC1, -, hθper, hθrel⟩ :=
    theta_exists τ C R hw (ellArg (pOf γ ρ) (qOf γ ρ)) hβC1
      (ellArg_strictMono _ _ hpq) (ellArg_add_two_pi _ _)
  have hk0 : ∀ t, homH τ C γ R ρ 0 t = circleMap C R (θ t) := fun t => by
    rw [homH_zero τ C γ R ρ θ hθrel t]
    rfl
  have hθd : ∀ t, HasDerivAt θ (deriv θ t) t := fun t =>
    ((hθC1.differentiable one_ne_zero) t).hasDerivAt
  have hθ'c : Continuous (deriv θ) := (contDiff_one_iff_deriv.mp hθC1).2
  -- Derivative of the circle loop `t ↦ homH 0 t`.
  have hk0' : ∀ t, HasDerivAt (fun x : ℝ => homH τ C γ R ρ 0 x)
      (deriv θ t • ((R : ℂ) * (Complex.exp ((θ t : ℂ) * Complex.I) * Complex.I))) t := by
    intro t
    have hfun : (fun x : ℝ => homH τ C γ R ρ 0 x) = fun x : ℝ => circleMap C R (θ x) :=
      funext hk0
    rw [hfun]
    exact (hasDerivAt_circle C R (θ t)).scomp t (hθd t)
  -- The circle integrand `g` and its properties.
  set g : ℝ → ℂ := fun s =>
    f (circleMap C R s) * ((R : ℂ) * (Complex.exp ((s : ℂ) * Complex.I) * Complex.I)) with hg_def
  have hcut : ∀ s : ℝ, circleMap C R s ∉ segment ℝ (τ - γ / 2) (τ + γ / 2) := by
    intro s hmem'
    have hx : τ - γ / 2 ∈ ball C R := by
      rw [Metric.mem_ball, dist_eq_norm]
      have e : τ - γ / 2 - C = (τ - C) - γ / 2 := by ring
      rw [e]; exact hB
    have hy : τ + γ / 2 ∈ ball C R := by
      rw [Metric.mem_ball, dist_eq_norm]
      have e : τ + γ / 2 - C = (τ - C) + γ / 2 := by ring
      rw [e]; exact hA
    have hb := (convex_ball C R).segment_subset hx hy hmem'
    simp only [Metric.mem_ball, dist_eq_norm, circleMap, add_sub_cancel_left, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg hR.le, Complex.norm_exp_ofReal_mul_I, mul_one,
      lt_self_iff_false] at hb
  have hgc : Continuous g := by
    apply Continuous.mul
    · refine continuous_iff_continuousAt.2 fun s => ?_
      have hmem : circleMap C R s ∈ closedBall C R := by
        simp only [Metric.mem_closedBall, dist_eq_norm, circleMap, add_sub_cancel_left, norm_mul,
          Complex.norm_real, Real.norm_of_nonneg hR.le, Complex.norm_exp_ofReal_mul_I, mul_one,
          le_refl]
      exact (hf _ hmem (hcut s)).continuousAt.comp (hasDerivAt_circle C R s).continuousAt
    · fun_prop
  have hgp : Function.Periodic g (2 * π) := by
    intro s
    simp only [hg_def]
    rw [show circleMap C R (s + 2 * π) = circleMap C R s from periodic_circleMap C R s,
      exp_real_add_two_pi s]
  -- The circle loop integral equals the circle integral (through θ).
  have hcI : circleIntegral f C R = ∫ s in (0 : ℝ)..(2 * π), g s := by
    unfold circleIntegral
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    simp only [hg_def, smul_eq_mul]
    rw [(hasDerivAt_circle C R s).deriv]
    ring
  have hγ0 : ∀ u ∈ Icc (0 : ℝ) 1,
      (sliceLoop (homHPair τ C γ R ρ) hΦ 0).extend u =
        (fun t : ℝ => homH τ C γ R ρ 0 t) (2 * π * u) := by
    intro u hu
    rw [Path.extend_apply _ hu]
    rfl
  have hloop0 : (∫ᶜ z in sliceLoop (homHPair τ C γ R ρ) hΦ 0, NlsGge.GK38.p6ComplexForm38 f z) =
      ∫ t in (0 : ℝ)..(2 * π), f (homH τ C γ R ρ 0 t) *
        (deriv θ t • ((R : ℂ) * (Complex.exp ((θ t : ℂ) * Complex.I) * Complex.I))) :=
    curve_loop_eq f (fun t : ℝ => homH τ C γ R ρ 0 t) _ hk0' (sliceLoop _ hΦ 0) hγ0
  -- The ellipse loop integral.
  have hk1 : ∀ t, HasDerivAt (fun x : ℝ => τ + ellF (pOf γ ρ) (qOf γ ρ) x)
      (deriv (fun s : ℝ => ellF (pOf γ ρ) (qOf γ ρ) s) t) t := fun t =>
    (((ellF_contDiff _ _).differentiable (by norm_num)) t).hasDerivAt.const_add τ
  have hγ1 : ∀ u ∈ Icc (0 : ℝ) 1,
      (sliceLoop (homHPair τ C γ R ρ) hΦ 1).extend u =
        (fun x : ℝ => τ + ellF (pOf γ ρ) (qOf γ ρ) x) (2 * π * u) := by
    intro u hu
    rw [Path.extend_apply _ hu]
    exact homH_one τ C γ R ρ hγ hρ1 (2 * π * u)
  have hloop1 : (∫ᶜ z in sliceLoop (homHPair τ C γ R ρ) hΦ 1, NlsGge.GK38.p6ComplexForm38 f z) =
      ∫ t in (0 : ℝ)..(2 * π), f (τ + ellF (pOf γ ρ) (qOf γ ρ) t) *
        deriv (fun s : ℝ => ellF (pOf γ ρ) (qOf γ ρ) s) t :=
    curve_loop_eq f (fun x : ℝ => τ + ellF (pOf γ ρ) (qOf γ ρ) x) _ hk1 (sliceLoop _ hΦ 1) hγ1
  -- Chain: circle = reparametrized g-integral = loop-0 integral = loop-1 integral = ellipse.
  calc circleIntegral f C R = ∫ s in (0 : ℝ)..(2 * π), g s := hcI
    _ = ∫ t in (0 : ℝ)..(2 * π), deriv θ t • g (θ t) :=
        (circle_reparam g θ (deriv θ) hθd hθ'c hgc hgp hθper).symm
    _ = ∫ t in (0 : ℝ)..(2 * π), f (homH τ C γ R ρ 0 t) *
        (deriv θ t • ((R : ℂ) * (Complex.exp ((θ t : ℂ) * Complex.I) * Complex.I))) := by
        refine intervalIntegral.integral_congr (fun t _ => ?_)
        simp only [hg_def]
        rw [hk0 t, mul_smul_comm]
    _ = ∫ᶜ z in sliceLoop (homHPair τ C γ R ρ) hΦ 0, NlsGge.GK38.p6ComplexForm38 f z := hloop0.symm
    _ = ∫ᶜ z in sliceLoop (homHPair τ C γ R ρ) hΦ 1, NlsGge.GK38.p6ComplexForm38 f z := hmain
    _ = ∫ t in (0 : ℝ)..(2 * π), f (τ + ellF (pOf γ ρ) (qOf γ ρ) t) *
        deriv (fun s : ℝ => ellF (pOf γ ρ) (qOf γ ρ) s) t := hloop1

end
end G2032Apply
end NlsGge.GKDefinitionDesign

