import Mathlib
import NlsGge.GK38.XiSqCenteredKernel
import NlsGge.GK38.XiSqChi
import NlsGge.GK38.XiSqLocal
import NlsGge.GK38.TauGamma
import NlsGge.ThirdConsultation.G2.G2032Leaves
import NlsGge.ThirdConsultation.G2.Reparam032L
import NlsGge.ThirdConsultation.G2.Reparam032M
import NlsGge.ThirdConsultation.G2.Reparam032O

/- G2-032 KERNEL-UNIT (proof development, AUTHOR; SUPPORTING; NOT self-reviewed). Requires the O module
   (G2032PerO.apply_gen, period_unit_integral; Reparam032O02), the L and M modules, and the landed
   Reparam032J chain, all inlined in the selftest. Result: the isolating-circle integral of the centred
   kernel equals the unit-circle integral
     (1/(16 h²)) ∫_0^{2π} χ(Jθ)(λ̇ − Jθ)² dθ,   h = (lamPlus − lamMinus)/4, Jθ = τ + h(e^{iθ}+e^{-iθ}). -/
set_option autoImplicit false

open Set Metric MeasureTheory Filter Topology
open scoped Real

namespace NlsGge.GKDefinitionDesign
namespace G2032KerP
noncomputable section

open NlsGge.GK38 NlsGge.GKDefinitionDesign.G2032B1 NlsGge.GKDefinitionDesign.G2032PerO
  NlsGge.GKDefinitionDesign.G2032Ellipse

/-- The unit-circle integrand after the Joukowski pullback (the `G` of the period module). -/
def Gk2 (φ : PotPair) (n : ℤ) (u : ℂ) : ℂ :=
  Complex.I * a5Chi38 n (φ, jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) u) *
    (lamDot φ n - jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) u) /
      (8 * ((lamPlus φ n - lamMinus φ n) / 4) * u ^ 2)

theorem exp_two_pi_sub (x : ℝ) :
    Complex.exp (((2 * π - x : ℝ) : ℂ) * Complex.I) = (Complex.exp ((x : ℂ) * Complex.I))⁻¹ := by
  rw [← Complex.exp_neg, show ((2 * π - x : ℝ) : ℂ) * Complex.I =
      -((x : ℂ) * Complex.I) + 2 * π * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem Jth_two_pi_sub (τ h : ℂ) (x : ℝ) : Jth τ h (2 * π - x) = Jth τ h x := by
  unfold Jth
  rw [exp_two_pi_sub, inv_inv]
  ring

theorem pt_gk2 (e X L h : ℂ) (he : e ≠ 0) (hh : h ≠ 0) :
    e * Complex.I * (Complex.I * X * L / (8 * h * e ^ 2)) = -(X * L) * e⁻¹ / (8 * h) := by
  have h1 : e * Complex.I * (Complex.I * X * L / (8 * h * e ^ 2)) =
      (Complex.I * Complex.I) * X * L * (e / e ^ 2) / (8 * h) := by ring
  rw [h1, Complex.I_mul_I, show e / e ^ 2 = e⁻¹ by rw [sq, ← div_div, div_self he, one_div]]
  ring

theorem gk2_annulus_diff (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (hγ : lamPlus φ n - lamMinus φ n ≠ 0)
    (ε : ℝ) (hann : ∀ u : ℂ, 1 - ε < ‖u‖ → ‖u‖ < 1 + ε → u ≠ 0 ∧
      (φ, jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) u) ∈ a5OmittedRootDomain38 n)
    (u : ℂ) (h1 : 1 - ε < ‖u‖) (h2 : ‖u‖ < 1 + ε) : DifferentiableAt ℂ (Gk2 φ n) u := by
  obtain ⟨hu0, hmem⟩ := hann u h1 h2
  have hh : (lamPlus φ n - lamMinus φ n) / 4 ≠ 0 := div_ne_zero hγ (by norm_num)
  have hJ : AnalyticAt ℂ (fun w => jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) w) u := by
    unfold jk
    exact analyticAt_const.add (analyticAt_const.mul (analyticAt_id.add (analyticAt_id.inv hu0)))
  have hc : AnalyticAt ℂ (fun w => a5Chi38 n (φ, jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) w)) u :=
    AnalyticAt.comp (g := a5Chi38 n)
      (f := fun w => (φ, jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) w))
      ((a5Chi_analytic38 n) _ hmem) (analyticAt_const.prod hJ)
  have hL : AnalyticAt ℂ (fun w => lamDot φ n - jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) w) u :=
    analyticAt_const.sub hJ
  have hne : 8 * ((lamPlus φ n - lamMinus φ n) / 4) * u ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hh) (pow_ne_zero 2 hu0)
  have hG : AnalyticAt ℂ (Gk2 φ n) u :=
    ((analyticAt_const.mul hc).mul hL).div (analyticAt_const.mul (analyticAt_id.pow 2)) hne
  exact hG.differentiableAt


/-- Pointwise integrand `χ(Jθ)` and the residue `λ̇ − Jθ` on the unit circle. -/
def Xf (φ : PotPair) (n : ℤ) (τ h : ℂ) (θ : ℝ) : ℂ := a5Chi38 n (φ, Jth τ h θ)
def Lf (φ : PotPair) (n : ℤ) (τ h : ℂ) (θ : ℝ) : ℂ := lamDot φ n - Jth τ h θ

theorem Jth_continuous (τ h : ℂ) : Continuous (fun θ : ℝ => Jth τ h θ) := by
  unfold Jth
  have hexp : Continuous (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  exact continuous_const.add (continuous_const.mul
    (hexp.add (hexp.inv₀ (fun θ => Complex.exp_ne_zero _))))

theorem Xf_continuous (φ : PotPair) (n : ℤ) (τ h : ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hann : ∀ u : ℂ, 1 - ε < ‖u‖ → ‖u‖ < 1 + ε → u ≠ 0 ∧
      (φ, jk τ h u) ∈ a5OmittedRootDomain38 n) :
    Continuous (fun θ : ℝ => Xf φ n τ h θ) := by
  apply continuous_iff_continuousAt.2
  intro θ
  have hn : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hmem := (hann (Complex.exp ((θ : ℂ) * Complex.I)) (by rw [hn]; linarith)
    (by rw [hn]; linarith)).2
  have hc : Continuous (fun θ : ℝ => (φ, Jth τ h θ)) :=
    (continuous_const (y := φ)).prodMk (Jth_continuous τ h)
  have hAt : ContinuousAt (a5Chi38 n) (φ, Jth τ h θ) := (a5Chi_analytic38 n _ hmem).continuousAt
  show ContinuousAt (fun θ : ℝ => a5Chi38 n (φ, Jth τ h θ)) θ
  exact ContinuousAt.comp (g := a5Chi38 n) (f := fun θ : ℝ => (φ, Jth τ h θ)) hAt hc.continuousAt

theorem exp_mul_I_continuous : Continuous (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) :=
  Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)

theorem exp_inv_continuous : Continuous (fun θ : ℝ => (Complex.exp ((θ : ℂ) * Complex.I))⁻¹) :=
  exp_mul_I_continuous.inv₀ (fun θ => Complex.exp_ne_zero _)

/-- The θ-integral identity used for the cross term (Pro-free, algebra only). -/
theorem unit_eval (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (hγ : lamPlus φ n - lamMinus φ n ≠ 0)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hann : ∀ u : ℂ, 1 - ε < ‖u‖ → ‖u‖ < 1 + ε → u ≠ 0 ∧
      (φ, jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) u) ∈ a5OmittedRootDomain38 n) :
    circleIntegral (Gk2 φ n) 0 1 =
      (1 / (16 * ((lamPlus φ n - lamMinus φ n) / 4) ^ 2)) *
        ∫ θ in (0 : ℝ)..(2 * π), Xf φ n (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) θ *
          Lf φ n (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) θ ^ 2 := by
  set τ := tauN φ n with hτ
  set h : ℂ := (lamPlus φ n - lamMinus φ n) / 4 with hhdef
  have hh : h ≠ 0 := div_ne_zero hγ (by norm_num)
  have hXc : Continuous (fun θ : ℝ => Xf φ n τ h θ) := Xf_continuous φ n τ h ε hε hε1 hann
  have hLc : Continuous (fun θ : ℝ => Lf φ n τ h θ) :=
    continuous_const.sub (Jth_continuous τ h)
  have hXL : Continuous (fun θ : ℝ => Xf φ n τ h θ * Lf φ n τ h θ) := hXc.mul hLc
  have hXL2 : Continuous (fun θ : ℝ => Xf φ n τ h θ * Lf φ n τ h θ ^ 2) := hXc.mul (hLc.pow 2)
  have hperiod : ∫ θ in (0 : ℝ)..(2 * π), Xf φ n τ h θ * Lf φ n τ h θ = 0 :=
    period_unit_integral φ hφ n hγ
  -- Step 1: circle integral to the θ-integral of X L e^{-iθ}
  have hcirc : circleIntegral (Gk2 φ n) 0 1 =
      ∫ θ in (0 : ℝ)..(2 * π), (-(1 / (8 * h))) * (Xf φ n τ h θ * Lf φ n τ h θ *
        (Complex.exp ((θ : ℂ) * Complex.I))⁻¹) := by
    unfold circleIntegral
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    have he : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    simp only [deriv_circleMap, circleMap_zero, smul_eq_mul, Complex.ofReal_one, one_mul]
    have key := pt_gk2 (Complex.exp ((θ : ℂ) * Complex.I)) (Xf φ n τ h θ) (Lf φ n τ h θ) h he hh
    exact key.trans (by ring)
  -- Step 2: reflection θ ↦ 2π − θ turns e^{-iθ} into e^{iθ}
  have hsym : ∫ θ in (0 : ℝ)..(2 * π), Xf φ n τ h θ * Lf φ n τ h θ *
        (Complex.exp ((θ : ℂ) * Complex.I))⁻¹ =
      ∫ θ in (0 : ℝ)..(2 * π), Xf φ n τ h θ * Lf φ n τ h θ * Complex.exp ((θ : ℂ) * Complex.I) := by
    have hcs := intervalIntegral.integral_comp_sub_left (a := 0) (b := 2 * π)
      (fun θ : ℝ => Xf φ n τ h θ * Lf φ n τ h θ * (Complex.exp ((θ : ℂ) * Complex.I))⁻¹) (2 * π)
    rw [show (2 * π - 2 * π : ℝ) = 0 by ring, show (2 * π - 0 : ℝ) = 2 * π by ring] at hcs
    have hpt : ∫ x in (0 : ℝ)..(2 * π), Xf φ n τ h (2 * π - x) * Lf φ n τ h (2 * π - x) *
        (Complex.exp (((2 * π - x : ℝ) : ℂ) * Complex.I))⁻¹ =
        ∫ x in (0 : ℝ)..(2 * π), Xf φ n τ h x * Lf φ n τ h x * Complex.exp ((x : ℂ) * Complex.I) := by
      apply intervalIntegral.integral_congr
      intro x _
      simp only [Xf, Lf, Jth_two_pi_sub, exp_two_pi_sub, inv_inv]
    exact hcs.symm.trans hpt
  -- Step 3: split e + e⁻¹
  have hU : ∫ θ in (0 : ℝ)..(2 * π), Xf φ n τ h θ * Lf φ n τ h θ *
        (Complex.exp ((θ : ℂ) * Complex.I) + (Complex.exp ((θ : ℂ) * Complex.I))⁻¹) =
      (∫ θ in (0 : ℝ)..(2 * π), Xf φ n τ h θ * Lf φ n τ h θ * (Complex.exp ((θ : ℂ) * Complex.I))⁻¹) +
      ∫ θ in (0 : ℝ)..(2 * π), Xf φ n τ h θ * Lf φ n τ h θ * Complex.exp ((θ : ℂ) * Complex.I) := by
    have c1 : Continuous (fun θ : ℝ => Xf φ n τ h θ * Lf φ n τ h θ *
        (Complex.exp ((θ : ℂ) * Complex.I))⁻¹) := hXL.mul exp_inv_continuous
    have c2 : Continuous (fun θ : ℝ => Xf φ n τ h θ * Lf φ n τ h θ * Complex.exp ((θ : ℂ) * Complex.I)) :=
      hXL.mul exp_mul_I_continuous
    rw [← intervalIntegral.integral_add (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [Pi.add_apply]
    ring
  -- Step 4: pointwise identity h X L (e + e⁻¹) = (λ̇ − τ) X L − X L²
  have hpt2 : ∀ θ : ℝ, h * (Xf φ n τ h θ * Lf φ n τ h θ *
        (Complex.exp ((θ : ℂ) * Complex.I) + (Complex.exp ((θ : ℂ) * Complex.I))⁻¹)) =
      (lamDot φ n - τ) * (Xf φ n τ h θ * Lf φ n τ h θ) -
        Xf φ n τ h θ * Lf φ n τ h θ * Lf φ n τ h θ := by
    intro θ
    have hL : Lf φ n τ h θ = (lamDot φ n - τ) - h * (Complex.exp ((θ : ℂ) * Complex.I) +
        (Complex.exp ((θ : ℂ) * Complex.I))⁻¹) := by
      unfold Lf Jth; ring
    rw [hL]
    ring
  -- Step 5: h U = −V
  have hV : h * (∫ θ in (0 : ℝ)..(2 * π), Xf φ n τ h θ * Lf φ n τ h θ *
        (Complex.exp ((θ : ℂ) * Complex.I) + (Complex.exp ((θ : ℂ) * Complex.I))⁻¹)) =
      -∫ θ in (0 : ℝ)..(2 * π), Xf φ n τ h θ * Lf φ n τ h θ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    have c3 : Continuous (fun θ : ℝ => (lamDot φ n - τ) * (Xf φ n τ h θ * Lf φ n τ h θ)) :=
      continuous_const.mul hXL
    have c4 : Continuous (fun θ : ℝ => Xf φ n τ h θ * Lf φ n τ h θ * Lf φ n τ h θ) :=
      hXL.mul hLc
    rw [intervalIntegral.integral_congr (fun θ _ => hpt2 θ),
      intervalIntegral.integral_sub (c3.intervalIntegrable _ _) (c4.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, hperiod, mul_zero, zero_sub]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    simp only
    ring
  -- Step 6: assemble
  set T := ∫ θ in (0 : ℝ)..(2 * π), Xf φ n τ h θ * Lf φ n τ h θ * (Complex.exp ((θ : ℂ) * Complex.I))⁻¹
    with hTdef
  set T' := ∫ θ in (0 : ℝ)..(2 * π), Xf φ n τ h θ * Lf φ n τ h θ * Complex.exp ((θ : ℂ) * Complex.I)
    with hT'def
  set U := ∫ θ in (0 : ℝ)..(2 * π), Xf φ n τ h θ * Lf φ n τ h θ *
    (Complex.exp ((θ : ℂ) * Complex.I) + (Complex.exp ((θ : ℂ) * Complex.I))⁻¹) with hUdef
  set V := ∫ θ in (0 : ℝ)..(2 * π), Xf φ n τ h θ * Lf φ n τ h θ ^ 2 with hVdef
  have hTV : 2 * h * T = -V := by
    linear_combination hV - h * hU + h * hsym
  have hT : T = -V / (2 * h) := by
    field_simp
    linear_combination hTV
  rw [hcirc, intervalIntegral.integral_const_mul]
  rw [← hTdef, hT]
  field_simp
  ring


theorem kernel_unit_circle (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ)
    (hγ : lamPlus φ n - lamMinus φ n ≠ 0) :
    circleIntegral (fun z => a5CenteredKernel38 n (φ, z)) (discC φ n) (discR φ n) =
      (1 / (16 * ((lamPlus φ n - lamMinus φ n) / 4) ^ 2)) *
        ∫ θ in (0 : ℝ)..(2 * π), Xf φ n (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) θ *
          Lf φ n (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) θ ^ 2 := by
  have hfa : ∀ z : ℂ, z ∈ actionCutDomain38 φ →
      AnalyticAt ℂ (fun z => a5CenteredKernel38 n (φ, z)) z :=
    fun z hz => AnalyticAt.comp (g := a5CenteredKernel38 n) (f := fun w : ℂ => (φ, w))
      (a5CenteredKernel_analytic38 n (φ, z) ⟨hφ, hz⟩) (analyticAt_const.prod analyticAt_id)
  obtain ⟨ρ0, hρ0, hK⟩ := apply_gen φ hφ n hγ (fun z => a5CenteredKernel38 n (φ, z)) hfa
  obtain ⟨ε, hε, hε1, hann⟩ := H_analytic_annulus φ hφ n
  obtain ⟨ρ1, hρ1a, hρ1b, hρ1c⟩ : ∃ ρ1 : ℝ, 1 < ρ1 ∧ ρ1 ≤ ρ0 ∧ ρ1 < 1 + ε :=
    ⟨min ρ0 (1 + ε / 2), lt_min hρ0 (by linarith), min_le_left _ _,
      lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩
  have hρpos : 0 < ρ1 := by linarith
  have hB := hK ρ1 hρ1a hρ1b
  have hA := G2032Chain.ellipse_chain (fun z => a5CenteredKernel38 n (φ, z)) (tauN φ n)
    (lamPlus φ n - lamMinus φ n) ρ1 hρpos
  have hC : circleIntegral (Gk2 φ n) 0 ρ1 =
      circleIntegral (fun u : ℂ => a5CenteredKernel38 n (φ, tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹)) *
        ((lamPlus φ n - lamMinus φ n) / 4 * (1 - (u ^ 2)⁻¹))) 0 ρ1 := by
    apply circleIntegral.integral_congr hρpos.le
    intro u hu
    have hnorm : ‖u‖ = ρ1 := by simpa using hu
    have hn : 1 < ‖u‖ := by rw [hnorm]; exact hρ1a
    exact (kernel_joukowski φ hφ n (sub_ne_zero.1 hγ) u hn).symm
  have hKG : circleIntegral (fun z => a5CenteredKernel38 n (φ, z)) (discC φ n) (discR φ n) =
      circleIntegral (Gk2 φ n) 0 ρ1 := by
    rw [hB, hC]
    exact hA
  have hB3 : circleIntegral (Gk2 φ n) 0 1 = circleIntegral (Gk2 φ n) 0 ρ1 :=
    G2032Annulus.circleIntegral_const_on_annulus (Gk2 φ n) (1 - ε) (1 + ε) 1 ρ1
      (by linarith) (by linarith) (by linarith) hρ1c
      (fun u h1 h2 => gk2_annulus_diff φ hφ n hγ ε hann u h1 h2)
  rw [hKG, ← hB3]
  exact unit_eval φ hφ n hγ ε hε hε1 hann

end
end G2032KerP
end NlsGge.GKDefinitionDesign
