import Mathlib
import NlsGge.GK38.XiSqPeriod
import NlsGge.GK38.XiSqChi
import NlsGge.GK38.XiSqLocal
import NlsGge.GK38.TauGamma
import NlsGge.ThirdConsultation.G2.G2032Leaves
import NlsGge.ThirdConsultation.G2.Reparam032L
import NlsGge.ThirdConsultation.G2.Reparam032M
import NlsGge.ThirdConsultation.G2.Reparam032J

                                                                                                       
                                                                                                     
                                                  
                                                                             
                                                                                            
                                                                                                  
set_option autoImplicit false

open Set Metric MeasureTheory Filter Topology
open scoped Real

namespace NlsGge.GKDefinitionDesign
namespace G2032PerO
noncomputable section

open NlsGge.GK38 NlsGge.GKDefinitionDesign.G2032B1 NlsGge.GKDefinitionDesign.G2032Apply
  NlsGge.GKDefinitionDesign.G2032Ellipse NlsGge.GKDefinitionDesign.G2032Homo

/-- Unit-circle Joukowski image `τ + h(e^{iθ} + e^{-iθ})`. -/
def Jth (τ h : ℂ) (θ : ℝ) : ℂ :=
  τ + h * (Complex.exp ((θ : ℂ) * Complex.I) + (Complex.exp ((θ : ℂ) * Complex.I))⁻¹)

theorem own_closedBall_not_gap (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (z : ℂ)
    (hz : z ∈ closedBall (discC φ n) (discR φ n))
    (hnot : z ∉ segment ℝ (tauN φ n - (lamPlus φ n - lamMinus φ n) / 2)
      (tauN φ n + (lamPlus φ n - lamMinus φ n) / 2)) :
    z ∉ gapSegments38 φ := by
  have hτ : tauN φ n = (lamPlus φ n + lamMinus φ n) / 2 := tauN_value38 φ hφ n
  have hom := a5OwnClosedBall_omittedDomain38 φ hφ (discC φ) (discR φ)
    (isolating_family38 φ hφ) n z hz
  intro hmem
  simp only [gapSegments38, Set.mem_iUnion] at hmem
  obtain ⟨m, hm⟩ := hmem
  by_cases hmn : m = n
  · subst hmn
    apply hnot
    have e1 : tauN φ m - (lamPlus φ m - lamMinus φ m) / 2 = lamMinus φ m := by rw [hτ]; ring
    have e2 : tauN φ m + (lamPlus φ m - lamMinus φ m) / 2 = lamPlus φ m := by rw [hτ]; ring
    rw [e1, e2]
    exact hm
  · exact hom.2 m hmn hm

theorem jk_not_own (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (u : ℂ) (hu : 1 < ‖u‖)
    (hγ : lamPlus φ n - lamMinus φ n ≠ 0) :
    jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) u ∉ segment ℝ (lamMinus φ n) (lamPlus φ n) := by
  intro hz
  obtain ⟨a, b, ha, hb, hab, hz'⟩ := hz
  have hτ : tauN φ n = (lamPlus φ n + lamMinus φ n) / 2 := tauN_value38 φ hφ n
  have hh0 : (lamPlus φ n - lamMinus φ n) / 4 ≠ 0 := div_ne_zero hγ (by norm_num)
  have hab' : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
  have hz2 : (a : ℂ) * lamMinus φ n + (b : ℂ) * lamPlus φ n =
      tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹) := by
    have h := hz'
    unfold jk at h
    simp only [Complex.real_smul] at h
    exact h
  have key : u + u⁻¹ = ((2 * (b - a) : ℝ) : ℂ) := by
    apply mul_left_cancel₀ hh0
    rw [hτ] at hz2
    push_cast
    linear_combination (-1 : ℂ) * hz2 + (lamMinus φ n + 2 * ((lamPlus φ n - lamMinus φ n) / 4)) * hab'
  have hu0 : u ≠ 0 := fun h0 => by rw [h0, norm_zero] at hu; linarith
  have him : (u + u⁻¹).im = 0 := by rw [key]; simp
  rw [Complex.add_im, Complex.inv_im] at him
  have hN : 1 < Complex.normSq u := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg u]
  have hy : u.im = 0 := by
    have h1 : u.im * (1 - 1 / Complex.normSq u) = 0 := by linear_combination him
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact h2
    · exfalso
      have h3 : 1 / Complex.normSq u < 1 := by
        rw [div_lt_one (by linarith)]; exact hN
      linarith
  have hre := congrArg Complex.re key
  rw [Complex.add_re, Complex.inv_re, Complex.ofReal_re] at hre
  rw [Complex.normSq_apply, hy] at hre hN
  simp only [mul_zero, add_zero] at hre hN
  have hx0 : u.re ≠ 0 := fun h0 => by rw [h0] at hN; norm_num at hN
  have hq : u.re / (u.re * u.re) = u.re⁻¹ := by field_simp
  rw [hq] at hre
  have hxq : u.re * u.re⁻¹ = 1 := mul_inv_cancel₀ hx0
  have hr1 : (0:ℝ) ≤ 2 + 2 * (b - a) := by linarith
  have hr2 : (0:ℝ) ≤ 2 - 2 * (b - a) := by linarith
  have h4 : (u.re - u.re⁻¹) ^ 2 = 0 := by
    nlinarith [sq_nonneg (u.re - u.re⁻¹), mul_nonneg hr1 hr2]
  have hsub : u.re - u.re⁻¹ = 0 := (pow_eq_zero_iff two_ne_zero).1 h4
  have hsq : u.re * u.re = 1 := by linear_combination u.re * hsub + hxq
  linarith

theorem jk_not_gap (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (u : ℂ) (hu : 1 < ‖u‖)
    (hγ : lamPlus φ n - lamMinus φ n ≠ 0)
    (hom : (φ, jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) u) ∈ a5OmittedRootDomain38 n) :
    jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) u ∉ gapSegments38 φ := by
  intro hmem
  simp only [gapSegments38, Set.mem_iUnion] at hmem
  obtain ⟨m, hm⟩ := hmem
  by_cases hmn : m = n
  · subst hmn
    exact jk_not_own φ hφ m u hu hγ hm
  · exact hom.2 m hmn hm

theorem alg_core (h u L χ : ℂ) (hh : h ≠ 0) (hu0 : u ≠ 0) (hB : u - u⁻¹ ≠ 0) :
    L / (Complex.I * (-(h * (u - u⁻¹)))) * χ * (h * (1 - (u ^ 2)⁻¹)) =
      Complex.I * χ * L / u := by
  have hsub : 1 - (u ^ 2)⁻¹ = (u - u⁻¹) * u⁻¹ := by
    rw [sq, mul_inv, sub_mul, mul_inv_cancel₀ hu0]
  have hD : h * (u - u⁻¹) ≠ 0 := mul_ne_zero hh hB
  have hq : (h * (u - u⁻¹)) / (Complex.I * (-(h * (u - u⁻¹)))) = Complex.I := by
    rw [div_eq_iff (mul_ne_zero Complex.I_ne_zero (neg_ne_zero.2 hD))]
    linear_combination (h * (u - u⁻¹)) * Complex.I_mul_I
  calc L / (Complex.I * (-(h * (u - u⁻¹)))) * χ * (h * (1 - (u ^ 2)⁻¹))
      = L * χ * u⁻¹ * ((h * (u - u⁻¹)) / (Complex.I * (-(h * (u - u⁻¹))))) := by
        rw [hsub]; ring
    _ = L * χ * u⁻¹ * Complex.I := by rw [hq]
    _ = Complex.I * χ * L / u := by ring

theorem pt_identity (e X L : ℂ) (he : e ≠ 0) :
    e * Complex.I * (Complex.I * X * L / e) = -(X * L) := by
  calc e * Complex.I * (Complex.I * X * L / e) = Complex.I * Complex.I * X * L * (e / e) := by ring
    _ = Complex.I * Complex.I * X * L := by rw [div_self he, mul_one]
    _ = -(X * L) := by rw [Complex.I_mul_I]; ring

theorem logQuot_joukowski (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (u : ℂ) (hu : 1 < ‖u‖)
    (hγ : lamPlus φ n - lamMinus φ n ≠ 0)
    (hmem : jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) u ∉ gapSegments38 φ) :
    a5LogQuotient38 φ (jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) u) *
        ((lamPlus φ n - lamMinus φ n) / 4 * (1 - (u ^ 2)⁻¹)) =
      Complex.I * a5Chi38 n (φ, jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) u) *
        (lamDot φ n - jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) u) / u := by
  have hh0 : (lamPlus φ n - lamMinus φ n) / 4 ≠ 0 := div_ne_zero hγ (by norm_num)
  obtain ⟨hu0, hA, hB, -⟩ := inv_facts u hu
  have hR := a5Chi_discrimDeriv_ratio38 n (φ, jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) u)
    ⟨hφ, hmem⟩
  dsimp only at hR
  have hg2 : gamma2 φ n = 16 * ((lamPlus φ n - lamMinus φ n) / 4) ^ 2 := by
    rw [gamma2_value38 φ hφ n]; ring
  have hz : tauN φ n - jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) u =
      -((lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹)) := by
    unfold jk; ring
  have hsimp : -((lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹)) * ((u - u⁻¹) / (u + u⁻¹)) =
      -((lamPlus φ n - lamMinus φ n) / 4 * (u - u⁻¹)) := by
    have e : (u - u⁻¹) / (u + u⁻¹) * (u + u⁻¹) = u - u⁻¹ := div_mul_cancel₀ _ hA
    linear_combination (-((lamPlus φ n - lamMinus φ n) / 4)) * e
  unfold a5LogQuotient38
  rw [hR]
  unfold stdRoot38
  rw [hg2, hz, sqrt_joukowski _ u hh0 hu, hsimp]
  exact alg_core _ _ _ _ hh0 hu0 hB

/-- Ellipse-to-annulus transport for an arbitrary `f` analytic off the own cut. -/
theorem apply_gen (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (hγ : lamPlus φ n - lamMinus φ n ≠ 0)
    (f : ℂ → ℂ) (hfa : ∀ z, z ∈ actionCutDomain38 φ → AnalyticAt ℂ f z) :
    ∃ ρ0 : ℝ, 1 < ρ0 ∧ ∀ ρ : ℝ, 1 < ρ → ρ ≤ ρ0 →
      circleIntegral f (discC φ n) (discR φ n) = ∫ t in (0 : ℝ)..(2 * π),
        f (tauN φ n + ellF (pOf (lamPlus φ n - lamMinus φ n) ρ) (qOf (lamPlus φ n - lamMinus φ n) ρ) t) *
          deriv (fun s : ℝ => ellF (pOf (lamPlus φ n - lamMinus φ n) ρ)
            (qOf (lamPlus φ n - lamMinus φ n) ρ) s) t := by
  have hf := isolating_family38 φ hφ
  have hs : ∀ m : ℤ, segment ℝ (lamMinus φ m) (lamPlus φ m) ⊆ ball (discC φ m) (discR φ m) := by
    obtain ⟨c, N, -, h⟩ := hf
    unfold IsolatingSpectral38 at h
    exact fun m => (h.1 m).1
  have hτ : tauN φ n = (lamPlus φ n + lamMinus φ n) / 2 := tauN_value38 φ hφ n
  have hlp : lamPlus φ n ∈ ball (discC φ n) (discR φ n) := hs n (right_mem_segment ℝ _ _)
  have hlm : lamMinus φ n ∈ ball (discC φ n) (discR φ n) := hs n (left_mem_segment ℝ _ _)
  have hA : ‖(tauN φ n - discC φ n) + (lamPlus φ n - lamMinus φ n) / 2‖ < discR φ n := by
    have e : (tauN φ n - discC φ n) + (lamPlus φ n - lamMinus φ n) / 2 = lamPlus φ n - discC φ n := by
      rw [hτ]; ring
    rw [e, ← dist_eq_norm]
    exact mem_ball.mp hlp
  have hB : ‖(tauN φ n - discC φ n) - (lamPlus φ n - lamMinus φ n) / 2‖ < discR φ n := by
    have e : (tauN φ n - discC φ n) - (lamPlus φ n - lamMinus φ n) / 2 = lamMinus φ n - discC φ n := by
      rw [hτ]; ring
    rw [e, ← dist_eq_norm]
    exact mem_ball.mp hlm
  have hf' : ∀ z ∈ closedBall (discC φ n) (discR φ n),
      z ∉ segment ℝ (tauN φ n - (lamPlus φ n - lamMinus φ n) / 2)
        (tauN φ n + (lamPlus φ n - lamMinus φ n) / 2) →
      AnalyticAt ℂ f z := by
    intro z hz hnot
    exact hfa z (own_closedBall_not_gap φ hφ n z hz hnot)
  exact apply032 (tauN φ n) (discC φ n) (lamPlus φ n - lamMinus φ n) (discR φ n) hγ hA hB f hf'

theorem period_pq (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (hγ : lamPlus φ n - lamMinus φ n ≠ 0) :
    ∃ ρ0 : ℝ, 1 < ρ0 ∧ ∀ ρ : ℝ, 1 < ρ → ρ ≤ ρ0 →
      circleIntegral (fun u : ℂ => a5LogQuotient38 φ
        (tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹)) *
          ((lamPlus φ n - lamMinus φ n) / 4 * (1 - (u ^ 2)⁻¹))) 0 ρ = 0 := by
  obtain ⟨ρ0, hρ0, hI⟩ := apply_gen φ hφ n hγ (a5LogQuotient38 φ)
    (fun z hz => a5LogQuotient_analytic38 φ hφ z hz)
  refine ⟨ρ0, hρ0, fun ρ hρ1 hρ2 => ?_⟩
  have hρpos : 0 < ρ := by linarith
  have hA := G2032Chain.ellipse_chain (a5LogQuotient38 φ) (tauN φ n)
    (lamPlus φ n - lamMinus φ n) ρ hρpos
  have hB := hI ρ hρ1 hρ2
  have hC : circleIntegral (a5LogQuotient38 φ) (discC φ n) (discR φ n) = 0 :=
    (a5FixedPeriod_zero38 φ hφ (discC φ) (discR φ) (isolating_family38 φ hφ) n).2
  rw [hC] at hB
  rw [← hA]
  exact hB.symm


theorem period_unit_integral (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (hγ : lamPlus φ n - lamMinus φ n ≠ 0) :
    ∫ θ in (0 : ℝ)..(2 * π), a5Chi38 n (φ, Jth (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) θ) *
      (lamDot φ n - Jth (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) θ) = 0 := by
  obtain ⟨ρ0, hρ0, hPq⟩ := period_pq φ hφ n hγ
  obtain ⟨ε, hε, hε1, hann⟩ := H_analytic_annulus φ hφ n
  let Pu : ℂ → ℂ := fun u => Complex.I * a5Chi38 n (φ, jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) u) *
    (lamDot φ n - jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) u) / u
  have hdiff : ∀ u : ℂ, 1 - ε < ‖u‖ → ‖u‖ < 1 + ε → DifferentiableAt ℂ Pu u := by
    intro u h1 h2
    obtain ⟨hu0, hmem⟩ := hann u h1 h2
    have hJ : AnalyticAt ℂ (fun w => jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) w) u := by
      unfold jk
      exact analyticAt_const.add (analyticAt_const.mul (analyticAt_id.add (analyticAt_id.inv hu0)))
    have hc : AnalyticAt ℂ (fun w => a5Chi38 n (φ, jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) w)) u :=
      AnalyticAt.comp (g := a5Chi38 n)
        (f := fun w => (φ, jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) w))
        ((a5Chi_analytic38 n) _ hmem) (analyticAt_const.prod hJ)
    have hL : AnalyticAt ℂ (fun w => lamDot φ n - jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) w) u :=
      analyticAt_const.sub hJ
    exact ((analyticAt_const.mul hc |>.mul hL).div analyticAt_id hu0).differentiableAt
  obtain ⟨ρ1, hρ1a, hρ1b, hρ1c⟩ : ∃ ρ1 : ℝ, 1 < ρ1 ∧ ρ1 ≤ ρ0 ∧ ρ1 < 1 + ε :=
    ⟨min ρ0 (1 + ε / 2), lt_min hρ0 (by linarith), min_le_left _ _,
      lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩
  have hB3 : circleIntegral Pu 0 1 = circleIntegral Pu 0 ρ1 :=
    G2032Annulus.circleIntegral_const_on_annulus Pu (1 - ε) (1 + ε) 1 ρ1 (by linarith)
      (by linarith) (by linarith) hρ1c hdiff
  have hsph : circleIntegral Pu 0 ρ1 = circleIntegral (fun u : ℂ =>
      a5LogQuotient38 φ (tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹)) *
        ((lamPlus φ n - lamMinus φ n) / 4 * (1 - (u ^ 2)⁻¹))) 0 ρ1 := by
    apply circleIntegral.integral_congr (by linarith)
    intro u hu
    have hnorm : ‖u‖ = ρ1 := by simpa using hu
    have h1 : 1 - ε < ‖u‖ := by rw [hnorm]; linarith
    have h2 : ‖u‖ < 1 + ε := by rw [hnorm]; exact hρ1c
    have hn : 1 < ‖u‖ := by rw [hnorm]; exact hρ1a
    obtain ⟨hu0, hmem⟩ := hann u h1 h2
    have hnot := jk_not_gap φ hφ n u hn hγ hmem
    exact (logQuot_joukowski φ hφ n u hn hγ hnot).symm
  have hsph0 : circleIntegral Pu 0 1 = 0 := by
    rw [hB3, hsph, hPq ρ1 hρ1a hρ1b]
  have heval : circleIntegral Pu 0 1 =
      -∫ θ in (0 : ℝ)..(2 * π), a5Chi38 n (φ, Jth (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) θ) *
        (lamDot φ n - Jth (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) θ) := by
    unfold circleIntegral
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    have he : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    simp only [deriv_circleMap, circleMap_zero, smul_eq_mul, Complex.ofReal_one, one_mul]
    exact pt_identity _ _ _ he
  rw [heval] at hsph0
  exact neg_eq_zero.mp hsph0

end
end G2032PerO
end NlsGge.GKDefinitionDesign
