import Mathlib
import NlsGge.Atomic.G2.G2032

                                                                                         
                                                                                           
                                                                                                             
                                                                     
                                                                                                               
                                                                                                      
                                                                                                                          
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open scoped Real
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GKDefinitionDesign.G2032B1 NlsGge.GKDefinitionDesign.G2032PerO
  NlsGge.GKDefinitionDesign.G2032Chain NlsGge.GKDefinitionDesign.G2032Annulus
  NlsGge.GKDefinitionDesign.G2032Arcsine

namespace NlsGge.GKDefinitionDesign
namespace G2042MomentA
noncomputable section

/-- Critical moment of order `j` on the isolating circle (Pro §26). -/
def criticalMoment (j : ℕ) (φ : PotPair) (n : ℤ) : ℂ :=
  (1 / (Real.pi : ℂ)) *
    circleIntegral
      (fun z : ℂ =>
        (z - lamDot φ n)^j *
          deriv (discrim φ) z / canonRoot38 φ z)
      (discC φ n) (discR φ n)

/-- Rescaled critical integrand (Pro §26). -/
def criticalMomentIntegrand (j : ℕ) (φ : PotPair)
    (n : ℤ) (t : ℝ) : ℂ :=
  ((t : ℂ) / 2 - gap φ n * a5CriticalA38 n φ)^(j+1) *
    a5Chi38 n (φ, tauN φ n + (t : ℂ) * gap φ n / 2) /
    (Real.sqrt (1 - t^2) : ℂ)

/-- The integrand without the square-root weight (rescaled variable). -/
def critArcF (j : ℕ) (φ : PotPair) (n : ℤ) (t : ℝ) : ℂ :=
  ((t : ℂ) / 2 - gap φ n * a5CriticalA38 n φ)^(j+1) *
    a5Chi38 n (φ, tauN φ n + (t : ℂ) * gap φ n / 2)

/-- Unscaled cut variable: `(τ + tγ/2 - λ̇)^(j+1) χ`. -/
def critArcS (j : ℕ) (φ : PotPair) (n : ℤ) (t : ℝ) : ℂ :=
  ((tauN φ n + (t : ℂ) * gap φ n / 2) - lamDot φ n)^(j+1) *
    a5Chi38 n (φ, tauN φ n + (t : ℂ) * gap φ n / 2)

/-- The ratio `Δ̇/canonRoot38` is analytic off the gap cuts. -/
theorem ratio_analytic_cut (φ : PotPair) (hφ : φ ∈ gkW) (z : ℂ)
    (hz : z ∉ gapSegments38 φ) :
    AnalyticAt ℂ (fun w : ℂ => deriv (discrim φ) w / canonRoot38 φ w) z := by
  have hp : (φ, z) ∈ rootDomain38 := ⟨hφ, hz⟩
  have h1 : AnalyticAt ℂ (fun w : ℂ => deriv (discrim φ) w) z :=
    AnalyticAt.comp (g := fun p : PotPair × ℂ => deriv (discrim p.1) p.2)
      (f := fun w : ℂ => (φ, w))
      (analyticOnNhd_discrimDeriv_joint38 (φ, z) (Set.mem_univ _))
      (analyticAt_const.prod analyticAt_id)
  have h2 : AnalyticAt ℂ (fun w : ℂ => canonRoot38 φ w) z :=
    AnalyticAt.comp (g := fun p : PotPair × ℂ => canonRoot38 p.1 p.2)
      (f := fun w : ℂ => (φ, w))
      (canonRoot_analytic38 (φ, z) hp)
      (analyticAt_const.prod analyticAt_id)
  exact h1.div h2 (canonRoot_ne_zero38 φ hφ z hz)

/-- The moment integrand `(w - λ̇)^j Δ̇/canonRoot38` is analytic off the gap cuts. -/
theorem moment_analytic_cut (j : ℕ) (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (z : ℂ)
    (hz : z ∉ gapSegments38 φ) :
    AnalyticAt ℂ (fun w : ℂ => (w - lamDot φ n)^j * deriv (discrim φ) w / canonRoot38 φ w) z := by
  have hA0 : AnalyticAt ℂ (fun w : ℂ => w - lamDot φ n) z := analyticAt_id.sub analyticAt_const
  have hp : (φ, z) ∈ rootDomain38 := ⟨hφ, hz⟩
  have h1 : AnalyticAt ℂ (fun w : ℂ => deriv (discrim φ) w) z :=
    AnalyticAt.comp (g := fun p : PotPair × ℂ => deriv (discrim p.1) p.2)
      (f := fun w : ℂ => (φ, w))
      (analyticOnNhd_discrimDeriv_joint38 (φ, z) (Set.mem_univ _))
      (analyticAt_const.prod analyticAt_id)
  have h2 : AnalyticAt ℂ (fun w : ℂ => canonRoot38 φ w) z :=
    AnalyticAt.comp (g := fun p : PotPair × ℂ => canonRoot38 p.1 p.2)
      (f := fun w : ℂ => (φ, w))
      (canonRoot_analytic38 (φ, z) hp)
      (analyticAt_const.prod analyticAt_id)
  exact ((hA0.pow j).mul h1).div h2 (canonRoot_ne_zero38 φ hφ z hz)

/-- Every moment integrand is circle integrable on the isolating circle (totalized before use). -/
theorem circleIntegrable_moment (j : ℕ) (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    CircleIntegrable (fun z : ℂ => (z - lamDot φ n)^j * deriv (discrim φ) z / canonRoot38 φ z)
      (discC φ n) (discR φ n) := by
  have hf := isolating_family38 φ hφ
  apply ContinuousOn.circleIntegrable (isolating_radius_pos38 hf n).le
  intro z hz
  exact (moment_analytic_cut j φ hφ n z
    (fixed_sphere_subset φ (discC φ) (discR φ) hf n hz)).continuousAt.continuousWithinAt

theorem critArcF_continuousOn (j : ℕ) (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    ContinuousOn (critArcF j φ n) (Icc (-1) 1) := by
  have hs : ∀ m : ℤ, segment ℝ (lamMinus φ m) (lamPlus φ m) ⊆ ball (discC φ m) (discR φ m) := by
    obtain ⟨c, N, -, h⟩ := isolating_family38 φ hφ
    unfold IsolatingSpectral38 at h
    exact fun m => (h.1 m).1
  have hτ : tauN φ n = (lamPlus φ n + lamMinus φ n) / 2 := tauN_value38 φ hφ n
  have hmem : ∀ t : ℝ, t ∈ Icc (-1 : ℝ) 1 →
      (φ, tauN φ n + (t : ℂ) * gap φ n / 2) ∈ a5OmittedRootDomain38 n := by
    intro t ht
    have hseg : tauN φ n + (t : ℂ) * gap φ n / 2 ∈ segment ℝ (lamMinus φ n) (lamPlus φ n) := by
      refine ⟨(1 - t) / 2, (1 + t) / 2, by linarith [ht.2], by linarith [ht.1], by ring, ?_⟩
      simp only [Complex.real_smul, gap]
      push_cast
      rw [hτ]
      ring
    exact a5OwnClosedBall_omittedDomain38 φ hφ (discC φ) (discR φ) (isolating_family38 φ hφ) n _
      (ball_subset_closedBall (hs n hseg))
  unfold critArcF
  apply ContinuousOn.mul
  · exact (by fun_prop : Continuous fun t : ℝ =>
      ((t : ℂ) / 2 - gap φ n * a5CriticalA38 n φ)^(j+1)).continuousOn
  · intro t ht
    apply ContinuousAt.continuousWithinAt
    have hAn := a5Chi_analytic38 n _ (hmem t ht)
    have hc : Continuous (fun t : ℝ => (φ, tauN φ n + (t : ℂ) * gap φ n / 2)) := by fun_prop
    exact ContinuousAt.comp (g := a5Chi38 n) (f := fun t : ℝ => (φ, tauN φ n + (t : ℂ) * gap φ n / 2))
      hAn.continuousAt hc.continuousAt

theorem lamDot_sub_tauN (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    lamDot φ n - tauN φ n = gap φ n ^ 2 * a5CriticalA38 n φ := by
  have h := a5CriticalA_identity38 n φ hφ
  rw [gamma2_value38 φ hφ n] at h
  exact h

theorem critArcS_eq_mul (j : ℕ) (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (t : ℝ) :
    critArcS j φ n t = gap φ n ^ (j+1) * critArcF j φ n t := by
  have hpt : (tauN φ n + (t : ℂ) * gap φ n / 2) - lamDot φ n =
      gap φ n * ((t : ℂ) / 2 - gap φ n * a5CriticalA38 n φ) := by
    linear_combination (-1 : ℂ) * lamDot_sub_tauN φ hφ n
  unfold critArcS critArcF
  rw [hpt, mul_pow, mul_assoc]

theorem critArcS_continuousOn (j : ℕ) (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    ContinuousOn (critArcS j φ n) (Icc (-1) 1) := by
  have h := (continuousOn_const (c := gap φ n ^ (j+1))).mul (critArcF_continuousOn j φ hφ n)
  refine h.congr ?_
  intro t _
  exact critArcS_eq_mul j φ hφ n t

theorem stdRoot_joukowski (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (u : ℂ) (hu : 1 < ‖u‖)
    (hγ : lamPlus φ n - lamMinus φ n ≠ 0) :
    stdRoot38 (tauN φ n) (gamma2 φ n)
        (tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹)) =
      -((lamPlus φ n - lamMinus φ n) / 4 * (u - u⁻¹)) := by
  obtain ⟨hu0, hA, hB, -⟩ := G2032B1.inv_facts u hu
  have hh0 : (lamPlus φ n - lamMinus φ n) / 4 ≠ 0 := div_ne_zero hγ (by norm_num)
  have hg2 : gamma2 φ n = 16 * ((lamPlus φ n - lamMinus φ n) / 4) ^ 2 := by
    rw [gamma2_value38 φ hφ n]; ring
  have hz : tauN φ n - (tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹)) =
      -((lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹)) := by ring
  have hinv : (u + u⁻¹) * (u + u⁻¹)⁻¹ = 1 := mul_inv_cancel₀ hA
  unfold stdRoot38
  rw [hz, hg2, G2032B1.sqrt_joukowski _ u hh0 hu]
  linear_combination (-(((lamPlus φ n - lamMinus φ n) / 4) * (u - u⁻¹))) * hinv

/-- Pure algebra of the Joukowski pointwise identity. -/
theorem joukowski_alg (j : ℕ) (P X χ h u : ℂ) (hu0 : u ≠ 0) (hh0 : h ≠ 0)
    (hw : u - u⁻¹ ≠ 0) (hX : X = -P) :
    P ^ j * (X / (Complex.I * -(h * (u - u⁻¹))) * χ) * (h * (u⁻¹ * (u - u⁻¹))) =
      -Complex.I * (P ^ (j+1) * χ) / u := by
  subst hX
  have hden : Complex.I * -(h * (u - u⁻¹)) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (neg_ne_zero.mpr (mul_ne_zero hh0 hw))
  have S : -P / (Complex.I * -(h * (u - u⁻¹))) * (h * (u⁻¹ * (u - u⁻¹))) =
      Complex.I * -P * u⁻¹ := by
    rw [div_mul_eq_mul_div, div_eq_iff hden]
    linear_combination ((-P) * u⁻¹ * h * (u - u⁻¹)) * Complex.I_mul_I
  linear_combination (P ^ j * χ) * S

/-- Joukowski pointwise identity on the ellipse image `|u| > 1`. -/
theorem integrand_joukowski (j : ℕ) (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (u : ℂ) (hu : 1 < ‖u‖)
    (hγ : lamPlus φ n - lamMinus φ n ≠ 0)
    (hom : (φ, tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹)) ∈ a5OmittedRootDomain38 n) :
    (tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹) - lamDot φ n)^j *
        deriv (discrim φ) (tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹)) /
          canonRoot38 φ (tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹)) *
      ((lamPlus φ n - lamMinus φ n) / 4 * (1 - (u ^ 2)⁻¹)) =
    -Complex.I * ((tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹) - lamDot φ n)^(j+1) *
        a5Chi38 n (φ, tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹))) / u := by
  obtain ⟨hu0, -, hB, -⟩ := G2032B1.inv_facts u hu
  have hJ := G2032PerO.jk_not_gap φ hφ n u hu hγ hom
  have hp : (φ, tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹)) ∈ rootDomain38 :=
    ⟨hφ, hJ⟩
  have hR : deriv (discrim φ) (tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹)) /
      canonRoot38 φ (tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹)) =
      (lamDot φ n - (tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹))) /
        (Complex.I * stdRoot38 (tauN φ n) (gamma2 φ n)
          (tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹))) *
        a5Chi38 n (φ, tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹)) :=
    a5Chi_discrimDeriv_ratio38 n (φ, tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹)) hp
  rw [stdRoot_joukowski φ hφ n u hu hγ] at hR
  have hu2 : (1 - (u ^ 2)⁻¹) = u⁻¹ * (u - u⁻¹) := by
    have h1 : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
    have h2 : (u ^ 2)⁻¹ = u⁻¹ * u⁻¹ := by rw [sq, mul_inv]
    rw [h2]
    linear_combination (-1 : ℂ) * h1
  have hh0 : (lamPlus φ n - lamMinus φ n) / 4 ≠ 0 := div_ne_zero hγ (by norm_num)
  simp only [mul_div_assoc]
  rw [hR, hu2]
  linear_combination joukowski_alg j
    (tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹) - lamDot φ n)
    (lamDot φ n - (tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹)))
    (a5Chi38 n (φ, tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹)))
    ((lamPlus φ n - lamMinus φ n) / 4) u hu0 hh0 hB (by ring)

/-- Algebra: the unit-circle integrand collapses (`e I (-I X)/e = X`). -/
theorem circle_unit_key (e X : ℂ) (he : e ≠ 0) :
    e * Complex.I * (-Complex.I * X / e) = X := by
  calc e * Complex.I * (-Complex.I * X / e) = (-(Complex.I * Complex.I)) * X * (e * e⁻¹) := by ring
    _ = X := by rw [Complex.I_mul_I, mul_inv_cancel₀ he]; ring

/-- Unit-circle evaluation with `2cos θ` and the Joukowski parametrisation. -/
theorem unit_circle_eq (j : ℕ) (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    circleIntegral (fun u : ℂ => -Complex.I *
        ((tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹) - lamDot φ n)^(j+1) *
          a5Chi38 n (φ, tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹))) / u) 0 1 =
      ∫ θ in (0:ℝ)..(2 * π), critArcS j φ n (Real.cos θ) := by
  unfold circleIntegral
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  have hc : circleMap (0:ℂ) 1 θ = Complex.exp ((θ : ℂ) * Complex.I) := by
    simp [circleMap]
  have he : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hJe : tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 *
      (Complex.exp ((θ : ℂ) * Complex.I) + (Complex.exp ((θ : ℂ) * Complex.I))⁻¹) =
      tauN φ n + ((Real.cos θ : ℝ) : ℂ) * gap φ n / 2 := by
    rw [exp_add_inv_eq]
    unfold gap
    ring
  rw [deriv_circleMap, hc, smul_eq_mul, hJe]
  unfold critArcS
  exact circle_unit_key _ _ he

/-- Contour-to-cut identity for a noncollapsed gap (Pro §26 moment route, G2-032 chain). -/
theorem circle_eq_cut (j : ℕ) (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ)
    (hγ : lamPlus φ n - lamMinus φ n ≠ 0) :
    circleIntegral (fun z : ℂ => (z - lamDot φ n)^j * deriv (discrim φ) z / canonRoot38 φ z)
      (discC φ n) (discR φ n) =
    2 * ∫ t in (-1 : ℝ)..1, critArcS j φ n t / ((Real.sqrt (1 - t^2) : ℝ) : ℂ) := by
  obtain ⟨ε, hε, hε1, hann⟩ := G2032B1.H_analytic_annulus φ hφ n
  have hfa : ∀ z ∈ actionCutDomain38 φ,
      AnalyticAt ℂ (fun z : ℂ => (z - lamDot φ n)^j * deriv (discrim φ) z / canonRoot38 φ z) z :=
    fun z hz => moment_analytic_cut j φ hφ n z hz
  obtain ⟨ρ0, hρ0, hK⟩ := G2032PerO.apply_gen φ hφ n hγ
    (fun z : ℂ => (z - lamDot φ n)^j * deriv (discrim φ) z / canonRoot38 φ z) hfa
  obtain ⟨ρ1, hρ1a, hρ1b, hρ1c⟩ : ∃ ρ1 : ℝ, 1 < ρ1 ∧ ρ1 ≤ ρ0 ∧ ρ1 < 1 + ε :=
    ⟨min ρ0 (1 + ε / 2), lt_min hρ0 (by linarith), min_le_left _ _,
      lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩
  have hρpos : (0:ℝ) < ρ1 := by linarith
  have hB := hK ρ1 hρ1a hρ1b
  have hA := G2032Chain.ellipse_chain
    (fun z : ℂ => (z - lamDot φ n)^j * deriv (discrim φ) z / canonRoot38 φ z)
    (tauN φ n) (lamPlus φ n - lamMinus φ n) ρ1 hρpos
  have hC : circleIntegral
      (fun u : ℂ => (fun z : ℂ => (z - lamDot φ n)^j * deriv (discrim φ) z / canonRoot38 φ z)
        (tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹)) *
          ((lamPlus φ n - lamMinus φ n) / 4 * (1 - (u ^ 2)⁻¹))) 0 ρ1 =
      circleIntegral (fun u : ℂ => -Complex.I *
        ((tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹) - lamDot φ n)^(j+1) *
          a5Chi38 n (φ, tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹))) / u) 0 ρ1 := by
    apply circleIntegral.integral_congr hρpos.le
    intro u hu
    have hn : ‖u‖ = ρ1 := by simpa using hu
    obtain ⟨-, hom⟩ := hann u (by rw [hn]; linarith) (by rw [hn]; linarith)
    exact integrand_joukowski j φ hφ n u (by rw [hn]; exact hρ1a) hγ hom
  have hD : circleIntegral (fun z : ℂ => (z - lamDot φ n)^j * deriv (discrim φ) z / canonRoot38 φ z)
      (discC φ n) (discR φ n) = circleIntegral (fun u : ℂ => -Complex.I *
        ((tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹) - lamDot φ n)^(j+1) *
          a5Chi38 n (φ, tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹))) / u) 0 ρ1 :=
    hB.trans (hA.trans hC)
  have hdiff : ∀ u : ℂ, 1 - ε < ‖u‖ → ‖u‖ < 1 + ε → DifferentiableAt ℂ (fun u : ℂ => -Complex.I *
        ((tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹) - lamDot φ n)^(j+1) *
          a5Chi38 n (φ, tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (u + u⁻¹))) / u) u := by
    intro u h1 h2
    obtain ⟨hu0, hom⟩ := hann u h1 h2
    have hJa : AnalyticAt ℂ
        (fun w : ℂ => tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (w + w⁻¹)) u :=
      analyticAt_const.add (analyticAt_const.mul (analyticAt_id.add (analyticAt_id.inv hu0)))
    have hχa : AnalyticAt ℂ (fun w : ℂ =>
        a5Chi38 n (φ, tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (w + w⁻¹))) u :=
      AnalyticAt.comp (g := a5Chi38 n)
        (f := fun w : ℂ => (φ, tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (w + w⁻¹)))
        (a5Chi_analytic38 n _ hom) (analyticAt_const.prod hJa)
    have hPa : AnalyticAt ℂ (fun w : ℂ =>
        (tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (w + w⁻¹) - lamDot φ n)^(j+1)) u :=
      (hJa.sub analyticAt_const).pow (j+1)
    exact ((analyticAt_const.mul (hPa.mul hχa)).div analyticAt_id hu0).differentiableAt
  have hE := (circleIntegral_const_on_annulus _ (1 - ε) (1 + ε) 1 ρ1 (by linarith) (by linarith)
    hρ1a.le hρ1c hdiff).symm
  have hF1 := unit_circle_eq j φ hφ n
  have hS := G2032Arcsine.arcsine_substitution (critArcS j φ n) (critArcS_continuousOn j φ hφ n)
  exact (hD.trans hE).trans (hF1.trans hS)

/-- Collapsed gap: the moment vanishes (Cauchy on the disc; Pro §26 collapsed case). -/
theorem circle_moment_collapsed (j : ℕ) (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ)
    (hγ : lamPlus φ n - lamMinus φ n = 0) :
    circleIntegral (fun z : ℂ => (z - lamDot φ n)^j * deriv (discrim φ) z / canonRoot38 φ z)
      (discC φ n) (discR φ n) = 0 := by
  have hf := isolating_family38 φ hφ
  have hr := isolating_radius_pos38 hf n
  have hgap : gap φ n = 0 := hγ
  have hLam : lamDot φ n = tauN φ n := by
    have h0 : lamDot φ n - tauN φ n = 0 := by rw [lamDot_sub_tauN φ hφ n, hgap]; ring
    exact sub_eq_zero.mp h0
  have hτ : tauN φ n = lamMinus φ n := by
    have hpm : lamPlus φ n = lamMinus φ n := sub_eq_zero.mp hγ
    rw [tauN_value38 φ hφ n, hpm]
    ring
  have hg2 : gamma2 φ n = 0 := by
    rw [gamma2_value38 φ hφ n, hγ]; ring
  have hstd : ∀ z : ℂ, stdRoot38 (tauN φ n) (gamma2 φ n) z = (tauN φ n - z) * Complex.sqrt 1 := by
    intro z
    unfold stdRoot38
    rw [hg2]
    simp
  have hne : ∀ z ∈ sphere (discC φ n) (discR φ n), tauN φ n - z ≠ 0 := by
    intro z hz heq
    have hzg : z ∉ gapSegments38 φ := fixed_sphere_subset φ (discC φ) (discR φ) hf n hz
    apply hzg
    unfold gapSegments38
    rw [Set.mem_iUnion]
    refine ⟨n, ?_⟩
    have hzt : z = lamMinus φ n := by
      have h1 : tauN φ n = z := sub_eq_zero.mp heq
      rw [← h1, hτ]
    rw [hzt]
    exact left_mem_segment ℝ _ _
  have hpt : ∀ z ∈ sphere (discC φ n) (discR φ n),
      (z - lamDot φ n)^j * deriv (discrim φ) z / canonRoot38 φ z =
        (z - tauN φ n)^j * a5Chi38 n (φ, z) * (1 / (Complex.I * Complex.sqrt 1)) := by
    intro z hz
    have hzg : z ∉ gapSegments38 φ := fixed_sphere_subset φ (discC φ) (discR φ) hf n hz
    have hp : (φ, z) ∈ rootDomain38 := ⟨hφ, hzg⟩
    have hR : deriv (discrim φ) z / canonRoot38 φ z =
        (lamDot φ n - z) / (Complex.I * stdRoot38 (tauN φ n) (gamma2 φ n) z) * a5Chi38 n (φ, z) :=
      a5Chi_discrimDeriv_ratio38 n (φ, z) hp
    rw [hstd z, hLam] at hR
    have hq : (tauN φ n - z) / (Complex.I * ((tauN φ n - z) * Complex.sqrt 1)) =
        1 / (Complex.I * Complex.sqrt 1) := by
      have hn := hne z hz
      rw [show Complex.I * ((tauN φ n - z) * Complex.sqrt 1) =
          (tauN φ n - z) * (Complex.I * Complex.sqrt 1) by ring,
        ← mul_div_mul_left (1:ℂ) (Complex.I * Complex.sqrt 1) hn, mul_one]
    rw [hq] at hR
    rw [hLam, mul_div_assoc, hR]
    ring
  have hG_an : ∀ z ∈ closedBall (discC φ n) (discR φ n),
      AnalyticAt ℂ (fun z : ℂ => (z - tauN φ n)^j * a5Chi38 n (φ, z) * (1 / (Complex.I * Complex.sqrt 1))) z := by
    intro z hz
    have hdom : (φ, z) ∈ a5OmittedRootDomain38 n :=
      a5OwnClosedBall_omittedDomain38 φ hφ (discC φ) (discR φ) hf n z hz
    have hχ : AnalyticAt ℂ (fun w : ℂ => a5Chi38 n (φ, w)) z :=
      AnalyticAt.comp (g := a5Chi38 n) (f := fun w : ℂ => (φ, w)) (a5Chi_analytic38 n _ hdom)
        (analyticAt_const.prod analyticAt_id)
    exact (((analyticAt_id.sub analyticAt_const).pow j).mul hχ).mul analyticAt_const
  have hG : circleIntegral
      (fun z : ℂ => (z - tauN φ n)^j * a5Chi38 n (φ, z) * (1 / (Complex.I * Complex.sqrt 1)))
      (discC φ n) (discR φ n) = 0 := by
    apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty
    · intro z hz
      exact (hG_an z hz).continuousAt.continuousWithinAt
    · intro z hz
      exact (hG_an z (ball_subset_closedBall hz.1)).differentiableAt
  exact (circleIntegral.integral_congr hr.le hpt).trans hG

/-- Rescaled critical moment identity (Pro §26, verbatim statement). -/
theorem criticalMoment_rescaled
    (j : ℕ) (hj : 1 ≤ j)
    (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    IntervalIntegrable
      (criticalMomentIntegrand j φ n) volume (-1) 1 ∧
    criticalMoment j φ n =
      (2 / (Real.pi : ℂ)) * (gap φ n)^(j+1) *
        ∫ t in (-1 : ℝ)..1, criticalMomentIntegrand j φ n t := by
  refine ⟨?_, ?_⟩
  · exact G2032Arcsine.arcsine_intervalIntegrable (critArcF j φ n) (critArcF_continuousOn j φ hφ n)
  · unfold criticalMoment
    by_cases hγ : lamPlus φ n - lamMinus φ n = 0
    · have hg : gap φ n = 0 := hγ
      rw [circle_moment_collapsed j φ hφ n hγ, hg, zero_pow (by omega : j + 1 ≠ 0)]
      simp
    · rw [circle_eq_cut j φ hφ n hγ]
      have hpt : ∀ t : ℝ, critArcS j φ n t / ((Real.sqrt (1 - t^2) : ℝ) : ℂ) =
          gap φ n ^ (j+1) * criticalMomentIntegrand j φ n t := by
        intro t
        rw [critArcS_eq_mul j φ hφ n t, mul_div_assoc]
        rfl
      have hint : ∫ t in (-1 : ℝ)..1, critArcS j φ n t / ((Real.sqrt (1 - t^2) : ℝ) : ℂ) =
          gap φ n ^ (j+1) * ∫ t in (-1 : ℝ)..1, criticalMomentIntegrand j φ n t := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_congr (fun t _ => hpt t)
      rw [hint]
      ring

end
end G2042MomentA
end NlsGge.GKDefinitionDesign
