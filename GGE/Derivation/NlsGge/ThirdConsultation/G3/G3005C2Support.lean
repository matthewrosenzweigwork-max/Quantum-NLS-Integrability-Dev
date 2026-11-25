import Mathlib
import NlsGge.Atomic.G2.G2021
import NlsGge.Atomic.G2.G2046
import NlsGge.Atomic.G2.G2072
import NlsGge.ThirdConsultation.G2.G2072Host
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G2.G2032Leaves
import NlsGge.ThirdConsultation.G2.Reparam032L
import NlsGge.ThirdConsultation.G2.Reparam032M
import NlsGge.ThirdConsultation.G2.Reparam032N
import NlsGge.ThirdConsultation.G2.Reparam032O
import NlsGge.ThirdConsultation.G3.G3005Host
import NlsGge.ThirdConsultation.G3.G3SourcePathHost

/- G3-005 SUPPORT C2 (proof development, AUTHOR; not self-reviewed). Target NlsGge/ThirdConsultation/G3/G3005C2Support.lean (proposed).
   Proves the second conjunct of Pro round 9 sec. 9 G3_005 (contour identity betaGapIntegral = s*pi*[m=n], s = -1) from the
   landed G2-032 Joukowski machinery (apply_gen: circle -> ellipse; ellipse_chain: ellipse -> |u| = rho circle; annulus
   constancy to |u| = 1; arcsine substitution) and the landed G2-072 / off-diagonal period facts.
   Key identity (g3005c2_period_eq): abelianPeriod38 m phi (psi n phi) = -2 * betaGapIntegral n m phi.
   Endpoint caps are NOT needed: on |u| = 1 the pulled-back differential psi/(2 i rootProduct) du/u is analytic across the
   unit circle, so the sqrt singularities are removed by the Joukowski chart. No hypothesis beyond sourceW and gap <> 0. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open scoped Real

namespace NlsGge.GKDefinitionDesign
namespace G3005C2
noncomputable section

theorem alg_pu (P R h u : ℂ) (hR : R ≠ 0) (hh : h ≠ 0) (hu0 : u ≠ 0) (hB : u - u⁻¹ ≠ 0) :
    P / (2 * Complex.I * (-(h * (u - u⁻¹))) * R) * (h * (1 - (u ^ 2)⁻¹)) =
      P / R * (Complex.I / (2 * u)) := by
  have hsub : 1 - (u ^ 2)⁻¹ = (u - u⁻¹) * u⁻¹ := by
    rw [sq, mul_inv, sub_mul, mul_inv_cancel₀ hu0]
  rw [hsub]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  generalize u - u⁻¹ = D at hB ⊢
  field_simp
  linear_combination (-P) * Complex.I_sq

theorem alg_unit (X e : ℂ) (he : e ≠ 0) :
    X * (Complex.I / (2 * e)) * (e * Complex.I) = -(X / 2) := by
  field_simp
  linear_combination (X) * Complex.I_sq

theorem jth_cos (τ h : ℂ) (θ : ℝ) :
    τ + h * (Complex.exp ((θ : ℂ) * Complex.I) + (Complex.exp ((θ : ℂ) * Complex.I))⁻¹) =
      τ + 2 * h * (Real.cos θ : ℂ) := by
  have h2 : (2 : ℂ) * Complex.cos (θ : ℂ) =
      Complex.exp ((θ : ℂ) * Complex.I) + Complex.exp (-(θ : ℂ) * Complex.I) :=
    Complex.two_cos (θ : ℂ)
  have hneg : Complex.exp (-(θ : ℂ) * Complex.I) = (Complex.exp ((θ : ℂ) * Complex.I))⁻¹ := by
    rw [← Complex.exp_neg]; ring_nf
  rw [Complex.ofReal_cos]
  rw [hneg] at h2
  linear_combination (-h) * h2

theorem sqrt_four_mul (s : ℝ) : Real.sqrt (4 * s) = 2 * Real.sqrt s := by
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
  congr 1
  rw [show (4:ℝ) = 2 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- Unit-circle integral of the Joukowski-pulled-back integrand. -/
theorem unit_circle (Pu g : ℂ → ℂ) (τ h : ℂ)
    (hP : ∀ u : ℂ, Pu u = g (τ + h * (u + u⁻¹)) * (Complex.I / (2 * u))) :
    circleIntegral Pu 0 1 = -(1 / 2 : ℂ) * ∫ θ in (0 : ℝ)..(2 * π), g (τ + 2 * h * (Real.cos θ : ℂ)) := by
  unfold circleIntegral
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  have he : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  simp only [deriv_circleMap, circleMap_zero, smul_eq_mul, Complex.ofReal_one, one_mul]
  rw [hP, jth_cos]
  have := alg_unit (g (τ + 2 * h * (Real.cos θ : ℂ))) _ he
  linear_combination this

/-- Arcsine substitution for the bank density (all totalized endpoint values are zero). -/
theorem arcsine_bank (G dens : ℝ → ℂ) (hG : ContinuousOn G (Icc 0 1))
    (hd : ∀ t ∈ Ioo (0:ℝ) 1, dens t = G t * ((2:ℂ) * (Real.sqrt (t*(1-t)) : ℝ))⁻¹)
    (hd0 : dens 0 = 0) (hd1 : dens 1 = 0) :
    ∫ θ in (0:ℝ)..(2*π), G ((Real.cos θ + 1)/2) = 4 * ∫ t in (0:ℝ)..1, dens t := by
  set F : ℝ → ℂ := fun x => G ((x+1)/2) with hF
  have hFc : ContinuousOn F (Icc (-1) 1) := by
    refine hG.comp (by fun_prop : Continuous fun x : ℝ => (x+1)/2).continuousOn ?_
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have h1 := G2032Arcsine.arcsine_substitution F hFc
  have h2 : ∫ t in (0:ℝ)..1, (fun x : ℝ => F x / ((Real.sqrt (1 - x^2) : ℝ) : ℂ)) (2*t - 1) =
      (2:ℝ)⁻¹ • ∫ x in (2*0-1:ℝ)..(2*1-1), F x / ((Real.sqrt (1 - x^2) : ℝ) : ℂ) :=
    intervalIntegral.integral_comp_mul_sub (fun x : ℝ => F x / ((Real.sqrt (1 - x^2) : ℝ) : ℂ))
      (by norm_num) 1
  have h3 : ∫ t in (0:ℝ)..1, (fun x : ℝ => F x / ((Real.sqrt (1 - x^2) : ℝ) : ℂ)) (2*t - 1) =
      ∫ t in (0:ℝ)..1, dens t := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le zero_le_one] at ht
    dsimp only
    by_cases h0 : t = 0
    · subst h0; rw [hd0]; simp [hF]
    by_cases h1' : t = 1
    · subst h1'; rw [hd1]; norm_num [hF]
    have htI : t ∈ Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1'⟩
    have hs : 0 ≤ t * (1 - t) := mul_nonneg ht.1 (by linarith [ht.2])
    have e1 : (2 * t - 1 + 1) / 2 = t := by ring
    have e2 : 1 - (2 * t - 1) ^ 2 = 4 * (t * (1 - t)) := by ring
    rw [hd t htI]
    simp only [hF]
    rw [e1, e2, sqrt_four_mul]
    push_cast
    rw [div_eq_mul_inv]
  rw [h3] at h2
  norm_num at h2
  have h4 : ∫ x in (-1:ℝ)..1, F x / ((Real.sqrt (1 - x^2) : ℝ) : ℂ) = 2 * ∫ t in (0:ℝ)..1, dens t := by
    rw [h2]; ring
  show ∫ θ in (0:ℝ)..(2*π), F (Real.cos θ) = _
  rw [h1, h4]
  ring


theorem canon_split (φ : PotPair) (hφ : φ ∈ gkW) (m : ℤ) (z : ℂ) (hz : z ∉ gapSegments38 φ) :
    canonRoot38 φ z = 2 * Complex.I * stdRoot38 (tauN φ m) (gamma2 φ m) z * rootProduct m (φ, z) := by
  have h := a5CanonRoot_omitted_factorization38 m (φ, z) ⟨hφ, hz⟩
  rw [h]
  unfold rootFactor38 rootProduct
  simp only
  ring

theorem std_jk (φ : PotPair) (hφ : φ ∈ gkW) (m : ℤ) (hγ : lamPlus φ m - lamMinus φ m ≠ 0)
    (u : ℂ) (hu : 1 < ‖u‖) :
    stdRoot38 (tauN φ m) (gamma2 φ m)
        (G2032B1.jk (tauN φ m) ((lamPlus φ m - lamMinus φ m) / 4) u) =
      -(((lamPlus φ m - lamMinus φ m) / 4) * (u - u⁻¹)) := by
  have hh0 : (lamPlus φ m - lamMinus φ m) / 4 ≠ 0 := div_ne_zero hγ (by norm_num)
  obtain ⟨hu0, hA, hB, -⟩ := G2032B1.inv_facts u hu
  have hg2 : gamma2 φ m = 16 * ((lamPlus φ m - lamMinus φ m) / 4) ^ 2 := by
    rw [gamma2_value38 φ hφ m]; ring
  have hz : tauN φ m - G2032B1.jk (tauN φ m) ((lamPlus φ m - lamMinus φ m) / 4) u =
      -((lamPlus φ m - lamMinus φ m) / 4 * (u + u⁻¹)) := by
    unfold G2032B1.jk; ring
  have hsimp : -((lamPlus φ m - lamMinus φ m) / 4 * (u + u⁻¹)) * ((u - u⁻¹) / (u + u⁻¹)) =
      -((lamPlus φ m - lamMinus φ m) / 4 * (u - u⁻¹)) := by
    have e : (u - u⁻¹) / (u + u⁻¹) * (u + u⁻¹) = u - u⁻¹ := div_mul_cancel₀ _ hA
    linear_combination (-((lamPlus φ m - lamMinus φ m) / 4)) * e
  unfold stdRoot38
  rw [hg2, hz, G2032B1.sqrt_joukowski _ u hh0 hu, hsimp]

theorem gap_mem (m : ℤ) (ψ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hspec : IsolatingSpectral38 ψ C R) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    lamMinus ψ m + (t:ℂ) * gap ψ m ∈ ball (C m) (R m) := by
  have hL : lamMinus ψ m ∈ ball (C m) (R m) := (hspec.1 m).1 (left_mem_segment ℝ _ _)
  have hR : lamPlus ψ m ∈ ball (C m) (R m) := (hspec.1 m).1 (right_mem_segment ℝ _ _)
  have h := (convex_ball (C m) (R m)).add_smul_sub_mem hL hR ht
  rw [Complex.real_smul] at h
  unfold gap
  exact h

theorem seg_dom (m : ℤ) (φ : PotPair) (hgk : φ ∈ gkW) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    (φ, lamMinus φ m + (t:ℂ) * gap φ m) ∈ a5OmittedRootDomain38 m := by
  obtain ⟨c, N, hg, hspec⟩ := isolating_family38 φ hgk
  exact a5OwnClosedBall_omittedDomain38 φ hgk (discC φ) (discR φ) ⟨c, N, hg, hspec⟩ m _
    (ball_subset_closedBall (gap_mem m φ (discC φ) (discR φ) hspec t ht))

theorem seg_cont (n m : ℤ) (φ : PotPair) (hgk : φ ∈ gkW) :
    ContinuousOn (fun t : ℝ => psi n φ (lamMinus φ m + (t:ℂ) * gap φ m) /
        rootProduct m (φ, lamMinus φ m + (t:ℂ) * gap φ m)) (Icc 0 1) := by
  have hz : Continuous (fun t : ℝ => lamMinus φ m + (t:ℂ) * gap φ m) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  intro t ht
  have hpsi : ContinuousAt (fun t : ℝ => psi n φ (lamMinus φ m + (t:ℂ) * gap φ m)) t :=
    ((p6PsiNumerator_entire38 n (sourceF n) φ _ (mem_univ _)).continuousAt).comp hz.continuousAt
  have hR : ContinuousAt (fun t : ℝ => rootProduct m (φ, lamMinus φ m + (t:ℂ) * gap φ m)) t :=
    ContinuousAt.comp (g := rootProduct m)
      (f := fun t : ℝ => ((φ, lamMinus φ m + (t:ℂ) * gap φ m) : PotPair × ℂ))
      ((G2_021 m).2.1 _ (seg_dom m φ hgk t ht)).continuousAt
      (continuous_const.prodMk hz).continuousAt
  exact (hpsi.div hR ((G2_021 m).2.2 _ (seg_dom m φ hgk t ht))).continuousWithinAt

theorem density_eq (n m : ℤ) (φ : PotPair) (t : ℝ) (hg : gap φ m ≠ 0)
    (hs : 0 < t*(1-t)) :
    betaGapDensity n m φ t =
      (psi n φ (lamMinus φ m + (t:ℂ) * gap φ m) /
        rootProduct m (φ, lamMinus φ m + (t:ℂ) * gap φ m)) *
        ((2:ℂ) * (Real.sqrt (t*(1-t)) : ℝ))⁻¹ := by
  unfold betaGapDensity
  dsimp only
  have hsq : (Real.sqrt (t*(1-t)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hs).ne'
  have hden : (2 * Complex.I * (-Complex.I * gap φ m * (Real.sqrt (t*(1-t)) : ℂ))) =
      2 * gap φ m * (Real.sqrt (t*(1-t)) : ℂ) := by
    linear_combination (-2 * gap φ m * (Real.sqrt (t*(1-t)) : ℂ)) * Complex.I_sq
  rw [hden]
  by_cases hR : rootProduct m (φ, lamMinus φ m + (t:ℂ) * gap φ m) = 0
  · simp [hR]
  · field_simp

theorem period_eq (n m : ℤ) (φ : PotPair) (hφ : φ ∈ sourceW) (hgap : gap φ m ≠ 0) :
    abelianPeriod38 m φ (psi n φ) = -2 * betaGapIntegral n m φ := by
  have hgk : φ ∈ gkW := sourceFamily.W_gk hφ
  have hγ : lamPlus φ m - lamMinus φ m ≠ 0 := hgap
  have hh0 : (lamPlus φ m - lamMinus φ m) / 4 ≠ 0 := div_ne_zero hγ (by norm_num)
  have hτ : tauN φ m = (lamPlus φ m + lamMinus φ m) / 2 := tauN_value38 φ hgk m
  have hfa : ∀ z, z ∈ actionCutDomain38 φ →
      AnalyticAt ℂ (fun z => psi n φ z / canonRoot38 φ z) z := by
    intro z hz
    have hp := p6PsiNumerator_entire38 n (sourceF n) φ z (mem_univ _)
    have hc : AnalyticAt ℂ (canonRoot38 φ) z :=
      AnalyticAt.comp (g := fun p : PotPair × ℂ => canonRoot38 p.1 p.2)
        (f := fun w : ℂ => (φ, w)) (canonRoot_analytic38 _ ⟨hgk, hz⟩)
        (analyticAt_const.prod analyticAt_id)
    exact hp.div hc (canonRoot_ne_zero38 φ hgk z hz)
  obtain ⟨ρ0, hρ0, hI⟩ :=
    G2032PerO.apply_gen φ hgk m hγ (fun z => psi n φ z / canonRoot38 φ z) hfa
  obtain ⟨ε, hε, hε1, hann⟩ := G2032B1.H_analytic_annulus φ hgk m
  set J : ℂ → ℂ := G2032B1.jk (tauN φ m) ((lamPlus φ m - lamMinus φ m) / 4) with hJ
  set Pu : ℂ → ℂ := fun u => psi n φ (J u) / rootProduct m (φ, J u) * (Complex.I / (2 * u))
    with hPu
  have hdiff : ∀ u : ℂ, 1 - ε < ‖u‖ → ‖u‖ < 1 + ε → DifferentiableAt ℂ Pu u := by
    intro u h1 h2
    obtain ⟨hu0, hmem⟩ := hann u h1 h2
    have hJa : AnalyticAt ℂ J u := by
      rw [hJ]; unfold G2032B1.jk
      exact analyticAt_const.add (analyticAt_const.mul (analyticAt_id.add (analyticAt_id.inv hu0)))
    have hp : AnalyticAt ℂ (fun w => psi n φ (J w)) u :=
      (p6PsiNumerator_entire38 n (sourceF n) φ (J u) (mem_univ _)).comp hJa
    have hr : AnalyticAt ℂ (fun w => rootProduct m (φ, J w)) u :=
      AnalyticAt.comp (g := rootProduct m) (f := fun w => (φ, J w))
        ((G2_021 m).2.1 _ hmem) (analyticAt_const.prod hJa)
    have hq : AnalyticAt ℂ (fun w : ℂ => Complex.I / (2 * w)) u :=
      analyticAt_const.div (analyticAt_const.mul analyticAt_id) (mul_ne_zero two_ne_zero hu0)
    exact ((hp.div hr ((G2_021 m).2.2 _ hmem)).mul hq).differentiableAt
  obtain ⟨ρ1, hρ1a, hρ1b, hρ1c⟩ : ∃ ρ1 : ℝ, 1 < ρ1 ∧ ρ1 ≤ ρ0 ∧ ρ1 < 1 + ε :=
    ⟨min ρ0 (1 + ε / 2), lt_min hρ0 (by linarith), min_le_left _ _,
      lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩
  have hρpos : 0 < ρ1 := by linarith
  have hA := G2032Chain.ellipse_chain (fun z => psi n φ z / canonRoot38 φ z) (tauN φ m)
    (lamPlus φ m - lamMinus φ m) ρ1 hρpos
  have hB := hI ρ1 hρ1a hρ1b
  have hcirc : circleIntegral (fun z => psi n φ z / canonRoot38 φ z) (discC φ m) (discR φ m) =
      circleIntegral (fun u : ℂ => (fun z => psi n φ z / canonRoot38 φ z)
        (tauN φ m + (lamPlus φ m - lamMinus φ m) / 4 * (u + u⁻¹)) *
          ((lamPlus φ m - lamMinus φ m) / 4 * (1 - (u ^ 2)⁻¹))) 0 ρ1 := by
    rw [← hA]; exact hB
  have hsph : circleIntegral (fun u : ℂ => (fun z => psi n φ z / canonRoot38 φ z)
        (tauN φ m + (lamPlus φ m - lamMinus φ m) / 4 * (u + u⁻¹)) *
          ((lamPlus φ m - lamMinus φ m) / 4 * (1 - (u ^ 2)⁻¹))) 0 ρ1 = circleIntegral Pu 0 ρ1 := by
    apply circleIntegral.integral_congr (by linarith)
    intro u hu
    have hnorm : ‖u‖ = ρ1 := by simpa using hu
    have h1 : 1 - ε < ‖u‖ := by rw [hnorm]; linarith
    have h2 : ‖u‖ < 1 + ε := by rw [hnorm]; exact hρ1c
    have hn : 1 < ‖u‖ := by rw [hnorm]; exact hρ1a
    obtain ⟨hu0, hmem⟩ := hann u h1 h2
    have hnot := G2032PerO.jk_not_gap φ hgk m u hn hγ hmem
    obtain ⟨-, -, hB', -⟩ := G2032B1.inv_facts u hn
    have hRne := (G2_021 m).2.2 _ hmem
    show psi n φ (J u) / canonRoot38 φ (J u) * ((lamPlus φ m - lamMinus φ m) / 4 * (1 - (u ^ 2)⁻¹)) =
      psi n φ (J u) / rootProduct m (φ, J u) * (Complex.I / (2 * u))
    rw [canon_split φ hgk m (J u) hnot, hJ, std_jk φ hgk m hγ u hn]
    exact alg_pu _ _ _ _ hRne hh0 hu0 hB'
  have hB3 : circleIntegral Pu 0 1 = circleIntegral Pu 0 ρ1 :=
    G2032Annulus.circleIntegral_const_on_annulus Pu (1 - ε) (1 + ε) 1 ρ1 (by linarith)
      (by linarith) (by linarith) hρ1c hdiff
  have hper : abelianPeriod38 m φ (psi n φ) = circleIntegral Pu 0 1 := by
    show circleIntegral (fun z => psi n φ z / canonRoot38 φ z) (discC φ m) (discR φ m) = _
    rw [hcirc, hsph, ← hB3]
  have hunit := unit_circle Pu (fun z => psi n φ z / rootProduct m (φ, z)) (tauN φ m)
    ((lamPlus φ m - lamMinus φ m) / 4) (fun u => rfl)
  have hd0 : betaGapDensity n m φ 0 = 0 := by unfold betaGapDensity; simp
  have hd1 : betaGapDensity n m φ 1 = 0 := by unfold betaGapDensity; simp
  have harc := arcsine_bank
    (fun t : ℝ => psi n φ (lamMinus φ m + (t:ℂ) * gap φ m) /
        rootProduct m (φ, lamMinus φ m + (t:ℂ) * gap φ m)) (betaGapDensity n m φ)
    (seg_cont n m φ hgk)
    (fun t ht => density_eq n m φ t hgap (mul_pos ht.1 (by linarith [ht.2]))) hd0 hd1
  have hconv : ∫ θ in (0:ℝ)..(2*π), (fun z => psi n φ z / rootProduct m (φ, z))
        (tauN φ m + 2 * ((lamPlus φ m - lamMinus φ m) / 4) * (Real.cos θ : ℂ)) =
      ∫ θ in (0:ℝ)..(2*π), psi n φ (lamMinus φ m + (((Real.cos θ + 1) / 2 : ℝ) : ℂ) * gap φ m) /
        rootProduct m (φ, lamMinus φ m + (((Real.cos θ + 1) / 2 : ℝ) : ℂ) * gap φ m) := by
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    dsimp only
    have he : tauN φ m + 2 * ((lamPlus φ m - lamMinus φ m) / 4) * (Real.cos θ : ℂ) =
        lamMinus φ m + (((Real.cos θ + 1) / 2 : ℝ) : ℂ) * gap φ m := by
      rw [hτ]; unfold gap; push_cast; ring
    rw [he]
  rw [hper, hunit, hconv, harc]
  unfold betaGapIntegral
  ring

end
end G3005C2

theorem g3005_c2_contour (n m : ℤ) (φ : SourcePotential) (hgap : gap φ.1 m ≠ 0) :
    ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
      betaGapIntegral n m φ.1 = s * (Real.pi : ℂ) * (if m = n then 1 else 0) := by
  refine ⟨-1, Or.inr rfl, ?_⟩
  have h := G3005C2.period_eq n m φ.1 φ.2 hgap
  by_cases hmn : m = n
  · subst hmn
    have h2 := (G2_072 φ.1 φ.2 m).2
    rw [h2] at h
    simp only [if_true]
    linear_combination (1/2 : ℂ) * h
  · have hnm : n ≠ m := fun e => hmn e.symm
    have h0 := (p6PsiNumerator_integrable_and_off_diagonal_periods38 n φ.1
      (sourceFamily.W_gk φ.2) (sourceF n) (sourceFamily.F_zero n φ.1 φ.2)).2 m hnm
    have h2 : abelianPeriod38 m φ.1 (psi n φ.1) = 0 := h0
    rw [h2] at h
    simp only [hmn, if_false]
    linear_combination (1/2 : ℂ) * h

end NlsGge.GKDefinitionDesign
