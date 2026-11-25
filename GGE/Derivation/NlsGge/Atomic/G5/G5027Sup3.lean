import Mathlib
import NlsGge.Atomic.G5.G5027Sup1
import NlsGge.Atomic.G5.G5027Sup2

/- G5-027 SUPPORT 3 `G5027Sup3` (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5027Sup3.lean, namespace NlsGge.GKDefinitionDesign.G5027Aux.
   Off-diagonal representation at a point with nonzero delta-fixed root (S3a of PLAN.md):
     offDiagonalBeta n m phi = tipRoot m b c phi * segK (tipG n m b c) a mu_m phi.
   Route: landed G3015Aux.segment_integral with rw := tipRoot (sign identity holds by definition of tipRoot) and
   rseg t := sqrtB c (a + t(mu - a) - b); its integrand is rewritten by the landed G3015Aux.factor
   (psi_n = 2 I rootProduct_m (nR - z) betaZeta on the isolating disc), and tipRoot is pulled out of the integral. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
namespace G5027Aux
noncomputable section

theorem offdiag_rep (n m : ℤ) (hmn : m ≠ n) (a b : PotPair → ℂ) (c : ℂ) (hc : c ≠ 0)
    (φ : PotPair) (hφ : φ ∈ sourceW \ collapsedSet m) (hbA : AnalyticAt ℂ b φ)
    (hab : ({a φ, b φ} : Set ℂ) = {lamMinus φ m, lamPlus φ m})
    (hslit : ∀ t ∈ Icc (0 : ℝ) 1,
      c * (a φ + (t : ℂ) * (muSeq φ m - a φ) - b φ) ∈ Complex.slitPlane)
    (hzb : ∀ t ∈ Icc (0 : ℝ) 1, a φ + (t : ℂ) * (muSeq φ m - a φ) - b φ ≠ 0)
    (hsq : tipRoot m b c φ ^ 2 = muSeq φ m - a φ) (hne : tipRoot m b c φ ≠ 0) :
    offDiagonalBeta n m φ =
      tipRoot m b c φ * segK (tipG n m b c) a (fun ψ => muSeq ψ m) φ := by
  have hW : φ ∈ sourceW := hφ.1
  have hgk : φ ∈ gkW := sourceFamily.W_gk hW
  have hγ : lamPlus φ m - lamMinus φ m ≠ 0 := G3024Endpoint.gap_ne m φ hφ
  obtain ⟨cc, N, hg, hspec⟩ := isolating_family38 φ hgk
  have haD : a φ ∈ ball (discC φ m) (discR φ m) := mem_disc_of_pair m φ hgk (a φ) (b φ) hab
  have hμD : muSeq φ m ∈ ball (discC φ m) (discR φ m) := (hspec.1 m).2.1
  have hzD : ∀ t ∈ Icc (0 : ℝ) 1, a φ + (t : ℂ) * (muSeq φ m - a φ) ∈ ball (discC φ m) (discR φ m) :=
    fun t ht => seg_mem_ball haD hμD ht
  have hdom : ∀ z ∈ ball (discC φ m) (discR φ m), (φ, z) ∈ a5OmittedRootDomain38 m := fun z hz =>
    ⟨hgk, fun k hk => closedBall_avoids_other_gaps φ hgk m k hk z (ball_subset_closedBall hz)⟩
  set rs : ℝ → ℂ := fun t => G3014Aux.sqrtB c (a φ + (t : ℂ) * (muSeq φ m - a φ) - b φ) with hrs
  have hρ0 : ∀ t ∈ Icc (0 : ℝ) 1, rs t ≠ 0 := fun t ht => G3014Aux.sqrtB_ne hc (hzb t ht)
  have hρsq : ∀ t ∈ Icc (0 : ℝ) 1, rs t ^ 2 = a φ + (t : ℂ) * (muSeq φ m - a φ) - b φ :=
    fun t _ => G3014Aux.sqrtB_sq hc _
  have hρc : ContinuousOn rs (Icc (0 : ℝ) 1) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    have hsA : AnalyticAt ℂ (fun y : ℂ => G3014Aux.sqrtB c y)
        (a φ + (t : ℂ) * (muSeq φ m - a φ) - b φ) :=
      G3014Aux.sqrtB_analyticAt (h := fun y : ℂ => y) analyticAt_id (hslit t ht)
    have hp : Continuous (fun s : ℝ => a φ + (s : ℂ) * (muSeq φ m - a φ) - b φ) := by fun_prop
    exact ContinuousAt.comp (g := fun y : ℂ => G3014Aux.sqrtB c y)
      (f := fun s : ℝ => a φ + (s : ℂ) * (muSeq φ m - a φ) - b φ) hsA.continuousAt hp.continuousAt
  have hrP0 : rootProduct m (φ, muSeq φ m) ≠ 0 := (G2_021 m).2.2 _ (hdom _ hμD)
  have hS1 : G3014Aux.sqrtB c (muSeq φ m - b φ) ≠ 0 := by
    have h := hzb 1 ⟨zero_le_one, le_rfl⟩
    refine G3014Aux.sqrtB_ne hc ?_
    intro h'
    apply h
    push_cast
    linear_combination h'
  have hrs1 : rs 1 = G3014Aux.sqrtB c (muSeq φ m - b φ) := by
    simp only [hrs]
    congr 1
    push_cast
    ring
  have hsign : 2 * Complex.I * rootProduct m (φ, muSeq φ m) * tipRoot m b c φ * rs 1 =
      antiDiscrim φ (muSeq φ m) := by
    rw [hrs1, tipRoot]
    field_simp
  -- pointwise identity of the integrands
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1,
      ((normalizedRoot n m φ - (a φ + (t : ℂ) * (muSeq φ m - a φ))) *
        betaZeta n m φ (a φ + (t : ℂ) * (muSeq φ m - a φ)) * tipRoot m b c φ / rs t) /
        (Real.sqrt t : ℂ) =
      tipRoot m b c φ * (tipG n m b c (φ, a φ + (t : ℂ) * (muSeq φ m - a φ)) /
        (Real.sqrt t : ℂ)) := by
    intro t ht
    have hz := hzD t ht
    have hf := G3015Aux.factor n m hmn φ hW hγ _ hz
    have hrP : rootProduct m (φ, a φ + (t : ℂ) * (muSeq φ m - a φ)) ≠ 0 := (G2_021 m).2.2 _ (hdom _ hz)
    have hr := hρ0 t ht
    simp only [tipG]
    rw [hf]
    simp only [hrs] at hr ⊢
    by_cases hs : (Real.sqrt t : ℂ) = 0
    · rw [hs]; simp
    · field_simp
  -- integrability of the tipG integrand
  have hgc : ContinuousOn (fun t : ℝ => tipG n m b c (φ, a φ + (t : ℂ) * (muSeq φ m - a φ)))
      (Icc (0 : ℝ) 1) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    have hA := tipG_analyticAt n m b c hc φ _ hW (hzD t ht) hbA (hslit t ht) (hzb t ht)
    have hp : Continuous (fun s : ℝ => ((φ, a φ + (s : ℂ) * (muSeq φ m - a φ)) : PotPair × ℂ)) := by
      fun_prop
    exact ContinuousAt.comp (g := tipG n m b c)
      (f := fun s : ℝ => ((φ, a φ + (s : ℂ) * (muSeq φ m - a φ)) : PotPair × ℂ))
      hA.continuousAt hp.continuousAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  have hI : IntervalIntegrable (fun t : ℝ =>
      tipG n m b c (φ, a φ + (t : ℂ) * (muSeq φ m - a φ)) / (Real.sqrt t : ℂ)) volume 0 1 :=
    integrable_div_sqrt _ C (hgc.mono Ioc_subset_Icc_self) (fun t ht => hC t (Ioc_subset_Icc_self ht))
  have hint : IntervalIntegrable (fun t : ℝ =>
      ((normalizedRoot n m φ - (a φ + (t : ℂ) * (muSeq φ m - a φ))) *
        betaZeta n m φ (a φ + (t : ℂ) * (muSeq φ m - a φ)) * tipRoot m b c φ / rs t) /
        (Real.sqrt t : ℂ)) volume 0 1 := by
    refine (hI.const_mul (tipRoot m b c φ)).congr ?_
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    exact (hpt t (Ioc_subset_Icc_self ht)).symm
  rw [G3015Aux.segment_integral n m hmn φ hW hγ (a φ) (b φ) (tipRoot m b c φ) rs hab hne hsq hρc
    hρ0 hρsq hsign hint]
  rw [intervalIntegral.integral_congr (g := fun t : ℝ => tipRoot m b c φ *
      (tipG n m b c (φ, a φ + (t : ℂ) * (muSeq φ m - a φ)) / (Real.sqrt t : ℂ))) (fun t ht => by
      rw [Set.uIcc_of_le zero_le_one] at ht
      exact hpt t ht), intervalIntegral.integral_const_mul]
  rfl

end
end G5027Aux
end NlsGge.GKDefinitionDesign
