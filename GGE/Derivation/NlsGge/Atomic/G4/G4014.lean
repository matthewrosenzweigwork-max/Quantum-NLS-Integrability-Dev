import Mathlib
import NlsGge.ThirdConsultation.G3.G3024Endpoint
import NlsGge.Atomic.G4.G4036Host
import NlsGge.Atomic.G4.G4036
import NlsGge.GK38.TauGamma

/- G4_014 PRODUCTION01 (proof development, AUTHOR; not semantically reviewed by its author).
   Target NlsGge/Atomic/G4/G4014.lean, namespace NlsGge.GKDefinitionDesign.
   Head `G4014` VERBATIM from the design STATEMENTS/G4.md:49-71 (byte-identical in followup1..10; no Pro round 4-12 entry restates G4-014).
   The only lexical difference is none: the head has no `λ`.
   Route (see G4014_ROUTE.md): the landed-candidate support `G3024Endpoint.g3024_endpoint_package` (the content of G3-024 for the
   Cartesian exponential, endpoint set included) gives analytic-integral e and labels a, b with {a, b} = {lamMinus, lamPlus}
   and Z+ = (b - a) exp(I e), where Z+ = gk16ActualScalarZPlus38 sourceF n.
   (1) bridge (new here): cartesianZExtended n 1 = Z+ and cartesianZExtended n (-1) = Z- on gkW (ownCorrection is, term by term,
       the Armstrong Cauchy coefficient, using tauN = (lamMinus+lamPlus)/2 and gamma2 = gap^2 on gkW);
   (2) Z+ * Z- = gamma2 = (b - a)^2 gives Z- = (b - a) exp(-I e);
   (3) analyticity of rho^- = a, rho^+ = b: a + b = 2 tauN (analytic, TauGamma), b - a = cartesianZExtended n 1 * exp(-I e)
       (analytic by landed G4036), so a = tauN - (b - a)/2 and b = tauN + (b - a)/2.
   No analytic anchor is used. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
namespace G4014Aux
noncomputable section

theorem ownCorrection_eq_gk16 (n : ℤ) (φ : PotPair) (hgk : φ ∈ gkW) (lam : ℂ) :
    ownCorrection n φ lam =
      gk16OwnCorrectionCoefficient38 φ n (p2Extend38 n (sourceF n φ)) (discC φ n) (discR φ n) lam := by
  have ht : tauN φ n = (lamMinus φ n + lamPlus φ n) / 2 := by
    rw [tauN_value38 φ hgk n]; ring
  have hg : gamma2 φ n = (lamPlus φ n - lamMinus φ n) ^ 2 := gamma2_value38 φ hgk n
  simp only [ownCorrection, gk16OwnCorrectionCoefficient38, rawBetaStdCauchyCoefficient38,
    rawBetaBoundaryCauchy38, normalizedZeta, standardRoot, ht, hg]

theorem cartZ_plus (n : ℤ) (φ : PotPair) (hgk : φ ∈ gkW) :
    cartesianZExtended n 1 φ = gk16ActualScalarZPlus38 sourceF n φ := by
  unfold cartesianZExtended gk16ActualScalarZPlus38
  rw [if_pos rfl, ownCorrection_eq_gk16 n φ hgk]
  rfl

theorem cartZ_minus (n : ℤ) (φ : PotPair) (hgk : φ ∈ gkW) :
    cartesianZExtended n (-1) φ = gk16ActualScalarZMinus38 sourceF n φ := by
  unfold cartesianZExtended gk16ActualScalarZMinus38
  rw [if_neg (by norm_num), ownCorrection_eq_gk16 n φ hgk]
  rfl

end
end G4014Aux

noncomputable section

theorem G4014 (n : ℤ) (φ₀ : PotPair) (hφ₀ : φ₀ ∈ sourceBetaW)
    (hgap : lamPlus φ₀ n ≠ lamMinus φ₀ n) :
  ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ IsOpen V ∧ V ⊆ sourceBetaW ∧
  ∃ ρminus ρplus η : PotPair → ℂ,
    AnalyticOnNhd ℂ ρminus V ∧ AnalyticOnNhd ℂ ρplus V ∧ AnalyticOnNhd ℂ η V ∧
    ∀ φ ∈ V,
      ((ρminus φ = lamMinus φ n ∧ ρplus φ = lamPlus φ n) ∨
       (ρminus φ = lamPlus φ n ∧ ρplus φ = lamMinus φ n)) ∧
      ρminus φ ≠ ρplus φ ∧
      (∀ a : ℤ, (a = 1 ∨ a = -1) →
        cartesianZExtended n a φ = (ρplus φ - ρminus φ) *
          Complex.exp ((a : ℂ) * Complex.I * η φ)) := by
  have hW : φ₀ ∈ sourceW := sourceFamily.V_W hφ₀
  have hnc : φ₀ ∈ sourceW \ collapsedSet n := by
    refine ⟨hW, fun hc => hgap ?_⟩
    have h2 : gamma2 φ₀ n = 0 := hc.2
    rw [gamma2_value38 φ₀ (sourceFamily.W_gk hW) n] at h2
    have := pow_eq_zero_iff (two_ne_zero) |>.mp h2
    exact sub_eq_zero.mp this
  obtain ⟨V, a, b, e, hVo, hφV, hVsub, hpair, hAne, hZ⟩ :
      ∃ (V : Set PotPair) (a b e : PotPair → ℂ), IsOpen V ∧ φ₀ ∈ V ∧ V ⊆ sourceW \ collapsedSet n ∧
        (∀ φ ∈ V, ({a φ, b φ} : Set ℂ) = {lamMinus φ n, lamPlus φ n}) ∧
        AnalyticOnNhd ℂ e V ∧
        ∀ φ ∈ V, gk16ActualScalarZPlus38 sourceF n φ = (b φ - a φ) * Complex.exp (Complex.I * e φ) := by
    obtain ⟨V, a, b, rω, rseg, hVo, hφV, hVsub, hpair, hAn, hZ⟩ :=
      G3024Endpoint.g3024_endpoint_package n φ₀ hnc
    exact ⟨V, a, b, _, hVo, hφV, hVsub, hpair, hAn, hZ⟩
  have hVB : IsOpen (V ∩ sourceBetaW) := hVo.inter sourceFamily.V_open
  have hφVB : φ₀ ∈ V ∩ sourceBetaW := ⟨hφV, hφ₀⟩
  -- pointwise facts on V ∩ sourceBetaW
  have key : ∀ φ ∈ V ∩ sourceBetaW,
      ((a φ = lamMinus φ n ∧ b φ = lamPlus φ n) ∨ (a φ = lamPlus φ n ∧ b φ = lamMinus φ n)) ∧
      (b φ - a φ) ^ 2 = (lamPlus φ n - lamMinus φ n) ^ 2 ∧
      b φ - a φ ≠ 0 ∧
      a φ + b φ = lamMinus φ n + lamPlus φ n := by
    intro φ hφ
    have hc := Set.pair_eq_pair_iff.1 (hpair φ hφ.1)
    have hgapne : lamPlus φ n - lamMinus φ n ≠ 0 := G3024Endpoint.gap_ne n φ (hVsub hφ.1)
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨Or.inl ⟨h1, h2⟩, ?_, ?_, ?_⟩
      · rw [h1, h2]
      · rw [h1, h2]; exact hgapne
      · rw [h1, h2]
    · refine ⟨Or.inr ⟨h1, h2⟩, ?_, ?_, ?_⟩
      · rw [h1, h2]; ring
      · rw [h1, h2]
        intro h
        apply hgapne
        linear_combination -h
      · rw [h1, h2]; ring
  have hgkB : ∀ φ ∈ V ∩ sourceBetaW, φ ∈ gkW := fun φ hφ =>
    sourceFamily.W_gk (sourceFamily.V_W hφ.2)
  -- b - a = Z+ * exp(-I e)
  have hdiff : ∀ φ ∈ V ∩ sourceBetaW,
      b φ - a φ = cartesianZExtended n 1 φ * Complex.exp (-(Complex.I * e φ)) := by
    intro φ hφ
    rw [G4014Aux.cartZ_plus n φ (hgkB φ hφ), hZ φ hφ.1, mul_assoc, ← Complex.exp_add,
      add_neg_cancel, Complex.exp_zero, mul_one]
  have hZan : AnalyticOnNhd ℂ (cartesianZExtended n 1) (V ∩ sourceBetaW) :=
    (G4036 n 1 (Or.inl rfl)).mono inter_subset_right
  have hean : AnalyticOnNhd ℂ e (V ∩ sourceBetaW) := hAne.mono inter_subset_left
  have hDan : AnalyticOnNhd ℂ (fun φ => cartesianZExtended n 1 φ * Complex.exp (-(Complex.I * e φ)))
      (V ∩ sourceBetaW) := by
    intro φ hφ
    exact (hZan φ hφ).mul (analyticAt_const.mul (hean φ hφ)).neg.cexp
  have htau : AnalyticOnNhd ℂ (fun φ : PotPair => tauN φ n) (V ∩ sourceBetaW) :=
    fun φ hφ => tauN_analytic n φ (hgkB φ hφ)
  have htauv : ∀ φ ∈ V ∩ sourceBetaW, tauN φ n = (lamMinus φ n + lamPlus φ n) / 2 := fun φ hφ => by
    rw [tauN_value38 φ (hgkB φ hφ) n]; ring
  refine ⟨V ∩ sourceBetaW, hVB.mem_nhds hφVB, hVB, inter_subset_right, a, b, e, ?_, ?_, ?_, ?_⟩
  · -- a = tauN - (b - a)/2
    have : AnalyticOnNhd ℂ (fun φ => tauN φ n - (cartesianZExtended n 1 φ *
        Complex.exp (-(Complex.I * e φ))) / 2) (V ∩ sourceBetaW) :=
      htau.sub (hDan.div analyticOnNhd_const (fun _ _ => two_ne_zero))
    refine this.congr hVB fun φ hφ => ?_
    rw [← hdiff φ hφ, htauv φ hφ]
    have := (key φ hφ).2.2.2
    linear_combination (-1 / 2 : ℂ) * this
  · have : AnalyticOnNhd ℂ (fun φ => tauN φ n + (cartesianZExtended n 1 φ *
        Complex.exp (-(Complex.I * e φ))) / 2) (V ∩ sourceBetaW) :=
      htau.add (hDan.div analyticOnNhd_const (fun _ _ => two_ne_zero))
    refine this.congr hVB fun φ hφ => ?_
    rw [← hdiff φ hφ, htauv φ hφ]
    have := (key φ hφ).2.2.2
    linear_combination (-1 / 2 : ℂ) * this
  · exact hean
  · intro φ hφ
    obtain ⟨hlab, hsq, hne, -⟩ := key φ hφ
    have hgk := hgkB φ hφ
    refine ⟨hlab, ?_, ?_⟩
    · intro h
      apply hne
      rw [h, sub_self]
    · intro k hk
      have hP : cartesianZExtended n 1 φ = (b φ - a φ) * Complex.exp (Complex.I * e φ) := by
        rw [G4014Aux.cartZ_plus n φ hgk, hZ φ hφ.1]
      have hprod := gk16_actual_scalar_models_product38 sourceF n φ hgk
      have hg2 := gamma2_value38 φ hgk n
      rw [← G4014Aux.cartZ_plus n φ hgk, ← G4014Aux.cartZ_minus n φ hgk] at hprod
      have hM : cartesianZExtended n (-1) φ = (b φ - a φ) * Complex.exp (-(Complex.I * e φ)) := by
        have hEE : Complex.exp (Complex.I * e φ) * Complex.exp (-(Complex.I * e φ)) = 1 := by
          rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
        have hnz : (b φ - a φ) * Complex.exp (Complex.I * e φ) ≠ 0 :=
          mul_ne_zero hne (Complex.exp_ne_zero _)
        apply mul_left_cancel₀ hnz
        rw [← hP, hprod, hg2, ← hsq, hP]
        linear_combination (-(b φ - a φ) ^ 2) * hEE
      rcases hk with rfl | rfl
      · rw [hP]
        simp
      · rw [hM]
        have : (((-1 : ℤ) : ℂ)) * Complex.I * e φ = -(Complex.I * e φ) := by push_cast; ring
        rw [this]

end
end NlsGge.GKDefinitionDesign
