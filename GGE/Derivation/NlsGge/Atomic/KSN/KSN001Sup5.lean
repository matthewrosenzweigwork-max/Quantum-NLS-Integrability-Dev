import Mathlib
import NlsGge.Atomic.KSN.KSN001Host
import NlsGge.Atomic.KSN.KSN001Sup1
import NlsGge.Atomic.G4.G4041
import NlsGge.Atomic.KSN.KSN001Sup2
import NlsGge.Atomic.KSN.KSN001Sup3
import NlsGge.Atomic.X.X006Real
import NlsGge.Atomic.G5.G5040
import NlsGge.Atomic.G5.G5018Sup1
import NlsGge.ThirdConsultation.G5.G5017Support1

/- KSN-001 SUPPORT 5 PRODUCTION02 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/KSN/KSN001Sup5.lean,
   namespace NlsGge.ThirdConsultation.KSN.KSN001Aux.
   Conjunct 1 of KSN001_main (followup12 STATEMENTS/KSN.md, verbatim): the complex canonical bracket on all of sourceBetaW.
   Route (proof development/KSN001_STOP.md, proof development/M1_DECISION.md option A, owner-approved):
   - bilinear expansion of pairPoisson for the two scalar Birkhoff combinations of cartesianX/Y (differentiable on
     sourceBetaW by landed G4041) gives (1/2)({X_n,X_m} + i{X_n,Y_m} - i{Y_n,X_m} + {Y_n,Y_m});
   - at real points the landed G5040 brackets and antisymmetry (G5018Sup1 pairPoissonCLM_antisymm) give -i δ_nm;
   - the difference is analytic on sourceBetaW (M3, KSN001Sup3) and vanishes on the real slice, so it vanishes on the
     preconnected neighbourhood of each point supplied by M1 (X006Real sourceBetaW_realConnected), by M2 (KSN001Sup2). -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.G5017Support1

namespace NlsGge.ThirdConsultation.KSN
namespace KSN001Aux
noncomputable section

/-- The bracket is bilinear in the derivatives: expansion for two-term linear combinations. -/
theorem pairPoisson_lin (f1 f2 g1 g2 : PotPair → ℂ) (c1 c2 d1 d2 : ℂ) (φ : PotPair)
    (hf1 : DifferentiableAt ℂ f1 φ) (hf2 : DifferentiableAt ℂ f2 φ)
    (hg1 : DifferentiableAt ℂ g1 φ) (hg2 : DifferentiableAt ℂ g2 φ) :
    pairPoisson (fun ψ => c1 * f1 ψ + c2 * f2 ψ) (fun ψ => d1 * g1 ψ + d2 * g2 ψ) φ =
      c1 * d1 * pairPoisson f1 g1 φ + c1 * d2 * pairPoisson f1 g2 φ +
        c2 * d1 * pairPoisson f2 g1 φ + c2 * d2 * pairPoisson f2 g2 φ := by
  let K : (PotPair →L[ℂ] ℂ) →L[ℂ] PotPair :=
    ((-Complex.I) • (ContinuousLinearMap.snd ℂ PhysicalL2 PhysicalL2).comp pairGradientL).prod
      (Complex.I • (ContinuousLinearMap.fst ℂ PhysicalL2 PhysicalL2).comp pairGradientL)
  have key : ∀ f g : PotPair → ℂ, pairPoisson f g φ = (fderiv ℂ f φ) (K (fderiv ℂ g φ)) :=
    fun f g => rfl
  have hF : fderiv ℂ (fun ψ => c1 * f1 ψ + c2 * f2 ψ) φ = c1 • fderiv ℂ f1 φ + c2 • fderiv ℂ f2 φ := by
    rw [fderiv_fun_add (hf1.const_mul c1) (hf2.const_mul c2), fderiv_const_mul hf1, fderiv_const_mul hf2]
  have hG : fderiv ℂ (fun ψ => d1 * g1 ψ + d2 * g2 ψ) φ = d1 • fderiv ℂ g1 φ + d2 • fderiv ℂ g2 φ := by
    rw [fderiv_fun_add (hg1.const_mul d1) (hg2.const_mul d2), fderiv_const_mul hg1, fderiv_const_mul hg2]
  rw [key, key f1 g1, key f1 g2, key f2 g1, key f2 g2, hF, hG, map_add, map_smul, map_smul]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul,
    map_add, map_smul]
  ring

/-- Antisymmetry of the bracket of two functions at a point. -/
theorem pairPoisson_antisymm_at (f g : PotPair → ℂ) (φ : PotPair) :
    pairPoisson f g φ = -pairPoisson g f φ :=
  pairPoissonCLM_antisymm (fderiv ℂ f φ) (fderiv ℂ g φ)

theorem scalarBirkhoff_true_eq (n : ℤ) :
    scalarBirkhoff true n = fun ψ => (1 / (Real.sqrt 2 : ℂ)) * cartesianX n ψ +
      (-Complex.I / (Real.sqrt 2 : ℂ)) * cartesianY n ψ := by
  funext ψ
  unfold scalarBirkhoff
  rw [if_pos rfl]
  ring

theorem scalarBirkhoff_false_eq (m : ℤ) :
    scalarBirkhoff false m = fun ψ => (1 / (Real.sqrt 2 : ℂ)) * cartesianX m ψ +
      (Complex.I / (Real.sqrt 2 : ℂ)) * cartesianY m ψ := by
  funext ψ
  unfold scalarBirkhoff
  rw [if_neg Bool.false_ne_true]
  ring

theorem scalarBirkhoff_analytic (b : Bool) (n : ℤ) :
    AnalyticOnNhd ℂ (scalarBirkhoff b n) sourceBetaW := by
  intro φ hφ
  have hX := (G4041 n).1 φ hφ
  have hY := (G4041 n).2 φ hφ
  cases b
  · rw [scalarBirkhoff_false_eq]
    exact (analyticAt_const.mul hX).add (analyticAt_const.mul hY)
  · rw [scalarBirkhoff_true_eq]
    exact (analyticAt_const.mul hX).add (analyticAt_const.mul hY)

/-- The bracket identity at the points of sourceBetaW in terms of the Cartesian brackets. -/
theorem bracket_expand (n m : ℤ) (φ : PotPair) (hφ : φ ∈ sourceBetaW) :
    pairPoisson (scalarBirkhoff true n) (scalarBirkhoff false m) φ =
      (1 / (Real.sqrt 2 : ℂ)) * (1 / (Real.sqrt 2 : ℂ)) * pairPoisson (cartesianX n) (cartesianX m) φ +
      (1 / (Real.sqrt 2 : ℂ)) * (Complex.I / (Real.sqrt 2 : ℂ)) *
        pairPoisson (cartesianX n) (cartesianY m) φ +
      (-Complex.I / (Real.sqrt 2 : ℂ)) * (1 / (Real.sqrt 2 : ℂ)) *
        pairPoisson (cartesianY n) (cartesianX m) φ +
      (-Complex.I / (Real.sqrt 2 : ℂ)) * (Complex.I / (Real.sqrt 2 : ℂ)) *
        pairPoisson (cartesianY n) (cartesianY m) φ := by
  rw [scalarBirkhoff_true_eq, scalarBirkhoff_false_eq]
  exact pairPoisson_lin _ _ _ _ _ _ _ _ φ ((G4041 n).1 φ hφ).differentiableAt
    ((G4041 n).2 φ hφ).differentiableAt ((G4041 m).1 φ hφ).differentiableAt
    ((G4041 m).2 φ hφ).differentiableAt

/-- Conjunct 1 on the real slice. -/
theorem bracket_real (u : PhysicalL2) (n m : ℤ) :
    pairPoisson (scalarBirkhoff true n) (scalarBirkhoff false m) (realSlice u) =
      if n = m then -Complex.I else 0 := by
  have hB : realSlice u ∈ sourceBetaW := sourceFamily.V_real (Set.mem_range_self u)
  rw [bracket_expand n m _ hB]
  obtain ⟨h1, h2, h3⟩ := G5040 u n m
  obtain ⟨-, h4, -⟩ := G5040 u m n
  rw [pairPoisson_antisymm_at (cartesianY n) (cartesianX m), h1, h2, h3, h4]
  have hinv : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, sqrt2_sq_complex]
    norm_num
  by_cases hnm : n = m
  · subst hnm
    simp only [eq_self_iff_true, if_true]
    linear_combination (-2 * Complex.I) * hinv
  · have hmn : ¬ m = n := fun h => hnm h.symm
    simp only [hnm, hmn, if_false]
    ring

/-- Conjunct 1 of KSN001_main. -/
theorem bracket_canonical : ∀ φ ∈ sourceBetaW, ∀ n m : ℤ,
    pairPoisson (scalarBirkhoff true n) (scalarBirkhoff false m) φ =
      if n = m then -Complex.I else 0 := by
  intro φ hφ n m
  obtain ⟨S, hSo, hSc, hSsub, hφS, u₀, hu₀⟩ := sourceBetaW_realConnected φ hφ
  have hA : AnalyticOnNhd ℂ (fun ψ => pairPoisson (scalarBirkhoff true n) (scalarBirkhoff false m) ψ -
      (if n = m then -Complex.I else 0)) S := by
    intro ψ hψ
    exact ((pairPoisson_analyticOnNhd _ _ (scalarBirkhoff_analytic true n)
      (scalarBirkhoff_analytic false m)) ψ (hSsub hψ)).sub analyticAt_const
  have h := analyticOnNhd_eq_zero_of_realSlice S hSo hSc _ hA u₀ hu₀
    (fun u _ => by rw [bracket_real, sub_self]) φ hφS
  exact sub_eq_zero.mp h

end
end KSN001Aux
end NlsGge.ThirdConsultation.KSN
