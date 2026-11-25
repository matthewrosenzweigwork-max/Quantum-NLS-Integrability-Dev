import Mathlib
import NlsGge.Atomic.G6.G6016Host
import NlsGge.Atomic.G6.G6020
import NlsGge.Atomic.G2.G2029
import NlsGge.Atomic.G1.G1069
import NlsGge.GK38.ActionRealBridge
import NlsGge.GK38.GradFundamental
import NlsGge.GK38.IsolatingFamily
import NlsGge.Atomic.G5.G5017Host
import NlsGge.ThirdConsultation.G5.G5017Support1
import NlsGge.Atomic.G5.G5012Sup1
import NlsGge.Atomic.G5.G5032Sup1

/- G6-017 SUPPORT 1 CORE (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G6/G6017Sup1Core.lean, namespace NlsGge.GKDefinitionDesign.G6017Aux.
   GK Theorem 20.1 (discriminant invariance along the I_n rotation), closure landed + G6016Host:
   (1) `pairPoisson_discrim_action`: {Delta(lam), I_n} = 0 at every phi in gkW, by the G5-017 argument with the
       G1-069 discriminant commutation in place of the action commutation: G2-029 writes dI_n as the contour integral
       of gradRootQuotient, the bracket functional commutes with the circle integral, and each integrand vanishes by G1-069;
   (2) `realSlice_actionField`: the real slice of the physical field X_{I_n} = -(i/2) grad I_n is the pair Hamiltonian
       field of gkActionC38 . n (landed action_real_bridge, gradient_realSlice_re, G5032Sup1 real-covector identity);
   (3) `core17`: G6-017 head from the G6-016 head (hypothesis H16 of its exact type, discharged in G6017):
       d/ds Delta(lam, c(s)) = dDelta(realSlice X_{I_n}) = {Delta(lam), I_n} = 0, constant by is_const_of_deriv_eq_zero,
       and c(0) = u. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open NlsGge.GK38.PoissonSpectral38
open NlsGge.GK38.ActionGradient
open NlsGge.ThirdConsultation.G5017Support1
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
namespace G6017Aux
noncomputable section

/-- {Delta(lam), I_n} = 0 (GK 18.1 / 20.1). -/
theorem pairPoisson_discrim_action (φ : PotPair) (hφ : φ ∈ gkW) (lam : ℂ) (n : ℤ) :
    pairPoisson (fun ψ : PotPair => discrim ψ lam) (fun ψ : PotPair => gkActionC38 ψ n) φ = 0 := by
  obtain ⟨hint, hfd, -⟩ := G2_029 φ hφ n
  have hn : fderiv ℂ (fun ψ : PotPair => gkActionC38 ψ n) φ =
      -(1 / (Real.pi : ℂ)) • circleIntegral (gradRootQuotient φ) (discC φ n) (discR φ n) :=
    hfd.fderiv
  let J : PotPair →L[ℂ] PotPair :=
    ((-Complex.I) • ContinuousLinearMap.snd ℂ PhysicalL2 PhysicalL2).prod
      (Complex.I • ContinuousLinearMap.fst ℂ PhysicalL2 PhysicalL2)
  let S : (PotPair →L[ℂ] ℂ) →L[ℂ] ℂ :=
    ((fderiv ℂ (fun ψ : PotPair => discrim ψ lam) φ).comp J).comp pairGradientL
  have hS : pairPoisson (fun ψ : PotPair => discrim ψ lam) (fun ψ : PotPair => gkActionC38 ψ n) φ =
      S (fderiv ℂ (fun ψ : PotPair => gkActionC38 ψ n) φ) := rfl
  have hz : ∀ z : ℂ, S (gradRootQuotient φ z) = 0 := by
    intro z
    have hJ : J (gradDiscrimL2 φ z) = spectralDiscrimHamField38 φ z := rfl
    have h1 : S (gradDiscrimCLM φ z) = 0 := by
      change (fderiv ℂ (fun ψ : PotPair => discrim ψ lam) φ)
        (J (pairGradientCLM (gradDiscrimCLM φ z))) = 0
      rw [pairGradientCLM_gradDiscrimCLM, hJ, (hasFDerivAt_discrim lam φ).fderiv]
      exact (G1_069 φ lam z).2.2.trans (G1_069 φ lam z).2.1
    unfold gradRootQuotient
    rw [map_smul, h1, smul_zero]
  have hz' : (fun z : ℂ => S (gradRootQuotient φ z)) = fun _ => 0 := funext hz
  rw [hS, hn, map_smul, clm_circleIntegral_comm S hint, hz']
  simp [circleIntegral]

/-- The real slice of X_{I_n} is the pair Hamiltonian field of the analytic action. -/
theorem realSlice_actionField (v : PhysicalL2) (n : ℤ) :
    realSlice (physicalHamiltonianField (fun w : PhysicalL2 => actualGapActionAllE02_38 w n) v) =
      pairHamiltonianField (fun ψ : PotPair => gkActionC38 ψ n) (realSlice v) := by
  have hφ : realSlice v ∈ gkW := realSlice_mem_gkW v
  have hd : DifferentiableAt ℂ (fun ψ : PotPair => gkActionC38 ψ n) (realSlice v) :=
    (G2_029 (realSlice v) hφ n).2.1.differentiableAt
  have hfun : (fun w : PhysicalL2 => actualGapActionAllE02_38 w n) =
      fun w : PhysicalL2 => (gkActionC38 (realSlice w) n).re := by
    funext w
    rw [ActionRealBridge.action_real_bridge w n, Complex.ofReal_re]
  have hgr : gradient (fun w : PhysicalL2 => actualGapActionAllE02_38 w n) v =
      pairGradientProjection (pairGradient (fun ψ : PotPair => gkActionC38 ψ n) (realSlice v)) := by
    rw [hfun]
    exact gradient_realSlice_re (fun ψ : PotPair => gkActionC38 ψ n) v hd
  have hstar : star (pairGradient (fun ψ : PotPair => gkActionC38 ψ n) (realSlice v)).2 =
      (pairGradient (fun ψ : PotPair => gkActionC38 ψ n) (realSlice v)).1 :=
    G5032Sup1.star_pairGradientCLM_snd _
      (G5032Sup1.fderiv_realSlice_im _ (fun w => by
        simp only [ActionRealBridge.action_real_bridge w n, Complex.ofReal_im]) v)
  set G : PotPair := pairGradient (fun ψ : PotPair => gkActionC38 ψ n) (realSlice v) with hG
  have hproj : pairGradientProjection G = G.2 + G.2 := by
    unfold pairGradientProjection
    rw [← hstar, star_star]
  have hX : physicalHamiltonianField (fun w : PhysicalL2 => actualGapActionAllE02_38 w n) v =
      (-Complex.I) • G.2 := by
    rw [physicalHamiltonianField, hgr, hproj, smul_add, ← two_smul ℝ (Complex.I • G.2), smul_smul,
      neg_smul]
    norm_num
  rw [hX]
  unfold pairHamiltonianField
  rw [← hG]
  refine Prod.ext rfl ?_
  show star ((-Complex.I) • G.2) = Complex.I • G.1
  rw [star_smul_lp, hstar]
  simp

/-- Core of G6-017; the G6-016 head enters as the hypothesis `H16` (exact type), discharged in G6017. -/
theorem core17
    (H16 : ∀ (n : ℤ) (u : PhysicalL2),
      (fun t : ℝ => physicalInverseBirkhoff
        (rotateOneCoordinate n t (physicalBirkhoff u))) 0 = u ∧
      ∀ t : ℝ, HasDerivAt
        (fun s : ℝ => physicalInverseBirkhoff
          (rotateOneCoordinate n s (physicalBirkhoff u)))
        (physicalHamiltonianField (fun v => actualGapActionAllE02_38 v n)
          (physicalInverseBirkhoff (rotateOneCoordinate n t (physicalBirkhoff u)))) t)
    (u : PhysicalL2) (n : ℤ) (t : ℝ) :
  let v := physicalInverseBirkhoff (rotateOneCoordinate n t (physicalBirkhoff u))
  (∀ lam : ℂ, discrim (realSlice v) lam = discrim (realSlice u) lam) ∧
  v ∈ isospectralSet u := by
  intro v
  obtain ⟨h0, hd⟩ := H16 n u
  have hdisc : ∀ lam : ℂ, discrim (realSlice v) lam = discrim (realSlice u) lam := by
    intro lam
    have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => discrim (realSlice
        (physicalInverseBirkhoff (rotateOneCoordinate n s (physicalBirkhoff u)))) lam) 0 s := by
      intro s
      set w : PhysicalL2 :=
        physicalInverseBirkhoff (rotateOneCoordinate n s (physicalBirkhoff u)) with hw
      have h1 : HasFDerivAt (fun x : PhysicalL2 => discrim (realSlice x) lam)
          (((gradDiscrimCLM (realSlice w) lam).restrictScalars ℝ).comp realSlice) w :=
        ((hasFDerivAt_discrim lam (realSlice w)).restrictScalars ℝ).comp w realSlice.hasFDerivAt
      have h2 := h1.comp_hasDerivAt s (hd s)
      have hz : (((gradDiscrimCLM (realSlice w) lam).restrictScalars ℝ).comp realSlice)
          (physicalHamiltonianField (fun v => actualGapActionAllE02_38 v n) w) = 0 := by
        show gradDiscrimCLM (realSlice w) lam
          (realSlice (physicalHamiltonianField (fun v => actualGapActionAllE02_38 v n) w)) = 0
        rw [realSlice_actionField, ← (hasFDerivAt_discrim lam (realSlice w)).fderiv]
        exact pairPoisson_discrim_action (realSlice w) (realSlice_mem_gkW w) lam n
      rw [hz] at h2
      exact h2
    have hconst := is_const_of_deriv_eq_zero (fun s => (hderiv s).differentiableAt)
      (fun s => (hderiv s).deriv) t 0
    have h0' : physicalInverseBirkhoff (rotateOneCoordinate n 0 (physicalBirkhoff u)) = u := h0
    simp only [h0'] at hconst
    exact hconst
  exact ⟨hdisc, hdisc⟩

end
end G6017Aux
end NlsGge.GKDefinitionDesign
