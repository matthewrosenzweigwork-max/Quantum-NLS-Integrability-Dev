import Mathlib
import NlsGge.Atomic.G2.G2029
import NlsGge.Atomic.G5.G5017Host
import NlsGge.ThirdConsultation.G5.G5017Support1
import NlsGge.GK38.PoissonActionSpectral
import NlsGge.GK38.IsolatingFamily

/- G5-017 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G5/G5017.lean, namespace
   NlsGge.GKDefinitionDesign. Head: STATEMENTS/G5.md G5-017 (followup7), verbatim; no lexical repair.
   Proof (GK 18.1): realSlice u in gkW (realSlice_mem_gkW); G2-029 gives CircleIntegrable and HasFDerivAt, so
   fderiv A_n = -(1/pi) * circle integral of gradRootQuotient. The map S := (fderiv A_m).comp J . pairGradientL is a continuous
   C-linear functional of the first-slot functional; S commutes with the circle integral (G5017Support1.clm_circleIntegral_comm).
   Pointwise S (gradRootQuotient phi z) = canonRoot^-1 * fderiv A_m (spectralDiscrimHamField phi z) = 0, using the Riesz bridge
   pairGradientCLM (gradDiscrimCLM phi z) = gradDiscrimL2 phi z (G5017Support1) and the landed action_spectral_commutation,
   i.e. the G1-069 spectral commutation integrated against the action contour. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.GK38
open NlsGge.GK38.PoissonSpectral38
open NlsGge.GK38.ActionGradient
open NlsGge.ThirdConsultation.G5017Support1

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5017 (u : PhysicalL2) (m n : ℤ) :
  pairPoisson (fun φ => gkActionC38 φ m) (fun φ => gkActionC38 φ n)
    (realSlice u) = 0 := by
  have hφ : realSlice u ∈ gkW := realSlice_mem_gkW u
  obtain ⟨hint, hfd, -⟩ := G2_029 (realSlice u) hφ n
  have hn : fderiv ℂ (fun ψ : PotPair => gkActionC38 ψ n) (realSlice u) =
      -(1 / (Real.pi : ℂ)) • circleIntegral (gradRootQuotient (realSlice u))
        (discC (realSlice u) n) (discR (realSlice u) n) := hfd.fderiv
  let J : PotPair →L[ℂ] PotPair :=
    ((-Complex.I) • ContinuousLinearMap.snd ℂ PhysicalL2 PhysicalL2).prod
      (Complex.I • ContinuousLinearMap.fst ℂ PhysicalL2 PhysicalL2)
  let S : (PotPair →L[ℂ] ℂ) →L[ℂ] ℂ :=
    ((fderiv ℂ (fun ψ : PotPair => gkActionC38 ψ m) (realSlice u)).comp J).comp pairGradientL
  have hS : pairPoisson (fun φ => gkActionC38 φ m) (fun φ => gkActionC38 φ n) (realSlice u) =
      S (fderiv ℂ (fun ψ : PotPair => gkActionC38 ψ n) (realSlice u)) := rfl
  have hz : ∀ z : ℂ, S (gradRootQuotient (realSlice u) z) = 0 := by
    intro z
    have hJ : J (gradDiscrimL2 (realSlice u) z) = spectralDiscrimHamField38 (realSlice u) z := rfl
    have hc := (action_spectral_commutation (realSlice u) hφ m z).2.2
    have h1 : S (gradDiscrimCLM (realSlice u) z) = 0 := by
      change (fderiv ℂ (fun ψ : PotPair => gkActionC38 ψ m) (realSlice u))
        (J (pairGradientCLM (gradDiscrimCLM (realSlice u) z))) = 0
      rw [pairGradientCLM_gradDiscrimCLM, hJ]
      exact hc
    unfold gradRootQuotient
    rw [map_smul, h1, smul_zero]
  have hz' : (fun z : ℂ => S (gradRootQuotient (realSlice u) z)) = fun _ => 0 := funext hz
  rw [hS, hn, map_smul, clm_circleIntegral_comm S hint, hz']
  simp [circleIntegral]

end
end NlsGge.GKDefinitionDesign
