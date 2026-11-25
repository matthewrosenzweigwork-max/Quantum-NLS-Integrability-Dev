import NlsGge.Hierarchy.ALQ4Limit38
import NlsGge.Hierarchy.ALFreeFields38
import NlsGge.Hierarchy.ALCorrector38
import NlsGge.Hierarchy.ALFreeDeterminant38
import NlsGge.Hierarchy.ALRatesBridge38
import NlsGge.Hierarchy.ALCompactConsistency38
import NlsGge.Hierarchy.ALPlaneConsistency38
import NlsGge.Hierarchy.ALNegativeQuartic38
import NlsGge.Hierarchy.ALTiltMeasure38
import NlsGge.Birkhoff.W04WeightedSmoothing38
import NlsGge.Birkhoff.S05FreeEnergy38b
import NlsGge.Hierarchy.ALEnergyAnalytic38
import NlsGge.Hierarchy.ALPositiveDecompositions38
import NlsGge.Hierarchy.ALFiniteMeasure38
import NlsGge.Hierarchy.ALMoments38
import NlsGge.Hierarchy.ALFullEnergy38
import NlsGge.Hierarchy.ALTransferDefs38
import NlsGge.Hierarchy.ALSampling38
import NlsGge.Hierarchy.ALSamplingV2Formula38
import NlsGge.Hierarchy.ALQ4Ensemble38
import NlsGge.Hierarchy.ALQ4Gaussian38
import NlsGge.Hierarchy.ALGaussianNormalizer38
import NlsGge.Hierarchy.ALTilt38
import NlsGge.Hierarchy.ALLaurent38
import NlsGge.Hierarchy.ALExteriorBranch38
import NlsGge.Hierarchy.ALQuadraticPart38
import NlsGge.Hierarchy.ALIsospectral38
import NlsGge.Hierarchy.ALGlobalFlow38
import NlsGge.Hierarchy.ALLiouvilleInvariance38
import NlsGge.Hierarchy.ALBoundaryKappa38
import NlsGge.Hierarchy.ALPoissonLiouville38
import NlsGge.Hierarchy.ALComplexMonodromy38
import NlsGge.Hierarchy.ALComplexExteriorLog38
import NlsGge.Hierarchy.ALPlaneWaveGap38
import NlsGge.Hierarchy.FullEnergyPlaneConvergence38
import NlsGge.Spectral.ActualComplexZsDysonProductHasSumV2
import NlsGge.Analysis.NaturalCover
import NlsGge.Definitions.PilotInterfaces
import NlsGge.Schur.FourierMultiplier
import NlsGge.Sobolev.SourceWeighted
import NlsGge.Sobolev.SourceEmbeddings
import NlsGge.Sobolev.FiniteFourier
import NlsGge.Birkhoff.F08Bare38g
import NlsGge.Birkhoff.F08Bare38d
import NlsGge.Birkhoff.F05Identity38
import NlsGge.Bootstrap

open scoped Nat
open NlsGge.AblowitzLadik NlsGge.HierarchyRiccati.Core
open Set Filter Topology

namespace NlsGge.ThirdConsultation.AL

theorem al015 {L : ℕ} [NeZero L]
    (γ : ℝ → ZMod L → ℂ) (t : ℝ) (hα : IsALField38 (γ t))
    (hγ : HasDerivAt γ (alX38 alHd (γ t)) t) (z : ℂ) (hz : z ≠ 0) :
  alX38 alHd (γ t) = alXd38 (γ t) ∧
  (∀ j : ZMod L, alXd38 (γ t) j =
    2*Complex.I*γ t j - Complex.I*((1-‖γ t j‖^2 : ℝ) : ℂ)*
      (γ t (j+1)+γ t (j-1))) ∧
  (∀ j : ZMod L, HasDerivAt (fun τ : ℝ => alTransfer38 (γ τ j) z)
    (alLaxB38 (γ t) z (j+1) * alTransfer38 (γ t j) z -
      alTransfer38 (γ t j) z * alLaxB38 (γ t) z j) t) ∧
  (∀ a : ZMod L → ℂ, IsALField38 a →
    2*(alC1 a).re - 2*alMass38 L a = -alHd a ∧
    alX38 (fun b : ZMod L → ℂ => 2*(alC1 b).re-2*alMass38 L b) a = -alXd38 a) ∧
  (∀ δ : ℝ → ZMod L → ℂ, IsAlGlobalCurve38 alHd δ →
    IsAlGlobalCurve38 (fun a : ZMod L → ℂ => -alHd a) (fun τ => δ (-τ)))
 := by
  have hγ' : HasDerivAt γ (alXd38 (γ t)) t := by
    rw [← alX38_alHd hα]; exact hγ
  have hneg : ∀ (H : (ZMod L → ℂ) → ℝ) (b : ZMod L → ℂ),
      alX38 (fun c => -H c) b = -alX38 H b := by
    intro H b
    funext j
    simp only [alX38, alWdb38, fderiv_fun_neg, neg_apply, Pi.neg_apply]
    push_cast
    ring
  have hfirst : ∀ a : ZMod L → ℂ, IsALField38 a →
      2*(alC1 a).re - 2*alMass38 L a = -alHd a := by
    intro a _
    unfold alHd
    rw [alMd_eq_alMass38]
    ring
  refine ⟨alX38_alHd hα, fun j => rfl, fun j => ?_, fun a ha => ⟨hfirst a ha, ?_⟩, fun δ hδ => ?_⟩
  · have hc : HasDerivAt (fun τ => γ τ j) (alXd38 (γ t) j) t := hasDerivAt_pi.1 hγ' j
    have hA := hasDerivAt_alTransfer38 (v := γ t (j-1)) (w := γ t (j+1)) hz (hα j) hc
    convert hA using 1
    simp only [alLaxB38, add_sub_cancel_right]
  · have hEv : (fun b => 2*(alC1 b).re - 2*alMass38 L b) =ᶠ[nhds a] (fun b => -alHd b) := by
      filter_upwards [(isOpen_alDisk38 (L := L)).mem_nhds ha] with b hb
      exact hfirst b hb
    have hfd := hEv.fderiv_eq (𝕜 := ℝ)
    have hX : alX38 (fun b => 2*(alC1 b).re - 2*alMass38 L b) a =
        alX38 (fun b => -alHd b) a := by
      funext j
      simp only [alX38, alWdb38]
      rw [hfd]
    rw [hX, hneg, alX38_alHd ha]
  · intro τ
    refine ⟨(hδ (-τ)).1, ?_⟩
    have h2 : HasDerivAt (fun τ : ℝ => -τ) (-1) τ := hasDerivAt_neg τ
    have h3 := (hδ (-τ)).2.scomp τ h2
    refine h3.congr_deriv ?_
    rw [hneg, neg_one_smul]

end NlsGge.ThirdConsultation.AL
