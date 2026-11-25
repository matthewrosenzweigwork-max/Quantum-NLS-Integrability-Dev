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

theorem al018 {L : ℕ} [NeZero L]
    (α₀ : ZMod L → ℂ) (h₀ : IsALField38 α₀) :
  ContDiff ℝ ⊤ (alXd38 (L := L)) ∧
  alFlow38 alHd 0 α₀ = α₀ ∧
  IsAlGlobalCurve38 alHd (fun t : ℝ => alFlow38 alHd t α₀) ∧
  IsCompact (alMassSublevel38 L (alMass38 L α₀)) ∧
  (∀ t : ℝ,
    alFlow38 alHd t α₀ ∈ alMassSublevel38 L (alMass38 L α₀) ∧
    alMass38 L (alFlow38 alHd t α₀) = alMass38 L α₀) ∧
  (∀ γ : ℝ → ZMod L → ℂ, γ 0 = α₀ → IsAlGlobalCurve38 alHd γ →
    γ = fun t : ℝ => alFlow38 alHd t α₀) ∧
  ∀ s t : ℝ,
    alFlow38 alHd (s+t) α₀ = alFlow38 alHd s (alFlow38 alHd t α₀) := by
  have hc1 : ContDiff ℝ (⊤ : WithTop ℕ∞) (alXd38 (L := L)) := by
    have hre : ∀ k : ZMod L, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun α : ZMod L → ℂ => (α k).re) :=
      fun k => Complex.reCLM.contDiff.comp (contDiff_apply ℝ ℂ k)
    have him : ∀ k : ZMod L, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun α : ZMod L → ℂ => (α k).im) :=
      fun k => Complex.imCLM.contDiff.comp (contDiff_apply ℝ ℂ k)
    have hcoord : ∀ k : ZMod L, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun α : ZMod L → ℂ => α k) :=
      fun k => contDiff_apply ℝ ℂ k
    have hn : ∀ k : ZMod L, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun α : ZMod L → ℂ =>
        (1 - ‖α k‖ ^ 2 : ℝ)) := by
      intro k
      have e : (fun α : ZMod L → ℂ => (1 - ‖α k‖ ^ 2 : ℝ)) = fun α : ZMod L → ℂ =>
          1 - ((α k).re * (α k).re + (α k).im * (α k).im) := by
        funext α
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      rw [e]
      exact contDiff_const.sub ((hre k).mul (hre k) |>.add ((him k).mul (him k)))
    have hI : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun _ : ZMod L → ℂ => (Complex.I : ℂ)) :=
      contDiff_const
    have hcast : ∀ k : ZMod L, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun α : ZMod L → ℂ =>
        (((1 - ‖α k‖ ^ 2 : ℝ)) : ℂ)) := fun k => Complex.ofRealCLM.contDiff.comp (hn k)
    rw [contDiff_pi]
    intro j
    unfold alXd38
    exact (contDiff_const.mul (hcoord j)).sub
      ((hI.mul (hcast j)).mul ((hcoord (j+1)).add (hcoord (j-1))))
  have hH : ContDiffOn ℝ 2 alHd (alDisk38 L) := alHd_contDiffOn38 (L := L)
  have hcons := alBracket_mass_alHd38 (L := L)
  have hfl := alFlow_spec38 hH hcons h₀
  have hγ : ∀ τ ∈ (Set.univ : Set ℝ), IsALField38 (alFlow38 alHd τ α₀) ∧
      HasDerivAt (fun τ => alFlow38 alHd τ α₀) (alX38 alHd (alFlow38 alHd τ α₀)) τ :=
    fun τ _ => hfl.2 τ
  have hcpt : ∀ R : ℝ, IsCompact (alMassSublevel38 L R) := by
    intro R
    have hexp : 0 < Real.exp (-R) := Real.exp_pos _
    have hmax : max (1 - Real.exp (-R)) 0 < 1 := max_lt (by linarith) one_pos
    have hr0lt : Real.sqrt (max (1 - Real.exp (-R)) 0) < 1 := by
      rw [Real.sqrt_lt' one_pos, one_pow]; exact hmax
    have hr0nn : 0 ≤ Real.sqrt (max (1 - Real.exp (-R)) 0) := Real.sqrt_nonneg _
    have hKdisk : Metric.closedBall (0 : ZMod L → ℂ)
        (Real.sqrt (max (1 - Real.exp (-R)) 0)) ⊆ alDisk38 L := by
      intro α hα
      rw [mem_closedBall_zero_iff] at hα
      show IsALField38 α
      intro j
      exact lt_of_le_of_lt (le_trans (norm_le_pi_norm α j) hα) hr0lt
    have hsub : alMassSublevel38 L R ⊆
        Metric.closedBall (0 : ZMod L → ℂ) (Real.sqrt (max (1 - Real.exp (-R)) 0)) := by
      intro α hα
      have hdisk : IsALField38 α := hα.1
      have hM : alMass38 L α ≤ R := hα.2
      rw [mem_closedBall_zero_iff]
      refine (pi_norm_le_iff_of_nonneg hr0nn).2 fun j => ?_
      have h1 := alNormSq_le_mass38 hdisk j
      have h2 : Real.exp (-R) ≤ Real.exp (-alMass38 L α) :=
        Real.exp_le_exp.2 (by linarith)
      have h3 : ‖α j‖ ^ 2 ≤ max (1 - Real.exp (-R)) 0 :=
        le_trans h1 (le_max_of_le_left (by linarith))
      calc ‖α j‖ = Real.sqrt (‖α j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (max (1 - Real.exp (-R)) 0) := Real.sqrt_le_sqrt h3
    have hcont : ContinuousOn (alMass38 L)
        (Metric.closedBall (0 : ZMod L → ℂ) (Real.sqrt (max (1 - Real.exp (-R)) 0))) :=
      fun α hα => (alMass_continuousAt38 (hKdisk hα)).continuousWithinAt
    have hset : alMassSublevel38 L R =
        Metric.closedBall (0 : ZMod L → ℂ) (Real.sqrt (max (1 - Real.exp (-R)) 0)) ∩
          alMass38 L ⁻¹' Set.Iic R := by
      ext α
      constructor
      · intro hα
        exact ⟨hsub hα, show alMass38 L α ≤ R from hα.2⟩
      · rintro ⟨hK', hM⟩
        exact ⟨hKdisk hK', show alMass38 L α ≤ R from hM⟩
    have hclosed : IsClosed (alMassSublevel38 L R) := by
      rw [hset]
      exact hcont.preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_Iic
    exact (isCompact_closedBall (0 : ZMod L → ℂ) _).of_isClosed_subset hclosed hsub
  have hmass : ∀ t, alMass38 L (alFlow38 alHd t α₀) = alMass38 L α₀ := by
    intro t
    have := alMass_const38 (U := Set.univ) isOpen_univ isPreconnected_univ hγ
      (Set.mem_univ t) (Set.mem_univ 0)
    exact this.trans (congrArg (alMass38 L) hfl.1)
  refine ⟨hc1, hfl.1, hfl.2, hcpt _, fun t => ⟨⟨(hfl.2 t).1, ?_⟩, hmass t⟩, ?_, fun s t => ?_⟩
  · show alMass38 L (alFlow38 alHd t α₀) ≤ alMass38 L α₀
    exact (hmass t).le
  · intro γ h0 hγc
    exact alFlow_unique_global38 hH hγc (fun t => hfl.2 t) (h0.trans hfl.1.symm)
  · exact alFlow_add38 hH hcons h₀ s t

end NlsGge.ThirdConsultation.AL
