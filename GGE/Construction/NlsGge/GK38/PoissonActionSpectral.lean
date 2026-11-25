import NlsGge.GK38.PoissonSpectralCommute
import NlsGge.GK38.ActionGradient
import NlsGge.GK38.ActionRealProbe

/-! The actual action derivative vanishes along every spectral Hamiltonian field. -/
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.AblowitzLadik
open NlsGge.GK38.PoissonSpectral38
namespace NlsGge.GK38.PoissonSpectral38
noncomputable section

def ActionSpectralCommuteTarget : Prop :=
  ∀ (φ : PotPair), φ ∈ gkW → ∀ (n : ℤ) (w : ℂ),
    CircleIntegrable
      (fun z => gradDiscrimCLM φ z (spectralDiscrimHamField38 φ w) /
        canonRoot38 φ z) (discC φ n) (discR φ n) ∧
    NlsGge.GK38.ActionGradient.actionGradientCLM38 φ n
      (spectralDiscrimHamField38 φ w) = 0 ∧
    fderiv ℂ (fun ψ : PotPair => gkActionC38 ψ n) φ
      (spectralDiscrimHamField38 φ w) = 0

theorem action_spectral_commutation (φ : PotPair) (hφ : φ ∈ gkW)
    (n : ℤ) (w : ℂ) :
    CircleIntegrable
      (fun z => gradDiscrimCLM φ z (spectralDiscrimHamField38 φ w) /
        canonRoot38 φ z) (discC φ n) (discR φ n) ∧
    NlsGge.GK38.ActionGradient.actionGradientCLM38 φ n
      (spectralDiscrimHamField38 φ w) = 0 ∧
    fderiv ℂ (fun ψ : PotPair => gkActionC38 ψ n) φ
      (spectralDiscrimHamField38 φ w) = 0 := by
  have hi := NlsGge.GK38.ActionGradient.gradRootQuotient_direction_circle_integrable
    φ hφ (discC φ) (discR φ) (isolating_family38 φ hφ) n
      (spectralDiscrimHamField38 φ w)
  have hz (z : ℂ) : gradDiscrimCLM φ z (spectralDiscrimHamField38 φ w) = 0 := by
    rw [gradDiscrimCLM_spectralDiscrimHamField38, spectralDiscrimPoisson38_eq_zero]
  have hf : (fun z => gradDiscrimCLM φ z (spectralDiscrimHamField38 φ w) /
      canonRoot38 φ z) = (fun _ : ℂ => (0 : ℂ)) := by
    funext z
    rw [hz, zero_div]
  refine ⟨hi, ?_, ?_⟩
  · rw [NlsGge.GK38.ActionGradient.actionGradientCLM_apply φ hφ n, hf]
    simp [circleIntegral]
  · rw [NlsGge.GK38.ActionGradient.action_fderiv_apply φ hφ n, hf]
    simp [circleIntegral]

theorem actionSpectralCommuteTarget : ActionSpectralCommuteTarget := by
  intro φ hφ n w
  exact action_spectral_commutation φ hφ n w

/-- The same actual field commutes with a nonzero signed action and a closed gap. -/
theorem probe_nonfree_active_and_collapsed (w : ℂ) :
    let u := planeL2 2 (planeWaveCoeff38 2 (2 : ℤ) (-3))
    u ≠ 0 ∧ gkActionC38 (realSlice u) (-2) = 9 ∧
      gkActionC38 (realSlice u) 2 = 0 ∧
      fderiv ℂ (fun ψ : PotPair => gkActionC38 ψ (-2)) (realSlice u)
        (spectralDiscrimHamField38 (realSlice u) w) = 0 ∧
      fderiv ℂ (fun ψ : PotPair => gkActionC38 ψ 2) (realSlice u)
        (spectralDiscrimHamField38 (realSlice u) w) = 0 := by
  dsimp only
  obtain ⟨hu, ha, hz⟩ := NlsGge.GK38.ActionRealProbe.nonfree_signed_plane
  exact ⟨hu, ha, hz,
    (action_spectral_commutation _ (realSlice_mem_gkW _) (-2) w).2.2,
    (action_spectral_commutation _ (realSlice_mem_gkW _) 2 w).2.2⟩

end
end NlsGge.GK38.PoissonSpectral38
