import NlsGge.Spectral.ActualPhysicalRawOscillatoryInner00UniformSmall36V3
import NlsGge.Spectral.ActualInteractionDyson00FirstPairIdentity36V1
import NlsGge.Schur.ActualPhysicalSourceIntervalCauchySchwarz33V2
import NlsGge.Spectral.ActualPhysicalInteractionDysonIdentification32V2
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- Actual first 00 Dyson pair tends uniformly to zero in real frequency,
over all endpoints and bounded nonnegative heights, including zero height.
This finite-order estimate does not assert full UHP normalization. -/
theorem actualPhysicalDyson00_firstPair_uniformFourierDecay37V1
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in cocompact ℝ,
      ∀ p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀,
        ‖genericRoughMatrixDysonTerm32
          (actualZsInteractionCoefficient32
            (fun s => naturalPhysicalCoverL2 u (s : SpectralCircle))
            ((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))) 2 (p.1 : ℝ) 0 0‖ < ε := by
  intro ε hε
  let η : ℝ := ε / (‖u‖ + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  filter_upwards [actualPhysicalRawOscillatoryInner00_uniformSmall36V3
    u Y₀ hY₀ η hη] with x hx
  intro p
  let U : ℝ → ℂ := fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)
  let z : ℂ := (x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ)
  let B := actualZsInteractionCoefficient32 U z
  have hB : ∀ i k, IntervalIntegrable (fun s => B s i k) volume 0 2 :=
    intervalIntegrable_actualPhysicalInteractionCoefficient32 u z
  have hU : IntervalIntegrable U volume 0 1 := by
    apply (naturalPhysicalCoverL2_intervalIntegrable_doubled u).mono_set
    simp only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    intro s hs
    exact ⟨hs.1, hs.2.trans (by norm_num)⟩
  have hsub : Set.uIcc (0 : ℝ) (p.1 : ℝ) ⊆ Set.uIcc (0 : ℝ) 1 := by
    simp only [Set.uIcc_of_le p.1.property.1,
      Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro s hs
    exact ⟨hs.1, hs.2.trans p.1.property.2⟩
  have hinner (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) (p.1 : ℝ)) :
      ‖∫ r in (0 : ℝ)..s,
        Complex.exp (2*Complex.I*z*((s : ℂ)-(r : ℂ))) * star (U r)‖ ≤ η := by
    let q : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀ :=
      (⟨s, ⟨hs.1, hs.2.trans p.1.property.2⟩⟩, p.2)
    simpa only [q, U, z] using (hx q).le
  have hmajor : IntervalIntegrable (fun s : ℝ => η*‖U s‖) volume 0 (p.1 : ℝ) :=
    (hU.norm.const_mul η).mono_set hsub
  have hpoint : ∀ᵐ s ∂volume, s ∈ Set.Ioc (0 : ℝ) (p.1 : ℝ) →
      ‖U s * (∫ r in (0 : ℝ)..s,
        Complex.exp (2*Complex.I*z*((s-r : ℝ) : ℂ)) * star (U r))‖ ≤ η*‖U s‖ := by
    apply Filter.Eventually.of_forall
    intro s hs
    rw [norm_mul]
    have hi := hinner s ⟨hs.1.le, hs.2⟩
    simp only [Complex.ofReal_sub] at *
    calc
      _ ≤ ‖U s‖*η := mul_le_mul_of_nonneg_left hi (norm_nonneg _)
      _ = _ := mul_comm _ _
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le p.1.property.1 hpoint hmajor
  have hmass := actualPhysicalRawCover_subintervalIntegral_norm_le33 u (p.1 : ℝ) p.1.property
  have hfinal : η*‖u‖ < ε := by
    dsimp [η]
    rw [div_mul_eq_mul_div]
    have hden : 0 < ‖u‖+1 := by positivity
    apply (div_lt_iff₀ hden).2
    nlinarith [norm_nonneg u]
  calc
    ‖genericRoughMatrixDysonTerm32 B 2 (p.1 : ℝ) 0 0‖
        ≤ ∫ s in (0 : ℝ)..(p.1 : ℝ), η*‖U s‖ := by
      rw [actualInteractionDyson00_firstPairIdentity36V1 U z (p.1 : ℝ)]
      exact hnorm
    _ = η*(∫ s in (0 : ℝ)..(p.1 : ℝ), ‖U s‖) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ η*‖u‖ := mul_le_mul_of_nonneg_left hmass hη.le
    _ < ε := hfinal
end NlsGge.SpectralFoundations
end
