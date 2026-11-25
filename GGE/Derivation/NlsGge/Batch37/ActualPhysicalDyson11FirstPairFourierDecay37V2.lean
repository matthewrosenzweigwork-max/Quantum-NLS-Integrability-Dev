import NlsGge.Batch37.ActualPhysical11WeightedInnerFourierIdentity37V2
import NlsGge.Spectral.ActualPhysicalHeightAmplitude11FourierSmall36V4
import NlsGge.Spectral.ActualInteractionDyson11FirstPairRescaling36V1
import NlsGge.Schur.ActualPhysicalSourceIntervalCauchySchwarz33V2
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis
/-- The actual height-rescaled first 11 pair has uniform frequency decay
over bounded nonnegative heights and unit endpoints. The opposite Fourier
frequency, starred outer source and exact damping weight are preserved. -/
theorem actualPhysicalDyson11_firstPair_uniformFourierDecay37V2
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in cocompact ℝ,
      ∀ p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀,
        ‖(Real.exp (-2*(p.2 : ℝ)*(p.1 : ℝ)) : ℂ) *
          genericRoughMatrixDysonTerm32
            (actualZsInteractionCoefficient32
              (fun s => naturalPhysicalCoverL2 u (s : SpectralCircle))
              ((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))) 2 (p.1 : ℝ) 1 1‖ < ε := by
  intro ε hε
  let η : ℝ := ε / (‖u‖+1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hneg : Tendsto (fun x : ℝ => -x) (cocompact ℝ) (cocompact ℝ) := by
    simpa only [mul_neg_one] using
      (Filter.tendsto_cocompact_mul_right₀ (a := (-1 : ℝ)) (by norm_num))
  have he := hneg.eventually
    (actualPhysicalHeightAmplitude11_fourierSmall36V4 u Y₀ hY₀ η hη)
  filter_upwards [he] with x hx
  intro p
  let U : ℝ → ℂ := fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)
  let P : ℝ → ℂ := fun s => ∫ r in (0 : ℝ)..s,
    U r*(complexRealOscillatoryPhase35 (2*x) r*
      (Real.exp (-2*(p.2 : ℝ)*r) : ℂ))
  have hinner (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) (p.1 : ℝ)) : ‖P s‖ ≤ η := by
    let q : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀ :=
      (⟨s,⟨hs.1,hs.2.trans p.1.property.2⟩⟩,p.2)
    have hid := actualPhysical11WeightedInner_fourierIdentity37V2 u Y₀ hY₀ q x
    change P s = _ at hid
    rw [hid]
    exact (hx q).le
  have hU : IntervalIntegrable U volume 0 1 := by
    apply (naturalPhysicalCoverL2_intervalIntegrable_doubled u).mono_set
    simp only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    intro s hs
    exact ⟨hs.1,hs.2.trans (by norm_num)⟩
  have hsub : Set.uIcc (0 : ℝ) (p.1 : ℝ) ⊆ Set.uIcc (0 : ℝ) 1 := by
    simp only [Set.uIcc_of_le p.1.property.1,
      Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro s hs
    exact ⟨hs.1,hs.2.trans p.1.property.2⟩
  have hmajor : IntervalIntegrable (fun s => η*‖U s‖) volume 0 (p.1 : ℝ) :=
    (hU.norm.const_mul η).mono_set hsub
  have hpoint : ∀ᵐ s ∂volume, s ∈ Set.Ioc (0 : ℝ) (p.1 : ℝ) →
      ‖(Real.exp (-2*(p.2 : ℝ)*((p.1 : ℝ)-s)) : ℂ) *
        complexRealOscillatoryPhase35 (-2*x) s * star (U s) * P s‖ ≤ η*‖U s‖ := by
    apply Filter.Eventually.of_forall
    intro s hs
    have hi := hinner s ⟨hs.1.le,hs.2⟩
    have harg : -2*(p.2 : ℝ)*((p.1 : ℝ)-s) ≤ 0 := by
      have := mul_nonneg p.2.property.1 (sub_nonneg.mpr hs.2)
      nlinarith
    have hexp := Real.exp_le_one_iff.mpr harg
    rw [norm_mul,norm_mul,norm_mul,
      complexRealOscillatoryPhase_norm35,norm_star,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_one]
    calc
      _ ≤ (1*‖U s‖)*η :=
        mul_le_mul (mul_le_mul_of_nonneg_right hexp (norm_nonneg _)) hi
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hb := intervalIntegral.norm_integral_le_of_norm_le p.1.property.1 hpoint hmajor
  have hfinal : η*‖u‖ < ε := by
    dsimp [η]
    rw [div_mul_eq_mul_div]
    have hden : 0 < ‖u‖+1 := by positivity
    apply (div_lt_iff₀ hden).2
    nlinarith [norm_nonneg u]
  rw [actualInteractionDyson11_firstPairRescaling36V1]
  calc
    _ ≤ ∫ s in (0 : ℝ)..(p.1 : ℝ),η*‖U s‖ := hb
    _ = η*(∫ s in (0 : ℝ)..(p.1 : ℝ),‖U s‖) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ η*‖u‖ := mul_le_mul_of_nonneg_left
      (actualPhysicalRawCover_subintervalIntegral_norm_le33 u (p.1 : ℝ) p.1.property) hη.le
    _ < ε := hfinal
end NlsGge.SpectralFoundations
end
