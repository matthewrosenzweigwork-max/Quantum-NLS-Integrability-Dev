import NlsGge.Spectral.GenericRoughMatrixEntryMajorant32V1
import NlsGge.Spectral.GenericRoughMatrixVolterraUniqueness32V1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations

/-- Entrywise integrable B times a true continuous state is integrable on the
same actual compact interval, including the two matrix terms. -/
theorem intervalIntegrable_genericRoughMatrixProduct32
    (B F : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (T : ℝ) (hT : 0 ≤ T)
    (hB : ∀ i k, IntervalIntegrable (fun s => B s i k) volume 0 T)
    (hF : ContinuousOn F (Set.Icc (0 : ℝ) T)) (i j : Fin 2) :
    IntervalIntegrable (fun s => (B s * F s) i j) volume 0 T := by
  have hc (k : Fin 2) : ContinuousOn (fun s => F s k j) (Set.uIcc (0 : ℝ) T) := by
    simpa only [Set.uIcc_of_le hT] using!
      ((continuous_apply j).comp_continuousOn ((continuous_apply k).comp_continuousOn hF))
  simpa only [Matrix.mul_apply, Fin.sum_univ_two] using
    ((hB i 0).mul_continuousOn (hc 0)).add ((hB i 1).mul_continuousOn (hc 1))

/-- Genuine same-initial-data uniqueness for every entrywise L¹ matrix
coefficient. The norm majorant is constructed from B, and the equation is
proved for the series separately; no uniqueness or target solution is assumed. -/
theorem genericRoughMatrixVolterra_same_initial_unique32
    (B : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (T : ℝ) (hT : 0 ≤ T)
    (hB : ∀ i k, IntervalIntegrable (fun s => B s i k) volume 0 T)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (F G : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hF : ContinuousOn F (Set.Icc (0 : ℝ) T))
    (hG : ContinuousOn G (Set.Icc (0 : ℝ) T))
    (hVF : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i j,
      F t i j = M i j + ∫ s in (0 : ℝ)..t, (B s * F s) i j)
    (hVG : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i j,
      G t i j = M i j + ∫ s in (0 : ℝ)..t, (B s * G s) i j) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, F t = G t := by
  let H : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun t => F t - G t
  have hH : ContinuousOn H (Set.Icc (0 : ℝ) T) := hF.sub hG
  have hHeq : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i j : Fin 2,
      H t i j = ∫ s in (0 : ℝ)..t, (B s * H s) i j := by
    intro t ht i j
    have hsub : Set.uIcc (0 : ℝ) t ⊆ Set.uIcc (0 : ℝ) T := by
      rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le hT]
      exact fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
    have hAF := (intervalIntegrable_genericRoughMatrixProduct32 B F T hT hB hF i j).mono_set hsub
    have hAG := (intervalIntegrable_genericRoughMatrixProduct32 B G T hT hB hG i j).mono_set hsub
    have hproduct : (fun s => (B s * H s) i j) =
        (fun s => (B s * F s) i j - (B s * G s) i j) := by
      funext s
      have hm := congrArg (fun N : Matrix (Fin 2) (Fin 2) ℂ => N i j)
        (Matrix.mul_sub (B s) (F s) (G s))
      simpa only [H] using! hm
    change F t i j - G t i j = _
    rw [hproduct, intervalIntegral.integral_sub hAF hAG, hVF t ht i j, hVG t ht i j]
    ring
  let q := genericRoughMatrixEntryMajorant32 B
  have hq := intervalIntegrable_genericRoughMatrixEntryMajorant32 B T hB
  have hp := genericRoughMatrixEntryMajorant_nonneg32 B
  have hm : ∀ s ∈ Set.Icc (0 : ℝ) T, actualComplexMatrixEntrySup (B s) ≤ q s :=
    fun s _ => genericRoughMatrixEntrySup_le_majorant32 B s
  have hzero := genericRoughMatrixHomogeneousVolterra_continuous_eq_zero32 B q T hq hp hm H hH hHeq
  intro t ht
  exact sub_eq_zero.mp (hzero t ht)

/-- Every continuous normalized Volterra state for a rough L¹ coefficient
agrees with the actual constructed Dyson series on its full interval. -/
theorem genericRoughMatrixVolterraSolution_eq_Dyson32
    (B : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (T : ℝ) (hT : 0 ≤ T)
    (hB : ∀ i k, IntervalIntegrable (fun s => B s i k) volume 0 T)
    (F : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hF : ContinuousOn F (Set.Icc (0 : ℝ) T))
    (hVF : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i j,
      F t i j = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j +
        ∫ s in (0 : ℝ)..t, (B s * F s) i j) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, F t = genericRoughMatrixDysonTsum32 B t := by
  obtain ⟨hc,heq⟩ := genericRoughMatrixDysonTsum_wellPosed32 B T hT hB
  have hG : ContinuousOn (genericRoughMatrixDysonTsum32 B) (Set.Icc (0 : ℝ) T) := by
    apply continuousOn_pi.2
    intro i
    apply continuousOn_pi.2
    intro j
    exact hc i j
  exact genericRoughMatrixVolterra_same_initial_unique32 B T hT hB 1
    F (genericRoughMatrixDysonTsum32 B) hF hG hVF heq

end NlsGge.SpectralFoundations
end
