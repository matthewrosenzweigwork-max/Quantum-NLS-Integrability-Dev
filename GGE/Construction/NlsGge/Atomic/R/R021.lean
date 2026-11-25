import Mathlib
import NlsGge.ThirdConsultation.R.R021Support3
import NlsGge.ThirdConsultation.R.CylCore06
import NlsGge.Atomic.R.R023

                                                                                                 
                                                                                                              
                                                                                                        
                                                                                
                                                                                                
                                                                            
                             
set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section

/-- The coordinate map of `E_s` is continuous. -/
theorem r021_continuous_coordE {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) :
    Continuous (NlsGge.Ramer.coordE c s) :=
  continuous_pi fun n => NlsGge.Ramer.continuous_coordE_apply c s n

/-- The norm of the `H`-valued cylinder on `E_s` is continuous. -/
theorem r021_continuous_cylFieldE_norm {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (N : ℕ)
    (f : NlsGge.Ramer.actualCMHead c N → NlsGge.Ramer.actualCMHead c N)
    (hf : Continuous f) :
    Continuous (fun x : RamerE c s => ‖cylFieldE c s N f x‖) := by
  have h1 : Continuous (fun x : RamerE c s =>
      f (NlsGge.Ramer.headPt c N (NlsGge.Ramer.coordE c s x))) :=
    hf.comp ((r021_continuous_headPt c N).comp (r021_continuous_coordE c s))
  have hval : Continuous (fun v : NlsGge.Ramer.actualCMHead c N =>
      (v : NlsGge.Ramer.ActualCM c)) := continuous_subtype_val
  exact continuous_norm.comp (hval.comp h1)

/-- The `H`-valued cylinder on `E_s` is almost everywhere strongly measurable. -/
theorem r021_aesm_cylFieldE {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (N : ℕ)
    {μ : Measure (RamerE c s)}
    (f : NlsGge.Ramer.actualCMHead c N → NlsGge.Ramer.actualCMHead c N) (hf : Continuous f) :
    AEStronglyMeasurable (cylFieldE c s N f) μ := by
  have h1 : Continuous (fun x : RamerE c s =>
      f (NlsGge.Ramer.headPt c N (NlsGge.Ramer.coordE c s x))) :=
    hf.comp ((r021_continuous_headPt c N).comp (r021_continuous_coordE c s))
  have hval : Continuous (fun v : NlsGge.Ramer.actualCMHead c N =>
      (v : NlsGge.Ramer.ActualCM c)) := continuous_subtype_val
  exact hval.comp_aestronglyMeasurable h1.aestronglyMeasurable

/-- The scalar cylinder divergence on `E_s` is continuous for a `C¹` level-`N` field. -/
theorem r021_continuous_cylDivE {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (N : ℕ)
    (f : NlsGge.Ramer.actualCMHead c N → NlsGge.Ramer.actualCMHead c N) (hf : ContDiff ℝ 1 f) :
    Continuous (fun x : RamerE c s => cylDivE c s N f x) :=
  (NlsGge.Ramer.continuous_finiteGaussianDivergence hf).comp
    ((r021_continuous_headPt c N).comp (r021_continuous_coordE c s))

theorem cylDiv_closable
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (N : ℕ → ℕ)
    (f : ∀ k : ℕ, NlsGge.Ramer.actualCMHead c (N k) →
      NlsGge.Ramer.actualCMHead c (N k))
    (hf : ∀ k : ℕ, GaussianL2CylindricalCore c (N k) (f k))
    (g : (ℤ → ℂ) → ℝ)
    (hg : MemLp g 2 (coordinateGaussian c))
    (hF : Tendsto
      (fun k : ℕ => eLpNorm
        (NlsGge.Ramer.cylField c (N k) (f k)) 2 (coordinateGaussian c))
      atTop (𝓝 0))
    (hD : Tendsto
      (fun k : ℕ => eLpNorm
        (fun z : ℤ → ℂ => NlsGge.Ramer.cylDiv c (N k) (f k) z - g z)
        2 (coordinateGaussian c))
      atTop (𝓝 0)) :
    g =ᵐ[coordinateGaussian c] 0 := by
  have hF' : Tendsto (fun k : ℕ => eLpNorm
      (fun z : ℤ → ℂ => ‖NlsGge.Ramer.cylField c (N k) (f k) z‖) 2
      (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0) :=
    hF.congr (fun k => (eLpNorm_norm _
      (r021_aesm_cylField c (N k) (f k) (r021_core_contDiff (hf k)).continuous)).symm)
  exact r021_cylDiv_closable_coord c f hf g hg hF' hD

theorem cylDiv_closable_E
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s)
    (N : ℕ → ℕ)
    (f : ∀ k : ℕ, NlsGge.Ramer.actualCMHead c (N k) →
      NlsGge.Ramer.actualCMHead c (N k))
    (hf : ∀ k : ℕ, GaussianL2CylindricalCore c (N k) (f k))
    (g : RamerE c s → ℝ)
    (hg : MemLp g 2 (ramerGaussian c s))
    (hF : Tendsto
      (fun k : ℕ => eLpNorm (cylFieldE c s (N k) (f k))
        2 (ramerGaussian c s))
      atTop (𝓝 0))
    (hD : Tendsto
      (fun k : ℕ => eLpNorm
        (fun x : RamerE c s => cylDivE c s (N k) (f k) x - g x)
        2 (ramerGaussian c s))
      atTop (𝓝 0)) :
    g =ᵐ[ramerGaussian c s] 0 := by
  have hR : Measurable (NlsGge.Measure.fullWeightedSequenceRealization c s) :=
    NlsGge.Measure.measurable_fullWeightedSequenceRealization c s
  have hmap : ramerGaussian c s = (NlsGge.Measure.fullWeightSequenceGaussian c.val).map
      (NlsGge.Measure.fullWeightedSequenceRealization c s) := rfl
  have hae : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      NlsGge.Ramer.coordE c s (NlsGge.Measure.fullWeightedSequenceRealization c s z) = z := by
    filter_upwards [NlsGge.Measure.ae_fullWeightedSequenceRealization_apply c s hs] with z hz
    funext n
    exact hz n
  have hpush : ∀ φ : RamerE c s → ℝ, AEStronglyMeasurable φ (ramerGaussian c s) →
      eLpNorm φ 2 (ramerGaussian c s) = eLpNorm
        (fun z => φ (NlsGge.Measure.fullWeightedSequenceRealization c s z)) 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
    intro φ hφ
    rw [hmap] at hφ ⊢
    exact eLpNorm_map_measure hφ hR.aemeasurable
  -- the H-valued norms of the E-cylinders, pulled back to the coordinate law
  have hFE : ∀ k : ℕ, eLpNorm (cylFieldE c s (N k) (f k)) 2 (ramerGaussian c s) =
      eLpNorm (fun z : ℤ → ℂ => ‖NlsGge.Ramer.cylField c (N k) (f k) z‖) 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
    intro k
    have hA := r021_aesm_cylFieldE c s (N k) (μ := ramerGaussian c s) (f k)
      (r021_core_contDiff (hf k)).continuous
    rw [← eLpNorm_norm _ hA, hpush _ (r021_continuous_cylFieldE_norm c s (N k) (f k)
      (r021_core_contDiff (hf k)).continuous).aestronglyMeasurable]
    refine eLpNorm_congr_ae ?_
    filter_upwards [hae] with z hz
    show ‖cylFieldE c s (N k) (f k) (NlsGge.Measure.fullWeightedSequenceRealization c s z)‖ =
      ‖NlsGge.Ramer.cylField c (N k) (f k) z‖
    unfold cylFieldE
    rw [hz]
  have hDE : ∀ k : ℕ, eLpNorm (fun x : RamerE c s => cylDivE c s (N k) (f k) x - g x) 2
      (ramerGaussian c s) = eLpNorm (fun z : ℤ → ℂ => NlsGge.Ramer.cylDiv c (N k) (f k) z -
        g (NlsGge.Measure.fullWeightedSequenceRealization c s z)) 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
    intro k
    have hcd := r021_continuous_cylDivE c s (N k) (f k) ((r021_core_contDiff (hf k)).of_le
      (by norm_num))
    have hA : AEStronglyMeasurable (fun x : RamerE c s => cylDivE c s (N k) (f k) x - g x)
        (ramerGaussian c s) :=
      hcd.aestronglyMeasurable.sub hg.aestronglyMeasurable
    rw [hpush _ hA]
    refine eLpNorm_congr_ae ?_
    filter_upwards [hae] with z hz
    show cylDivE c s (N k) (f k) (NlsGge.Measure.fullWeightedSequenceRealization c s z) -
        g (NlsGge.Measure.fullWeightedSequenceRealization c s z) =
      NlsGge.Ramer.cylDiv c (N k) (f k) z -
        g (NlsGge.Measure.fullWeightedSequenceRealization c s z)
    unfold cylDivE
    rw [hz]
  -- the limit function is L² on the coordinate law
  have hη : MemLp (fun z : ℤ → ℂ => g (NlsGge.Measure.fullWeightedSequenceRealization c s z)) 2
      (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
    have hg' : MemLp g 2 ((NlsGge.Measure.fullWeightSequenceGaussian c.val).map
        (NlsGge.Measure.fullWeightedSequenceRealization c s)) := by
      rw [← hmap]; exact hg
    exact hg'.comp_of_map hR.aemeasurable
  have hF' : Tendsto (fun k : ℕ => eLpNorm
      (fun z : ℤ → ℂ => ‖NlsGge.Ramer.cylField c (N k) (f k) z‖) 2
      (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0) :=
    hF.congr hFE
  have hD' : Tendsto (fun k : ℕ => eLpNorm
      (fun z : ℤ → ℂ => NlsGge.Ramer.cylDiv c (N k) (f k) z -
        g (NlsGge.Measure.fullWeightedSequenceRealization c s z)) 2
      (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0) :=
    hD.congr hDE
  have hcoord := r021_cylDiv_closable_coord c f hf
    (fun z => g (NlsGge.Measure.fullWeightedSequenceRealization c s z)) hη hF' hD'
  -- pull the coordinate a.e. vanishing back to E_s along the realization
  have hgm : AEStronglyMeasurable g (ramerGaussian c s) := hg.aestronglyMeasurable
  obtain ⟨g', hg'sm, hgg'⟩ : ∃ g' : RamerE c s → ℝ, StronglyMeasurable g' ∧
      g =ᵐ[ramerGaussian c s] g' :=
    ⟨hgm.mk g, hgm.stronglyMeasurable_mk, hgm.ae_eq_mk⟩
  have h2 : g' ∘ (NlsGge.Measure.fullWeightedSequenceRealization c s) =ᵐ[
      NlsGge.Measure.fullWeightSequenceGaussian c.val] 0 := by
    have h3 : g ∘ (NlsGge.Measure.fullWeightedSequenceRealization c s) =ᵐ[
        NlsGge.Measure.fullWeightSequenceGaussian c.val]
        g' ∘ (NlsGge.Measure.fullWeightedSequenceRealization c s) :=
      ae_eq_comp hR.aemeasurable (by rw [← hmap]; exact hgg')
    exact h3.symm.trans hcoord
  have h4 : ∀ᵐ x ∂(ramerGaussian c s), g' x = 0 := by
    rw [hmap]
    exact (ae_map_iff hR.aemeasurable
      (measurableSet_eq_fun hg'sm.measurable measurable_const)).2 h2
  exact hgg'.trans h4

end
end NlsGge.ThirdConsultation.R
