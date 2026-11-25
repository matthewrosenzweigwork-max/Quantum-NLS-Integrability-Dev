import Mathlib
import NlsGge.ThirdConsultation.R.RamerSetting06
import NlsGge.Atomic.R.R030
import NlsGge.Ramer.TruncatedDivergenceLimit
import NlsGge.Ramer.CylindricalDensityConvergence
import NlsGge.Ramer.DivergenceIdentificationGlobal
import NlsGge.Ramer.SpaceTransfer

                                                                                                 
                                                                                                    
                                                                                                                           
                                                                                                           
                                                                                                                               
                                                                                                                 
                                                                                  
                                                                                                                              
                                                                                                           
set_option autoImplicit false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section

/-- **Transport of convergence in measure along a measurable map.**  If `R` is measurable and the
`f n`, `g` are a.e.-strongly measurable for the pushforward `γ.map R`, then convergence in measure of
`f n ∘ R → g ∘ R` for `γ` gives convergence in measure of `f n → g` for `γ.map R`. -/
theorem tendstoInMeasure_map_of_aestronglyMeasurable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {γ : Measure α} {R : α → β} (hR : Measurable R)
    {f : ℕ → β → ℝ} {g : β → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) (γ.map R))
    (hg : AEStronglyMeasurable g (γ.map R))
    (h : TendstoInMeasure γ (fun n a => f n (R a)) atTop (fun a => g (R a))) :
    TendstoInMeasure (γ.map R) f atTop g := by
  have hf' : ∀ n, Measurable ((hf n).mk (f n)) := fun n => (hf n).stronglyMeasurable_mk.measurable
  have hg' : Measurable (hg.mk g) := hg.stronglyMeasurable_mk.measurable
  have hfR : ∀ n, (fun a => f n (R a)) =ᵐ[γ] fun a => (hf n).mk (f n) (R a) := fun n =>
    ae_of_ae_map hR.aemeasurable (hf n).ae_eq_mk
  have hgR : (fun a => g (R a)) =ᵐ[γ] fun a => hg.mk g (R a) :=
    ae_of_ae_map hR.aemeasurable hg.ae_eq_mk
  have h' : TendstoInMeasure γ (fun n a => (hf n).mk (f n) (R a)) atTop
      (fun a => hg.mk g (R a)) := h.congr hfR hgR
  have hmk : TendstoInMeasure (γ.map R) (fun n => (hf n).mk (f n)) atTop (hg.mk g) := by
    intro ε hε
    have hset : ∀ n, MeasurableSet {x | ε ≤ edist ((hf n).mk (f n) x) (hg.mk g x)} := fun n =>
      measurableSet_le measurable_const ((hf' n).edist hg')
    have := h' ε hε
    refine this.congr (fun n => ?_)
    exact (Measure.map_apply hR (hset n)).symm
  exact hmk.congr (fun n => (hf n).ae_eq_mk.symm) hg.ae_eq_mk.symm

/-- Restriction of convergence in measure to a subset. -/
theorem tendstoInMeasure_restrict_of_tendstoInMeasure
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : ℕ → α → ℝ} {g : α → ℝ}
    (h : TendstoInMeasure μ f atTop g) (A : Set α) :
    TendstoInMeasure (μ.restrict A) f atTop g := by
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
    (fun n => bot_le) (fun n => Measure.restrict_le_self _)

section R056
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

local notation "E" => RamerE c s
local notation "H" => RamerH c
local notation "μ" => ramerGaussian c s
local notation "J" => ramerJac c s hs

theorem local_tendstoInMeasure_cylDensity
    (K : E → H) (hK : ContDiff ℝ 2 K) :
    ∀ x₀ : E, ∃ r : ℝ, 0 < r ∧
      TendstoInMeasure ((μ).restrict (ball x₀ r))
        (cylindricalDensity c s K) atTop (J K) := by
  intro x₀
  refine ⟨1, one_pos, tendstoInMeasure_restrict_of_tendstoInMeasure ?_ _⟩
  have hspec := Classical.choose_spec (NlsGge.Ramer.divergence_identification c s hs K hK)
  have hdef : NlsGge.Ramer.ramerDiv c s hs K =
      Classical.choose (NlsGge.Ramer.divergence_identification c s hs K hK) := by
    unfold NlsGge.Ramer.ramerDiv; rw [dif_pos hK]
  rw [← hdef] at hspec
  obtain ⟨hm, -, h3, -, -⟩ := hspec
  have hconv := NlsGge.Ramer.tendstoInMeasure_cylindricalDensity c s hs K hK
    (NlsGge.Ramer.ramerDiv c s hs K) h3
  have hRm := NlsGge.Measure.measurable_fullWeightedSequenceRealization c s
  have hcoordm := NlsGge.Ramer.measurable_coordE c s
  have hJeq : J K = NlsGge.Ramer.ramerJE c s hs K (NlsGge.Ramer.ramerDiv c s hs K) := by
    funext x; rw [NlsGge.Ramer.ramerJE_eq]; rfl
  show TendstoInMeasure (NlsGge.Measure.fullWeightedSequenceGaussian c s)
    (cylindricalDensity c s K) atTop (J K)
  refine tendstoInMeasure_map_of_aestronglyMeasurable (γ := NlsGge.Measure.fullWeightSequenceGaussian c.val)
    (R := NlsGge.Measure.fullWeightedSequenceRealization c s) hRm ?_ ?_ ?_
  · intro N
    refine Measurable.aestronglyMeasurable ?_
    unfold cylindricalDensity
    refine (NlsGge.Ramer.measurable_finiteRamerDensity_of_continuous _ ?_).comp
      ((NlsGge.Ramer.measurable_headPt c N).comp hcoordm)
    exact continuous_id.add (NlsGge.Ramer.contDiff_truncField c s K hK N).continuous
  · rw [hJeq]
    exact NlsGge.Ramer.aestronglyMeasurable_ramerJE c s hs K (hK.of_le (by norm_num)) _ hm
  · refine TendstoInMeasure.congr (fun i => ?_) ?_ hconv
    · filter_upwards [NlsGge.Ramer.coordE_realization_ae c s hs] with z hz
      show _ = cylindricalDensity c s K i (NlsGge.Measure.fullWeightedSequenceRealization c s z)
      unfold cylindricalDensity
      rw [hz]
    · filter_upwards [NlsGge.Ramer.coordE_realization_ae c s hs] with z hz
      show NlsGge.Ramer.ramerJ c s hs K (NlsGge.Ramer.ramerDiv c s hs K) z =
        J K (NlsGge.Measure.fullWeightedSequenceRealization c s z)
      simp only [NlsGge.Ramer.ramerJ, ramerJac, hsDerivH, hz]

theorem cylindricalDensity_finite_formula
    (K : E → H) (hK : ContDiff ℝ 2 K) (N : ℕ) (x : E) :
    let v := NlsGge.Ramer.headPt c N (NlsGge.Ramer.coordE c s x)
    let F := NlsGge.Ramer.truncField c s K N
    cylindricalDensity c s K N x =
      |(fderiv ℝ (fun w : NlsGge.Ramer.actualCMHead c N => w + F w) v).det| *
        Real.exp ((‖v‖ ^ 2 - ‖v + F v‖ ^ 2) / 2) := by
  intro v F
  have hF : Differentiable ℝ F :=
    (NlsGge.Ramer.contDiff_truncField c s K hK N).differentiable (by norm_num)
  have h := finite_ramer_density_identity F v (hF v)
  exact h.1.trans h.2

end R056
end
end NlsGge.ThirdConsultation.R
