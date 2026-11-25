import Mathlib
import NlsGge.Atomic.R.R029
import NlsGge.Atomic.R.R055
import NlsGge.Atomic.R.R056
import NlsGge.ThirdConsultation.R.R037Support
import NlsGge.ThirdConsultation.R.RamerSetting06B

                                                                                                                                
                                                                                     
                                                                                                                                        
                                                                                                                            
                                                                                                                                    
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section
section R058Support
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

local notation "E" => RamerE c s
local notation "H" => RamerH c
local notation "μ" => ramerGaussian c s
local notation "J" => ramerJac c s hs

/-- Local step of S1: on a ball where the approximants converge in `L²` to `d`, `d` agrees a.e. with `ramerDiv ∘ coordE`. -/
theorem v2_div_ae_eq_ramerDiv_ball
    (K : E → H) (hK : ContDiff ℝ 2 K) (d : E → ℝ) (x₀ : E) (r : ℝ)
    (hL1 : Tendsto (fun N : ℕ => eLpNorm
      ((ball x₀ r).indicator (fun x : E => ramerApprox c s hs K N x - d x))
      2 (ramerGaussian c s)) atTop (𝓝 0)) :
    d =ᵐ[(ramerGaussian c s).restrict (ball x₀ r)]
      fun x => NlsGge.Ramer.ramerDiv c s hs K (NlsGge.Ramer.coordE c s x) := by
  obtain ⟨φ, hφ, hae⟩ := ae_tendsto_ramerA_ramerDiv c s hs K hK
  have h2 : Tendsto (fun j : ℕ => eLpNorm
      ((ball x₀ r).indicator (fun x : E => ramerApprox c s hs K (φ j) x - d x))
      2 (ramerGaussian c s)) atTop (𝓝 0) := hL1.comp hφ.tendsto_atTop
  have hconv : TendstoInMeasure (ramerGaussian c s)
      (fun j : ℕ => (ball x₀ r).indicator (fun x : E => ramerApprox c s hs K (φ j) x - d x))
      atTop (0 : E → ℝ) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_
    simp only [sub_zero]
    exact h2
  obtain ⟨ψ, hψ, hae2⟩ := hconv.exists_seq_tendsto_ae
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball]
  filter_upwards [hae, hae2] with x hx1 hx2 hxb
  have h3 : Tendsto (fun i : ℕ => ramerApprox c s hs K (φ (ψ i)) x - d x) atTop (𝓝 0) := by
    refine hx2.congr (fun i => ?_)
    simp only [Set.indicator_of_mem hxb]
  have h4 : Tendsto (fun i : ℕ => ramerApprox c s hs K (φ (ψ i)) x) atTop
      (𝓝 (NlsGge.Ramer.ramerDiv c s hs K (NlsGge.Ramer.coordE c s x))) :=
    hx1.comp hψ.tendsto_atTop
  have h5 := h4.sub_const (d x)
  have h6 := tendsto_nhds_unique h5 h3
  linarith

/-- **S1.** The divergence of `LocalRamerApproxLimit` is a.e. the production representative `ramerDiv ∘ coordE`. -/
theorem v2_div_ae_eq_ramerDiv
    (K : E → H) (hK : ContDiff ℝ 2 K) (d : E → ℝ)
    (hL : LocalRamerApproxLimit c s hs K d) :
    d =ᵐ[ramerGaussian c s]
      fun x => NlsGge.Ramer.ramerDiv c s hs K (NlsGge.Ramer.coordE c s x) := by
  choose r hr hL1 _ using hL
  obtain ⟨T, hTc, hTcov⟩ := NlsGge.Ramer.exists_countable_cover_balls c s r hr
  have hae : ∀ x ∈ T, ∀ᵐ z ∂(ramerGaussian c s), z ∈ ball x (r x) →
      d z = NlsGge.Ramer.ramerDiv c s hs K (NlsGge.Ramer.coordE c s z) := by
    intro x _
    exact (ae_restrict_iff' measurableSet_ball).1
      (v2_div_ae_eq_ramerDiv_ball c s hs K hK d x (r x) (hL1 x))
  have hall := (MeasureTheory.ae_ball_iff hTc).2 hae
  filter_upwards [hall] with z hz
  obtain ⟨y, hy, hzy⟩ := hTcov z
  exact hz y hy hzy

/-- **S2.** Global convergence in measure of the cylindrical densities to the Ramer Jacobian. -/
theorem tendstoInMeasure_cylindricalDensity_ramerJac
    (K : E → H) (hK : ContDiff ℝ 2 K) :
    TendstoInMeasure (ramerGaussian c s) (cylindricalDensity c s K) atTop (J K) := by
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
  refine tendstoInMeasure_map_of_aestronglyMeasurable
    (γ := NlsGge.Measure.fullWeightSequenceGaussian c.val)
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

end R058Support
end
end NlsGge.ThirdConsultation.R
