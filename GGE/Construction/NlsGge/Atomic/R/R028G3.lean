import Mathlib
import NlsGge.Atomic.R.R021
import NlsGge.Atomic.R.R022
import NlsGge.Atomic.R.R025
import NlsGge.ThirdConsultation.R.RamerSetting06
import NlsGge.Ramer.TruncLimitClosedDiv
import NlsGge.Ramer.DivergenceIdentificationBounded
import NlsGge.Ramer.RamerLemma54

                                                                                                  
                                                                                                              
                                             
                                                        
                                                                      
                                                                                                              
                                                                                                                       
                                                                                                                         
                                                                                                                     
                                                                                                             
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section
section R028G3
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

/-- Transport of an `L²(μ)` seminorm to the raw coordinate law, when the two integrands agree a.e. along
the realization. -/
theorem r028_eLpNorm_transport (φ : RamerE c s → ℝ) (ψ : (ℤ → ℂ) → ℝ)
    (hφ : AEStronglyMeasurable φ (ramerGaussian c s))
    (hae : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      φ (NlsGge.Measure.fullWeightedSequenceRealization c s z) = ψ z) :
    eLpNorm φ 2 (ramerGaussian c s) =
      eLpNorm ψ 2 (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
  rw [r025_eLpNorm_transport c s φ hφ]
  exact eLpNorm_congr_ae hae

/-- An a.e. equality of the scalar limit transfers the convergence of the approximants. -/
theorem r028_tendsto_congr_ae (f : ℕ → (ℤ → ℂ) → ℝ) {η η' : (ℤ → ℂ) → ℝ}
    (h : η =ᵐ[NlsGge.Measure.fullWeightSequenceGaussian c.val] η')
    (ht : Tendsto (fun N => eLpNorm (fun z => f N z - η z) 2
      (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0)) :
    Tendsto (fun N => eLpNorm (fun z => f N z - η' z) 2
      (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0) := by
  refine ht.congr (fun N => ?_)
  apply eLpNorm_congr_ae
  filter_upwards [h] with z hz
  simp only [hz]

include hs in
/-- **E-level closed divergence of a raw limit.** If the raw field `G ∘ R` has the raw closed divergence `η'`
(strongly measurable), then `G` has the E-level closed divergence `η' ∘ coordE`. -/
theorem r028_isClosedDiv_of_raw (G : RamerE c s → RamerH c) (hG : ContDiff ℝ 2 G) (B : ℝ)
    (hB : ∀ x, ‖G x‖ ≤ B) (η : (ℤ → ℂ) → ℝ) (hηsm : StronglyMeasurable η)
    (hη : NlsGge.Ramer.IsClosedDiv c
      (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η) :
    IsClosedDiv c s G (fun x => η (NlsGge.Ramer.coordE c s x)) := by
  obtain ⟨hηL, N, g, Cg, p, hgC, hgb, hgd, hF, hD⟩ := hη
  have hcoord : Continuous (NlsGge.Ramer.coordE c s) := r021_continuous_coordE c s
  have hR : Measurable (NlsGge.Measure.fullWeightedSequenceRealization c s) :=
    NlsGge.Measure.measurable_fullWeightedSequenceRealization c s
  have hae := r025_ae_coord c s hs
  have hdm : StronglyMeasurable (fun x : RamerE c s => η (NlsGge.Ramer.coordE c s x)) :=
    hηsm.comp_measurable hcoord.measurable
  haveI : IsProbabilityMeasure (ramerGaussian c s) := by
    unfold ramerGaussian; infer_instance
  -- finite cores of the raw witnesses
  have hcore : ∀ k, GaussianL2CylindricalCore c (N k) (g k) := by
    intro k
    have hA : (0 : ℝ) ≤ |Cg k| := abs_nonneg _
    have hb : ∀ x, ‖g k x‖ ≤ |Cg k| * (1 + ‖x‖) ^ p k := fun x =>
      (hgb k x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    have hd : ∀ x, ‖fderiv ℝ (g k) x‖ ≤ |Cg k| * (1 + ‖x‖) ^ p k := fun x =>
      (hgd k x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    obtain ⟨h1, h2⟩ := r025_finite_core (g k) (hgC k) _ hA (p k) hb hd
    unfold GaussianL2CylindricalCore
    exact ⟨hgC k, h1, h2⟩
  -- the bounded field is in L²
  have hGL : MemLp G 2 (ramerGaussian c s) :=
    MemLp.of_bound hG.continuous.aestronglyMeasurable B (Eventually.of_forall hB)
  -- the scalar limit on E_s
  have hdL : MemLp (fun x : RamerE c s => η (NlsGge.Ramer.coordE c s x)) 2
      (ramerGaussian c s) := by
    have hmeas : AEStronglyMeasurable (fun x : RamerE c s => η (NlsGge.Ramer.coordE c s x))
        (Measure.map (NlsGge.Measure.fullWeightedSequenceRealization c s)
          (NlsGge.Measure.fullWeightSequenceGaussian c.val)) :=
      hdm.aestronglyMeasurable
    have hμ : ramerGaussian c s = (NlsGge.Measure.fullWeightSequenceGaussian c.val).map
        (NlsGge.Measure.fullWeightedSequenceRealization c s) := rfl
    rw [hμ, memLp_map_measure_iff hmeas hR.aemeasurable]
    refine hηL.ae_eq ?_
    filter_upwards [hae] with z hz
    show η z = η (NlsGge.Ramer.coordE c s (NlsGge.Measure.fullWeightedSequenceRealization c s z))
    rw [hz]
  -- the field limit on E_s
  have hFlim : Tendsto (fun k : ℕ => eLpNorm
      (fun x : RamerE c s => cylFieldE c s (N k) (g k) x - G x) 2 (ramerGaussian c s))
      atTop (𝓝 0) := by
    have hEq : ∀ k, eLpNorm (fun x : RamerE c s => cylFieldE c s (N k) (g k) x - G x) 2
        (ramerGaussian c s) = eLpNorm (fun z : ℤ → ℂ =>
          ‖NlsGge.Ramer.cylField c (N k) (g k) z -
            G (NlsGge.Measure.fullWeightedSequenceRealization c s z)‖) 2
          (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
      intro k
      have hA : AEStronglyMeasurable (fun x : RamerE c s => cylFieldE c s (N k) (g k) x - G x)
          (ramerGaussian c s) :=
        (r021_aesm_cylFieldE c s (N k) (μ := ramerGaussian c s) (g k) (hgC k).continuous).sub
          hG.continuous.aestronglyMeasurable
      calc eLpNorm (fun x : RamerE c s => cylFieldE c s (N k) (g k) x - G x) 2
            (ramerGaussian c s)
          = eLpNorm (fun x : RamerE c s => ‖cylFieldE c s (N k) (g k) x - G x‖) 2
              (ramerGaussian c s) := (eLpNorm_norm _ hA).symm
        _ = eLpNorm (fun z : ℤ → ℂ =>
              ‖cylFieldE c s (N k) (g k)
                (NlsGge.Measure.fullWeightedSequenceRealization c s z) -
                G (NlsGge.Measure.fullWeightedSequenceRealization c s z)‖) 2
              (NlsGge.Measure.fullWeightSequenceGaussian c.val) :=
            r025_eLpNorm_transport c s (fun x => ‖cylFieldE c s (N k) (g k) x - G x‖) hA.norm
        _ = eLpNorm (fun z : ℤ → ℂ =>
              ‖NlsGge.Ramer.cylField c (N k) (g k) z -
                G (NlsGge.Measure.fullWeightedSequenceRealization c s z)‖) 2
              (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
            refine eLpNorm_congr_ae ?_
            filter_upwards [hae] with z hz
            show ‖cylFieldE c s (N k) (g k)
                (NlsGge.Measure.fullWeightedSequenceRealization c s z) -
                G (NlsGge.Measure.fullWeightedSequenceRealization c s z)‖ =
              ‖NlsGge.Ramer.cylField c (N k) (g k) z -
                G (NlsGge.Measure.fullWeightedSequenceRealization c s z)‖
            unfold cylFieldE
            rw [hz]
    exact hF.congr (fun k => (hEq k).symm)
  -- the divergence limit on E_s
  have hDlim : Tendsto (fun k : ℕ => eLpNorm
      (fun x : RamerE c s => cylDivE c s (N k) (g k) x - η (NlsGge.Ramer.coordE c s x)) 2
      (ramerGaussian c s)) atTop (𝓝 0) := by
    have hEq2 : ∀ k, eLpNorm (fun x : RamerE c s =>
          cylDivE c s (N k) (g k) x - η (NlsGge.Ramer.coordE c s x)) 2 (ramerGaussian c s) =
        eLpNorm (fun z : ℤ → ℂ => NlsGge.Ramer.cylDiv c (N k) (g k) z - η z) 2
          (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
      intro k
      have hcd : Continuous (fun x : RamerE c s => cylDivE c s (N k) (g k) x) :=
        r021_continuous_cylDivE c s (N k) (g k) ((hgC k).of_le (by norm_num))
      have hA : AEStronglyMeasurable (fun x : RamerE c s =>
          cylDivE c s (N k) (g k) x - η (NlsGge.Ramer.coordE c s x)) (ramerGaussian c s) :=
        hcd.aestronglyMeasurable.sub hdm.aestronglyMeasurable
      refine r028_eLpNorm_transport c s _ _ hA ?_
      filter_upwards [hae] with z hz
      show cylDivE c s (N k) (g k)
          (NlsGge.Measure.fullWeightedSequenceRealization c s z) -
          η (NlsGge.Ramer.coordE c s (NlsGge.Measure.fullWeightedSequenceRealization c s z)) =
        NlsGge.Ramer.cylDiv c (N k) (g k) z - η z
      unfold cylDivE
      rw [hz]
    exact hD.congr (fun k => (hEq2 k).symm)
  unfold IsClosedDiv
  exact ⟨hGL, hdL, N, g, hcore, hFlim, hDlim⟩

/-- **G3, bounded transport.** For a bounded `C²` field `G` with bounded derivative there is an E-level
closed divergence `dG` whose `L²(μ)` approximants are the two Ramer and v2 approximants of `G`. -/
theorem r028_bounded_transport (G : RamerE c s → RamerH c) (hG : ContDiff ℝ 2 G)
    (hB : BoundedFieldAndDerivative G) :
    ∃ dG : RamerE c s → ℝ, IsClosedDiv c s G dG ∧
      Tendsto (fun N : ℕ => eLpNorm (fun x : RamerE c s => ramerApprox c s hs G N x - dG x) 2
        (ramerGaussian c s)) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => eLpNorm (fun x : RamerE c s => literalCylDiv c s G N x - dG x) 2
        (ramerGaussian c s)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hB
  have hGb : ∀ x, ‖G x‖ ≤ C := fun x => (hC x).1
  have hDb : ∀ x, ‖fderiv ℝ G x‖ ≤ C := fun x => (hC x).2
  obtain ⟨η, hηL, hlim1, hlim2⟩ :=
    NlsGge.Ramer.divergence_identification_bounded c s hs G hG C hGb hDb
  obtain ⟨η', hη'sm, hηae⟩ : ∃ η' : (ℤ → ℂ) → ℝ, StronglyMeasurable η' ∧
      η =ᵐ[NlsGge.Measure.fullWeightSequenceGaussian c.val] η' :=
    ⟨hηL.aestronglyMeasurable.mk η, hηL.aestronglyMeasurable.stronglyMeasurable_mk,
      hηL.aestronglyMeasurable.ae_eq_mk⟩
  have hη'L : MemLp η' 2 (NlsGge.Measure.fullWeightSequenceGaussian c.val) :=
    hηL.ae_eq hηae
  have hlim1' := r028_tendsto_congr_ae c
    (fun N z => NlsGge.Ramer.cylDiv c N (NlsGge.Ramer.truncField c s G N) z) hηae hlim1
  have hlim2' := r028_tendsto_congr_ae c
    (fun N z => NlsGge.Ramer.ramerA c s (le_of_lt (lt_trans (by norm_num) hs)) N G z) hηae hlim2
  have hdm : StronglyMeasurable (fun x : RamerE c s => η' (NlsGge.Ramer.coordE c s x)) :=
    hη'sm.comp_measurable (r021_continuous_coordE c s).measurable
  have hae := r025_ae_coord c s hs
  -- transport of the Ramer approximants
  have hT1 : ∀ N : ℕ, eLpNorm (fun x : RamerE c s =>
        ramerApprox c s hs G N x - η' (NlsGge.Ramer.coordE c s x)) 2 (ramerGaussian c s) =
      eLpNorm (fun z : ℤ → ℂ =>
        NlsGge.Ramer.ramerA c s (le_of_lt (lt_trans (by norm_num) hs)) N G z - η' z) 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
    intro N
    have hc : Continuous (fun x : RamerE c s => ramerApprox c s hs G N x) :=
      NlsGge.Ramer.continuous_ramerA_coordE c s hs N G (hG.of_le (by norm_num))
    have hA : AEStronglyMeasurable (fun x : RamerE c s =>
        ramerApprox c s hs G N x - η' (NlsGge.Ramer.coordE c s x)) (ramerGaussian c s) :=
      hc.aestronglyMeasurable.sub hdm.aestronglyMeasurable
    refine r028_eLpNorm_transport c s _ _ hA ?_
    filter_upwards [hae] with z hz
    show ramerApprox c s hs G N (NlsGge.Measure.fullWeightedSequenceRealization c s z) -
        η' (NlsGge.Ramer.coordE c s (NlsGge.Measure.fullWeightedSequenceRealization c s z)) =
      NlsGge.Ramer.ramerA c s (le_of_lt (lt_trans (by norm_num) hs)) N G z - η' z
    unfold ramerApprox
    rw [hz]
  -- transport of the v2 truncated divergences
  have hT2 : ∀ N : ℕ, eLpNorm (fun x : RamerE c s =>
        literalCylDiv c s G N x - η' (NlsGge.Ramer.coordE c s x)) 2 (ramerGaussian c s) =
      eLpNorm (fun z : ℤ → ℂ =>
        NlsGge.Ramer.cylDiv c N (NlsGge.Ramer.truncField c s G N) z - η' z) 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
    intro N
    have hc : Continuous (fun x : RamerE c s => literalCylDiv c s G N x) :=
      r021_continuous_cylDivE c s N (NlsGge.Ramer.truncField c s G N)
        ((NlsGge.Ramer.contDiff_truncField c s G hG N).of_le (by norm_num))
    have hA : AEStronglyMeasurable (fun x : RamerE c s =>
        literalCylDiv c s G N x - η' (NlsGge.Ramer.coordE c s x)) (ramerGaussian c s) :=
      hc.aestronglyMeasurable.sub hdm.aestronglyMeasurable
    refine r028_eLpNorm_transport c s _ _ hA ?_
    filter_upwards [hae] with z hz
    show literalCylDiv c s G N (NlsGge.Measure.fullWeightedSequenceRealization c s z) -
        η' (NlsGge.Ramer.coordE c s (NlsGge.Measure.fullWeightedSequenceRealization c s z)) =
      NlsGge.Ramer.cylDiv c N (NlsGge.Ramer.truncField c s G N) z - η' z
    unfold literalCylDiv
    rw [hz]
  have hφ1 : Tendsto (fun N : ℕ => eLpNorm (fun x : RamerE c s =>
      ramerApprox c s hs G N x - η' (NlsGge.Ramer.coordE c s x)) 2 (ramerGaussian c s))
      atTop (𝓝 0) :=
    hlim2'.congr (fun N => (hT1 N).symm)
  have hφ2 : Tendsto (fun N : ℕ => eLpNorm (fun x : RamerE c s =>
      literalCylDiv c s G N x - η' (NlsGge.Ramer.coordE c s x)) 2 (ramerGaussian c s))
      atTop (𝓝 0) :=
    hlim1'.congr (fun N => (hT2 N).symm)
  have hraw : NlsGge.Ramer.IsClosedDiv c
      (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η' :=
    NlsGge.Ramer.isClosedDiv_of_tendsto_truncField c s hs G hG C hGb hDb η' hη'L hlim1'
  exact ⟨fun x => η' (NlsGge.Ramer.coordE c s x),
    r028_isClosedDiv_of_raw c s hs G hG C hGb η' hη'sm hraw, hφ1, hφ2⟩

end R028G3
end
end NlsGge.ThirdConsultation.R
