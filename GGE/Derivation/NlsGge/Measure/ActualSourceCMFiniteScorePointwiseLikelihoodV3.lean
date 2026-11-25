import NlsGge.Measure.ActualSourceCMFiniteScoreL2LimitV2
import NlsGge.Measure.ActualSourceCMFiniteScoreExponentIdentityV2
import NlsGge.Measure.CountableGaussianCMLikelihoodRN
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace NlsGge.Measure

/-- The L² likelihood density from the actual raw-coordinate RN theorem agrees
almost everywhere with the exponential of the L² score limit minus half the
actual CM energy. The proof synchronizes AE subsequences of the score and
likelihood, then passes the finite exponent identity to their common limit. -/
theorem exists_actualSourceCMFiniteScore_pointwiseLikelihood_v3
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c)) :
    ∃ S L : MeasureTheory.Lp ℝ 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val),
      Tendsto (fun N : ℕ =>
        NlsGge.Measure.actualSourceCMFiniteScorePartialLp c x N)
        atTop (nhds S) ∧
      Tendsto (NlsGge.Measure.commonSourceLikelihoodLpSequenceOfMemLp
        lower upper c (NlsGge.Measure.actualSourceCMSequence c x)
        (fun N => NlsGge.Measure.memLp_commonSourceLikelihoodReal c N
          (NlsGge.Measure.actualSourceCMSequence c x)))
        atTop (nhds L) ∧
      (∀ᵐ z ∂NlsGge.Measure.fullWeightSequenceGaussian c.val,
        L z = Real.exp (S z -
          (∑' n : ℤ, NlsGge.Pilot.cmModeWeight c n *
            ‖NlsGge.Measure.actualSourceCMSequence c x n‖ ^ 2) / 2)) ∧
      (NlsGge.Measure.fullWeightSequenceGaussian c.val).map
        (fun z : ℤ → ℂ => fun n => z n + NlsGge.Measure.actualSourceCMSequence c x n) =
      (NlsGge.Measure.fullWeightSequenceGaussian c.val).withDensity
        (fun z => ENNReal.ofReal (L z)) := by
  obtain ⟨S, hS, hSmeas⟩ :=
    NlsGge.Measure.exists_actualSourceCMFiniteScoreL2Limit_v2 c x
  obtain ⟨L, hL, hnonneg, hmass, hRN⟩ :=
    NlsGge.Measure.exists_actualSourceCMCommonLikelihoodL2Limit_countableRN c x
  let μ : Measure (ℤ → ℂ) := NlsGge.Measure.fullWeightSequenceGaussian c.val
  let h : ℤ → ℂ := NlsGge.Measure.actualSourceCMSequence c x
  let hmem : ∀ N : ℕ, MeasureTheory.MemLp
      (fun z : ℤ → ℂ =>
        NlsGge.Measure.commonSourceLikelihoodReal lower upper c N h z)
      2 μ := fun N => NlsGge.Measure.memLp_commonSourceLikelihoodReal c N h
  let u : ℕ → MeasureTheory.Lp ℝ 2 μ :=
    NlsGge.Measure.commonSourceLikelihoodLpSequenceOfMemLp lower upper c h hmem
  have hL' : Tendsto u atTop (nhds L) := by
    simpa [u, hmem, h, μ] using hL
  have hScoreMeasure : MeasureTheory.TendstoInMeasure μ
      (fun N => NlsGge.Measure.actualSourceCMFiniteScorePartialLp c x N)
      atTop S :=
    MeasureTheory.tendstoInMeasure_of_tendsto_Lp hS
  have hLikelihoodMeasure : MeasureTheory.TendstoInMeasure μ (fun N => u N) atTop L :=
    MeasureTheory.tendstoInMeasure_of_tendsto_Lp hL'
  obtain ⟨ns, hns, hScoreAE⟩ := hScoreMeasure.exists_seq_tendsto_ae
  have hLikelihoodMeasureNS := hLikelihoodMeasure.comp hns.tendsto_atTop
  obtain ⟨ms, hms, hLikelihoodAE⟩ := hLikelihoodMeasureNS.exists_seq_tendsto_ae
  let idx : ℕ → ℕ := fun k => ns (ms k)
  have hScoreAESub : ∀ᵐ z ∂μ,
      Tendsto (fun k =>
        NlsGge.Measure.actualSourceCMFiniteScorePartialLp c x (idx k) z)
        atTop (nhds (S z)) := by
    filter_upwards [hScoreAE] with z hz
    have hcomp := hz.comp hms.tendsto_atTop
    simpa only [Function.comp_def, idx] using hcomp
  have hScoreRep : ∀ N : ℕ, ∀ᵐ z ∂μ,
      NlsGge.Measure.actualSourceCMFiniteScorePartialLp c x N z =
        NlsGge.Measure.actualSourceCMFiniteScorePartial c x N z := by
    intro N
    have hmemScore :=
      (NlsGge.Measure.hasGaussianLaw_fullWeightSequenceGaussian_partialScalar
        c 0 N (NlsGge.Measure.actualSourceCMFiniteScoreFunctional c x)).memLp_two
    have hsame :
        NlsGge.Measure.actualSourceCMFiniteScorePartialLp c x N =
          hmemScore.toLp (NlsGge.Measure.actualSourceCMFiniteScorePartial c x N) := by
      rfl
    filter_upwards [hmemScore.coeFn_toLp] with z hz
    rw [hsame]
    exact hz
  have hLikelihoodRep : ∀ N : ℕ, ∀ᵐ z ∂μ,
      u N z = NlsGge.Measure.commonSourceLikelihoodReal lower upper c N h z := by
    intro N
    filter_upwards [(hmem N).coeFn_toLp] with z hz
    simpa [u, NlsGge.Measure.commonSourceLikelihoodLpSequenceOfMemLp,
      NlsGge.Measure.commonSourceLikelihoodLpOfMemLp] using hz
  have hScoreRawAE : ∀ᵐ z ∂μ,
      Tendsto (fun k =>
        NlsGge.Measure.actualSourceCMFiniteScorePartial c x (idx k) z)
        atTop (nhds (S z)) := by
    filter_upwards [hScoreAESub, ae_all_iff.mpr hScoreRep] with z hz hrep
    exact hz.congr (fun k => hrep (idx k))
  have hLikelihoodRawAE : ∀ᵐ z ∂μ,
      Tendsto (fun k =>
        NlsGge.Measure.commonSourceLikelihoodReal lower upper c (idx k) h z)
        atTop (nhds (L z)) := by
    filter_upwards [hLikelihoodAE, ae_all_iff.mpr hLikelihoodRep] with z hz hrep
    exact hz.congr (fun k => hrep (idx k))
  have henergy : Tendsto
      (fun k => NlsGge.Measure.commonSourceLikelihoodEnergy lower upper c
        (idx k) h)
      atTop
      (nhds (∑' n : ℤ, NlsGge.Pilot.cmModeWeight c n *
        ‖NlsGge.Measure.actualSourceCMSequence c x n‖ ^ 2)) := by
    simpa only [Function.comp_def, idx, h] using
      (NlsGge.Measure.actualSourceCMPartialEnergyTendsto c x).comp
        (hns.comp hms).tendsto_atTop
  have hfinite (N : ℕ) (z : ℤ → ℂ) :
      NlsGge.Measure.commonSourceLikelihoodReal lower upper c N h z =
        Real.exp (NlsGge.Measure.actualSourceCMFiniteScorePartial c x N z -
          NlsGge.Measure.commonSourceLikelihoodEnergy lower upper c N h / 2) := by
    change Real.exp
        (NlsGge.Measure.commonSourceLikelihoodExponent lower upper c N h z) = _
    rw [NlsGge.Measure.actualSourceCMFiniteScoreExponentIdentity_v1 c x N z]
  have hformula : ∀ᵐ z ∂μ,
      L z = Real.exp (S z -
        (∑' n : ℤ, NlsGge.Pilot.cmModeWeight c n *
          ‖NlsGge.Measure.actualSourceCMSequence c x n‖ ^ 2) / 2) := by
    filter_upwards [hScoreRawAE, hLikelihoodRawAE,
      ae_all_iff.mpr hScoreRep, ae_all_iff.mpr hLikelihoodRep] with
      z hScore hLikelihood hScoreValues hLikelihoodValues
    have hScoreSub : Tendsto
        (fun k => NlsGge.Measure.actualSourceCMFiniteScorePartial c x (idx k) z)
        atTop (nhds (S z)) := hScore
    have hLikelihoodSub : Tendsto
        (fun k => NlsGge.Measure.commonSourceLikelihoodReal lower upper c
          (idx k) h z)
        atTop (nhds (L z)) := hLikelihood
    have hinner : Tendsto
        (fun k => NlsGge.Measure.actualSourceCMFiniteScorePartial c x (idx k) z -
          NlsGge.Measure.commonSourceLikelihoodEnergy lower upper c (idx k) h / 2)
        atTop
        (nhds (S z -
          (∑' n : ℤ, NlsGge.Pilot.cmModeWeight c n *
            ‖NlsGge.Measure.actualSourceCMSequence c x n‖ ^ 2) / 2)) := by
      exact hScoreSub.sub (henergy.div_const 2)
    have hexp := Real.continuous_exp.continuousAt.tendsto.comp hinner
    have hseq (k : ℕ) :
        NlsGge.Measure.commonSourceLikelihoodReal lower upper c (idx k) h z =
          Real.exp (NlsGge.Measure.actualSourceCMFiniteScorePartial c x (idx k) z -
            NlsGge.Measure.commonSourceLikelihoodEnergy lower upper c (idx k) h / 2) :=
      hfinite (idx k) z
    have hexpLikelihood := hexp.congr (fun k => (hseq k).symm)
    exact tendsto_nhds_unique hLikelihoodSub hexpLikelihood
  refine ⟨S, L, hS, hL', ?_, hRN⟩
  simpa [μ] using hformula

end NlsGge.Measure
