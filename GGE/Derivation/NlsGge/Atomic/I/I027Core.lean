import Mathlib
import NlsGge.Atomic.I.I033Core
import NlsGge.Atomic.I.IEnsembleCore

/- I-027 CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). SUPPORT (no packet increment).
   Target NlsGge/Atomic/I/I027Core.lean, namespace NlsGge.ThirdConsultation.I027C.
   Pro's route (v2 text after A:eq:weakconvergence and the positivity-of-actions argument in A:thm:main;
   Birkhoff/S04Moments38 l1_density_convergence38), for any house record Bk with hB (glue: the round-14 bridge):
   * L¹: pointwise for EVERY z, ρN N z = e^{-R̄(P_Λ z)}/Z_Λ (P_Λ z ∈ Ω₀ always; IEnsC finite identities), and
     ρ =ᵐ e^{-R̄}/Z_W (IEnsC.remainder_ae_of, ZW_eq_of); then the landed l1_density_convergence38.  Integrability:
     the R̄-form is measurable and bounded by 1/Z_Λ + 1/Z_W, and the ρN-form agrees with it a.e.
   * actions: a complex Gaussian with positive rate has no atom at 0 (component laws gaussianReal with positive
     variance 1/(2a) have null singletons), so γ_W-a.s. every coordinate is nonzero; on Ω₀ the action of Φ⁻¹z is |z_n|²
     (action_cleanΦinv38); transfer to the weighted law by μ ≪ γ_W, then through the measurable map physicalOfSequence
     to the field law (the set {∀ n, 0 < I_n} is measurable: L²-continuity of every actual action, landed S7).
   * singularity (COMPARES THE ACTUAL FIELD LAWS): every finite-gap field Φ⁻¹(extZero S w) has I_n = 0 for n ∉ S,
     so the finite-gap law gives measure 0 to {∀ n, 0 < I_n}, which carries the full physical law. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology NNReal
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.I

namespace NlsGge.ThirdConsultation.I027C

theorem complexGaussian_zero (a : ℝ) (ha : 0 < a) : complexGaussian a {0} = 0 := by
  have hv : componentVariance a ≠ 0 := by
    unfold componentVariance
    exact (Real.toNNReal_pos.2 (by positivity)).ne'
  haveI := ProbabilityTheory.nullSingletonClass_gaussianReal (μ := 0) hv
  unfold complexGaussian
  rw [Measure.map_apply Complex.measurableEquivRealProd.symm.measurable (measurableSet_singleton 0)]
  refine measure_mono_null (t := ({0} : Set ℝ) ×ˢ Set.univ) (fun p hp => ?_) ?_
  · have h0 : Complex.measurableEquivRealProd.symm p = 0 := hp
    have h1 := congrArg Complex.re h0
    simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true]
    simpa [Complex.measurableEquivRealProd, Complex.equivRealProd] using h1
  · rw [Measure.prod_prod, measure_singleton, zero_mul]

theorem coord_ne_zero_ae (q : ℤ → ℝ) (hq : ∀ n, 0 < q n) :
    ∀ᵐ z ∂countableComplexGaussian q, ∀ n : ℤ, z n ≠ 0 := by
  rw [ae_all_iff]
  intro n
  rw [ae_iff]
  have e : {z : ℤ → ℂ | ¬ z n ≠ 0} = (fun z : ℤ → ℂ => z n) ⁻¹' {0} := by
    ext z; simp
  rw [e, ← Measure.map_apply (measurable_pi_apply n) (measurableSet_singleton _)]
  unfold countableComplexGaussian
  rw [Measure.infinitePi_map_eval]
  exact complexGaussian_zero (q n) (hq n)

theorem measurableSet_actions_pos :
    MeasurableSet {u : PhysicalL2 | ∀ n : ℤ, 0 < actualGapActionAllE02_38 u n} := by
  rw [Set.setOf_forall]
  exact MeasurableSet.iInter fun n =>
    measurableSet_lt measurable_const (NlsGge.GK38.gapAction_L2_continuous38 n).measurable

theorem i027_of (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (Λ : ℕ → Finset ℤ) (hΛ : IsExhaustion38 Λ) :
    let W := weight c.val
    let ρ := fun z : ℤ → ℂ => Real.exp (-sequenceRemainder W z) / limitNormalizer W
    let ρN := fun (N : ℕ) (z : ℤ → ℂ) =>
      Real.exp (-remainderForWeight W (physicalOfSequence (projFin38 (Λ N) z))) /
        finiteRelativeNormalizer W (Λ N)
    (∀ N : ℕ, Integrable (fun z : ℤ → ℂ => |ρN N z - ρ z|)
      (fullWeightSequenceGaussian c.val)) ∧
    Tendsto (fun N : ℕ => ∫ z : ℤ → ℂ, |ρN N z - ρ z|
      ∂fullWeightSequenceGaussian c.val) atTop (𝓝 0) ∧
    (∀ᵐ u ∂physicalLaw W, ∀ n : ℤ, 0 < actualGapActionAllE02_38 u n) ∧
    ∀ S : Finset ℤ, (finiteGapLaw W S).MutuallySingular (physicalLaw W) := by
  dsimp only
  obtain ⟨hl, _hlu, hb⟩ := c.property
  have hb' : ∀ j : ℕ, lower ≤ c.val j := fun j => (hb j).1
  have hu' : ∀ j : ℕ, c.val j ≤ upper := fun j => (hb j).2
  have hW := weight_continuous38 hl hb' hu'
  have hRm := NlsGge.ThirdConsultation.I033C.measurable_sequenceRemainder Bk hB (weight c.val) hW
  have h0 := NlsGge.ThirdConsultation.I033C.sequenceRemainder_nonneg (weight c.val)
  have hPm : Measurable physicalOfSequence := by
    rw [show physicalOfSequence = Bk.cleanΦinv from (funext hB).symm]
    exact Bk.measurable_cleanΦinv
  have hfin := fun S : Finset ℤ => NlsGge.ThirdConsultation.IEnsC.ensemble_finite_of Bk hB lower upper c S
  have hZW := NlsGge.ThirdConsultation.IEnsC.ZW_eq_of Bk hB lower upper c
  have hae := NlsGge.ThirdConsultation.IEnsC.remainder_ae_of Bk hB lower upper c
  obtain ⟨hZ, -⟩ := Bk.ZW38_pos_le_one lower upper c.val hl hb' hu'
  -- pointwise form of the finite-cutoff density
  have hρN : ∀ (N : ℕ) (z : ℤ → ℂ),
      Real.exp (-remainderForWeight (weight c.val) (physicalOfSequence (projFin38 (Λ N) z))) /
        finiteRelativeNormalizer (weight c.val) (Λ N) =
      Real.exp (-(Bk.Rbar38 c.val (projFin38 (Λ N) z))) / Bk.ZΛ38 c.val (Λ N) := by
    intro N z
    rw [← (hfin (Λ N)).1, Bk.Rbar38_of_mem c.val (projFin38_mem_Omega038 c.val (Λ N) z),
      ← NlsGge.ThirdConsultation.I017C.remainderForWeight_eq c.val hW, hB]
  have hρ : ∀ᵐ z ∂fullWeightSequenceGaussian c.val,
      Real.exp (-sequenceRemainder (weight c.val) z) / limitNormalizer (weight c.val) =
        Real.exp (-(Bk.Rbar38 c.val z)) / Bk.ZW38 c.val := by
    filter_upwards [hae] with z hz
    rw [hz, hZW]
  have hdiff : ∀ N : ℕ, (fun z : ℤ → ℂ =>
      |Real.exp (-(Bk.Rbar38 c.val (projFin38 (Λ N) z))) / Bk.ZΛ38 c.val (Λ N) -
        Real.exp (-(Bk.Rbar38 c.val z)) / Bk.ZW38 c.val|) =ᵐ[fullWeightSequenceGaussian c.val]
      (fun z : ℤ → ℂ =>
      |Real.exp (-remainderForWeight (weight c.val) (physicalOfSequence (projFin38 (Λ N) z))) /
          finiteRelativeNormalizer (weight c.val) (Λ N) -
        Real.exp (-sequenceRemainder (weight c.val) z) / limitNormalizer (weight c.val)|) := by
    intro N
    filter_upwards [hρ] with z hz
    rw [hρN N z, hz]
  have hRbm := Bk.measurable_Rbar38 lower upper c.val hl hb' hu'
  -- absolute continuity of the weighted law
  have hac : weightedSequenceLaw (weight c.val) ≪ fullWeightSequenceGaussian c.val := by
    rw [NlsGge.ThirdConsultation.I033C.law_eq]; exact gibbsLaw38_ac _ _ hRm h0
  have hq : ∀ n : ℤ, 0 < fullWeightRate c.val n := fun n => fullWeightRate_pos lower upper c.val hl hb' hu' n
  have hA := measurableSet_actions_pos
  have hpos : ∀ᵐ u ∂physicalLaw (weight c.val), ∀ n : ℤ, 0 < actualGapActionAllE02_38 u n := by
    unfold physicalLaw
    rw [ae_map_iff hPm.aemeasurable hA]
    refine hac.ae_le ?_
    filter_upwards [ae_mem_Omega038 lower upper c.val hl hb' hu', coord_ne_zero_ae _ hq] with z hz hz0
    intro n
    have hz1 := BirkhoffTop38.mem_seqSobolev38_of_Omega038 c.val hz 1
    rw [← hB, Bk.action_cleanΦinv38 z hz1 n]
    exact pow_pos (norm_pos_iff.2 (hz0 n)) 2
  refine ⟨fun N => ?_, ?_, hpos, fun S => ?_⟩
  · obtain ⟨hZN, -⟩ := Bk.ZΛ38_pos_le_one lower upper c.val hl hb' hu' (Λ N)
    refine Integrable.congr ?_ (hdiff N)
    refine Integrable.of_bound (C := 1 / Bk.ZΛ38 c.val (Λ N) + 1 / Bk.ZW38 c.val)
      ((((Real.measurable_exp.comp (hRbm.comp (measurable_projFin38 (Λ N))).neg).div_const _).sub
        ((Real.measurable_exp.comp hRbm.neg).div_const _)).abs.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_abs]
    have e1 : Real.exp (-(Bk.Rbar38 c.val (projFin38 (Λ N) z))) ≤ 1 :=
      Bk.exp_neg_Rbar38_le_one lower upper c.val hl hb' hu' _
    have e2 : Real.exp (-(Bk.Rbar38 c.val z)) ≤ 1 := Bk.exp_neg_Rbar38_le_one lower upper c.val hl hb' hu' _
    have p1 := Real.exp_pos (-(Bk.Rbar38 c.val (projFin38 (Λ N) z)))
    have p2 := Real.exp_pos (-(Bk.Rbar38 c.val z))
    have d1 : Real.exp (-(Bk.Rbar38 c.val (projFin38 (Λ N) z))) / Bk.ZΛ38 c.val (Λ N) ≤ 1 / Bk.ZΛ38 c.val (Λ N) :=
      div_le_div_of_nonneg_right e1 hZN.le
    have d2 : Real.exp (-(Bk.Rbar38 c.val z)) / Bk.ZW38 c.val ≤ 1 / Bk.ZW38 c.val :=
      div_le_div_of_nonneg_right e2 hZ.le
    have n1 : 0 ≤ Real.exp (-(Bk.Rbar38 c.val (projFin38 (Λ N) z))) / Bk.ZΛ38 c.val (Λ N) :=
      div_nonneg p1.le hZN.le
    have n2 : 0 ≤ Real.exp (-(Bk.Rbar38 c.val z)) / Bk.ZW38 c.val := div_nonneg p2.le hZ.le
    rw [abs_le]
    constructor <;> linarith
  · have h := Bk.l1_density_convergence38 lower upper c.val hl hb' hu' hΛ
    refine h.congr (fun N => integral_congr_ae (hdiff N))
  · refine ⟨{u : PhysicalL2 | ∀ n : ℤ, 0 < actualGapActionAllE02_38 u n}, hA, ?_, ?_⟩
    · unfold finiteGapLaw
      rw [Measure.map_apply ((NlsGge.ThirdConsultation.I017C.field_eq38 Bk hB S) ▸
        Bk.measurable_finiteGapField38 S) hA]
      have hempty : finiteGapField S ⁻¹' {u : PhysicalL2 | ∀ n : ℤ, 0 < actualGapActionAllE02_38 u n} = ∅ := by
        ext w
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall, not_lt]
        obtain ⟨n, -, hn⟩ := (Set.infinite_univ.diff S.finite_toSet).nonempty
        have hnS : n ∉ S := hn
        have hmem : extZero38 S w ∈ Omega038 c.val := by
          have := projFin38_mem_Omega038 c.val S (extZero38 S w)
          rwa [projFin38_extZero38] at this
        have hz1 := BirkhoffTop38.mem_seqSobolev38_of_Omega038 c.val hmem 1
        refine ⟨n, ?_⟩
        show actualGapActionAllE02_38 (physicalOfSequence (extZero38 S w)) n ≤ 0
        rw [← hB, Bk.action_cleanΦinv38 _ hz1 n, extZero38_apply_of_not_mem w hnS, norm_zero]
        norm_num
      rw [hempty, measure_empty]
    · exact ae_iff.1 hpos

end NlsGge.ThirdConsultation.I027C
