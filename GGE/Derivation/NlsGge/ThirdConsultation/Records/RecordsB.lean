import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W04WeightedSmoothing38c
import NlsGge.Birkhoff.W05FiniteGap38
import NlsGge.Birkhoff.W05ChargeSeries38
import NlsGge.Birkhoff.W06Jacobian38b
import NlsGge.Birkhoff.W07Probability38e
import NlsGge.Birkhoff.W08Compact38b
import NlsGge.Birkhoff.W09Approx38b
import NlsGge.Birkhoff.W10Localized38i
import NlsGge.Birkhoff.W11Equivalence38f
import NlsGge.Birkhoff.W12Bridge38
import NlsGge.Atomic.R.R098
import NlsGge.Atomic.R.R099
import NlsGge.Atomic.R.R100
import NlsGge.Atomic.R.R104
import NlsGge.Atomic.R.R105
import NlsGge.Atomic.R.R109
import NlsGge.Atomic.R.R110
import NlsGge.Atomic.R.R112
import NlsGge.Atomic.R.R115
import NlsGge.Atomic.R.R118
import NlsGge.Atomic.R.R119
import NlsGge.Atomic.R.R122
import NlsGge.Atomic.R.R130
import NlsGge.Atomic.R.R137
import NlsGge.Atomic.R.R138
import NlsGge.Atomic.R.R139
import NlsGge.Atomic.R.R147
import NlsGge.Atomic.T.T033

/-!
Author: proof development. Requested W04-W12 concrete record assembly, baseline bd117f03e.
The notation B/O below denotes the accepted actual pair, not theorem parameters.
Version 02: root repair attempt 1; explicit W08/W10/W11 conjunction proofs.
All heads are explicit conjunctions copied from the record declarations.
Canonical divergence/map/measurability premises are discharged inside proofs.
No worker compilation or independent statement acceptance is claimed.
-/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace Real ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Weights NlsGge.SpectralFoundations NlsGge.HierarchyRiccati.Core
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.Records
local notation "B" => NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38
local notation "O" => NlsGge.ThirdConsultation.PDE.actualOneSmoothingInput38

/-- Concrete assembly for W04; author candidate, compilation/review pending. -/
theorem W04_concrete {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) :
    (∀ x ∈ seqE38 c s, (B).T x - x ∈ seqE38 c (s - 1)) ∧
    (AnalyticOnNhd ℝ (eMap38 c s (s - 1) (fun y => (B).T y - y) ((B).K_mem_E38 O c s)) Set.univ) ∧
    (∀ x ∈ seqE38 c s, (B).Tinv x - x ∈ seqE38 c (s - 1)) ∧
    (AnalyticOnNhd ℝ (eMap38 c s (s - 1) (fun y => (B).Tinv y - y) ((B).Kinv_mem_E38 O c s))
      Set.univ) ∧
    (AnalyticOnNhd ℝ ((B).weightedHomeoE38 O c s) Set.univ) ∧
    (AnalyticOnNhd ℝ ((B).weightedHomeoE38 O c s).symm Set.univ) ∧
    (∀ y : ECarrier38 c s,
      eCoe38 c s ((B).weightedHomeoE38 O c s y) = (B).T (eCoe38 c s y)) ∧
    (∀ y : ECarrier38 c s,
      eCoe38 c s (((B).weightedHomeoE38 O c s).symm y) = (B).Tinv (eCoe38 c s y)) ∧
    (∀ hs : s ≤ 1,
      (∀ x ∈ seqE38 c s, (B).T x - x ∈ weightedSubmodule (cmModeWeight c)) ∧
      (∀ x ∈ seqE38 c s, (B).Tinv x - x ∈ weightedSubmodule (cmModeWeight c))) := by
  exact ⟨(B).K_mem_E38 O c s, NlsGge.ThirdConsultation.R.r098_main c s,
    (B).Kinv_mem_E38 O c s, (B).analytic_Kinv_E38 O c s,
    (B).analytic_weightedHomeoE38 O c s, NlsGge.ThirdConsultation.R.r099_main c s,
    (B).weightedHomeoE38_apply O c s, (B).weightedHomeoE38_symm_apply O c s,
    fun hs => NlsGge.ThirdConsultation.R.r100_main c hs⟩

/-- Concrete assembly for W05; author candidate, compilation/review pending. -/
theorem W05_concrete {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : s < 3 / 4) :
    ((∀ u : FinvE38 c s,
      Summable (fun n : ℤ => remainderSummand38 c.val u.1 n)) ∧
    @Continuous (FinvE38 c s) ℝ (topFinvE38 c s) _ (fun u => remainder38 c.val u.1) ∧
    (∀ u : FinvE38 c s, 0 ≤ remainder38 c.val u.1) ∧
    (∀ u : FinvE38 c s, spectralEnergyW38 c.val u.1 ≠ ⊤ →
      Summable (fun n : ℤ => fullWeightRate c.val n * ‖(B).Φ u.1 n‖ ^ 2) ∧
      (spectralEnergyW38 c.val u.1).toReal =
        ∑' n : ℤ, fullWeightRate c.val n * ‖(B).Φ u.1 n‖ ^ 2 + remainder38 c.val u.1)) ∧
    ((∀ u : FinvE38 c s, Summable (fun n : ℤ => remainderSummand38 c.val u.1 n)) ∧
    @Continuous (FinvE38 c s) ℝ (topFinvE38 c s) _ (fun u => remainder38 c.val u.1) ∧
    (∀ u : FinvE38 c s, 0 ≤ remainder38 c.val u.1) ∧
    (∀ u : FinvE38 c s, ∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
      smoothL2_38 U hU hper = u.1) ∧
    (∀ u : FinvE38 c s, ∀ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
      smoothL2_38 U hU hper = u.1 → chargeSeriesW38 c.val U ≠ ⊤ →
      Summable (fun n : ℤ => fullWeightRate c.val n * ‖(B).Φ u.1 n‖ ^ 2) ∧
      (chargeSeriesW38 c.val U).toReal =
        ∑' n : ℤ, fullWeightRate c.val n * ‖(B).Φ u.1 n‖ ^ 2 + remainder38 c.val u.1) ∧
    (∀ u : FinvE38 c s, ∀ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
      smoothL2_38 U hU hper = u.1 → spectralEnergyW38 c.val u.1 = chargeSeriesW38 c.val U)) ∧
    (∀ x : ECarrier38 c s,
      ∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
      smoothL2_38 U hU hper = physOfE38 c s x ∧
      spectralEnergyW38 c.val (physOfE38 c s x) =
        ∑' j : ℕ, ENNReal.ofReal (NlsGge.coefficient c.val j * localCharge38 U j)) ∧
    (Continuous (fun x : ECarrier38 c s => remainder38 c.val (physOfE38 c s x))) ∧
    (∀ (x : ECarrier38 c s) {Λ : ℕ → Finset ℤ}, IsExhaustion38 Λ →
      Tendsto (fun N : ℕ => (B).finiteGapApproxE38 c s O x (Λ N)) atTop (𝓝 x) ∧
    (∀ N : ℕ,
      physOfE38 c s ((B).finiteGapApproxE38 c s O x (Λ N)) =
        (B).cleanΦinv (projFin38 (Λ N) ((B).Φ (physOfE38 c s x)))) ∧
    (∀ N : ℕ, Summable (fun n : ℤ => remainderSummand38 c.val
        (physOfE38 c s ((B).finiteGapApproxE38 c s O x (Λ N))) n) ∧
      0 ≤ remainder38 c.val (physOfE38 c s ((B).finiteGapApproxE38 c s O x (Λ N)))) ∧
    Tendsto (fun N : ℕ => remainder38 c.val (physOfE38 c s ((B).finiteGapApproxE38 c s O x (Λ N))))
      atTop (𝓝 (remainder38 c.val (physOfE38 c s x))) ∧
    0 ≤ remainder38 c.val (physOfE38 c s x)) := by
  exact ⟨(B).W05_38 c s O hs, (B).W05_chargeSeries_38 O hs,
    spectralEnergyW38_eq_chargeSeries_physOfE38 c s, NlsGge.ThirdConsultation.R.r104_main c s hs,
    fun x {_} hΛ => NlsGge.ThirdConsultation.R.r105_main c s hs x hΛ⟩

/-- Concrete assembly for W06; author candidate, compilation/review pending. -/
theorem W06_concrete {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    (RamerDivergence38 c s ((B).KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) (NlsGge.ThirdConsultation.R.canonicalDelta c s hs (le_one_of_lt_three_quarters_W06_38 hs')) ∧
      ((NlsGge.Measure.fullWeightedSequenceGaussian c s).map (TW06_38 (B) O c s).symm =
          (NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity
            (fun x => ENNReal.ofReal (JW06_38 c s hs
              ((B).KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) (NlsGge.ThirdConsultation.R.canonicalDelta c s hs (le_one_of_lt_three_quarters_W06_38 hs')) x)) ∧
        (∀ x, 0 < JW06_38 c s hs ((B).KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) (NlsGge.ThirdConsultation.R.canonicalDelta c s hs (le_one_of_lt_three_quarters_W06_38 hs')) x) ∧
        Integrable (JW06_38 c s hs ((B).KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) (NlsGge.ThirdConsultation.R.canonicalDelta c s hs (le_one_of_lt_three_quarters_W06_38 hs')))
          (NlsGge.Measure.fullWeightedSequenceGaussian c s) ∧
        ∫ x, JW06_38 c s hs ((B).KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) (NlsGge.ThirdConsultation.R.canonicalDelta c s hs (le_one_of_lt_three_quarters_W06_38 hs')) x
          ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) = 1 ∧
        ((NlsGge.Measure.fullWeightedSequenceGaussian c s).map (TW06_38 (B) O c s) ≪
            NlsGge.Measure.fullWeightedSequenceGaussian c s ∧
          NlsGge.Measure.fullWeightedSequenceGaussian c s ≪
            (NlsGge.Measure.fullWeightedSequenceGaussian c s).map (TW06_38 (B) O c s)) ∧
        ((NlsGge.Measure.fullWeightedSequenceGaussian c s).map (TW06_38 (B) O c s).symm ≪
            NlsGge.Measure.fullWeightedSequenceGaussian c s ∧
          NlsGge.Measure.fullWeightedSequenceGaussian c s ≪
            (NlsGge.Measure.fullWeightedSequenceGaussian c s).map (TW06_38 (B) O c s).symm)) ∧
      ((∀ x, 0 < fW06_38 c s hs ((B).KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) (NlsGge.ThirdConsultation.R.canonicalDelta c s hs (le_one_of_lt_three_quarters_W06_38 hs')) x) ∧
        Integrable (fW06_38 c s hs ((B).KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) (NlsGge.ThirdConsultation.R.canonicalDelta c s hs (le_one_of_lt_three_quarters_W06_38 hs')))
          (NlsGge.Measure.fullWeightedSequenceGaussian c s) ∧
        ∫ x, fW06_38 c s hs ((B).KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) (NlsGge.ThirdConsultation.R.canonicalDelta c s hs (le_one_of_lt_three_quarters_W06_38 hs')) x
          ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) = (B).ZW38 c.val ∧
        (B).muW38 c.val = ENNReal.ofReal (1 / (B).ZW38 c.val) •
          ((NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity
            (fun x => ENNReal.ofReal (fW06_38 c s hs
              ((B).KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) (NlsGge.ThirdConsultation.R.canonicalDelta c s hs (le_one_of_lt_three_quarters_W06_38 hs')) x))).map
            (physFW06_38 c s) ∧
        (B).muW38 c.val =
          ((NlsGge.Measure.fullWeightedSequenceGaussian c s).map (physFW06_38 c s)).withDensity
            (fun u => ENNReal.ofReal (1 / (B).ZW38 c.val *
              physFun38 c s (fW06_38 c s hs
                ((B).KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) (NlsGge.ThirdConsultation.R.canonicalDelta c s hs (le_one_of_lt_three_quarters_W06_38 hs'))) u)) ∧
        ((B).muW38 c.val ≪
            (NlsGge.Measure.fullWeightedSequenceGaussian c s).map (physFW06_38 c s) ∧
          (NlsGge.Measure.fullWeightedSequenceGaussian c s).map (physFW06_38 c s) ≪
            (B).muW38 c.val))) ∧
    (IsProbabilityMeasure (NlsGge.Measure.fullWeightedSequenceGaussian c s) ∧
    (NlsGge.Measure.fullWeightedSequenceGaussian c s).Regular ∧
    (∀ U : Set (FullWeightedHilbert c s), IsOpen U → U.Nonempty →
      0 < NlsGge.Measure.fullWeightedSequenceGaussian c s U)) ∧
    ((∀ h : ActualCM c, ‖h‖ ^ 2 = 2 * ∑' n : ℤ, sourceRate c n * ‖cmCoord h n‖ ^ 2) ∧
    ((NlsGge.Analysis.RegularizedDeterminant.cmInclusionHS c s hs).toCLM = inclE c s hs) ∧
    ‖NlsGge.Analysis.RegularizedDeterminant.cmInclusionHS c s hs‖ ^ 2 =
      ∑' n : ℤ, Real.rpow (japaneseBracket n) (-2 * s)) ∧
    ((NlsGge.Measure.fullWeightedSequenceGaussian c s).map (physFW06_38 c s) =
      (NlsGge.Measure.fullWeightSequenceGaussian c.val).map
        (physFW06_38 c s ∘ NlsGge.Measure.fullWeightedSequenceRealization c s)) := by
  let hs1 : s ≤ 1 := le_one_of_lt_three_quarters_W06_38 hs'
  obtain ⟨hδ, hmap, hpos, hint, hone⟩ := NlsGge.ThirdConsultation.R.canonicalDelta_characterization c s hs hs1
  have hJ : AEMeasurable (fun x => ENNReal.ofReal (NlsGge.ThirdConsultation.R.actualRamerJac c s hs hs1 x))
      (fullWeightedSequenceGaussian c s) := hint.aemeasurable.ennreal_ofReal
  have hq := quasiInvariant_W06_38 (B) c s O
    (NlsGge.ThirdConsultation.R.actualRamerJac c s hs hs1) hmap hJ hpos
  have hd := density_W06_38 (B) c s O hs hs'
    (NlsGge.ThirdConsultation.R.actualRamerJac c s hs hs1) hmap hint hpos
  have hp := NlsGge.ThirdConsultation.R.actual_density_pushforward c s hs hs'
  have hm := muW38_eq_map_W06 (B) c s O hs hs'.le
    (NlsGge.ThirdConsultation.R.actualRamerJac c s hs hs1) hmap hJ
  exact ⟨⟨hδ, ⟨hmap, hpos, hint, hone, hq⟩,
    hp.1, hp.2.1, hp.2.2.1, hm, hd.2.2.2.2.1, hd.2.2.2.2.2⟩,
    W06_01_38 c s hs, W06_02_38 c s hs, gammaF_eq_W06_38 c s⟩

/-- Concrete assembly for W07; author candidate, compilation/review pending. -/
theorem W07_concrete {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    (RamerDivergence38 c s ((B).KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) (NlsGge.ThirdConsultation.R.canonicalDelta c s hs (le_one_of_lt_three_quarters_W06_38 hs')) ∧
      (∀ N : ℕ, ∫ x, fN38 c s N x ∂(fullWeightedSequenceGaussian c s) = relativePartition38 c N) ∧
      Integrable (fW06_38 c s hs ((B).KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) (NlsGge.ThirdConsultation.R.canonicalDelta c s hs (le_one_of_lt_three_quarters_W06_38 hs')))
        (fullWeightedSequenceGaussian c s) ∧
      ∫ x, fW06_38 c s hs ((B).KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) (NlsGge.ThirdConsultation.R.canonicalDelta c s hs (le_one_of_lt_three_quarters_W06_38 hs')) x
        ∂(fullWeightedSequenceGaussian c s) = (B).ZW38 c.val ∧
      TendstoInMeasure (fullWeightedSequenceGaussian c s) (fun N x => fN38 c s N x) atTop
        (fW06_38 c s hs ((B).KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) (NlsGge.ThirdConsultation.R.canonicalDelta c s hs (le_one_of_lt_three_quarters_W06_38 hs'))) ∧
      0 < (B).ZW38 c.val ∧
      (∀ a : ℝ, a < (B).ZW38 c.val → ∀ᶠ N : ℕ in atTop, a < relativePartition38 c N) ∧
      ENNReal.ofReal ((B).ZW38 c.val) ≤
        liminf (fun N : ℕ => ENNReal.ofReal (relativePartition38 c N)) atTop) ∧
    (∀ (hs1 : s ≤ 1) (N : ℕ) (x : FullWeightedHilbert c s),
      fN38 c s N x =
      Real.exp (-(remainder38 c.val (physOfE38 c s (projE38 c s N x)))) *
        Real.exp (-(‖(B).yN38 O c hs1 N x -
          ((cmTrunc c N ((B).yN38 O c hs1 N x) : actualCMHead c N) : ActualCM c)‖ ^ 2 / 2)) *
        Real.exp (-(‖(headPt c N (coordE c s x) : ActualCM c) +
          ((cmTrunc c N ((B).yN38 O c hs1 N x) : actualCMHead c N) : ActualCM c)‖ ^ 2 -
            ‖(headPt c N (coordE c s x) : ActualCM c)‖ ^ 2) / 2)) := by
  have hc := NlsGge.ThirdConsultation.R.actual_fN_tendstoInMeasure c s hs hs'
  obtain ⟨δ, hδ, hN, hi, hz, ht, hpos, hev, hlim⟩ := W07_38 (B) O c s hs hs'
  exact ⟨⟨(NlsGge.ThirdConsultation.R.canonicalDelta_characterization c s hs
      (le_one_of_lt_three_quarters_W06_38 hs')).1,
    hN, hc.1, hc.2.1, hc.2.2, hpos, hev, hlim⟩,
    fun hs1 N x => NlsGge.ThirdConsultation.R.r112_main c s hs' hs1 N x⟩

/-- Concrete assembly for W08; author candidate, compilation/review pending. -/
theorem W08_concrete (R : ℝ) :
    (IsCompact (closure (ballH1 R))) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ ballH1 R, ‖fderiv ℝ ((B).Kfwd1 O) x‖ ≤ C) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ ballH1 R, ∀ y ∈ ballH1 R,
      ‖(B).Kfwd1 O x - (B).Kfwd1 O y‖ ≤ C * ‖x - y‖) ∧
    (∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ ballH1 R, ∀ y ∈ ballH1 R,
      ‖x - y‖ ≤ L * ‖(B).TC 1 x - (B).TC 1 y‖) ∧
    ((∃ N₀ : ℕ, ∀ N ≥ N₀, Set.InjOn ((B).TN N) (ballV38 N R)) ∧
      (∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ x ∈ ballV38 N R,
        abs (|(B).detTN N x| - 1) < ε) ∧
      (∀ᶠ N : ℕ in atTop, ∀ x ∈ ballV38 N R,
        (B).detTN N x ≠ 0 ∧ |(B).detTN N x|⁻¹ ≤ 2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact isCompact_closure_ballH1 R
  · exact (B).exists_fderiv_Kfwd1_bound O R
  · exact NlsGge.ThirdConsultation.R.r118_main R
  · exact NlsGge.ThirdConsultation.R.r119_main R
  · refine ⟨?_, ?_, ?_⟩
    · exact (B).injOn_TN_ballV38 O R
    · exact (B).eventually_abs_detTN_sub_one_lt O R
    · exact NlsGge.ThirdConsultation.R.r122_main R

/-- Concrete assembly for W09; author candidate, compilation/review pending. -/
theorem W09_concrete {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)
    (z : ECarrier38 c s) :
    (∃ xN : ℕ → ECarrier38 c s,
      Tendsto xN atTop (𝓝 (((B).weightedHomeoE38 O c s).symm z)) ∧
      (∀ᶠ N in atTop, (B).GalerkinSol38 N (eCoe38 c s z) (eCoe38 c s (xN N))) ∧
      ∀ R : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ y w : H2_38, ‖y‖ ≤ R → ‖w‖ ≤ R →
        (B).GalerkinSol38 N (eCoe38 c s z) (carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y) →
        carrierCoe38 (((1 + 1 : ℕ)) : ℝ) w = eCoe38 c s (xN N) →
        (B).GalerkinSol38 N (eCoe38 c s z) (eCoe38 c s (xN N)) →
        carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y = eCoe38 c s (xN N)) ∧
    (∃ xN : ℕ → ECarrier38 c s,
      Tendsto xN atTop (𝓝 (((B).weightedHomeoE38 O c s).symm z)) ∧
      (∀ᶠ N in atTop, (B).GalerkinSol38 N (eCoe38 c s z) (eCoe38 c s (xN N))) ∧
      ∀ R : ℝ, ‖eToSob38 c s (((1 + 1 : ℕ)) : ℝ) (((B).weightedHomeoE38 O c s).symm z)‖ < R →
        ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ y : H2_38, ‖y‖ ≤ R →
          (B).GalerkinSol38 N (eCoe38 c s z) (carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y) →
          carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y = eCoe38 c s (xN N)) ∧
    (∀ R : ℝ,
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ ζ : ℤ → ℂ, ∀ y w : H2_38, ‖y‖ ≤ R → ‖w‖ ≤ R →
      (B).GalerkinSol38 N ζ (carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y) →
      (B).GalerkinSol38 N ζ (carrierCoe38 (((1 + 1 : ℕ)) : ℝ) w) →
      carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y = carrierCoe38 (((1 + 1 : ℕ)) : ℝ) w) := by
  exact ⟨(B).W09_localGalerkinInverse O c s z,
    (B).W09_localGalerkinInverse_ball O c s z, NlsGge.ThirdConsultation.R.r130_main⟩

/-- Concrete assembly for W10; author candidate, compilation/review pending. -/
theorem W10_concrete {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4)
    {χ : ℝ → ℝ} {R : ℝ} (hχ : CutoffProfile38 χ) (hR : 0 < R) :
    ((∀ F : PhysicalL2 → ℝ, Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)) →
      (∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) →
      Tendsto (fun N : ℕ => ∫ x, F (physOfE38 c s (projE38 c s N x)) *
          chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
          ∂(fullWeightedSequenceGaussian c s))
        atTop (𝓝 ((B).ZW38 c.val * ∫ u, F u * chiR38 χ R u ∂((B).muW38 c.val)))) ∧
    (∀ (r : ℝ) (hr : 0 ≤ r) (F : PhysicalL2 → ℝ),
      Continuous (fun y : SobolevCarrier38 r => F (physOfCarrier38 r hr y)) →
      (∃ M, ∀ y : SobolevCarrier38 r, |F (physOfCarrier38 r hr y)| ≤ M) →
      Tendsto (fun N : ℕ => ∫ x, F (physOfE38 c s (projE38 c s N x)) *
          chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
          ∂(fullWeightedSequenceGaussian c s))
        atTop (𝓝 ((B).ZW38 c.val * ∫ u, F u * chiR38 χ R u ∂((B).muW38 c.val)))) ∧
    (0 < ∫ u, chiR38 χ R u ∂((B).muW38 c.val) ∧
      IsProbabilityMeasure ((B).locLimitLaw38 c χ R) ∧
      (∀ F : PhysicalL2 → ℝ, Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)) →
        (∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) →
        Tendsto (fun N : ℕ =>
          (∫ x, F (physOfE38 c s (projE38 c s N x)) *
            chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
            ∂(fullWeightedSequenceGaussian c s)) /
          ∫ x, chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
            ∂(fullWeightedSequenceGaussian c s)) atTop
          (𝓝 (∫ u, F u ∂((B).locLimitLaw38 c χ R)))) ∧
      (∀ (r : ℝ) (hr : 0 ≤ r) (F : PhysicalL2 → ℝ),
        Continuous (fun y : SobolevCarrier38 r => F (physOfCarrier38 r hr y)) →
        (∃ M, ∀ y : SobolevCarrier38 r, |F (physOfCarrier38 r hr y)| ≤ M) →
        Tendsto (fun N : ℕ =>
          (∫ x, F (physOfE38 c s (projE38 c s N x)) *
            chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
            ∂(fullWeightedSequenceGaussian c s)) /
          ∫ x, chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
            ∂(fullWeightedSequenceGaussian c s)) atTop
          (𝓝 (∫ u, F u ∂((B).locLimitLaw38 c χ R)))))) ∧
    (∀ N : ℕ, Integrable (fN38 c s N) (fullWeightedSequenceGaussian c s)) ∧
    (∃ χ : ℝ → ℝ, CutoffProfile38 χ) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro F hF hFb
      exact NlsGge.ThirdConsultation.R.r137_main c s hs hs' hχ hR F hF hFb
    · intro r hr F hF hFb
      exact (B).W10_localized_Sobolev38 O c hs hs' hχ hR r hr F hF hFb
    · refine ⟨?_, ?_, ?_, ?_⟩
      · exact NlsGge.ThirdConsultation.R.r138_main c s hs hs' hχ hR
      · exact (B).isProbabilityMeasure_locLimitLaw38 O c hs hs' hχ hR
      · intro F hF hFb
        exact (NlsGge.ThirdConsultation.R.r139_main c s hs hs' hχ hR F hF hFb).2
      · intro r hr F hF hFb
        exact NlsGge.ThirdConsultation.R.r139_2 c s hs hs' hχ hR r hr F hF hFb
  · intro N
    exact NlsGge.Birkhoff.BirkhoffInput38.integrable_fN38 c hs N
  · exact exists_cutoffProfile38

/-- Concrete assembly for W11; author candidate, compilation/review pending. -/
theorem W11_concrete {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    (RamerDivergence38 c s ((B).KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) (NlsGge.ThirdConsultation.R.canonicalDelta c s hs (le_one_of_lt_three_quarters_W06_38 hs'))) ∧
    (List.TFAE
        [ W11Normalizer38 (B) c,
          Tendsto (fun N : ℕ => ∫ x, |fN38 c s N x -
              fW06_38 c s hs ((B).KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) (NlsGge.ThirdConsultation.R.canonicalDelta c s hs (le_one_of_lt_three_quarters_W06_38 hs')) x|
            ∂(fullWeightedSequenceGaussian c s)) atTop (𝓝 0),
          UniformIntegrable (fun N x => fN38 c s N x) 1 (fullWeightedSequenceGaussian c s),
          W11Weak38 (B) c s,
          W11Tight38 c ]) ∧
    (List.TFAE [
      Tendsto (fun N : ℕ => relativePartition38 c N) atTop (𝓝 ((B).ZW38 c.val)),
      NlsGge.ThirdConsultation.R.L1Converges (fullWeightedSequenceGaussian c s) (fun N : ℕ => fN38 c s N)
        (NlsGge.ThirdConsultation.R.actualRamerDensity c s hs (le_one_of_lt_three_quarters_W06_38 hs')),
      UniformIntegrable (fun N : ℕ => fN38 c s N) 1 (fullWeightedSequenceGaussian c s),
      W11Weak38 (B) c s,
      W11Tight38 c]) ∧
    (∀ (χ : ℝ → ℝ), CutoffProfile38 χ → ∀ R : ℝ, 0 < R →
      Tendsto (fun N : ℕ => ∫ x, chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
        ∂(fullWeightedSequenceGaussian c s)) atTop
      (𝓝 ((B).ZW38 c.val * ∫ u, chiR38 χ R u ∂((B).muW38 c.val))) ∧
    0 < (B).ZW38 c.val * ∫ u, chiR38 χ R u ∂((B).muW38 c.val) ∧
    ∀ᶠ N : ℕ in atTop, 0 < ∫ x, chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
        ∂(fullWeightedSequenceGaussian c s)) ∧
    (∀ (χ : ℝ → ℝ), CutoffProfile38 χ → ∀ R : ℝ, 0 < R → ∀ u : PhysicalL2,
      0 ≤ 1 - chiR38 χ R u ∧ 1 - chiR38 χ R u ≤ (h2Tail38 R).indicator 1 u) := by
  have hδ := (NlsGge.ThirdConsultation.R.canonicalDelta_characterization c s hs
    (le_one_of_lt_three_quarters_W06_38 hs')).1
  refine ⟨hδ, ?_, ?_, ?_, ?_⟩
  · exact ((B).W11_38 O c hs hs').2 _ hδ
  · exact NlsGge.ThirdConsultation.R.actual_W11 c s hs hs'
  · intro χ hχ radius hr
    exact (B).W10_F1_W11 O c hs hs' (χ := χ) (R := radius) hχ hr
  · intro χ hχ radius hr u
    exact NlsGge.Birkhoff.BirkhoffInput38.one_sub_chiR_le_indicator_W11
      (χ := χ) (R := radius) hχ hr u

/-- Concrete assembly for W12; author candidate, compilation/review pending. -/
theorem W12_concrete {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ * upper < lower)
    {s : ℝ} (hs : s < 3 / 4) :
    (((∀ u : FinvE38 c s, EB38 c.val u.1 ≠ ⊤) ∧
      @Continuous (FinvE38 c s) ℝ (topFinvE38 c s) _ (fun u => (EB38 c.val u.1).toReal)) ∧
    (0 < Dtilt38 c.val δ ∧
      HasProd (fun n : ℤ => 1 - δ * bRate38 c.val n / fullWeightRate c.val n)
        (Dtilt38 c.val δ)) ∧
    (Integrable (fun u => Real.exp (δ * (EB38 c.val u).toReal)) ((B).muW38 c.val) ∧
      (∀ᵐ u ∂((B).muW38 c.val), EB38 c.val u ≠ ⊤) ∧
      ∫ u, Real.exp (δ * (EB38 c.val u).toReal) ∂((B).muW38 c.val) =
        (B).ZW38 (tiltCoef38 c.val δ) / ((B).ZW38 c.val * Dtilt38 c.val δ)) ∧
    (∀ u : FinvE38 c s,
      ENNReal.ofReal (weight c.val ‖u.1‖ - NlsGge.coefficient c.val 0) ≤ EB38 c.val u.1)) ∧
    (∫⁻ u, ENNReal.ofReal (Real.exp (δ * (EB38 c.val u).toReal)) ∂((B).muW38 c.val) =
      ENNReal.ofReal ((B).ZW38 (tiltCoef38 c.val δ) / ((B).ZW38 c.val * Dtilt38 c.val δ))) ∧
    (fullWeightSequenceGaussian (tiltCoef38 c.val δ) =
      (fullWeightSequenceGaussian c.val).withDensity
        (fun z => ENNReal.ofReal (Dtilt38 c.val δ * Real.exp (δ * bEnergy38 c.val z)))) ∧
    (∀ u : FinvE38 c s,
      ∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
      smoothL2_38 U hU hper = u.1 ∧ EB38 c.val u.1 = chargeSeriesW38 (bCoef38 c.val) U) ∧
    (∀ᵐ u ∂((B).muW38 c.val), ∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
      smoothL2_38 U hU hper = u ∧ EB38 c.val u = chargeSeriesW38 (bCoef38 c.val) U) ∧
    ((∀ᵐ u ∂NlsGge.ThirdConsultation.T.muW c, EB38 c.val u ≠ ⊤) ∧
    Integrable (fun u : PhysicalL2 => Real.exp (δ * (EB38 c.val u).toReal))
      (NlsGge.ThirdConsultation.T.muW c) ∧
    (∫ u : PhysicalL2, Real.exp (δ * (EB38 c.val u).toReal) ∂NlsGge.ThirdConsultation.T.muW c) =
      NlsGge.ThirdConsultation.T.ZW (tiltBounded38 c hδ0 hδ) / (NlsGge.ThirdConsultation.T.ZW c * NlsGge.ThirdConsultation.T.Ddelta c δ)) := by
  exact ⟨(B).W12_38 O c hδ0 hδ hs, (B).tilt_lintegral_W12_38 c hδ0 hδ,
    gaussian_tilt_density38 c hδ0 hδ, EB38_eq_chargeSeries_FinvE38 c s,
    (B).ae_EB38_eq_chargeSeries c,
    NlsGge.ThirdConsultation.T.lowerWeightTilt_exact_moment lower upper c δ hδ0 hδ⟩

end NlsGge.ThirdConsultation.Records
end
