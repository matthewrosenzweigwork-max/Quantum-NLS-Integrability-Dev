import NlsGge.Birkhoff.W06Jacobian38b
import NlsGge.Birkhoff.W07Probability38e
import NlsGge.Birkhoff.W08Compact38b
import NlsGge.Birkhoff.W09Approx38b
import NlsGge.Birkhoff.W10Localized38i
import NlsGge.Birkhoff.F09Limit38g
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing

/-!
# Actual Birkhoff consumers B: additive author wrappers

Source: `paper/v2.tex`, SHA256
`0e7c2e61a06ab6886124c3891c73e0b8997ab71473eaf75b05c524098a58e3ec`.
This file specializes generic declarations to the SAME actual Birkhoff and
one-smoothing producers. Every other generic binder is retained. This is an
author submission for independent semantic review, not claim acceptance.

Source bundles and their existing generic declarations:

* W06, `D:thm:Ramer`, lines 1521-1543: `W06_38` gives both inverse Gaussian
  change of variables and the physical density/equivalence, with the same
  existential divergence. `W06_01_38` and `W06_02_38` give the full-support
  Gaussian and the real Cameron-Martin normalization used in its proof.
  `ramer_W06_38`, `muW38_eq_map_W06`, and `gammaF_eq_W06_38` are constituent
  identities already assembled by that headline, not additional premises.
* W07, `D:prop:probability`, lines 1554-1574: `W07_38` gives probability
  convergence and the normalizer liminf. `fN38_decomp` is the full finite
  energy decomposition (lines 1567-1571); `integral_fN38` is in the headline.
  `integrable_fN38` certifies that its finite integrals are Bochner integrals.
  The later remark about convergence of negative logarithms has no separate
  generic declaration located in the inspected Birkhoff sources; no wrapper
  for that additional assertion is claimed here.
* W08, `D:lem:localinject`, lines 1587-1614:
  `W08_localInject_determinant` includes eventual injectivity, uniform absolute
  determinant convergence, nonvanishing, and the reciprocal bound for EVERY
  real radius. Compactness and the two Lipschitz bounds are proof ingredients
  in `W08Compact38`, already consumed by the headline.
* W09, `D:lem:localinverse`, lines 1616-1633: BOTH
  `W09_localGalerkinInverse` (common fixed ball uniqueness) and
  `W09_localGalerkinInverse_ball` (eventual uniqueness above the inverse norm)
  are specialized without a derivative or Newton hypothesis.
* W10, `D:thm:localized`, lines 1635-1663: `W10_38` jointly contains weighted
  and ordinary Sobolev test convergence, positive localized normalizer, and
  both normalized conclusions. `integrable_locIntegrand38`,
  `integrable_chiR_fN38`, and `integrable_F_chiR_muW38` supply its integrability
  companions. `exists_cutoffProfile38` is an imported proved existence fact;
  the arbitrary profile/radius binders of the generic theorem are preserved.
* NEW-F09, `F:cor:limit`, lines 1702-1722 and 1774-1794: `F09_38` jointly
  gives normalizers with a uniform positive lower bound, unnormalized tests,
  normalized weak convergence, a uniform normalized exponential H2 moment,
  and sequence/physical common-Gaussian L1 convergence, with one divergence.

Stopped records: the following required modules have NO object in the prescribed
CleanBuildX55-20261110 parent and are outside its root-closure order list. They
are neither imported nor rebuilt by this author:

* W11: `W11Equivalence38f` (`W11_38`, the five-entry TFAE, also containing the
  uniform-integrability formulation of the source's four criteria).
* W12: `W12Bridge38` (`EB38_eq_chargeSeries_FinvE38` and
  `BirkhoffInput38.ae_EB38_eq_chargeSeries`), required with `W12_38` to identify
  the spectral EB functional with the source's lower local-charge series.
* NEW-F10: `F10Bridge38` (`L1_F10_forall_delta38`) and `F10Claim38`
  (`L1_F10_38`); the existential L1 assertion already in NEW-F09 is retained
  there but is not relabelled as the missing forall-divergence export.
* NEW-F11: `S04Moments38e` (`BirkhoffTop38.ae_muW38_chargeFn_eq`), needed
  together with `F11_38` and the B-free `chargeFn38_planeL2` to identify both
  sides with the source's actual local charges. `exact_identity38`,
  `tiltDet_lower38`, and `tiltDet_tendsto38` give the finite tilt/prod identities.
* SIGNED-MOMENTS: `SignedMoments38g` (`signedMoments_38`,
  `signedMoment_single_38`, `signedChargeFn_ae_spectral_38`) and
  `SignedMomentsBridge38` (`signedChargeFn38_planeL2`). These accompany
  `signedSpectral_cs38`, `signedSpectral_amgm38`,
  `continuous_oddChargeSobolev38`, and `oddChargeSobolev_cs38` for the full
  lines 1822-1829 bundle.
* L06: `ALQ4Ensemble38` and `ALQ4Limit38` (actual AL laws, positive normalizer,
  `alQ4Z_tendsto38`, `alQ4_weak_tendsto38`, `alQ4_probMeasure_tendsto38`),
  `L06Clause38` (`L06_08a_free38`: unmodified m=2 Fourier limit), and
  `F05Identity38j` (`L06_08b_38`: finite-gap identification, shared with F05).

All eight direct imports above were found both in the supplied root-closure
order list and as compiled objects in the prescribed parent. No root import,
producer, generic theorem, manuscript, or dependency is edited by this module.
-/

set_option autoImplicit false

noncomputable section

namespace LiebLiniger.FixedPeriod.EXT

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38
  NlsGge.SpectralFoundations NlsGge.Weights NlsGge.Birkhoff
  NlsGge.HierarchyRiccati.Core
  NlsGge.Ramer NlsGge.Analysis.RegularizedDeterminant Filter Topology
  NlsGge.ThirdConsultation.PDE
open scoped ENNReal Real

/-- W06 Gaussian companion. The real numbers `lower` and `upper` bound every
coefficient of `c`, whose type includes positive lower bound. The real `s` obeys
`hs : 1/2 < s`. The conclusion makes the full weighted Gaussian on `E_s` a
regular probability measure and assigns positive mass to every nonempty open
set `U` of that space; `U` is arbitrary. -/
theorem actual_w06_gaussian38 {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    IsProbabilityMeasure (NlsGge.Measure.fullWeightedSequenceGaussian c s) ∧
    (NlsGge.Measure.fullWeightedSequenceGaussian c s).Regular ∧
    (∀ U : Set (FullWeightedHilbert c s), IsOpen U → U.Nonempty →
      0 < NlsGge.Measure.fullWeightedSequenceGaussian c s U) := by
  exact NlsGge.Birkhoff.W06_01_38 c s hs

/-- W06 Cameron-Martin companion. For arbitrary real coefficient bounds `lower`,
`upper`, admitted sequence `c`, and real regularity `s` with `hs : 1/2 < s`,
every Cameron-Martin vector `h` has squared real norm twice the rate-weighted
coordinate sum over all integer modes `n`. The canonical Hilbert-Schmidt
inclusion equals `inclE`, and its squared norm is the Japanese-bracket sum. -/
theorem actual_w06_cameron_martin38 {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    (∀ h : ActualCM c, ‖h‖ ^ 2 = 2 * ∑' n : ℤ, sourceRate c n * ‖cmCoord h n‖ ^ 2) ∧
    ((NlsGge.Analysis.RegularizedDeterminant.cmInclusionHS c s hs).toCLM = inclE c s hs) ∧
    ‖NlsGge.Analysis.RegularizedDeterminant.cmInclusionHS c s hs‖ ^ 2 =
      ∑' n : ℤ, Real.rpow (japaneseBracket n) (-2 * s) := by
  exact NlsGge.Birkhoff.W06_02_38 c s hs

/-- W06 full actual change of coordinates. The implicit real bounds `lower`,
`upper` and admitted sequence `c` are arbitrary; `s` is any real regularity with
`hs : 1/2 < s` and `hs' : s < 3/4`. There exists one sequence divergence `δK`
used throughout the conclusion. For every weighted point `x`, its Ramer
Jacobian and full density are positive. Both are integrable; their integrals
are respectively one and the actual normalizer. The same Jacobian gives the
inverse-pushforward formula, both directions of Gaussian quasi-invariance,
and the actual GGE density and equivalence on physical fields `u`. -/
theorem actual_w06_38 {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    ∃ δK : (ℤ → ℂ) → ℝ,
      RamerDivergence38 c s (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c (le_one_of_lt_three_quarters_W06_38 hs')) δK ∧
      ((NlsGge.Measure.fullWeightedSequenceGaussian c s).map (TW06_38 actualBirkhoffInput38 actualOneSmoothingInput38 c s).symm =
          (NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity
            (fun x => ENNReal.ofReal (JW06_38 c s hs
              (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c (le_one_of_lt_three_quarters_W06_38 hs')) δK x)) ∧
        (∀ x, 0 < JW06_38 c s hs (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c (le_one_of_lt_three_quarters_W06_38 hs')) δK x) ∧
        Integrable (JW06_38 c s hs (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c (le_one_of_lt_three_quarters_W06_38 hs')) δK)
          (NlsGge.Measure.fullWeightedSequenceGaussian c s) ∧
        ∫ x, JW06_38 c s hs (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c (le_one_of_lt_three_quarters_W06_38 hs')) δK x
          ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) = 1 ∧
        ((NlsGge.Measure.fullWeightedSequenceGaussian c s).map (TW06_38 actualBirkhoffInput38 actualOneSmoothingInput38 c s) ≪
            NlsGge.Measure.fullWeightedSequenceGaussian c s ∧
          NlsGge.Measure.fullWeightedSequenceGaussian c s ≪
            (NlsGge.Measure.fullWeightedSequenceGaussian c s).map (TW06_38 actualBirkhoffInput38 actualOneSmoothingInput38 c s)) ∧
        ((NlsGge.Measure.fullWeightedSequenceGaussian c s).map (TW06_38 actualBirkhoffInput38 actualOneSmoothingInput38 c s).symm ≪
            NlsGge.Measure.fullWeightedSequenceGaussian c s ∧
          NlsGge.Measure.fullWeightedSequenceGaussian c s ≪
            (NlsGge.Measure.fullWeightedSequenceGaussian c s).map (TW06_38 actualBirkhoffInput38 actualOneSmoothingInput38 c s).symm)) ∧
      ((∀ x, 0 < fW06_38 c s hs (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c (le_one_of_lt_three_quarters_W06_38 hs')) δK x) ∧
        Integrable (fW06_38 c s hs (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c (le_one_of_lt_three_quarters_W06_38 hs')) δK)
          (NlsGge.Measure.fullWeightedSequenceGaussian c s) ∧
        ∫ x, fW06_38 c s hs (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c (le_one_of_lt_three_quarters_W06_38 hs')) δK x
          ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) = actualBirkhoffInput38.ZW38 c.val ∧
        actualBirkhoffInput38.muW38 c.val = ENNReal.ofReal (1 / actualBirkhoffInput38.ZW38 c.val) •
          ((NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity
            (fun x => ENNReal.ofReal (fW06_38 c s hs
              (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c (le_one_of_lt_three_quarters_W06_38 hs')) δK x))).map
            (physFW06_38 c s) ∧
        actualBirkhoffInput38.muW38 c.val =
          ((NlsGge.Measure.fullWeightedSequenceGaussian c s).map (physFW06_38 c s)).withDensity
            (fun u => ENNReal.ofReal (1 / actualBirkhoffInput38.ZW38 c.val *
              physFun38 c s (fW06_38 c s hs
                (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c (le_one_of_lt_three_quarters_W06_38 hs')) δK) u)) ∧
        (actualBirkhoffInput38.muW38 c.val ≪
            (NlsGge.Measure.fullWeightedSequenceGaussian c s).map (physFW06_38 c s) ∧
          (NlsGge.Measure.fullWeightedSequenceGaussian c s).map (physFW06_38 c s) ≪
            actualBirkhoffInput38.muW38 c.val)) := by
  exact NlsGge.Birkhoff.W06_38 actualBirkhoffInput38 actualOneSmoothingInput38 c s hs hs'

/-- W07 actual probability limit. The implicit real coefficient bounds `lower`,
`upper`, admitted sequence `c`, and real `s` with `hs : 1/2 < s < 3/4`
(the upper inequality is `hs'`) remain arbitrary. A single divergence `δK`
identifies the integrable limiting full density. For every natural cutoff `N`,
the finite density has integral equal to its original relative partition.
The densities at weighted points `x` converge in probability. The actual
normalizer is positive, every real `a` below it is eventually below the
finite partitions, and their extended-real liminf is at least that normalizer. -/
theorem actual_w07_38 {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    ∃ δK : (ℤ → ℂ) → ℝ,
      RamerDivergence38 c s (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c (le_one_of_lt_three_quarters_W06_38 hs')) δK ∧
      (∀ N : ℕ, ∫ x, fN38 c s N x ∂(fullWeightedSequenceGaussian c s) = relativePartition38 c N) ∧
      Integrable (fW06_38 c s hs (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c (le_one_of_lt_three_quarters_W06_38 hs')) δK)
        (fullWeightedSequenceGaussian c s) ∧
      ∫ x, fW06_38 c s hs (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c (le_one_of_lt_three_quarters_W06_38 hs')) δK x
        ∂(fullWeightedSequenceGaussian c s) = actualBirkhoffInput38.ZW38 c.val ∧
      TendstoInMeasure (fullWeightedSequenceGaussian c s) (fun N x => fN38 c s N x) atTop
        (fW06_38 c s hs (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c (le_one_of_lt_three_quarters_W06_38 hs')) δK) ∧
      0 < actualBirkhoffInput38.ZW38 c.val ∧
      (∀ a : ℝ, a < actualBirkhoffInput38.ZW38 c.val → ∀ᶠ N : ℕ in atTop, a < relativePartition38 c N) ∧
      ENNReal.ofReal (actualBirkhoffInput38.ZW38 c.val) ≤
        liminf (fun N : ℕ => ENNReal.ofReal (relativePartition38 c N)) atTop := by
  exact NlsGge.Birkhoff.W07_38 actualBirkhoffInput38 actualOneSmoothingInput38 c s hs hs'

/-- W07 exact finite-energy decomposition for the actual map. The real bounds
`lower`, `upper` and admitted `c` are arbitrary. The implicit real `s` obeys
`hs' : s < 3/4` and `hs1 : s ≤ 1`. For any natural cutoff `N` and weighted
point `x`, the unchanged finite density equals the product of the spectral
remainder weight, omitted high Cameron-Martin energy weight, and compressed
Gaussian energy-difference weight. All head vectors use this same cutoff. -/
theorem actual_w07_decomposition38 {lower upper : ℝ} (c : BoundedCoefficients lower upper) {s : ℝ} (hs' : s < 3 / 4) (hs1 : s ≤ 1) (N : ℕ) (x : FullWeightedHilbert c s) :
    fN38 c s N x =
      Real.exp (-(remainder38 c.val (physOfE38 c s (projE38 c s N x)))) *
        Real.exp (-(‖actualBirkhoffInput38.yN38 actualOneSmoothingInput38 c hs1 N x -
          ((cmTrunc c N (actualBirkhoffInput38.yN38 actualOneSmoothingInput38 c hs1 N x) : actualCMHead c N) : ActualCM c)‖ ^ 2 / 2)) *
        Real.exp (-(‖(headPt c N (coordE c s x) : ActualCM c) +
          ((cmTrunc c N (actualBirkhoffInput38.yN38 actualOneSmoothingInput38 c hs1 N x) : actualCMHead c N) : ActualCM c)‖ ^ 2 -
            ‖(headPt c N (coordE c s x) : ActualCM c)‖ ^ 2) / 2) := by
  exact actualBirkhoffInput38.fN38_decomp actualOneSmoothingInput38 c hs' hs1 N x

/-- W08 all-radius actual finite-section control. For every real radius `R`,
there is a natural threshold `N₀` above which each finite map is injective on
its closed h2 ball. For every positive real tolerance `ε`, the absolute
determinant tends uniformly to one there as the natural cutoff `N` grows.
Eventually at every ball point `x` the determinant is nonzero and its absolute
reciprocal is at most two. No positivity restriction on `R` is imposed. -/
theorem actual_w08_local_injectivity_determinant38 (R : ℝ) :
    (∃ N₀ : ℕ, ∀ N ≥ N₀, Set.InjOn (actualBirkhoffInput38.TN N) (ballV38 N R)) ∧
    (∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ x ∈ ballV38 N R, abs (|actualBirkhoffInput38.detTN N x| - 1) < ε) ∧
    (∀ᶠ N : ℕ in atTop, ∀ x ∈ ballV38 N R, actualBirkhoffInput38.detTN N x ≠ 0 ∧ |actualBirkhoffInput38.detTN N x|⁻¹ ≤ 2) := by
  exact actualBirkhoffInput38.W08_localInject_determinant actualOneSmoothingInput38 R

/-- W09 actual inverse branch with common-ball uniqueness. Real coefficient
bounds `lower`, `upper`, admitted `c`, real `s`, and weighted target `z` are
arbitrary. There is a sequence `xN` converging to the same actual inverse of
`z` and solving the Galerkin equation eventually. For each real radius `R`,
one natural threshold `N₀` works for all cutoffs `N ≥ N₀` and all h2 vectors
`y`, `w` in that ball: if `y` solves the equation, `w` represents the branch,
and the branch solves it, then `y` and the branch have equal coordinates. -/
theorem actual_w09_local_galerkin_inverse38 {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (z : ECarrier38 c s) :
    ∃ xN : ℕ → ECarrier38 c s,
      Tendsto xN atTop (𝓝 ((actualBirkhoffInput38.weightedHomeoE38 actualOneSmoothingInput38 c s).symm z)) ∧
      (∀ᶠ N in atTop, actualBirkhoffInput38.GalerkinSol38 N (eCoe38 c s z) (eCoe38 c s (xN N))) ∧
      ∀ R : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ y w : H2_38, ‖y‖ ≤ R → ‖w‖ ≤ R →
        actualBirkhoffInput38.GalerkinSol38 N (eCoe38 c s z) (carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y) →
        carrierCoe38 (((1 + 1 : ℕ)) : ℝ) w = eCoe38 c s (xN N) →
        actualBirkhoffInput38.GalerkinSol38 N (eCoe38 c s z) (eCoe38 c s (xN N)) →
        carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y = eCoe38 c s (xN N) := by
  exact actualBirkhoffInput38.W09_localGalerkinInverse actualOneSmoothingInput38 c s z

/-- W09 eventual uniqueness above the actual inverse norm. For arbitrary real
bounds `lower`, `upper`, admitted `c`, real regularity `s`, and weighted target
`z`, one branch `xN` converges to the actual inverse and eventually solves
the finite equation. For each real `R` strictly larger than that inverse
point's h2 norm, some natural `N₀` works for every cutoff `N ≥ N₀` and every
h2 vector `y` of norm at most `R`: solving the Galerkin equation forces its
coordinates to equal the branch. No derivative or contraction premise occurs. -/
theorem actual_w09_local_galerkin_inverse_ball38 {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (z : ECarrier38 c s) :
    ∃ xN : ℕ → ECarrier38 c s,
      Tendsto xN atTop (𝓝 ((actualBirkhoffInput38.weightedHomeoE38 actualOneSmoothingInput38 c s).symm z)) ∧
      (∀ᶠ N in atTop, actualBirkhoffInput38.GalerkinSol38 N (eCoe38 c s z) (eCoe38 c s (xN N))) ∧
      ∀ R : ℝ, ‖eToSob38 c s (((1 + 1 : ℕ)) : ℝ) ((actualBirkhoffInput38.weightedHomeoE38 actualOneSmoothingInput38 c s).symm z)‖ < R →
        ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ y : H2_38, ‖y‖ ≤ R →
          actualBirkhoffInput38.GalerkinSol38 N (eCoe38 c s z) (carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y) →
          carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y = eCoe38 c s (xN N) := by
  exact actualBirkhoffInput38.W09_localGalerkinInverse_ball actualOneSmoothingInput38 c s z

/-- W10 actual localized and normalized limits. Real bounds `lower`, `upper`,
admitted `c`, and real `s` with `hs : 1/2 < s` and `hs' : s < 3/4` are
arbitrary. The implicit function `χ : ℝ → ℝ` is any cutoff profile certified
by `hχ`; the implicit real radius `R` obeys `hR : 0 < R`. For every physical
test `F` whose pullback to the weighted space is continuous and bounded
by some real `M`, the localized finite integrals converge to the actual
normalizer times the actual localized integral. The same holds for every
nonnegative real Sobolev order `r`, proof `hr`, and test continuous and bounded
on that carrier. The localized limiting mass is positive, its normalized
law is a probability, and both classes of normalized test expectations
converge to it. All finite limits use the natural cutoff `N`. -/
theorem actual_w10_38 {lower upper : ℝ} (c : BoundedCoefficients lower upper) {s : ℝ} (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) :
    (∀ F : PhysicalL2 → ℝ, Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)) →
      (∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) →
      Tendsto (fun N : ℕ => ∫ x, F (physOfE38 c s (projE38 c s N x)) *
          chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
          ∂(fullWeightedSequenceGaussian c s))
        atTop (𝓝 (actualBirkhoffInput38.ZW38 c.val * ∫ u, F u * chiR38 χ R u ∂(actualBirkhoffInput38.muW38 c.val)))) ∧
    (∀ (r : ℝ) (hr : 0 ≤ r) (F : PhysicalL2 → ℝ),
      Continuous (fun y : SobolevCarrier38 r => F (physOfCarrier38 r hr y)) →
      (∃ M, ∀ y : SobolevCarrier38 r, |F (physOfCarrier38 r hr y)| ≤ M) →
      Tendsto (fun N : ℕ => ∫ x, F (physOfE38 c s (projE38 c s N x)) *
          chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
          ∂(fullWeightedSequenceGaussian c s))
        atTop (𝓝 (actualBirkhoffInput38.ZW38 c.val * ∫ u, F u * chiR38 χ R u ∂(actualBirkhoffInput38.muW38 c.val)))) ∧
    (0 < ∫ u, chiR38 χ R u ∂(actualBirkhoffInput38.muW38 c.val) ∧
      IsProbabilityMeasure (actualBirkhoffInput38.locLimitLaw38 c χ R) ∧
      (∀ F : PhysicalL2 → ℝ, Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)) →
        (∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) →
        Tendsto (fun N : ℕ =>
          (∫ x, F (physOfE38 c s (projE38 c s N x)) *
            chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
            ∂(fullWeightedSequenceGaussian c s)) /
          ∫ x, chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
            ∂(fullWeightedSequenceGaussian c s)) atTop
          (𝓝 (∫ u, F u ∂(actualBirkhoffInput38.locLimitLaw38 c χ R)))) ∧
      (∀ (r : ℝ) (hr : 0 ≤ r) (F : PhysicalL2 → ℝ),
        Continuous (fun y : SobolevCarrier38 r => F (physOfCarrier38 r hr y)) →
        (∃ M, ∀ y : SobolevCarrier38 r, |F (physOfCarrier38 r hr y)| ≤ M) →
        Tendsto (fun N : ℕ =>
          (∫ x, F (physOfE38 c s (projE38 c s N x)) *
            chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
            ∂(fullWeightedSequenceGaussian c s)) /
          ∫ x, chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
            ∂(fullWeightedSequenceGaussian c s)) atTop
          (𝓝 (∫ u, F u ∂(actualBirkhoffInput38.locLimitLaw38 c χ R))))) := by
  exact actualBirkhoffInput38.W10_38 actualOneSmoothingInput38 c hs hs' hχ hR

/-- Finite-density integrability companion for W07/W10. For arbitrary real
coefficient bounds `lower`, `upper`, admitted `c`, implicit real regularity
`s` with `hs : 1/2 < s`, and natural cutoff `N`, the original finite full
density is Bochner integrable under the full weighted Gaussian. -/
theorem actual_finite_density_integrable38 {lower upper : ℝ} (c : BoundedCoefficients lower upper) {s : ℝ} (hs : (1 : ℝ) / 2 < s) (N : ℕ) :
    Integrable (fN38 c s N) (fullWeightedSequenceGaussian c s) := by
  exact NlsGge.Birkhoff.BirkhoffInput38.integrable_fN38 c hs N

/-- W10 finite numerator integrability. The real bounds `lower`, `upper`,
admitted sequence `c`, and implicit real `s` with `hs : 1/2 < s` are
arbitrary. The implicit cutoff `χ` has profile proof `hχ`; implicit radius
`R` has positivity proof `hR`. The physical test `F` has continuous weighted
pullback `hF`, and `hFb` supplies a real bound `M` at every weighted point
`y`. For every natural cutoff `N`, its localized finite integrand is
Bochner integrable under the full weighted Gaussian. -/
theorem actual_w10_integrable_loc_integrand38 {lower upper : ℝ} (c : BoundedCoefficients lower upper) {s : ℝ} (hs : (1 : ℝ) / 2 < s) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)))
    (hFb : ∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) (N : ℕ) :
    Integrable (locIntegrand38 c χ R F N) (fullWeightedSequenceGaussian c s) := by
  exact actualBirkhoffInput38.integrable_locIntegrand38 actualOneSmoothingInput38 c hs hχ hR F hF hFb N

/-- W10 finite denominator integrability. For arbitrary real bounds `lower`,
`upper`, admitted `c`, implicit real `s` with `hs : 1/2 < s`, implicit
profile `χ` certified by `hχ`, implicit positive real radius `R` certified
by `hR`, and natural cutoff `N`, the cutoff times the unchanged finite
density is Bochner integrable at weighted points `x` under the full Gaussian. -/
theorem actual_w10_integrable_cutoff_weight38 {lower upper : ℝ} (c : BoundedCoefficients lower upper) {s : ℝ} (hs : (1 : ℝ) / 2 < s) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (N : ℕ) :
    Integrable (fun x : FullWeightedHilbert c s =>
      chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x)
      (fullWeightedSequenceGaussian c s) := by
  exact actualBirkhoffInput38.integrable_chiR_fN38 actualOneSmoothingInput38 c hs hχ hR N

/-- W10 limiting numerator integrability. For arbitrary real bounds `lower`,
`upper`, admitted `c`, implicit real `s` with `hs : 1/2 < s` and
`hs' : s < 3/4`, implicit profile `χ` with proof `hχ`, and implicit positive
real radius `R` with proof `hR`, let the physical test `F` have continuous
weighted pullback `hF` and real uniform bound `M` supplied by `hFb` at all
weighted points `y`. Then `F` times the cutoff is Bochner integrable at
physical fields `u` under the same actual limiting GGE. -/
theorem actual_w10_integrable_limit_integrand38 {lower upper : ℝ} (c : BoundedCoefficients lower upper) {s : ℝ} (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)))
    (hFb : ∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) :
    Integrable (fun u => F u * chiR38 χ R u) (actualBirkhoffInput38.muW38 c.val) := by
  exact actualBirkhoffInput38.integrable_F_chiR_muW38 actualOneSmoothingInput38 c hs hs' hχ hR F hF hFb

/-- NEW-F09 complete actual Fourier-limit bundle. The implicit real bounds
`lower`, `upper`, admitted coefficient sequence `c`, and implicit real `s`
with `hs : 1/2 < s` and `hs' : s < 3/4` remain arbitrary. The finite
partitions converge to the positive actual normalizer and share a positive
real lower bound `δ` for every natural cutoff `N`. Every physical test `F`
with continuous bounded weighted pullback (real bound `M`, point `y`) has
the asserted unnormalized and normalized limits; so does every test with
continuous bounded pullback at nonnegative real Sobolev order `r` and proof
`hr`. Each finite law is a probability. Some real `η > 0` and real bound `C`
work for all cutoffs for the H2 exponential moment and its integrability,
with almost-everywhere H2 membership. One sequence divergence `δK` identifies
the integrable limiting density of integral Z and gives integrability of
every finite density difference and L1 convergence on both the weighted
sequence space (points `x`) and the common physical Gaussian (fields `u`). -/
theorem actual_f09_38 {lower upper : ℝ} (c : BoundedCoefficients lower upper) {s : ℝ} (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    (Tendsto (fun N : ℕ => relativePartition38 c N) atTop (𝓝 (actualBirkhoffInput38.ZW38 c.val)) ∧
      0 < actualBirkhoffInput38.ZW38 c.val ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, δ ≤ relativePartition38 c N) ∧
    ((∀ F : PhysicalL2 → ℝ, Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)) →
        (∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) →
        Tendsto (fun N : ℕ => ∫ x, F (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
          ∂(fullWeightedSequenceGaussian c s)) atTop
          (𝓝 (actualBirkhoffInput38.ZW38 c.val * ∫ u, F u ∂(actualBirkhoffInput38.muW38 c.val)))) ∧
      (∀ (r : ℝ) (hr : 0 ≤ r) (F : PhysicalL2 → ℝ),
        Continuous (fun y : SobolevCarrier38 r => F (physOfCarrier38 r hr y)) →
        (∃ M, ∀ y : SobolevCarrier38 r, |F (physOfCarrier38 r hr y)| ≤ M) →
        Tendsto (fun N : ℕ => ∫ x, F (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
          ∂(fullWeightedSequenceGaussian c s)) atTop
          (𝓝 (actualBirkhoffInput38.ZW38 c.val * ∫ u, F u ∂(actualBirkhoffInput38.muW38 c.val))))) ∧
    ((∀ N : ℕ, IsProbabilityMeasure (nuWN38 c N)) ∧
      (∀ F : PhysicalL2 → ℝ, Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)) →
        (∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) →
        Tendsto (fun N : ℕ => ∫ u, F u ∂(nuWN38 c N)) atTop
          (𝓝 (∫ u, F u ∂(actualBirkhoffInput38.muW38 c.val)))) ∧
      (∀ (r : ℝ) (hr : 0 ≤ r) (F : PhysicalL2 → ℝ),
        Continuous (fun y : SobolevCarrier38 r => F (physOfCarrier38 r hr y)) →
        (∃ M, ∀ y : SobolevCarrier38 r, |F (physOfCarrier38 r hr y)| ≤ M) →
        Tendsto (fun N : ℕ => ∫ u, F u ∂(nuWN38 c N)) atTop
          (𝓝 (∫ u, F u ∂(actualBirkhoffInput38.muW38 c.val))))) ∧
    (∃ η C : ℝ, 0 < η ∧ ∀ N : ℕ,
      (∀ᵐ u ∂(nuWN38 c N), fourierSeq38 u ∈ seqSobolev38 (((2 : ℕ)) : ℝ)) ∧
      Integrable (fun u => Real.exp (η * ‖physH38 2 u‖ ^ 2)) (nuWN38 c N) ∧
      ∫ u, Real.exp (η * ‖physH38 2 u‖ ^ 2) ∂(nuWN38 c N) ≤ C) ∧
    (∃ δK : (ℤ → ℂ) → ℝ,
      RamerDivergence38 c s (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c (le_one_of_lt_three_quarters_W06_38 hs')) δK ∧
      Integrable (fW06_38 c s hs (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c (le_one_of_lt_three_quarters_W06_38 hs')) δK)
        (fullWeightedSequenceGaussian c s) ∧
      ∫ x, fW06_38 c s hs (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c (le_one_of_lt_three_quarters_W06_38 hs')) δK x
        ∂(fullWeightedSequenceGaussian c s) = actualBirkhoffInput38.ZW38 c.val ∧
      (∀ N : ℕ, Integrable (fun x => fN38 c s N x -
        fW06_38 c s hs (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c (le_one_of_lt_three_quarters_W06_38 hs')) δK x)
        (fullWeightedSequenceGaussian c s)) ∧
      Tendsto (fun N : ℕ => ∫ x, |fN38 c s N x -
        fW06_38 c s hs (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c (le_one_of_lt_three_quarters_W06_38 hs')) δK x|
        ∂(fullWeightedSequenceGaussian c s)) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => ∫ u, |physFun38 c s (fN38 c s N) u -
        physFun38 c s (fW06_38 c s hs (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c (le_one_of_lt_three_quarters_W06_38 hs')) δK) u|
        ∂((fullWeightedSequenceGaussian c s).map (physFW06_38 c s))) atTop (𝓝 0)) := by
  exact actualBirkhoffInput38.F09_38 actualOneSmoothingInput38 c hs hs'

end LiebLiniger.FixedPeriod.EXT

end
