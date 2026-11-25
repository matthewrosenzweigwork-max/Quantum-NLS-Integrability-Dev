import NlsGge.Birkhoff.W11Equivalence38f
import NlsGge.Birkhoff.W12Bridge38
import NlsGge.Birkhoff.F10Bridge38
import NlsGge.Birkhoff.F11Claim38f
import NlsGge.Birkhoff.SignedMomentsBridge38
import NlsGge.Hierarchy.ALQ4Limit38
import NlsGge.Birkhoff.L06Clause38
import NlsGge.Birkhoff.F05Identity38j
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing

/-!
# Actual Birkhoff consumers B2: resumed additive wrappers

Source: `paper/v2.tex`, SHA256
`0e7c2e61a06ab6886124c3891c73e0b8997ab71473eaf75b05c524098a58e3ec`.
Every statement copies an existing generic declaration with only its Birkhoff
and one-smoothing inputs specialized to the SAME actual producers. All other
binders are retained; Birkhoff-free companions keep their original statements.
The topological parent in the F11 identification is that same input's parent.
This is an author submission requiring independent semantic review.

Coverage and source-level generic inventory:

* W11 (`D:thm:equivalence`, lines 1671-1691): `W11_38` jointly supplies
  divergence existence and all five equivalent criteria, including uniform
  integrability. Its constituent generic lemmas `tendsto_iff_l1_W11`,
  `l1_iff_uniformIntegrable_W11`, `W10_F1_W11`, and
  `one_sub_chiR_le_indicator_W11` are already consumed by that bundle.
* W12 (`D:prop:tilt`, lines 1836-1863): `W12_38` jointly supplies extended
  energy finiteness, real-valued continuity, positive determinant product,
  integrable exact limiting tilt, almost-everywhere finiteness, and mass
  coercivity. BOTH `EB38_eq_chargeSeries_FinvE38` and
  `ae_EB38_eq_chargeSeries` identify that energy with the full lower-charge
  series on its source carriers. The generic `tilt_lintegral_W12_38`,
  `tilt_integral_W12_38`, `gaussian_tilt_density38`, shifted-weight algebra,
  and `hasProd_tilt38` are proof constituents consumed by these statements.
* NEW-F10 (`F:eq:L1`, lines 1702-1722, 1774-1798): `L1_F10_38` supplies
  integrability and L1 convergence on both common Gaussian carriers, with one
  divergence. `L1_F10_forall_delta38` preserves every admissible divergence.
  `tendsto_integral_abs_sub_F10_38` and `integral_abs_sub_eq_F10_38` are its
  existing Birkhoff-free proof ingredients.
* NEW-F11 (`F:cor:charge`, lines 1801-1819): `F11_38`, `F11_chargeexp38`,
  `F11_moments38`, `F11_moment_single38`, both charge identification bridges
  `chargeFn38_planeL2`, `ae_muW38_chargeFn_eq`, and the exact finite tilt
  `exact_identity38` with `tiltDet_lower38`, `tiltDet_tendsto38`.
* SIGNED-MOMENTS (`F:rem:signed`, lines 1822-1829): `signedMoments_38`,
  `signedMoment_single_38`, `signedChargeFn_ae_spectral_38`,
  `signedChargeFn38_planeL2`, `signedSpectral_even_eq_localCharge38`,
  `signedSpectral_moments38`, `signedSpectral_cs38`, `signedSpectral_amgm38`,
  `continuous_oddChargeSobolev38`, `oddChargeSobolev_cs38`. The existing
  definition `signedSpectralMoment38` retains the exact 2/pi normalization.
  Its spectral integrability premises remain ordinary arbitrary-data binders;
  they are proved for smooth representatives by `signedSpectral_moments38`.
* L06 (`C:thm:AL`, lines 2196-2224): `alQ4Ensemble38`, `alQ4Normalizer38`,
  `alQ4Z_tendsto38`, `alQ4Z2_pos38`, `alQ4_weak_tendsto38`,
  `alQ4_probMeasure_tendsto38`, `L06_08a_free38`, `L06_08b_38`, retaining
  the direct law `alQ4Rho38`. The finite-mesh and limiting hypotheses are
  copied separately; only the identification specializes B/O.

W07's additional negative-log remark (lines 1576-1578) remains uncovered:
no generic theorem stating that nonlinear-energy limit was located in the
tracked permitted sources. No new premise or weaker replacement is added.

All imports have union-root objects. Closure membership is recorded in the
external author report: several required generic modules occur only in the
supplied extension order, not the supplied release-root order. This file does
not modify the earlier ActualConsumersB submission, a root import, or a source.
-/

set_option autoImplicit false

noncomputable section

namespace LiebLiniger.FixedPeriod.EXT

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38
  NlsGge.SpectralFoundations NlsGge.Weights NlsGge.Birkhoff
  NlsGge.HierarchyRiccati.Core NlsGge.AblowitzLadik
  NlsGge.Ramer NlsGge.Analysis.RegularizedDeterminant Filter Topology
  NlsGge.ThirdConsultation.PDE
open scoped ENNReal Real ContDiff BoundedContinuousFunction

/-- W11 equivalent convergence criteria for the actual producers. The implicit real
bounds `lower`, `upper` and admitted coefficient sequence `c` are arbitrary;
the implicit real `s` satisfies `hs : 1/2 < s` and `hs' : s < 3/4`.
A divergence `δK` exists. For every such divergence, normalizer convergence,
common-Gaussian L1 convergence, uniform integrability, weighted weak convergence,
and boundedness in probability of the H2 norm are equivalent, with the same
actual measure, normalizer and divergence throughout. -/
theorem actual_w11_38 {lower upper : ℝ} (c : BoundedCoefficients lower upper) {s : ℝ} (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    (∃ δK : (ℤ → ℂ) → ℝ,
      RamerDivergence38 c s (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c (le_one_of_lt_three_quarters_W06_38 hs')) δK) ∧
    ∀ δK : (ℤ → ℂ) → ℝ,
      RamerDivergence38 c s (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c (le_one_of_lt_three_quarters_W06_38 hs')) δK →
      List.TFAE
        [ W11Normalizer38 actualBirkhoffInput38 c,
          Tendsto (fun N : ℕ => ∫ x, |fN38 c s N x -
              fW06_38 c s hs (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c (le_one_of_lt_three_quarters_W06_38 hs')) δK x|
            ∂(fullWeightedSequenceGaussian c s)) atTop (𝓝 0),
          UniformIntegrable (fun N x => fN38 c s N x) 1 (fullWeightedSequenceGaussian c s),
          W11Weak38 actualBirkhoffInput38 c s,
          W11Tight38 c ] := by
  exact NlsGge.Birkhoff.BirkhoffInput38.W11_38 actualBirkhoffInput38 actualOneSmoothingInput38 c hs hs'

/-- W12 exact limiting tilt for the actual producers. The implicit real bounds
`lower`, `upper`, admitted sequence `c`, and implicit real tilt `δ` obey
`hδ0 : 0 < δ` and `hδ : δ * upper < lower`; the implicit real `s` obeys
`hs : s < 3/4`. The extended nonnegative energy is finite and its real value
continuous on every weighted physical point `u`. Its determinant product is
positive; the exponential tilt is integrable for the actual law, the energy
is finite almost everywhere, and the exact normalizer ratio and mass coercivity
hold. All integer modes, including zero, occur in the product. -/
theorem actual_w12_38 {lower upper : ℝ} (c : BoundedCoefficients lower upper) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ * upper < lower) {s : ℝ} (hs : s < 3 / 4) :
    ((∀ u : FinvE38 c s, EB38 c.val u.1 ≠ ⊤) ∧
      @Continuous (FinvE38 c s) ℝ (topFinvE38 c s) _ (fun u => (EB38 c.val u.1).toReal)) ∧
    (0 < Dtilt38 c.val δ ∧
      HasProd (fun n : ℤ => 1 - δ * bRate38 c.val n / fullWeightRate c.val n)
        (Dtilt38 c.val δ)) ∧
    (Integrable (fun u => Real.exp (δ * (EB38 c.val u).toReal)) (actualBirkhoffInput38.muW38 c.val) ∧
      (∀ᵐ u ∂(actualBirkhoffInput38.muW38 c.val), EB38 c.val u ≠ ⊤) ∧
      ∫ u, Real.exp (δ * (EB38 c.val u).toReal) ∂(actualBirkhoffInput38.muW38 c.val) =
        actualBirkhoffInput38.ZW38 (tiltCoef38 c.val δ) / (actualBirkhoffInput38.ZW38 c.val * Dtilt38 c.val δ)) ∧
    (∀ u : FinvE38 c s,
      ENNReal.ofReal (weight c.val ‖u.1‖ - NlsGge.coefficient c.val 0) ≤ EB38 c.val u.1) := by
  exact NlsGge.Birkhoff.BirkhoffInput38.W12_38 actualBirkhoffInput38 actualOneSmoothingInput38 c hδ0 hδ hs

/-- W12 charge-series companion on the weighted physical space. The implicit real
bounds `lower`, `upper`, admitted `c`, real `s`, and weighted physical field `u`
are arbitrary. There is a smooth period-one representative `U`, with smoothness
proof `hU` and periodicity proof `hper`, equal to `u`, whose full shifted local
charge series equals the extended nonnegative spectral energy. -/
theorem actual_w12_charge_series38  {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (u : FinvE38 c s) :
    ∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
      smoothL2_38 U hU hper = u.1 ∧ EB38 c.val u.1 = chargeSeriesW38 (bCoef38 c.val) U := by
  exact NlsGge.Birkhoff.EB38_eq_chargeSeries_FinvE38 c s u

/-- W12 charge-series companion for the actual law. For arbitrary implicit real
bounds `lower`, `upper` and admitted sequence `c`, almost every physical field
`u` under the actual law has a smooth period-one representative `U`, with
smoothness and periodicity witnesses `hU`, `hper`, equal to `u`, and its full
shifted local charge series equals the extended nonnegative spectral energy. -/
theorem actual_w12_ae_charge_series38  {lower upper : ℝ} (c : BoundedCoefficients lower upper) :
    ∀ᵐ u ∂(actualBirkhoffInput38.muW38 c.val), ∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
      smoothL2_38 U hU hper = u ∧ EB38 c.val u = chargeSeriesW38 (bCoef38 c.val) U := by
  exact NlsGge.Birkhoff.BirkhoffInput38.ae_EB38_eq_chargeSeries actualBirkhoffInput38 c

/-- F10 common-Gaussian L1 limit for the actual producers. The implicit real
bounds `lower`, `upper`, admitted sequence `c`, and implicit real `s` obeying
`hs : 1/2 < s`, `hs' : s < 3/4` are arbitrary. One divergence `δK` gives an
integrable full density with integral the actual normalizer. For every natural
cutoff `N` the density difference is integrable, and its absolute integral
tends to zero both on the sequence Gaussian and its physical pushforward.
Both convergence clauses use this same divergence. -/
theorem actual_f10_l1_38 {lower upper : ℝ} (c : BoundedCoefficients lower upper) {s : ℝ} (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    ∃ δK : (ℤ → ℂ) → ℝ,
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
        ∂((fullWeightedSequenceGaussian c s).map (physFW06_38 c s))) atTop (𝓝 0) := by
  exact NlsGge.Birkhoff.BirkhoffInput38.L1_F10_38 actualBirkhoffInput38 actualOneSmoothingInput38 c hs hs'

/-- F10 L1 limit for every admissible divergence of the actual map. The implicit
real bounds `lower`, `upper`, admitted sequence `c`, implicit real `s` with
`hs : 1/2 < s` and `hs' : s < 3/4`, sequence function `δ`, and proof `hδ`
that it is a Gaussian divergence are arbitrary. The absolute density difference
has Gaussian integral tending to zero. The ordinary divergence premise is
retained exactly; existence is already concluded by W11 and the F10 bundle. -/
theorem actual_f10_l1_forall_divergence38  {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) {s : ℝ} (hs : (1:ℝ)/2 < s) (hs' : s < 3/4)
    (δ : (ℤ → ℂ) → ℝ)
    (hδ : RamerDivergence38 c s (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c (le_one_of_lt_three_quarters_W06_38 hs')) δ) :
    Tendsto (fun N : ℕ => ∫ x, |fN38 c s N x -
        fW06_38 c s hs (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c (le_one_of_lt_three_quarters_W06_38 hs')) δ x|
        ∂(fullWeightedSequenceGaussian c s)) atTop (𝓝 0) := by
  exact NlsGge.Birkhoff.BirkhoffInput38.L1_F10_forall_delta38 actualBirkhoffInput38 actualOneSmoothingInput38 c hs hs' δ hδ

/-- F11 full positive-charge bundle for the actual producers. The implicit real
bounds `lower`, `upper`, admitted `c`, natural Sobolev index `m` and proof
`hm : 2 ≤ m` are arbitrary. For every natural `J ≤ m-1` and real coefficient
family `t` with `0 ≤ t j < β_j` for `j ≤ J`, one real bound `C` controls the
integrable exponential at every natural cutoff `N`. For every finite family
`jj : Fin n → ℕ` with indices at most `m-1` and natural powers `p`, its mixed
product is integrable under every finite law and the actual law, and the finite
expectations tend to the actual expectation. -/
theorem actual_f11_38 {lower upper : ℝ} (c : BoundedCoefficients lower upper)  (m : ℕ) (hm : 2 ≤ m) :
    (∀ (J : ℕ), J ≤ m - 1 → ∀ t : ℕ → ℝ, (∀ j ≤ J, 0 ≤ t j ∧ t j < NlsGge.coefficient c.val j) →
      ∃ C : ℝ, ∀ N : ℕ,
        Integrable (fun u => Real.exp (∑ j ∈ Finset.range (J + 1), t j * chargeFn38 m j u))
            (nuWN38 c N) ∧
          ∫ u, Real.exp (∑ j ∈ Finset.range (J + 1), t j * chargeFn38 m j u) ∂(nuWN38 c N) ≤ C) ∧
    (∀ (n : ℕ) (jj : Fin n → ℕ), (∀ i, jj i ≤ m - 1) → ∀ p : Fin n → ℕ,
      (∀ N : ℕ, Integrable (fun u => ∏ i, chargeFn38 m (jj i) u ^ p i) (nuWN38 c N)) ∧
        Integrable (fun u => ∏ i, chargeFn38 m (jj i) u ^ p i) (actualBirkhoffInput38.muW38 c.val) ∧
        Tendsto (fun N : ℕ => ∫ u, ∏ i, chargeFn38 m (jj i) u ^ p i ∂(nuWN38 c N)) atTop
          (𝓝 (∫ u, ∏ i, chargeFn38 m (jj i) u ^ p i ∂(actualBirkhoffInput38.muW38 c.val)))) := by
  exact NlsGge.Birkhoff.BirkhoffInput38.F11_38 actualBirkhoffInput38 actualOneSmoothingInput38 c m hm

/-- F11 exponential bound for the actual producers. The implicit real bounds
`lower`, `upper`, admitted `c`, natural `m ≥ 2` witnessed by `hm`, natural
`J ≤ m-1` witnessed by `hJ`, real coefficient family `t`, and strict positive
charge admissibility proof `ht` are arbitrary. One real bound `C` controls the
integrable finite exponential of the first `J+1` charges for every cutoff `N`. -/
theorem actual_f11_charge_exp38 {lower upper : ℝ} (c : BoundedCoefficients lower upper)  (m : ℕ) (hm : 2 ≤ m) (J : ℕ) (hJ : J ≤ m - 1) (t : ℕ → ℝ)
    (ht : ∀ j ≤ J, 0 ≤ t j ∧ t j < NlsGge.coefficient c.val j) :
    ∃ C : ℝ, ∀ N : ℕ,
      Integrable (fun u => Real.exp (∑ j ∈ Finset.range (J + 1), t j * chargeFn38 m j u))
          (nuWN38 c N) ∧
        ∫ u, Real.exp (∑ j ∈ Finset.range (J + 1), t j * chargeFn38 m j u) ∂(nuWN38 c N) ≤ C := by
  exact NlsGge.Birkhoff.BirkhoffInput38.F11_chargeexp38 actualBirkhoffInput38 actualOneSmoothingInput38 c m hm J hJ t ht

/-- F11 mixed moments for the actual producers. The implicit real coefficient
bounds `lower`, `upper`, admitted `c`, natural `m ≥ 2` witnessed by `hm`,
natural family size `n`, indices `jj : Fin n → ℕ` bounded by `m-1` via `hjj`,
and natural powers `p : Fin n → ℕ` are arbitrary. The mixed product is
integrable under every finite cutoff law and the actual law; its finite
expectations tend to its actual expectation. -/
theorem actual_f11_moments38 {lower upper : ℝ} (c : BoundedCoefficients lower upper)  (m : ℕ) (hm : 2 ≤ m) (n : ℕ) (jj : Fin n → ℕ) (hjj : ∀ i, jj i ≤ m - 1)
    (p : Fin n → ℕ) :
    (∀ N : ℕ, Integrable (fun u => ∏ i, chargeFn38 m (jj i) u ^ p i) (nuWN38 c N)) ∧
      Integrable (fun u => ∏ i, chargeFn38 m (jj i) u ^ p i) (actualBirkhoffInput38.muW38 c.val) ∧
      Tendsto (fun N : ℕ => ∫ u, ∏ i, chargeFn38 m (jj i) u ^ p i ∂(nuWN38 c N)) atTop
        (𝓝 (∫ u, ∏ i, chargeFn38 m (jj i) u ^ p i ∂(actualBirkhoffInput38.muW38 c.val))) := by
  exact NlsGge.Birkhoff.BirkhoffInput38.F11_moments38 actualBirkhoffInput38 actualOneSmoothingInput38 c m hm n jj hjj p

/-- F11 single moments for the actual producers. The implicit real bounds
`lower`, `upper`, admitted `c`, natural `m ≥ 2` with proof `hm`, natural
charge index `j ≤ m-1` with proof `hj`, and natural power `p` are arbitrary.
The power is integrable under every finite cutoff law and the actual law,
and its finite expectations tend to its actual expectation. -/
theorem actual_f11_single_moment38 {lower upper : ℝ} (c : BoundedCoefficients lower upper)  (m : ℕ) (hm : 2 ≤ m) (j : ℕ) (hj : j ≤ m - 1) (p : ℕ) :
    (∀ N : ℕ, Integrable (fun u => chargeFn38 m j u ^ p) (nuWN38 c N)) ∧
      Integrable (fun u => chargeFn38 m j u ^ p) (actualBirkhoffInput38.muW38 c.val) ∧
      Tendsto (fun N : ℕ => ∫ u, chargeFn38 m j u ^ p ∂(nuWN38 c N)) atTop
        (𝓝 (∫ u, chargeFn38 m j u ^ p ∂(actualBirkhoffInput38.muW38 c.val))) := by
  exact NlsGge.Birkhoff.BirkhoffInput38.F11_moment_single38 actualBirkhoffInput38 actualOneSmoothingInput38 c m hm j hj p

/-- F11 finite-law charge identification. The natural indices `m`, `j`, proofs
`hm : 2 ≤ m`, `hjm : j ≤ m`, natural cutoff `N`, and Fourier-plane vector `z`
are arbitrary. The continuous charge evaluated on its physical field equals
the local polynomial charge of its period-one trigonometric representative. -/
theorem actual_f11_plane_charge38  (m j : ℕ) (hm : 2 ≤ m) (hjm : j ≤ m) (N : ℕ) (z : FourierPlane N) :
    chargeFn38 m j (planeL2 N z) = localCharge38 (planeReal N z) j := by
  exact NlsGge.Birkhoff.chargeFn38_planeL2 m j hm hjm N z

/-- F11 actual-law charge identification. The real bounds `lower`, `upper`, raw
coefficient sequence `c`, positive lower-bound proof `hlower`, and pointwise
bound proofs `hbound`, `hupper` are arbitrary. For natural `m`, `j` satisfying
`hm : 2 ≤ m` and `hjm : j ≤ m`, almost every field `u` of the actual law has
a smooth period-one representative `U`, with witnesses `hU`, `hper`, equal to
`u`, whose local charge equals both `chargeFn38 m j u` and the spectral integral
with the fixed `2/π` normalization. The topological input is the parent of the
same actual Birkhoff input. -/
theorem actual_f11_ae_charge38 (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) (m j : ℕ) (hm : 2 ≤ m) (hjm : j ≤ m) :
    ∀ᵐ u : PhysicalL2 ∂(actualBirkhoffInput38.muW38 c), ∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
      (hper : Function.Periodic U 1), smoothL2_38 U hU hper = u ∧
      chargeFn38 m j u = localCharge38 U j ∧
      chargeFn38 m j u = (2 / Real.pi) * ∫ t : ℝ, (2 * t) ^ (2 * j) * actualGapHeightE02_38 u t := by
  exact NlsGge.Birkhoff.BirkhoffTop38.ae_muW38_chargeFn_eq actualBirkhoffInput38.toBirkhoffTop38 lower upper c hlower hbound hupper m j hm hjm

/-- F11 exact finite positive-charge tilt. The implicit real bounds `lower`,
`upper`, admitted `c`, implicit natural `J`, implicit real family `t` and its
admissibility proof `ht`, natural `m ≥ 2` with proof `hm`, proof `hJ : J ≤ m`,
and natural cutoff `N` are arbitrary. The finite exponential is integrable,
and its expectation is exactly the inverse finite determinant times the ratio
of the tilted and original finite normalizers. -/
theorem actual_f11_exact_tilt38 {lower upper : ℝ} (c : BoundedCoefficients lower upper) {J : ℕ} {t : ℕ → ℝ}
    (ht : TiltAdmissible38 c J t) (m : ℕ) (hm : 2 ≤ m) (hJ : J ≤ m) (N : ℕ) :
    Integrable (fun u => Real.exp (∑ j ∈ Finset.range (J + 1), t j * chargeFn38 m j u))
        (nuWN38 c N) ∧
      ∫ u, Real.exp (∑ j ∈ Finset.range (J + 1), t j * chargeFn38 m j u) ∂(nuWN38 c N) =
        (tiltDet38 c J t N)⁻¹ *
          (relativePartition38 (tiltedCoefficients38 c ht) N / relativePartition38 c N) := by
  exact NlsGge.Birkhoff.exact_identity38 c ht m hm hJ N

/-- F11 determinant lower bound. The implicit real bounds `lower`, `upper`,
admitted `c`, natural last charge index `J`, real family `t` and admissibility
proof `ht` are arbitrary. There exists one positive real `δ` below every
finite-cutoff determinant, uniformly over all natural cutoffs `N`. -/
theorem actual_f11_tilt_determinant_lower38 {lower upper : ℝ} {c : BoundedCoefficients lower upper} {J : ℕ} {t : ℕ → ℝ} (ht : TiltAdmissible38 c J t) : ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, δ ≤ tiltDet38 c J t N := by
  exact NlsGge.Birkhoff.tiltDet_lower38 ht

/-- F11 determinant limit. The implicit real bounds `lower`, `upper`, admitted
`c`, natural last charge index `J`, real family `t` and admissibility proof
`ht` are arbitrary. The finite determinant sequence converges to some strictly
positive real limit `D`. -/
theorem actual_f11_tilt_determinant_tendsto38 {lower upper : ℝ} {c : BoundedCoefficients lower upper} {J : ℕ} {t : ℕ → ℝ} (ht : TiltAdmissible38 c J t) :
    ∃ D : ℝ, 0 < D ∧ Tendsto (tiltDet38 c J t) atTop (𝓝 D) := by
  exact NlsGge.Birkhoff.tiltDet_tendsto38 ht

/-- Signed mixed moments for the actual producers. The implicit real bounds
`lower`, `upper`, admitted `c`, natural `m ≥ 2` with proof `hm`, natural family
size `n`, signed indices `kk : Fin n → ℕ` bounded by `2*m-2` via `hkk`, and
natural powers `p` are arbitrary. Their finite mixed product is integrable
under every finite law and the actual law, and its finite expectations tend
to its actual expectation. -/
theorem actual_signed_moments38 {lower upper : ℝ} (c : BoundedCoefficients lower upper)  (m : ℕ) (hm : 2 ≤ m) (n : ℕ) (kk : Fin n → ℕ) (hkk : ∀ i, kk i ≤ 2 * m - 2)
    (p : Fin n → ℕ) :
    (∀ N : ℕ, Integrable (fun u => ∏ i, signedChargeFn38 m (kk i) u ^ p i) (nuWN38 c N)) ∧
      Integrable (fun u => ∏ i, signedChargeFn38 m (kk i) u ^ p i) (actualBirkhoffInput38.muW38 c.val) ∧
      Tendsto (fun N : ℕ => ∫ u, ∏ i, signedChargeFn38 m (kk i) u ^ p i ∂(nuWN38 c N)) atTop
        (𝓝 (∫ u, ∏ i, signedChargeFn38 m (kk i) u ^ p i ∂(actualBirkhoffInput38.muW38 c.val))) := by
  exact NlsGge.Birkhoff.BirkhoffInput38.signedMoments_38 actualBirkhoffInput38 actualOneSmoothingInput38 c m hm n kk hkk p

/-- Signed single moments for the actual producers. The implicit real bounds
`lower`, `upper`, admitted `c`, natural `m ≥ 2` with proof `hm`, natural signed
index `k ≤ 2*m-2` with proof `hk`, and natural power `p` are arbitrary. This
power is integrable under every finite law and the actual law, and its finite
expectations converge to its actual expectation. -/
theorem actual_signed_single_moment38 {lower upper : ℝ} (c : BoundedCoefficients lower upper)  (m : ℕ) (hm : 2 ≤ m) (k : ℕ) (hk : k ≤ 2 * m - 2) (p : ℕ) :
    (∀ N : ℕ, Integrable (fun u => signedChargeFn38 m k u ^ p) (nuWN38 c N)) ∧
      Integrable (fun u => signedChargeFn38 m k u ^ p) (actualBirkhoffInput38.muW38 c.val) ∧
      Tendsto (fun N : ℕ => ∫ u, signedChargeFn38 m k u ^ p ∂(nuWN38 c N)) atTop
        (𝓝 (∫ u, signedChargeFn38 m k u ^ p ∂(actualBirkhoffInput38.muW38 c.val))) := by
  exact NlsGge.Birkhoff.BirkhoffInput38.signedMoment_single_38 actualBirkhoffInput38 actualOneSmoothingInput38 c m hm k hk p

/-- Signed actual-law identification. The implicit real bounds `lower`, `upper`,
admitted `c`, natural `m ≥ 2` with proof `hm`, and natural signed index
`k ≤ 2*m-2` with proof `hk` are arbitrary. Almost every physical field `u`
under the actual law has continuous signed charge equal to its signed spectral
moment with the source's fixed normalization. -/
theorem actual_signed_ae_spectral38 {lower upper : ℝ} (c : BoundedCoefficients lower upper)  (m : ℕ) (hm : 2 ≤ m) (k : ℕ) (hk : k ≤ 2 * m - 2) :
    ∀ᵐ u : PhysicalL2 ∂(actualBirkhoffInput38.muW38 c.val), signedChargeFn38 m k u = signedSpectralMoment38 u k := by
  exact NlsGge.Birkhoff.BirkhoffInput38.signedChargeFn_ae_spectral_38 actualBirkhoffInput38 actualOneSmoothingInput38 c m hm k hk

/-- Signed finite-law identification. The natural Sobolev index `m`, signed index
`k`, cutoff `N`, proofs `hm : 2 ≤ m`, `hk : k ≤ 2*m-2`, and Fourier-plane
vector `z` are arbitrary. The continuous signed charge on its physical field
is the signed spectral moment on that same field. -/
theorem actual_signed_plane_spectral38  (m k N : ℕ) (hm : 2 ≤ m) (hk : k ≤ 2*m-2) (z : FourierPlane N) :
    signedChargeFn38 m k (planeL2 N z) = signedSpectralMoment38 (planeL2 N z) k := by
  exact NlsGge.Birkhoff.signedChargeFn38_planeL2 m k N hm hk z

/-- Signed even spectral identification. The complex function `U` on the real
line, smoothness proof `hU`, period-one proof `hper`, and natural charge index
`j` are arbitrary. Its signed spectral moment of index `2*j` equals its local
positive even charge. -/
theorem actual_signed_even_local38  (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
    (hper : Function.Periodic U 1) (j : ℕ) :
    signedSpectralMoment38 (smoothL2_38 U hU hper) (2 * j) = localCharge38 U j := by
  exact NlsGge.Birkhoff.signedSpectral_even_eq_localCharge38 U hU hper j

/-- Signed smooth spectral moments. The complex function `U` on the real line,
smoothness proof `hU`, period-one proof `hper`, and natural upper index `J`
are arbitrary. Each spectral moment through index `2*J` is integrable, and
for every natural `j` with `j+1 ≤ J` the odd signed spectral moment equals
the corresponding local polynomial charge. -/
theorem actual_signed_smooth_moments38  (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1)
    (J : ℕ) :
    (∀ k ≤ 2 * J, Integrable (fun t : ℝ =>
        (2 * t) ^ k * actualGapHeightE02_38 (smoothL2_38 U hU hper) t)) ∧
    ∀ j : ℕ, j + 1 ≤ J →
      signedSpectralMoment38 (smoothL2_38 U hU hper) (2 * j + 1) = oddLocalCharge38 U j := by
  exact NlsGge.Birkhoff.signedSpectral_moments38 U hU hper J

/-- Signed spectral bound. The physical field `u`, natural adjacent-moment index
`j`, and ordinary integrability proofs `i0`, `i1`, `i2` for its spectral
moments of orders `2*j`, `2*j+1`, `2*j+2` are arbitrary. The square of the odd moment is bounded by the product of its adjacent even moments.
These integrability premises are retained exactly; the smooth-moment theorem
supplies them on smooth representatives. -/
theorem actual_signed_spectral_cs38  (u : PhysicalL2) (j : ℕ)
    (i0 : Integrable (fun t : ℝ => (2 * t) ^ (2 * j) * actualGapHeightE02_38 u t))
    (i1 : Integrable (fun t : ℝ => (2 * t) ^ (2 * j + 1) * actualGapHeightE02_38 u t))
    (i2 : Integrable (fun t : ℝ => (2 * t) ^ (2 * j + 2) * actualGapHeightE02_38 u t)) :
    signedSpectralMoment38 u (2 * j + 1) ^ 2 ≤
      signedSpectralMoment38 u (2 * j) * signedSpectralMoment38 u (2 * j + 2) := by
  exact NlsGge.Birkhoff.signedSpectral_cs38 u j i0 i1 i2

/-- Signed spectral bound. The physical field `u`, natural adjacent-moment index
`j`, and ordinary integrability proofs `i0`, `i1`, `i2` for its spectral
moments of orders `2*j`, `2*j+1`, `2*j+2` are arbitrary. The absolute odd moment is bounded by half the sum of its adjacent even moments.
These integrability premises are retained exactly; the smooth-moment theorem
supplies them on smooth representatives. -/
theorem actual_signed_spectral_amgm38  (u : PhysicalL2) (j : ℕ)
    (i0 : Integrable (fun t : ℝ => (2 * t) ^ (2 * j) * actualGapHeightE02_38 u t))
    (i1 : Integrable (fun t : ℝ => (2 * t) ^ (2 * j + 1) * actualGapHeightE02_38 u t))
    (i2 : Integrable (fun t : ℝ => (2 * t) ^ (2 * j + 2) * actualGapHeightE02_38 u t)) :
    |signedSpectralMoment38 u (2 * j + 1)| ≤
      (signedSpectralMoment38 u (2 * j) + signedSpectralMoment38 u (2 * (j + 1))) / 2 := by
  exact NlsGge.Birkhoff.signedSpectral_amgm38 u j i0 i1 i2

/-- Signed polynomial continuity. The natural Sobolev index `m`, odd-charge
index `j`, and proof `hmj : j+2 ≤ m` are arbitrary. The odd local charge's
Sobolev representative is continuous on the fixed space `H^(m-1)`. -/
theorem actual_signed_odd_sobolev_continuous38  (m j : ℕ) (hmj : j + 2 ≤ m) :
    Continuous (oddChargeSobolev38 m j) := by
  exact NlsGge.Birkhoff.continuous_oddChargeSobolev38 m j hmj

/-- Signed Sobolev Cauchy-Schwarz bound. The natural Sobolev index `m`, odd-charge
index `j`, proof `hmj : j+2 ≤ m`, and vector `x` of `H^(m-1)` are arbitrary.
The square of the odd-charge representative is at most the product of its
two adjacent even-charge representatives on that same vector. -/
theorem actual_signed_odd_sobolev_cs38  (m j : ℕ) (hmj : j + 2 ≤ m) (x : SobolevHilbert ((m - 1 : ℕ) : ℝ)) :
    oddChargeSobolev38 m j x ^ 2 ≤ chargeSobolev38 m j x * chargeSobolev38 m (j + 1) x := by
  exact NlsGge.Birkhoff.oddChargeSobolev_cs38 m j hmj x

/-- L06 finite-mesh AL ensemble. The implicit real coefficients `β₀`, `β₁`,
`β₂`, proofs `hβ₀ : 0 < β₀`, `hβ₁ : 0 ≤ β₁`, `hβ₂ : 0 ≤ β₂`, implicit
natural mesh index `N`, proof `hN : 1 ≤ N`, and mesh restriction
`hh : alh38 N < β₀` are arbitrary. The AL law is a probability measure; its
density is integrable with positive bounded partition; every integer symbol
is positive; its Fourier weight is measurable and between zero and one at
every vector `v`, and integrable under its Gaussian. The relative normalizer
is positive and at most one, and the exact Liouville/Gaussian factorization
holds, including the zero mode. -/
theorem actual_al_q4_ensemble38  {β₀ β₁ β₂ : ℝ} (hβ₀ : 0 < β₀) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) {N : ℕ}
    (hN : 1 ≤ N) (hh : alh38 N < β₀) :
    IsProbabilityMeasure (alQ4Eta38 β₀ β₁ β₂ N) ∧
    Integrable (alQ4Density38 β₀ β₁ β₂ N) ∧
    0 < alQ4Partition38 β₀ β₁ β₂ N ∧
    alQ4Partition38 β₀ β₁ β₂ N ≤ (Real.pi * alh38 N / β₀) ^ (2 * N + 1) ∧
    (∀ ν : ℤ, 0 < alSymbol38 β₀ β₁ β₂ N ν) ∧
    Measurable (fun û : ZMod (2 * N + 1) → ℂ => alQ4F38 β₀ β₁ β₂ N (alQ4V38 N û)) ∧
    (∀ v, 0 ≤ alQ4F38 β₀ β₁ β₂ N v ∧ alQ4F38 β₀ β₁ β₂ N v ≤ 1) ∧
    Integrable (fun û : ZMod (2 * N + 1) → ℂ => alQ4F38 β₀ β₁ β₂ N (alQ4V38 N û))
      (alQ4Gauss38 β₀ β₁ β₂ N) ∧
    0 < alQ4Z38 β₀ β₁ β₂ N ∧ alQ4Z38 β₀ β₁ β₂ N ≤ 1 ∧
    alQ4Partition38 β₀ β₁ β₂ N =
      alh38 N ^ (2 * N + 1) *
        (∏ ν ∈ Finset.Icc (-(N : ℤ)) N, Real.pi / alSymbol38 β₀ β₁ β₂ N ν) *
        alQ4Z38 β₀ β₁ β₂ N := by
  exact NlsGge.AblowitzLadik.alQ4Ensemble38 hβ₀ hβ₁ hβ₂ hN hh

/-- L06 finite-mesh normalizer. The implicit real coefficients `β₀`, `β₁`,
`β₂`, proofs `hβ₁ : 0 ≤ β₁`, `hβ₂ : 0 ≤ β₂`, implicit natural mesh index
`N`, proof `hN : 1 ≤ N`, and restriction `hh : alh38 N < β₀` are arbitrary.
The physical partition equals the mesh-power factor times the full finite
Gaussian product times the relative partition. No additional positivity
premise for `β₀` is introduced. -/
theorem actual_al_q4_normalizer38  {β₀ β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) {N : ℕ} (hN : 1 ≤ N)
    (hh : alh38 N < β₀) :
    alQ4Partition38 β₀ β₁ β₂ N =
      alh38 N ^ (2 * N + 1) *
        (∏ ν ∈ Finset.Icc (-(N : ℤ)) N, Real.pi / alSymbol38 β₀ β₁ β₂ N ν) *
        alQ4Z38 β₀ β₁ β₂ N := by
  exact NlsGge.AblowitzLadik.alQ4Normalizer38 hβ₁ hβ₂ hN hh

/-- L06 relative partition limit. The implicit real coefficients `β₀`, `β₁`,
`β₂` and proofs `h0 : 0 < β₀`, `h1 : 0 ≤ β₁`, `h2 : 0 < β₂` are arbitrary.
The lattice relative partition converges to the continuum relative partition. -/
theorem actual_al_q4_partition_tendsto38 {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 ≤ β₁) (h2 : 0 < β₂) :
    Tendsto (alQ4Z38 β₀ β₁ β₂) atTop (𝓝 (alQ4Z2_38 β₀ β₁ β₂)) := by
  exact NlsGge.AblowitzLadik.alQ4Z_tendsto38 h0 h1 h2

/-- L06 continuum partition positivity. The implicit real coefficients `β₀`,
`β₁`, `β₂` and proofs `h0 : 0 < β₀`, `h1 : 0 ≤ β₁`, `h2 : 0 < β₂` are
arbitrary. The continuum Q4 relative partition is strictly positive. -/
theorem actual_al_q4_limit_partition_pos38 {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 ≤ β₁) (h2 : 0 < β₂) : 0 < alQ4Z2_38 β₀ β₁ β₂ := by
  exact NlsGge.AblowitzLadik.alQ4Z2_pos38 h0 h1 h2

/-- L06 AL weak continuum limit. The implicit real coefficients `β₀`, `β₁`,
`β₂`, proofs `h0 : 0 < β₀`, `h1 : 0 ≤ β₁`, `h2 : 0 < β₂`, real regularity
`s`, proof `hs : s < 3/2`, and bounded continuous real test `φ` on `H^s` are
arbitrary. Expectations under the interpolated lattice laws converge to the
expectation under the direct continuum Q4 law on that same space. -/
theorem actual_al_q4_weak_tendsto38 {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 ≤ β₁) (h2 : 0 < β₂) (s : ℝ) (hs : s < 3 / 2)
    (φ : BoundedContinuousFunction (SobolevHilbert s) ℝ) :
    Tendsto (fun N : ℕ => ∫ x, φ x ∂(alQ4Mu38 s β₀ β₁ β₂ N)) atTop
      (𝓝 (∫ x, φ x ∂(alQ4Rho38 s β₀ β₁ β₂))) := by
  exact NlsGge.AblowitzLadik.alQ4_weak_tendsto38 h0 h1 h2 s hs φ

/-- L06 AL probability-measure convergence. The implicit real coefficients
`β₀`, `β₁`, `β₂`, proofs `h0 : 0 < β₀`, `h1 : 0 ≤ β₁`, `h2 : 0 < β₂`,
real regularity `s` and proof `hs : s < 3/2` are arbitrary. The interpolated
lattice probability measures converge weakly to the continuum Q4 probability
measure on `H^s`. -/
theorem actual_al_q4_probability_tendsto38 {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 ≤ β₁) (h2 : 0 < β₂) (s : ℝ)
    (hs : s < 3 / 2) :
    Tendsto (fun N : ℕ => alQ4MuPM38 h0 h1 h2.le s N) atTop (𝓝 (alQ4RhoPM38 h0 h1 h2 s)) := by
  exact NlsGge.AblowitzLadik.alQ4_probMeasure_tendsto38 h0 h1 h2 s hs

/-- L06 unmodified Fourier limit. The implicit real coefficients `β₀`, `β₁`,
`β₂`, positive-coefficient proofs `h0`, `h1`, `h2`, implicit real regularity
`s`, proof `hs : s < 3/2`, and bounded continuous real test `φ` on `H^s` are
arbitrary. The original order-two bare Fourier expectations converge to the
direct Q4 expectation, and the original Fourier partition divided by its
exact finite Gaussian product converges to the same continuum partition. -/
theorem actual_l06_fourier_limit38  {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 < β₁) (h2 : 0 < β₂) {s : ℝ}
    (hs : s < 3 / 2) (φ : SobolevHilbert s →ᵇ ℝ) :
    Tendsto (fun N : ℕ => ∫ u, φ u ∂(nuBareS38 2 (alQ4Beta38 β₀ β₁ β₂) N s)) atTop
      (𝓝 (∫ u, φ u ∂(alQ4Rho38 s β₀ β₁ β₂))) ∧
    Tendsto (fun N : ℕ => ZcalBare38 2 (alQ4Beta38 β₀ β₁ β₂) N /
      ∏ n ∈ Finset.Icc (-(N : ℤ)) N,
        (Real.pi / finiteHierarchyRate38 2 (alQ4Beta38 β₀ β₁ β₂) n)) atTop
      (𝓝 (alQ4Z2_38 β₀ β₁ β₂)) := by
  exact NlsGge.Birkhoff.L06_08a_free38 h0 h1 h2 hs φ

/-- L06 finite-gap identification for the actual producers. The implicit real
coefficients `β₀`, `β₁`, `β₂`, positive-coefficient proofs `h0`, `h1`, `h2`,
and arbitrary real regularity `s` are retained. The reflected Gaussian and
unreflected Gaussian have the same realization law; the order-two nonlinear
potential is the direct Q4 potential at every `u : Hm1 2`; the actual
finite-gap normalizer is the Q4 normalizer; and the actual finite-gap law,
realized on `H^s`, equals the direct continuum Q4 law. This is the L06.08b
obligation also shared with F05. -/
theorem actual_l06_finite_gap_identification38  {β₀ β₁ β₂ : ℝ}
    (h0 : 0 < β₀) (h1 : 0 < β₁) (h2 : 0 < β₂) (s : ℝ) :
    (((gammaM38 2 (alQ4Beta38 β₀ β₁ β₂)).map reflect38).map
        (seqRealization38 (sobolevModeWeight s)) =
      (gammaM38 2 (alQ4Beta38 β₀ β₁ β₂)).map (seqRealization38 (sobolevModeWeight s))) ∧
    (∀ u : Hm1 2, Vm38 2 (alQ4Beta38 β₀ β₁ β₂) u =
      alV2_38 β₁ β₂ (reSob38 ((2 - 1 : ℕ) : ℝ) 1 u)) ∧
    ZM38 actualBirkhoffInput38 2 (alQ4Beta38 β₀ β₁ β₂) = alQ4Z2_38 β₀ β₁ β₂ ∧
    (muM38 actualBirkhoffInput38 2 (alQ4Beta38 β₀ β₁ β₂)).map (reSob38 ((2 - 1 : ℕ) : ℝ) s) =
      alQ4Rho38 s β₀ β₁ β₂ := by
  exact NlsGge.Birkhoff.L06_08b_38 actualBirkhoffInput38 actualOneSmoothingInput38 h0 h1 h2 s

end LiebLiniger.FixedPeriod.EXT
