import NlsGge.Atomic.T.T009
import NlsGge.Atomic.T.T010
import NlsGge.Atomic.T.T014
import NlsGge.Atomic.T.T020
import NlsGge.Atomic.T.T023
import NlsGge.Atomic.R.R109
import NlsGge.Birkhoff.F10Bridge38
import NlsGge.Birkhoff.SignedMomentsBridge38
import NlsGge.ThirdConsultation.Main.PeriodicInfiniteChargeGGE

                                                                              
                                                                            
                                                                           
                                                                            
                                                                            
                                                                                  
                                
                                                                       
set_option autoImplicit false
noncomputable section

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff BoundedContinuousFunction
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38
open NlsGge.Birkhoff NlsGge.SpectralFoundations NlsGge.NLS38
open NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation.PDE

namespace NlsGge.ThirdConsultation.Records

/-- NEW-F09: the entire F09 conjunction at the actual pair, together with
T-010's literal weighted-carrier law formulation. The normalizer clause reuses
T-009; neither weighted nor ordinary Sobolev test classes are restricted. -/
theorem NEW_F09_concrete {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) {s : ℝ}
    (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
  (
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
        ∂((fullWeightedSequenceGaussian c s).map (physFW06_38 c s))) atTop (𝓝 0))
  ) ∧
    ((∀ N : ℕ, IsProbabilityMeasure (T.fullFourierLawE c s N)) ∧
      IsProbabilityMeasure (T.muWE c s hs hs') ∧
      ∀ F : ECarrier38 c s →ᵇ ℝ,
        Tendsto (fun N : ℕ => ∫ x, F x ∂T.fullFourierLawE c s N) atTop
          (𝓝 (∫ x, F x ∂T.muWE c s hs hs'))) := by
  have hlegacy := actualBirkhoffInput38.F09_38 actualOneSmoothingInput38 c hs hs'
  have hnormalizers := T.fullFourier_normalizers_limit_lower lower upper c
  rw [T.ZW_eq_actual lower upper c] at hnormalizers
  exact ⟨⟨⟨hnormalizers.2.1, hnormalizers.1, hnormalizers.2.2⟩, hlegacy.2⟩,
    T.fullFourier_weak_weighted lower upper c s hs hs'⟩

/-- NEW-F10: canonical common-space densities, their integrability and
normalization, both coordinate and physical L1 convergence, the eLpNorm form
from T-014, and the concrete minimum identity from the source proof.
Ramer divergence is a proved conclusion, supplied internally by R-109. -/
theorem NEW_F10_concrete {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) {s : ℝ}
    (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    RamerDivergence38 c s
      (actualBirkhoffInput38.KW06_38 actualOneSmoothingInput38 c
        (le_one_of_lt_three_quarters_W06_38 hs'))
      (R.canonicalDelta c s hs (le_one_of_lt_three_quarters_W06_38 hs')) ∧
    (∀ N : ℕ, Integrable (fN38 c s N) (fullWeightedSequenceGaussian c s)) ∧
    Integrable (T.fullFourierDensity c s hs hs') (fullWeightedSequenceGaussian c s) ∧
    (∫ x, T.fullFourierDensity c s hs hs' x ∂fullWeightedSequenceGaussian c s) =
      actualBirkhoffInput38.ZW38 c.val ∧
    (∀ N : ℕ, Integrable
      (fun x : ECarrier38 c s => fN38 c s N x - T.fullFourierDensity c s hs hs' x)
      (fullWeightedSequenceGaussian c s)) ∧
    Tendsto (fun N : ℕ => ∫ x, |fN38 c s N x - T.fullFourierDensity c s hs hs' x|
      ∂fullWeightedSequenceGaussian c s) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => ∫ u,
      |physFun38 c s (fN38 c s N) u -
        physFun38 c s (T.fullFourierDensity c s hs hs') u|
      ∂((fullWeightedSequenceGaussian c s).map (physFW06_38 c s))) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => eLpNorm
      (fun x : ECarrier38 c s => fN38 c s N x - T.fullFourierDensity c s hs hs' x)
      1 (fullWeightedSequenceGaussian c s)) atTop (𝓝 0) ∧
    (∀ N : ℕ,
      (∫ x, |fN38 c s N x - T.fullFourierDensity c s hs hs' x|
        ∂fullWeightedSequenceGaussian c s) =
      (∫ x, fN38 c s N x ∂fullWeightedSequenceGaussian c s) +
        (∫ x, T.fullFourierDensity c s hs hs' x ∂fullWeightedSequenceGaussian c s) -
        2 * ∫ x, min (fN38 c s N x) (T.fullFourierDensity c s hs hs' x)
          ∂fullWeightedSequenceGaussian c s) := by
  have hdiv := R.canonicalDelta_spec c s hs (le_one_of_lt_three_quarters_W06_38 hs')
  have hpacket := T.fullFourier_densities_L1 lower upper c s hs hs'
  have hmean := hpacket.2.2.1
  rw [T.ZW_eq_actual lower upper c] at hmean
  have hL1 : Tendsto (fun N : ℕ => ∫ x,
      |fN38 c s N x - T.fullFourierDensity c s hs hs' x|
      ∂fullWeightedSequenceGaussian c s) atTop (𝓝 0) :=
    actualBirkhoffInput38.L1_F10_forall_delta38 actualOneSmoothingInput38 c hs hs'
      (R.canonicalDelta c s hs (le_one_of_lt_three_quarters_W06_38 hs')) hdiv
  refine ⟨hdiv, hpacket.1, hpacket.2.1, hmean,
    (fun N => (hpacket.1 N).sub hpacket.2.1), hL1, ?_, hpacket.2.2.2, ?_⟩
  · refine hL1.congr fun N => ?_
    rw [(measurableEmbedding_physFW06_38 c s).integral_map]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have hN := physFun38_physOfE38 (c := c) (s := s) (fN38 c s N) x
    have hW := physFun38_physOfE38 (c := c) (s := s)
      (fun y : FullWeightedHilbert c s => T.fullFourierDensity c s hs hs' y) x
    exact congrArg₂ (fun a b : ℝ => |a - b|) hN.symm hW.symm
  · intro N
    exact integral_abs_sub_eq_F10_38 (hpacket.1 N) hpacket.2.1

/-- NEW-F11: all strictly subcritical finite exponential tilts and finite
products, with all original m-indexed statements retained. The extra conjuncts
retain the single-charge statement, exact tilt identity, positive determinant
limit/lower bound, plane identification, and accepted T-020 Finset formulation. -/
theorem NEW_F11_concrete {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (m : ℕ) (hm : 2 ≤ m) :
  (
    (∀ (J : ℕ), J ≤ m - 1 → ∀ t : ℕ → ℝ, (∀ j ≤ J, 0 ≤ t j ∧ t j < NlsGge.coefficient c.val j) →
      ∃ C : ℝ, ∀ N : ℕ,
        Integrable (fun u => Real.exp (∑ j ∈ Finset.range (J + 1), t j * chargeFn38 m j u))
            (nuWN38 c N) ∧
          ∫ u, Real.exp (∑ j ∈ Finset.range (J + 1), t j * chargeFn38 m j u) ∂(nuWN38 c N) ≤ C) ∧
    (∀ (n : ℕ) (jj : Fin n → ℕ), (∀ i, jj i ≤ m - 1) → ∀ p : Fin n → ℕ,
      (∀ N : ℕ, Integrable (fun u => ∏ i, chargeFn38 m (jj i) u ^ p i) (nuWN38 c N)) ∧
        Integrable (fun u => ∏ i, chargeFn38 m (jj i) u ^ p i) (actualBirkhoffInput38.muW38 c.val) ∧
        Tendsto (fun N : ℕ => ∫ u, ∏ i, chargeFn38 m (jj i) u ^ p i ∂(nuWN38 c N)) atTop
          (𝓝 (∫ u, ∏ i, chargeFn38 m (jj i) u ^ p i ∂(actualBirkhoffInput38.muW38 c.val))))
  ) ∧
    (∀ (j : ℕ), j ≤ m - 1 → ∀ p : ℕ,
      (∀ N : ℕ, Integrable (fun u => chargeFn38 m j u ^ p) (nuWN38 c N)) ∧
      Integrable (fun u => chargeFn38 m j u ^ p) (actualBirkhoffInput38.muW38 c.val) ∧
      Tendsto (fun N : ℕ => ∫ u, chargeFn38 m j u ^ p ∂nuWN38 c N) atTop
        (𝓝 (∫ u, chargeFn38 m j u ^ p ∂actualBirkhoffInput38.muW38 c.val))) ∧
    (∀ (J : ℕ) (t : ℕ → ℝ) (ht : TiltAdmissible38 c J t), J ≤ m → ∀ N : ℕ,
      Integrable (fun u => Real.exp (∑ j ∈ Finset.range (J + 1), t j * chargeFn38 m j u))
        (nuWN38 c N) ∧
      (∫ u, Real.exp (∑ j ∈ Finset.range (J + 1), t j * chargeFn38 m j u) ∂nuWN38 c N) =
        (tiltDet38 c J t N)⁻¹ *
          (relativePartition38 (tiltedCoefficients38 c ht) N / relativePartition38 c N)) ∧
    (∀ (J : ℕ) (t : ℕ → ℝ), TiltAdmissible38 c J t →
      (∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, δ ≤ tiltDet38 c J t N) ∧
      (∃ D : ℝ, 0 < D ∧ Tendsto (tiltDet38 c J t) atTop (𝓝 D))) ∧
    (∀ (j : ℕ), j ≤ m → ∀ (N : ℕ) (z : FourierPlane N),
      chargeFn38 m j (planeL2 N z) = localCharge38 (planeReal N z) j) ∧
    (∀ (indices : Finset ℕ) (powers : ℕ → ℕ),
      (∀ N : ℕ, Integrable (T.chargeMonomial indices powers) (T.fullFourierLaw c N)) ∧
      Integrable (T.chargeMonomial indices powers) (T.muW c) ∧
      Tendsto (fun N : ℕ => ∫ u, T.chargeMonomial indices powers u ∂T.fullFourierLaw c N)
        atTop (𝓝 (∫ u, T.chargeMonomial indices powers u ∂T.muW c))) := by
  refine ⟨actualBirkhoffInput38.F11_38 actualOneSmoothingInput38 c m hm,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj p
    exact actualBirkhoffInput38.F11_moment_single38 actualOneSmoothingInput38 c m hm j hj p
  · intro J t ht hJ N
    exact exact_identity38 c ht m hm hJ N
  · intro J t ht
    exact ⟨tiltDet_lower38 ht, tiltDet_tendsto38 ht⟩
  · intro j hj N z
    exact chargeFn38_planeL2 m j hm hj N z
  · intro indices powers
    exact T.fullFourier_fixedCharge_moments_tendsto lower upper c indices powers

/-- SIGNED-MOMENTS: the literal 2/pi normalization, finite smooth spectral
moments, even and odd identifications, both adjacent-even inequalities,
Sobolev continuity, plane and almost-everywhere identifications, all original
finite families and powers, and the accepted T-023 mixed-product formulation. -/
theorem SIGNED_MOMENTS_concrete {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (m : ℕ) (hm : 2 ≤ m) :
    (∀ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1) (k : ℕ),
      Integrable (fun t : ℝ =>
        (2 * t) ^ k * actualGapHeightE02_38 (smoothL2_38 U hU hper) t)) ∧
    (∀ (u : PhysicalL2) (k : ℕ), signedSpectralMoment38 u k =
      (2 / Real.pi) * ∫ t : ℝ, (2 * t) ^ k * actualGapHeightE02_38 u t) ∧
    (∀ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1) (j : ℕ),
      signedSpectralMoment38 (smoothL2_38 U hU hper) (2 * j) = localCharge38 U j ∧
      signedSpectralMoment38 (smoothL2_38 U hU hper) (2 * j + 1) = oddLocalCharge38 U j ∧
      |signedSpectralMoment38 (smoothL2_38 U hU hper) (2 * j + 1)| ^ 2 ≤
        signedSpectralMoment38 (smoothL2_38 U hU hper) (2 * j) *
          signedSpectralMoment38 (smoothL2_38 U hU hper) (2 * j + 2) ∧
      |signedSpectralMoment38 (smoothL2_38 U hU hper) (2 * j + 1)| ≤
        (signedSpectralMoment38 (smoothL2_38 U hU hper) (2 * j) +
          signedSpectralMoment38 (smoothL2_38 U hU hper) (2 * (j + 1))) / 2) ∧
    (∀ (j : ℕ), j + 2 ≤ m →
      Continuous (oddChargeSobolev38 m j) ∧
      ∀ x : SobolevHilbert ((m - 1 : ℕ) : ℝ),
        oddChargeSobolev38 m j x ^ 2 ≤ chargeSobolev38 m j x * chargeSobolev38 m (j + 1) x ∧
        |oddChargeSobolev38 m j x| ≤
          (chargeSobolev38 m j x + chargeSobolev38 m (j + 1) x) / 2) ∧
    (∀ (k : ℕ), k ≤ 2 * m - 2 →
      Continuous (fun y : SobolevCarrier38 ((m - 1 : ℕ) : ℝ) =>
        signedChargeFn38 m k
          (physOfCarrier38 ((m - 1 : ℕ) : ℝ) (Nat.cast_nonneg _) y))) ∧
    (∀ (k : ℕ), k ≤ 2 * m - 2 → ∀ (N : ℕ) (z : FourierPlane N),
      signedChargeFn38 m k (planeL2 N z) = signedSpectralMoment38 (planeL2 N z) k) ∧
    (∀ (k : ℕ), k ≤ 2 * m - 2 →
      ∀ᵐ u : PhysicalL2 ∂actualBirkhoffInput38.muW38 c.val,
        signedChargeFn38 m k u = signedSpectralMoment38 u k) ∧
    (∀ (n : ℕ) (kk : Fin n → ℕ), (∀ i, kk i ≤ 2 * m - 2) → ∀ p : Fin n → ℕ,
      (∀ N : ℕ, Integrable (fun u => ∏ i, signedChargeFn38 m (kk i) u ^ p i) (nuWN38 c N)) ∧
      Integrable (fun u => ∏ i, signedChargeFn38 m (kk i) u ^ p i)
        (actualBirkhoffInput38.muW38 c.val) ∧
      Tendsto (fun N : ℕ => ∫ u, ∏ i, signedChargeFn38 m (kk i) u ^ p i ∂nuWN38 c N)
        atTop (𝓝 (∫ u, ∏ i, signedChargeFn38 m (kk i) u ^ p i
          ∂actualBirkhoffInput38.muW38 c.val))) ∧
    (∀ (k : ℕ), k ≤ 2 * m - 2 → ∀ p : ℕ,
      (∀ N : ℕ, Integrable (fun u => signedChargeFn38 m k u ^ p) (nuWN38 c N)) ∧
      Integrable (fun u => signedChargeFn38 m k u ^ p) (actualBirkhoffInput38.muW38 c.val) ∧
      Tendsto (fun N : ℕ => ∫ u, signedChargeFn38 m k u ^ p ∂nuWN38 c N) atTop
        (𝓝 (∫ u, signedChargeFn38 m k u ^ p ∂actualBirkhoffInput38.muW38 c.val))) ∧
    (∀ (signedIndices evenIndices : Finset ℕ) (powersSigned powersEven : ℕ → ℕ),
      (∀ N : ℕ, Integrable
        (T.signedChargeMonomial signedIndices evenIndices powersSigned powersEven)
        (T.fullFourierLaw c N)) ∧
      Integrable (T.signedChargeMonomial signedIndices evenIndices powersSigned powersEven)
        (T.muW c) ∧
      Tendsto (fun N : ℕ => ∫ u,
        T.signedChargeMonomial signedIndices evenIndices powersSigned powersEven u
          ∂T.fullFourierLaw c N) atTop
        (𝓝 (∫ u, T.signedChargeMonomial signedIndices evenIndices powersSigned powersEven u
          ∂T.muW c))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro U hU hper k
    exact (signedSpectral_moments38 U hU hper (k + 1)).1 k (by omega)
  · intro u k
    rfl
  · intro U hU hper j
    obtain ⟨hint, hodd⟩ := signedSpectral_moments38 U hU hper (j + 1)
    have i0 := hint (2 * j) (by omega)
    have i1 := hint (2 * j + 1) (by omega)
    have i2 := hint (2 * j + 2) (by omega)
    refine ⟨signedSpectral_even_eq_localCharge38 U hU hper j,
      hodd j le_rfl, ?_, signedSpectral_amgm38 _ j i0 i1 i2⟩
    simpa only [sq_abs] using signedSpectral_cs38 (smoothL2_38 U hU hper) j i0 i1 i2
  · intro j hj
    exact ⟨continuous_oddChargeSobolev38 m j hj,
      fun x => ⟨oddChargeSobolev_cs38 m j hj x, oddChargeSobolev_amgm38 m j hj x⟩⟩
  · intro k hk
    exact continuous_signedChargeFn_physOfCarrier38 m k hm hk
  · intro k hk N z
    exact signedChargeFn38_planeL2 m k N hm hk z
  · intro k hk
    exact actualBirkhoffInput38.signedChargeFn_ae_spectral_38 actualOneSmoothingInput38 c m hm k hk
  · intro n kk hkk p
    exact actualBirkhoffInput38.signedMoments_38 actualOneSmoothingInput38 c m hm n kk hkk p
  · intro k hk p
    exact actualBirkhoffInput38.signedMoment_single_38 actualOneSmoothingInput38 c m hm k hk p
  · intro signedIndices evenIndices powersSigned powersEven
    exact T.fullFourier_signedCharge_moments_tendsto lower upper c
      signedIndices evenIndices powersSigned powersEven

/-- Supplement to landed MAIN, containing only record declaration forms
not literally printed there: all extension indices for charge moments, carrier
pushforward invariance, and the Fourier-sequence null-set formulation. -/
theorem S04_concrete (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) :
    (∀ (m j : ℕ), j ≤ m - 1 → ∀ p : ℕ,
      Integrable (fun u : PhysicalL2 => |chargeFn38 m j u| ^ p) (actualMuW c)) ∧
    (∀ (m : ℕ) (hm : 1 ≤ m) (t : ℝ)
      [MeasurableSpace (SobolevCarrier38 (m : ℝ))]
      [BorelSpace (SobolevCarrier38 (m : ℝ))],
      ((actualMuW c).map (physH38 m)).map (nlsFlowC m hm t) =
        (actualMuW c).map (physH38 m)) ∧
    actualMuW c {u : PhysicalL2 | fourierSeq38 u ∉ seqSobolev38 ((1 : ℕ) : ℝ)} = 0 := by
  have hM : BirkhoffMolnar38 actualBirkhoffTop38 := actualBirkhoffInput38.toMolnar
  refine ⟨?_, ?_, ?_⟩
  · intro m j hj p
    exact actualBirkhoffTop38.integrable_muW38_charge_pow
      lower upper c hlower hbound hupper hM m j hj p
  · intro m hm t instM instB
    exact actualBirkhoffTop38.S04_08_nlsFlow_invariant_muW_Hm
      lower upper c hlower hbound hupper actualBirkhoffNLSFlowInput38 m hm t
  · exact actualBirkhoffTop38.muW38_junk_null38 lower upper c hlower hbound hupper

end NlsGge.ThirdConsultation.Records
