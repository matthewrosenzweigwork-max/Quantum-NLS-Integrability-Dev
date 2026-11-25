import LiebLiniger.FixedPeriod.Atomic.ORIG.B018SmoothMoment
import NlsGge.Spectral.SobolevToL2Map38
import NlsGge.Hierarchy.RiccatiPhysicalH1Q2ContinuousEnergyExtensionAfterScalarL1Prerequisites
import NlsGge.Hierarchy.RiccatiUnitPeriodIntervalToPhysicalHaar
import NlsGge.Birkhoff.F07MassMoment38b

/-! # B018.C02 (record NEW-E01), fixed Sobolev case: H-based moment composition
(paper/v2.tex l.209-214, `F:eq:moment`, "smooth approximation extends each such fixed-charge
inequality to its stated Sobolev domain").

For `j ≥ 1` and `x ∈ H^j`, with `M = Q₀(x)`, `H = Q₂(x)`, `Q_{2j}` the continuous extensions
`chargeSobolev38 (j+1) ·` and `u` the `L²` field of `x`: `|u|⁴` is integrable,
`H ≥ ∫|u|⁴ ≥ M²`, `Q_{2j} ≥ H^{(j+1)/2}`, `Q_{2j} ≥ M^{j+1}`; for `x ≠ 0`, `M > 0` and
`Q_{2j} ≥ H^j/M^{j-1} ≥ H^{(j+1)/2}`.
Route: Fourier truncations (smooth trigonometric polynomials, `smoothMomentH38`,
`planeMoment38`), convergence in `H^j`, continuity of the charges and of the quartic integral
(through the canonical continuous `H¹` representative).
The statement of `sobolevMomentH38` is the reviewed frozen statement (STATEMENTS_SG08_B018.md). -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open MeasureTheory NlsGge.Pilot
open scoped ContDiff

section B018SobolevLemmas

open Filter Topology NlsGge.SpectralFoundations NlsGge.Sobolev38 NlsGge.Analysis

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-- The `L²` field of a Fourier truncation is the `L²` class of its trigonometric polynomial. -/
theorem sobolevToL2_trunc_B018 (k N : ℕ) (x : SobolevHilbert (k : ℝ)) :
    sobolevToL2_38 k (truncSobolev38 (k : ℝ) N x) =
      ContinuousMap.toLp 2 spatialMeasure ℂ
        (riccatiSmoothPeriodicLiftContinuousMapRecovery30First (truncField38 (k : ℝ) N x)
          (contDiff_truncField38 (k : ℝ) N x).continuous (periodic_truncField38 (k : ℝ) N x)) := by
  apply physicalFourierL2.injective
  apply lp.ext
  funext n
  rw [physicalFourierL2_apply, physicalFourierL2_apply, sobolevToL2_38_fourier,
    truncSobolev38_link]

/-- Quartic integral of a truncation: Haar integral = unit-interval integral of the polynomial. -/
theorem quartic_trunc_B018 (k N : ℕ) (x : SobolevHilbert (k : ℝ)) :
    ∫ z, ‖(sobolevToL2_38 k (truncSobolev38 (k : ℝ) N x) : PhysicalCircle → ℂ) z‖ ^ 4
        ∂spatialMeasure =
      ∫ t in (0 : ℝ)..1, ‖truncField38 (k : ℝ) N x t‖ ^ 4 := by
  rw [sobolevToL2_trunc_B018]
  have hae : (fun z => ‖(ContinuousMap.toLp 2 spatialMeasure ℂ
        (riccatiSmoothPeriodicLiftContinuousMapRecovery30First (truncField38 (k : ℝ) N x)
          (contDiff_truncField38 (k : ℝ) N x).continuous (periodic_truncField38 (k : ℝ) N x))
          : PhysicalCircle → ℂ) z‖ ^ 4) =ᵐ[spatialMeasure]
      fun z => ‖(riccatiSmoothPeriodicLiftContinuousMapRecovery30First (truncField38 (k : ℝ) N x)
          (contDiff_truncField38 (k : ℝ) N x).continuous (periodic_truncField38 (k : ℝ) N x)) z‖ ^ 4 :=
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure
      (riccatiSmoothPeriodicLiftContinuousMapRecovery30First (truncField38 (k : ℝ) N x)
        (contDiff_truncField38 (k : ℝ) N x).continuous (periodic_truncField38 (k : ℝ) N x))).mono
      fun z hz => by dsimp only; rw [hz]
  rw [integral_congr_ae hae,
    ← NlsGge.HierarchyRiccati.unitIntervalIntegral_lift_eq_spatialHaar
      (fun z => ‖(riccatiSmoothPeriodicLiftContinuousMapRecovery30First (truncField38 (k : ℝ) N x)
          (contDiff_truncField38 (k : ℝ) N x).continuous (periodic_truncField38 (k : ℝ) N x)) z‖ ^ 4)]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  show ‖AddCircle.liftIoc 1 0 (truncField38 (k : ℝ) N x) (t : PhysicalCircle)‖ ^ 4 = _
  rw [liftIoc_coe_eq38 _ (periodic_truncField38 (k : ℝ) N x) t]

/-- `H^k → H¹` (`k ≥ 1`), typed into the real Sobolev carrier `SobolevHilbert 1`. -/
def sobolevToH1Real_B018 (k : ℕ) (hk : 1 ≤ k) (y : SobolevHilbert (k : ℝ)) : SobolevHilbert 1 :=
  sobolevToH1_38 k hk y

theorem continuous_sobolevToH1Real_B018 (k : ℕ) (hk : 1 ≤ k) :
    Continuous (sobolevToH1Real_B018 k hk) :=
  continuous_sobolevToH1_38 k hk

theorem carrier_eq_sobolevToL2_B018 (k : ℕ) (hk : 1 ≤ k) (x : SobolevHilbert (k : ℝ)) :
    physicalH1CarrierToL2AfterAcceptedCoordinate (sobolevToH1Real_B018 k hk x) = sobolevToL2_38 k x := by
  apply physicalFourierL2.injective
  apply lp.ext
  funext n
  rw [physicalFourierL2_apply, physicalFourierL2_apply,
    physicalH1CarrierToL2AfterAcceptedCoordinate_fourier, sobolevToL2_38_fourier]
  rfl

theorem toLp_canonical_B018 (k : ℕ) (hk : 1 ≤ k) (x : SobolevHilbert (k : ℝ)) :
    ContinuousMap.toLp 2 spatialMeasure ℂ
        (physicalH1CanonicalContinuousRepresentativeCLM (sobolevToH1Real_B018 k hk x)) =
      sobolevToL2_38 k x := by
  rw [physicalH1CanonicalContinuousRepresentativeCLM_apply]
  unfold physicalH1CarrierContinuousAfterAcceptedCoordinate
  rw [physicalH1Continuous_toLp, carrier_eq_sobolevToL2_B018]

/-- The `L²` field of `x ∈ H^k` (`k ≥ 1`) agrees a.e. with its canonical continuous representative. -/
theorem ae_eq_canonical_B018 (k : ℕ) (hk : 1 ≤ k) (x : SobolevHilbert (k : ℝ)) :
    (sobolevToL2_38 k x : PhysicalCircle → ℂ) =ᵐ[spatialMeasure]
      (physicalH1CanonicalContinuousRepresentativeCLM (sobolevToH1Real_B018 k hk x) :
        PhysicalCircle → ℂ) := by
  rw [← toLp_canonical_B018 k hk x]
  exact ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure _

theorem quartic_eq_canonical_B018 (k : ℕ) (hk : 1 ≤ k) (x : SobolevHilbert (k : ℝ)) :
    ∫ z, ‖(sobolevToL2_38 k x : PhysicalCircle → ℂ) z‖ ^ 4 ∂spatialMeasure =
      physicalH1QuarticIntegralAfterScalarL1Prerequisites
        (physicalH1CanonicalContinuousRepresentativeCLM (sobolevToH1Real_B018 k hk x)) := by
  rw [physicalH1QuarticIntegralAfterScalarL1Prerequisites_eq_integral]
  exact integral_congr_ae ((ae_eq_canonical_B018 k hk x).mono fun z hz => by dsimp only; rw [hz])

/-- `|u|⁴` is integrable for the `L²` field of `x ∈ H^k`, `k ≥ 1`. -/
theorem integrable_quartic_B018 (k : ℕ) (hk : 1 ≤ k) (x : SobolevHilbert (k : ℝ)) :
    Integrable (fun z : PhysicalCircle => ‖(sobolevToL2_38 k x : PhysicalCircle → ℂ) z‖ ^ 4)
      spatialMeasure := by
  have hF : Integrable (fun z => ‖(physicalH1CanonicalContinuousRepresentativeCLM
      (sobolevToH1Real_B018 k hk x)) z‖ ^ 4) spatialMeasure := by
    apply ((physicalH1CanonicalContinuousRepresentativeCLM
      (sobolevToH1Real_B018 k hk x)).continuous.norm.pow 4).integrable_of_hasCompactSupport
    exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)
  exact hF.congr ((ae_eq_canonical_B018 k hk x).mono fun z hz => by dsimp only; rw [hz])

/-- The quartic integral is continuous on `H^k`, `k ≥ 1`. -/
theorem continuous_quartic_B018 (k : ℕ) (hk : 1 ≤ k) :
    Continuous (fun y : SobolevHilbert (k : ℝ) =>
      ∫ z, ‖(sobolevToL2_38 k y : PhysicalCircle → ℂ) z‖ ^ 4 ∂spatialMeasure) := by
  have h : (fun y : SobolevHilbert (k : ℝ) =>
      ∫ z, ‖(sobolevToL2_38 k y : PhysicalCircle → ℂ) z‖ ^ 4 ∂spatialMeasure) =
      fun y => physicalH1QuarticIntegralAfterScalarL1Prerequisites
        (physicalH1CanonicalContinuousRepresentativeCLM (sobolevToH1Real_B018 k hk y)) :=
    funext fun y => quartic_eq_canonical_B018 k hk y
  rw [h]
  exact continuous_physicalH1QuarticIntegralAfterScalarL1Prerequisites.comp
    (physicalH1CanonicalContinuousRepresentativeCLM.continuous.comp
      (continuous_sobolevToH1Real_B018 k hk))

/-- `Q₀(x) = Σ|x_n|² > 0` for `x ≠ 0`. -/
theorem mass_pos_B018 (m : ℕ) (x : SobolevHilbert ((m - 1 : ℕ) : ℝ)) (hx : x ≠ 0) :
    0 < chargeSobolev38 m 0 x := by
  rw [NlsGge.Birkhoff.chargeSobolev38_zero m x]
  obtain ⟨n, hn⟩ : ∃ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from x) n ≠ 0 := by
    by_contra h
    push_neg at h
    apply hx
    apply Subtype.ext
    funext n
    exact h n
  have hs := (weightedHilbert_hasSum (sobolevModeWeight ((m - 1 : ℕ) : ℝ))
    (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from x)).summable
  have hsum : Summable (fun n : ℤ =>
      ‖(show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from x) n‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
    have h1 := one_le_sobolevModeWeight38 (m - 1) n
    have h2 : 0 ≤ ‖(show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from x) n‖ ^ 2 := by
      positivity
    nlinarith
  exact hsum.tsum_pos (fun n => by positivity) n (pow_pos (norm_pos_iff.2 hn) 2)

/-- The fixed-Sobolev H-based moment chain, stated on `H^{m-1}`, `m ≥ 2`. -/
theorem sobolevMoment_core_B018 (m : ℕ) (hm : 2 ≤ m) (x : SobolevHilbert ((m - 1 : ℕ) : ℝ)) :
    Integrable (fun z : PhysicalCircle =>
      ‖(sobolevToL2_38 (m - 1) x : PhysicalCircle → ℂ) z‖ ^ 4) spatialMeasure ∧
    (chargeSobolev38 m 0 x) ^ 2 ≤
      ∫ z, ‖(sobolevToL2_38 (m - 1) x : PhysicalCircle → ℂ) z‖ ^ 4 ∂spatialMeasure ∧
    ∫ z, ‖(sobolevToL2_38 (m - 1) x : PhysicalCircle → ℂ) z‖ ^ 4 ∂spatialMeasure ≤
      chargeSobolev38 m 1 x ∧
    (chargeSobolev38 m 1 x) ^ ((((m - 1 : ℕ) : ℝ) + 1) / 2) ≤ chargeSobolev38 m (m - 1) x ∧
    (chargeSobolev38 m 0 x) ^ ((m - 1) + 1) ≤ chargeSobolev38 m (m - 1) x ∧
    (x ≠ 0 →
      0 < chargeSobolev38 m 0 x ∧
      (chargeSobolev38 m 1 x) ^ (m - 1) / (chargeSobolev38 m 0 x) ^ ((m - 1) - 1) ≤
        chargeSobolev38 m (m - 1) x ∧
      (chargeSobolev38 m 1 x) ^ ((((m - 1 : ℕ) : ℝ) + 1) / 2) ≤
        (chargeSobolev38 m 1 x) ^ (m - 1) / (chargeSobolev38 m 0 x) ^ ((m - 1) - 1)) := by
  have hk : 1 ≤ m - 1 := by omega
  have hT := tendsto_truncSobolev38 ((m - 1 : ℕ) : ℝ) x
  have cM := continuous_chargeSobolev38 m 0 (by omega)
  have cH := continuous_chargeSobolev38 m 1 (by omega)
  have cQ := continuous_chargeSobolev38 m (m - 1) le_rfl
  have cG := continuous_quartic_B018 (m - 1) hk
  have hplane : ∀ i : ℕ, i ≤ m → ∀ N : ℕ,
      chargeSobolev38 m i (truncSobolev38 ((m - 1 : ℕ) : ℝ) N x) =
        localCharge38 (truncField38 ((m - 1 : ℕ) : ℝ) N x) i := fun i hi N =>
    chargeSobolev38_smooth m i hm hi _ (contDiff_truncField38 _ N x)
      (periodic_truncField38 _ N x) _ (truncSobolev38_link _ N x)
  have hsm := fun N : ℕ => smoothMomentH38 (truncField38 ((m - 1 : ℕ) : ℝ) N x)
    (contDiff_truncField38 _ N x) (periodic_truncField38 _ N x)
  have hGN := fun N : ℕ => quartic_trunc_B018 (m - 1) N x
  have hMQ : (chargeSobolev38 m 0 x) ^ 2 ≤
      ∫ z, ‖(sobolevToL2_38 (m - 1) x : PhysicalCircle → ℂ) z‖ ^ 4 ∂spatialMeasure :=
    le_of_tendsto_of_tendsto' ((cM.pow 2).continuousAt.tendsto.comp hT)
      (cG.continuousAt.tendsto.comp hT) (fun N => by
        simp only [Function.comp_apply, Pi.pow_apply, Pi.mul_apply]
        rw [hplane 0 (by omega) N, hGN N]
        exact (hsm N).1)
  have hQH : ∫ z, ‖(sobolevToL2_38 (m - 1) x : PhysicalCircle → ℂ) z‖ ^ 4 ∂spatialMeasure ≤
      chargeSobolev38 m 1 x :=
    le_of_tendsto_of_tendsto' (cG.continuousAt.tendsto.comp hT)
      (cH.continuousAt.tendsto.comp hT) (fun N => by
        simp only [Function.comp_apply, Pi.pow_apply, Pi.mul_apply]
        rw [hplane 1 (by omega) N, hGN N]
        exact (hsm N).2.1)
  have hrp : (chargeSobolev38 m 1 x) ^ ((((m - 1 : ℕ) : ℝ) + 1) / 2) ≤
      chargeSobolev38 m (m - 1) x :=
    le_of_tendsto_of_tendsto'
      (((Real.continuous_rpow_const (by positivity)).comp cH).continuousAt.tendsto.comp hT)
      (cQ.continuousAt.tendsto.comp hT) (fun N => by
        simp only [Function.comp_apply, Pi.pow_apply, Pi.mul_apply]
        rw [hplane 1 (by omega) N, hplane (m - 1) (by omega) N]
        exact ((hsm N).2.2 (m - 1) hk).1)
  have hmass : (chargeSobolev38 m 0 x) ^ ((m - 1) + 1) ≤ chargeSobolev38 m (m - 1) x := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
    exact chargeMoment_mass_sobolev38 m hm x
  have hclear : (chargeSobolev38 m 1 x) ^ (m - 1) ≤
      (chargeSobolev38 m 0 x) ^ ((m - 1) - 1) * chargeSobolev38 m (m - 1) x :=
    le_of_tendsto_of_tendsto' ((cH.pow (m - 1)).continuousAt.tendsto.comp hT)
      (((cM.pow ((m - 1) - 1)).mul cQ).continuousAt.tendsto.comp hT) (fun N => by
        simp only [Function.comp_apply, Pi.pow_apply, Pi.mul_apply]
        rw [hplane 0 (by omega) N, hplane 1 (by omega) N, hplane (m - 1) (by omega) N]
        exact planeMoment38 N (fun i => (show WeightedHilbert
          (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from x) (modeIndex N i)) (m - 1) hk)
  refine ⟨integrable_quartic_B018 (m - 1) hk x, hMQ, hQH, hrp, hmass, fun hx => ?_⟩
  have hMpos := mass_pos_B018 m x hx
  refine ⟨hMpos, ?_, rpow_le_pow_div_B018 _ _ (m - 1) hk hMpos (hMQ.trans hQH)⟩
  rw [div_le_iff₀ (pow_pos hMpos _), mul_comm]
  exact hclear

end B018SobolevLemmas

/-- **B018.C02, fixed Sobolev.** For each `j ≥ 1` and every `x ∈ H^j` (the domain of the
continuous extension `Q_{2j} = chargeSobolev38 (j+1) j`), with `M = Q₀(x)`, `H = Q₂(x)` and
`u ∈ L²` the field of `x`: `|u|⁴` is integrable, `H ≥ ∫|u|⁴ ≥ M²`, `Q_{2j} ≥ H^{(j+1)/2}`,
`Q_{2j} ≥ M^{j+1}`; for `x ≠ 0`, `M > 0` and `Q_{2j} ≥ H^j/M^{j-1} ≥ H^{(j+1)/2}`. -/
theorem sobolevMomentH38 (j : ℕ) (hj : 1 ≤ j) (x : SobolevHilbert ((j : ℕ) : ℝ)) :
    Integrable (fun z : PhysicalCircle =>
      ‖(NlsGge.SpectralFoundations.sobolevToL2_38 j x : PhysicalCircle → ℂ) z‖ ^ 4)
      spatialMeasure ∧
    (chargeSobolev38 (j + 1) 0 x) ^ 2 ≤
      ∫ z, ‖(NlsGge.SpectralFoundations.sobolevToL2_38 j x : PhysicalCircle → ℂ) z‖ ^ 4
        ∂spatialMeasure ∧
    ∫ z, ‖(NlsGge.SpectralFoundations.sobolevToL2_38 j x : PhysicalCircle → ℂ) z‖ ^ 4
        ∂spatialMeasure ≤ chargeSobolev38 (j + 1) 1 x ∧
    (chargeSobolev38 (j + 1) 1 x) ^ (((j : ℝ) + 1) / 2) ≤ chargeSobolev38 (j + 1) j x ∧
    (chargeSobolev38 (j + 1) 0 x) ^ (j + 1) ≤ chargeSobolev38 (j + 1) j x ∧
    (x ≠ 0 →
      0 < chargeSobolev38 (j + 1) 0 x ∧
      (chargeSobolev38 (j + 1) 1 x) ^ j / (chargeSobolev38 (j + 1) 0 x) ^ (j - 1) ≤
        chargeSobolev38 (j + 1) j x ∧
      (chargeSobolev38 (j + 1) 1 x) ^ (((j : ℝ) + 1) / 2) ≤
        (chargeSobolev38 (j + 1) 1 x) ^ j / (chargeSobolev38 (j + 1) 0 x) ^ (j - 1)) := by
  exact sobolevMoment_core_B018 (j + 1) (by omega) x

end NlsGge.HierarchyRiccati.Core
