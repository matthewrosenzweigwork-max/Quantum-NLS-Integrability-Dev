import NlsGge.Birkhoff.H02Hierarchy38c

/-! # H02, part 4: `Z_m → Z_W > 0` and `μ_m ⇀ μ_W` in every fixed integer Sobolev space

v2 `B:prop:hierarchy` (l.879-913), conditional on `B : BirkhoffTop38`.

Statement. For the hierarchy coefficients `0 < lower ≤ c_j ≤ upper` (v2 `eq:weight` is the case
`[lower, upper] = [1, 2]`), `a_{m,n} = W_m(2πn)`, `γ_m` the product complex Gaussian with rates
`a_{m,n}` (`gammaM38 m (coefficient c)`), `Z_m = ∫ e^{-R_m(Φ⁻¹z)} dγ_m`, `μ_m = (Φ⁻¹)_#(Z_m⁻¹ e^{-R_m}γ_m)`:

* `Z_m → Z_W` and `Z_W > 0` (S03/S04 objects `ZW38`, `muW38`);
* for each `m ≥ 2`, `0 < Z_m ≤ 1`, `μ_m` is a probability measure, carried by `H^{m-1}`;
* for each integer `r ≥ 0` and every bounded continuous `F` on `H^r` (identified with the carrier of
  `h^r` through `physH38`, as in S04), `∫ F dμ_m → ∫ F dμ_W` as `m → ∞`; the measures `μ_m` are
  carried by `H^r` for `m ≥ r + 1` ("for the sufficiently large `m` on which the measures are
  supported there").

The proof is the coupling of v2: all measures are pushed forward from one standard Gaussian product
`stdGauss38`; the numerators and denominators converge by dominated convergence (bound
`‖F‖`, resp. `1`, because every `R̄_m ≥ 0`), the pointwise limit on the probability-one set `Ω₁`
being supplied by part 3.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.SpectralFoundations NlsGge.Weights
  NlsGge.Sobolev38 Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace BirkhoffTop38

variable (B : BirkhoffTop38) (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
  (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper)

/-- `∫ F(Φ⁻¹ z |_{H^r}) e^{-R̄_m(z)} dγ_m(z)`. -/
def hierNum38 (c : ℕ → ℝ) (m r : ℕ) (F : SobolevCarrier38 (r : ℝ) →ᵇ ℝ) : ℝ :=
  ∫ z, F (B.cleanTinvC r z) * Real.exp (-(B.hierRbar38 c m z))
    ∂(NlsGge.HierarchyRiccati.Core.gammaM38 m (coefficient c))

theorem hierZ38_eq_hierNum38 (m : ℕ) :
    B.hierZ38 c m = B.hierNum38 c m 0 (BoundedContinuousFunction.const _ 1) := by
  unfold hierZ38 hierNum38
  simp only [BoundedContinuousFunction.const_apply, one_mul]

include hlower hbound

/-- `∫ F dμ_m` in `γ_m`-coordinates. -/
theorem integral_hierMu38 {m : ℕ} (hm : 2 ≤ m) (r : ℕ) (F : SobolevCarrier38 (r : ℝ) →ᵇ ℝ) :
    ∫ u, F (physH38 r u) ∂(B.hierMu38 c m) = B.hierNum38 c m r F / B.hierZ38 c m := by
  obtain ⟨hZ, -⟩ := B.hierZ38_pos_le_one lower c hlower hbound hm
  unfold hierMu38
  rw [integral_map B.measurable_cleanΦinv.aemeasurable
    (measurable_comp_physH38 r F).aestronglyMeasurable]
  unfold hierMuHat38
  rw [integral_withDensity_exp_neg38 _ _ (B.measurable_hierRbar38 lower c hlower hbound hm) _ hZ]
  unfold hierNum38
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  simp only [physH38_cleanΦinv]
  ring

include hupper

/-- The numerator in the coupling coordinates. -/
theorem hierNum38_eq_coupled {m : ℕ} (hm : 2 ≤ m) (r : ℕ) (F : SobolevCarrier38 (r : ℝ) →ᵇ ℝ) :
    B.hierNum38 c m r F = ∫ g, F (B.cleanTinvC r (zHier38 c m g)) *
      Real.exp (-(B.hierRbar38 c m (zHier38 c m g))) ∂stdGauss38 := by
  let _ : MeasurableSpace (SobolevCarrier38 (r : ℝ)) := borel _
  have : BorelSpace (SobolevCarrier38 (r : ℝ)) := ⟨rfl⟩
  unfold hierNum38
  have hq := hierRate38_pos lower c hlower hbound m
  exact integral_eq_integral_scale38 (hierRate38 c m) hq _
    ((F.continuous.measurable.comp (B.measurable_cleanTinvC r)).mul
      (Real.measurable_exp.comp (B.measurable_hierRbar38 lower c hlower hbound hm).neg))

theorem integral_Wnum_coupled38 (r : ℕ) (F : SobolevCarrier38 (r : ℝ) →ᵇ ℝ) :
    ∫ z, F (B.cleanTinvC r z) * Real.exp (-(B.Rbar38 c z)) ∂(fullWeightSequenceGaussian c) =
      ∫ g, F (B.cleanTinvC r (zFull38 c g)) *
        Real.exp (-(B.Rbar38 c (zFull38 c g))) ∂stdGauss38 := by
  let _ : MeasurableSpace (SobolevCarrier38 (r : ℝ)) := borel _
  have : BorelSpace (SobolevCarrier38 (r : ℝ)) := ⟨rfl⟩
  have hq := fullWeightRate_pos lower upper c hlower hbound hupper
  exact integral_eq_integral_scale38 (fullWeightRate c) hq _
    ((F.continuous.measurable.comp (B.measurable_cleanTinvC r)).mul
      (Real.measurable_exp.comp (B.measurable_Rbar38 lower upper c hlower hbound hupper).neg))

/-- **Numerators converge** (v2 l.909-911: dominated convergence, bound `‖F‖` because
`e^{-R_m} ≤ 1`). -/
theorem tendsto_hierNum38 (r : ℕ) (F : SobolevCarrier38 (r : ℝ) →ᵇ ℝ) :
    Tendsto (fun m : ℕ => B.hierNum38 c m r F) atTop
      (𝓝 (∫ z, F (B.cleanTinvC r z) * Real.exp (-(B.Rbar38 c z))
        ∂(fullWeightSequenceGaussian c))) := by
  let _ : MeasurableSpace (SobolevCarrier38 (r : ℝ)) := borel _
  have : BorelSpace (SobolevCarrier38 (r : ℝ)) := ⟨rfl⟩
  rw [B.integral_Wnum_coupled38 lower upper c hlower hbound hupper r F]
  have hmeas : ∀ m : ℕ, 2 ≤ m → Measurable (fun g : ℤ → ℂ =>
      F (B.cleanTinvC r (zHier38 c m g)) * Real.exp (-(B.hierRbar38 c m (zHier38 c m g)))) :=
    fun m hm => ((F.continuous.measurable.comp (B.measurable_cleanTinvC r)).mul
      (Real.measurable_exp.comp (B.measurable_hierRbar38 lower c hlower hbound hm).neg)).comp
      (measurable_scaleSeq38 (hierRate38 c m))
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := stdGauss38) (l := atTop)
    (F := fun (m : ℕ) (g : ℤ → ℂ) =>
      F (B.cleanTinvC r (zHier38 c m g)) * Real.exp (-(B.hierRbar38 c m (zHier38 c m g))))
    (f := fun g : ℤ → ℂ => F (B.cleanTinvC r (zFull38 c g)) *
      Real.exp (-(B.Rbar38 c (zFull38 c g)))) (fun _ => ‖F‖)
    (by filter_upwards [eventually_ge_atTop 2] with m hm using (hmeas m hm).aestronglyMeasurable)
    (by
      filter_upwards [eventually_ge_atTop 2] with m hm
      refine Filter.Eventually.of_forall (fun g => ?_)
      rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
      have h0 := B.hierRbar38_nonneg lower c hlower hbound hm (zHier38 c m g)
      calc ‖F (B.cleanTinvC r (zHier38 c m g))‖ * Real.exp (-(B.hierRbar38 c m (zHier38 c m g)))
          ≤ ‖F‖ * 1 := mul_le_mul (F.norm_coe_le_norm _)
            (by rw [Real.exp_le_one_iff]; linarith) (Real.exp_pos _).le (norm_nonneg _)
        _ = ‖F‖ := mul_one _)
    (integrable_const _)
    (by
      filter_upwards [ae_mem_Omega1_38 lower upper c hlower hbound hupper] with g hg
      exact ((F.continuous.tendsto _).comp
        (B.tendsto_cleanTinvC_scale38 lower upper c hlower hbound hupper hg r)).mul
        ((Real.continuous_exp.tendsto _).comp
          (B.tendsto_hierRbar_scale38 lower upper c hlower hbound hupper hg).neg))
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with m hm
  exact (B.hierNum38_eq_coupled lower upper c hlower hbound hupper hm r F).symm

/-- **`Z_m → Z_W`.** -/
theorem tendsto_hierZ38 : Tendsto (fun m : ℕ => B.hierZ38 c m) atTop (𝓝 (B.ZW38 c)) := by
  have h := B.tendsto_hierNum38 lower upper c hlower hbound hupper 0
    (BoundedContinuousFunction.const (SobolevCarrier38 ((0 : ℕ) : ℝ)) 1)
  simp only [BoundedContinuousFunction.const_apply, one_mul] at h
  unfold ZW38
  refine h.congr (fun m => ?_)
  rw [hierZ38_eq_hierNum38]

/-- `μ_m` is carried by `H^{m-1}` (the support of `γ_m`, v2 l.656-657). -/
theorem ae_hierMu38_sobolev {m : ℕ} (hm : 2 ≤ m) :
    ∀ᵐ u : PhysicalL2 ∂(B.hierMu38 c m),
      SobolevSquareSummable ((m - 1 : ℕ) : ℝ) (physicalFourier u) := by
  have hβ : ∀ i ≤ m, 0 ≤ coefficient c i := fun i _ =>
    (coefficient_pos lower c hlower hbound i).le
  have hg := NlsGge.HierarchyRiccati.Core.ae_summable38 (m := m) (β := coefficient c) hm hβ
    (coefficient_pos lower c hlower hbound 0) (coefficient_pos lower c hlower hbound m)
  have hset : MeasurableSet {u : PhysicalL2 | fourierSeq38 u ∈ seqSobolev38 ((m - 1 : ℕ) : ℝ)} :=
    (measurableSet_seqSobolev38 _).preimage measurable_fourierSeq38
  have h : ∀ᵐ u : PhysicalL2 ∂(B.hierMu38 c m), fourierSeq38 u ∈ seqSobolev38 ((m - 1 : ℕ) : ℝ) :=
    (ae_map_iff B.measurable_cleanΦinv.aemeasurable hset).2
      (withDensity_absolutelyContinuous _ _ (by
        filter_upwards [hg] with z hz
        have hz' : z ∈ seqSobolev38 ((m - 1 : ℕ) : ℝ) := (mem_seqSobolev38_iff _ _).2 hz
        show fourierSeq38 (B.cleanΦinv z) ∈ seqSobolev38 ((m - 1 : ℕ) : ℝ)
        rw [B.fourierSeq38_cleanΦinv z (seqSobolev38_natCast_mono hz')]
        exact B.mapsTo_Tinv (m - 1) z hz'))
  filter_upwards [h] with u hu
  exact (fourierSeq38_mem_iff _ u).1 hu

/-- For `m ≥ r + 1` (and `m ≥ 2`) `μ_m` is carried by `H^r`. -/
theorem ae_hierMu38_sobolev_nat {m : ℕ} (hm : 2 ≤ m) (r : ℕ) (hr : r + 1 ≤ m) :
    ∀ᵐ u : PhysicalL2 ∂(B.hierMu38 c m), SobolevSquareSummable (r : ℝ) (physicalFourier u) := by
  filter_upwards [B.ae_hierMu38_sobolev lower upper c hlower hbound hupper hm] with u hu
  exact sobolevSquareSummable_restrict (r : ℝ) ((m - 1 : ℕ) : ℝ)
    (by exact_mod_cast (by omega : r ≤ m - 1)) _ hu

/-- **H02 (v2 `B:prop:hierarchy`), conditional on the E01 input `B`.** -/
theorem H02_hierarchy_limit_38 :
    ((Tendsto (fun m : ℕ => B.hierZ38 c m) atTop (𝓝 (B.ZW38 c))) ∧ 0 < B.ZW38 c) ∧
    (∀ m : ℕ, 2 ≤ m → 0 < B.hierZ38 c m ∧ B.hierZ38 c m ≤ 1 ∧
      IsProbabilityMeasure (B.hierMu38 c m) ∧
      ∀ᵐ u : PhysicalL2 ∂(B.hierMu38 c m),
        SobolevSquareSummable ((m - 1 : ℕ) : ℝ) (physicalFourier u)) ∧
    ∀ r : ℕ,
      (∀ m : ℕ, 2 ≤ m → r + 1 ≤ m → ∀ᵐ u : PhysicalL2 ∂(B.hierMu38 c m),
        SobolevSquareSummable (r : ℝ) (physicalFourier u)) ∧
      ∀ F : SobolevCarrier38 (r : ℝ) →ᵇ ℝ,
        Tendsto (fun m : ℕ => ∫ u, F (physH38 r u) ∂(B.hierMu38 c m)) atTop
          (𝓝 (∫ u, F (physH38 r u) ∂(B.muW38 c))) := by
  obtain ⟨hZW, -⟩ := B.ZW38_pos_le_one lower upper c hlower hbound hupper
  refine ⟨⟨B.tendsto_hierZ38 lower upper c hlower hbound hupper, hZW⟩, fun m hm => ?_, fun r => ?_⟩
  · obtain ⟨h1, h2⟩ := B.hierZ38_pos_le_one lower c hlower hbound hm
    exact ⟨h1, h2, B.isProbabilityMeasure_hierMu38 lower c hlower hbound hm,
      B.ae_hierMu38_sobolev lower upper c hlower hbound hupper hm⟩
  · refine ⟨fun m hm hr => B.ae_hierMu38_sobolev_nat lower upper c hlower hbound hupper hm r hr,
      fun F => ?_⟩
    rw [B.integral_muW38 lower upper c hlower hbound hupper r F]
    have hlim := (B.tendsto_hierNum38 lower upper c hlower hbound hupper r F).div
      (B.tendsto_hierZ38 lower upper c hlower hbound hupper) hZW.ne'
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with m hm
    exact (B.integral_hierMu38 lower c hlower hbound hm r F).symm

end BirkhoffTop38

end NlsGge.Birkhoff
end
