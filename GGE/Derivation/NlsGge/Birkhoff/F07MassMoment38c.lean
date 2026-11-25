import NlsGge.Birkhoff.F07MassMoment38b

/-! # F07 (v2 `C:lem:massmoment`), file c: statements

* `F07_momentineq38` (`C:eq:momentineq`, F07.01-.02, Phi-free): `Q_{2m-2}(u) ≥ Q_0(u)^m` on
  `H^{m-1}`.  `Q_{2j}` is `chargeSobolev38 m j`, the continuous extension to `H^{m-1}` of the local
  charge (identified with the spectral charge on smooth fields in `ChargeJensenSobolev38`).  Proof:
  `Q_{2m-2} ≥ Q_0^m` on Fourier planes (Jensen on the spectral measure, `planeMoment_mass38`), and
  density and continuity (`chargeMoment_mass_sobolev38`).
* `F07_tiltedIntegral38` (`C:eq:tiltedIntegral`, F07.06, conditional on `B`, `O` through F05):
  `∫ e^{-V_m + δ Q_{2m-2}} dγ^F = Z_m'/d_δ < ∞`.
* `F07_expMass38` (`C:eq:expMass`, F07.07): `∫ exp(-V_m + δ Q_0^m) dγ^F < ∞`, `0 < δ < β_{m-1}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.HierarchyRiccati.Core Filter Topology
open scoped ENNReal ContDiff

/-- **F07 part 1 (v2 `C:eq:momentineq`).**  `Q_{2m-2}(u) ≥ Q_0(u)^m` for `u ∈ H^{m-1}`, `m ≥ 2`,
with `Q_0(u) = Σ_n |û(n)|² = ‖u‖²_{L²}` and `Q_{2m-2}` the continuous extension to `H^{m-1}`. -/
theorem F07_momentineq38 (m : ℕ) (hm : 2 ≤ m) (u : Hm1 m) :
    (∑' n : ℤ, ‖(show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from u) n‖ ^ 2) ^ m ≤
      chargeSobolev38 m (m - 1) u := by
  rw [← chargeSobolev38_zero m u]
  exact chargeMoment_mass_sobolev38 m hm u

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-- `chargeSobolev38 m j` *is* the continuous extension to `H^{m-1}` of the spectral charge `Q_{2j}`
of smooth periodic fields: any continuous `G` on `H^{m-1}` that agrees with `spectralCharge38` at
every smooth field (linked to its Sobolev coefficients) equals it (`j ≤ m - 1`).  This is the
extension meant by v2 ("density and continuity of `Q_{2m-2}` on `H^{m-1}`"). -/
theorem chargeSobolev38_unique (m j : ℕ) (hm : 2 ≤ m) (hj : j ≤ m - 1) (G : Hm1 m → ℝ)
    (hG : Continuous G)
    (hGs : ∀ (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1) (x : Hm1 m),
      (∀ n : ℤ, (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from x) n =
        physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)) n) →
        G x = spectralCharge38 u hu hper j) :
    G = chargeSobolev38 m j := by
  funext x
  have h1 : Tendsto (fun N : ℕ => G (truncSobolev38 _ N x)) atTop (𝓝 (G x)) :=
    (hG.tendsto x).comp (tendsto_truncSobolev38 _ x)
  have h2 : Tendsto (fun N : ℕ => chargeSobolev38 m j (truncSobolev38 _ N x)) atTop
      (𝓝 (chargeSobolev38 m j x)) :=
    ((continuous_chargeSobolev38 m j hj).tendsto x).comp (tendsto_truncSobolev38 _ x)
  have heq : ∀ N : ℕ, G (truncSobolev38 _ N x) = chargeSobolev38 m j (truncSobolev38 _ N x) := by
    intro N
    rw [chargeSobolev38_smooth_spectral m j hm (by omega) (truncField38 _ N x)
      (contDiff_truncField38 _ N x) (periodic_truncField38 _ N x) _ (truncSobolev38_link _ N x)]
    exact hGs _ (contDiff_truncField38 _ N x) (periodic_truncField38 _ N x) _
      (truncSobolev38_link _ N x)
  exact tendsto_nhds_unique h1 (h2.congr fun N => (heq N).symm)

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
  {m : ℕ} {β : ℕ → ℝ} {δ : ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

include O hm hβ in
/-- **F07 (v2 `C:eq:tiltedIntegral`, F07.06).**  Conditional on `B`, `O` (through F05 for the
lowered coefficient vector `β' = lowerCoef38 m β δ`): for `0 ≤ δ < β_{m-1}`,
`e^{-V_m + δ Q_{2m-2}}` is `γ_m^F`-integrable and its integral is `Z_m'/d_δ`, where `Z_m' = Z_{m}(β')`
and `d_δ = ∏ a'_n/a_{m,n}`. -/
theorem F07_tiltedIntegral38 (hδ0 : 0 ≤ δ) (hδ : δ < β (m - 1)) :
    Integrable (fun u : Hm1 m =>
      Real.exp (-(Vm38 m β u) + δ * chargeSobolev38 m (m - 1) u)) (gammaFM38 m β) ∧
    ∫ u, Real.exp (-(Vm38 m β u) + δ * chargeSobolev38 m (m - 1) u) ∂(gammaFM38 m β) =
      ZM38 B m (lowerCoef38 m β δ) / dDelta38 m β δ := by
  obtain ⟨hd0, -⟩ := hasProd_dDelta38 hm hβ hδ0 hδ
  set d := dDelta38 m β δ with hd
  set β' := lowerCoef38 m β δ with hβ'def
  have hβ' : ∀ j ≤ m, 0 < β' j := lowerCoef_pos38 hβ hδ
  obtain ⟨-, hint', hI', hZ, -⟩ := F05_cor_identity38 B O hm hβ'
  set h : Hm1 m → ℝ := fun u => Real.exp (-(Vm38 m β u) + δ * chargeSobolev38 m (m - 1) u) with hh
  have hcont : Continuous h := by
    refine Real.continuous_exp.comp (((continuous_Vm38 hm hβ).neg).add
      (continuous_const.mul (continuous_chargeSobolev38 m (m - 1) le_rfl)))
  -- pointwise factorization `h u = e^{-V'(u)} e^{δ S(u)}`
  have hfac : ∀ u : Hm1 m, h u =
      Real.exp (-(Vm38 m β' u)) * Real.exp (δ * chargeQuad38 _ (m - 1) u) := by
    intro u
    rw [← Real.exp_add, hh]
    simp only
    rw [Vm_lower38 hm u]
    congr 1
    ring
  have hV'cont : Continuous (fun u : Hm1 m => Real.exp (-(Vm38 m β' u))) :=
    Real.continuous_exp.comp (continuous_Vm38 hm hβ').neg
  have hT := measurable_tiltDensityH38 m δ d
  have hlin : ∫⁻ u, ENNReal.ofReal (Real.exp (-(Vm38 m β' u))) ∂(gammaFM38 m β') =
      ENNReal.ofReal d * ∫⁻ u, ENNReal.ofReal (h u) ∂(gammaFM38 m β) := by
    rw [gammaFM38_tilt hm hβ hδ0 hδ,
      lintegral_withDensity_eq_lintegral_mul _ hT hV'cont.measurable.ennreal_ofReal,
      ← lintegral_const_mul _ hcont.measurable.ennreal_ofReal]
    refine lintegral_congr fun u => ?_
    simp only [Pi.mul_apply, tiltDensityH38, hfac u]
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    ring
  have hlhs : ∫⁻ u, ENNReal.ofReal (Real.exp (-(Vm38 m β' u))) ∂(gammaFM38 m β') =
      ENNReal.ofReal (ZM38 B m β') := by
    rw [← hI']
    exact (ofReal_integral_eq_lintegral_ofReal hint'
      (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le)).symm
  have hL : ∫⁻ u, ENNReal.ofReal (h u) ∂(gammaFM38 m β) = ENNReal.ofReal (ZM38 B m β' / d) := by
    rw [ENNReal.ofReal_div_of_pos hd0]
    rw [ENNReal.eq_div_iff (ENNReal.ofReal_pos.2 hd0).ne' ENNReal.ofReal_ne_top]
    rw [← hlin, hlhs]
  have hfin : Integrable h (gammaFM38 m β) := by
    refine ⟨hcont.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le), hL]
    exact ENNReal.ofReal_lt_top
  refine ⟨hfin, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le)
    hcont.aestronglyMeasurable, hL, ENNReal.toReal_ofReal (div_nonneg hZ.1.le hd0.le)]

include O hm hβ in
/-- **F07 (v2 `C:eq:expMass`, F07.07).**  For `0 < δ < β_{m-1}`,
`∫ exp[-V_m(u) + δ Q_0(u)^m] dγ_m^F(u) < ∞`; in fact the integral is at most `Z_m'/d_δ`. -/
theorem F07_expMass38 (hδ0 : 0 < δ) (hδ : δ < β (m - 1)) :
    Integrable (fun u : Hm1 m =>
      Real.exp (-(Vm38 m β u) + δ * (chargeSobolev38 m 0 u) ^ m)) (gammaFM38 m β) ∧
    ∫ u, Real.exp (-(Vm38 m β u) + δ * (chargeSobolev38 m 0 u) ^ m) ∂(gammaFM38 m β) ≤
      ZM38 B m (lowerCoef38 m β δ) / dDelta38 m β δ := by
  obtain ⟨hint, hI⟩ := F07_tiltedIntegral38 B O hm hβ hδ0.le hδ
  have hcont : Continuous (fun u : Hm1 m =>
      Real.exp (-(Vm38 m β u) + δ * (chargeSobolev38 m 0 u) ^ m)) :=
    Real.continuous_exp.comp (((continuous_Vm38 hm hβ).neg).add
      (continuous_const.mul ((continuous_chargeSobolev38 m 0 (Nat.zero_le _)).pow m)))
  have hle : ∀ u : Hm1 m, Real.exp (-(Vm38 m β u) + δ * (chargeSobolev38 m 0 u) ^ m) ≤
      Real.exp (-(Vm38 m β u) + δ * chargeSobolev38 m (m - 1) u) := fun u => by
    refine Real.exp_le_exp.2 ?_
    have := chargeMoment_mass_sobolev38 m hm u
    nlinarith
  refine ⟨hint.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_), ?_⟩
  · rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hle u
  · rw [← hI]
    exact integral_mono (hint.mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact hle u)) hint hle

end BirkhoffInput38

end NlsGge.Birkhoff

end
