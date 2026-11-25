import NlsGge.Birkhoff.S03Measure38d
import NlsGge.Measure.FiniteGaussian

/-! # S04 (v2 `A:thm:main`, l.428-456), sub-claims S04.01-S04.04: construction and convergence

Claim packet `blueprint/claims/S04.md`; layer design `campaign/BIRKHOFF_LAYER_DESIGN.md` §2, §4
(row S04), §5 (wave B1). Everything B-dependent is CONDITIONAL on `B : BirkhoffTop38` (E01 stays
open). S04.07-.08 (invariance under the NLS flow) are out of scope here.

## Conventions (v2 preserved)
* `γ_W = fullWeightSequenceGaussian c`, the countable product of proper complex Gaussians with
  density `(a_n/π) e^{-a_n|z|²}` (real-component variance `1/(2 a_n)`), `a_n = W(2πn)`, all
  integer coordinates (zero mode included); weights `0 < lower ≤ c_j ≤ upper`.
* The finite-gap measures live in `z`-coordinates on `ℂ^Λ` (`Λ : Finset ℤ`, `↥Λ → ℂ`) with the
  product Lebesgue measure `∏ d²z_n = finiteComplexVolume Λ`:
  `𝓔_W(u) = (2/π)∫ W(2λ) v(λ;u) dλ` (`energyW38`), `𝒵_Λ = ∫ e^{-𝓔_W(Φ⁻¹z)} ∏ d²z_n`
  (`ZcalΛ38`), `ν̂_Λ = 𝒵_Λ⁻¹ e^{-𝓔_W(Φ⁻¹z)} ∏ d²z_n` (`nuHat38`), `ν_Λ = (Φ⁻¹)_# ν̂_Λ`
  (`nu38`), `Z_Λ = 𝒵_Λ / ∏ (π/a_n)` (`ZΛ38`). `Φ⁻¹` is the cleaned inverse
  `B.cleanΦinv` (the actual inverse on `h⁰`, `0` elsewhere; the null/junk set is explicit).
* `H^m` (physical Sobolev space) is identified with the carrier `h^m = SobolevCarrier38 m` by the
  isometry `𝓕` (`physH38 m`, cleaned off `H^m`; `norm_physH38`, `physH38_sub`,
  `physH38_surjective_on`). Weak convergence on `H^m` means convergence of `∫ F(physH38 m u) dν`
  for every bounded continuous `F : h^m →ᵇ ℝ`.

## Sub-claim map (this file)
* S04.01-.03: `S04_01_03_38` (reuses `Rbar38`, `ZW38`, `muHatW38`, `muW38` of S03), plus the finite
  ensembles `isProbabilityMeasure_nuHat38`, `nuHat38_eq_relative`, `ZΛ38_pos_le_one`,
  `ZcalΛ38_pos_le` (v2 `A:eq:finitecanonical`, `A:eq:relativefinite`).
* S04.04: `weak_convergence_S04_38` (`A:eq:weakconvergence`), `integral_nu38` (the displayed ratio
  formula on the full product), `l1_density_convergence38` (L¹(γ_W) convergence of densities).
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.SpectralFoundations NlsGge.Weights
  NlsGge.Sobolev38 Filter Topology
open scoped ENNReal BoundedContinuousFunction

theorem continuous_fourierSeq38 : Continuous fourierSeq38 :=
  lp.uniformContinuous_coe.continuous.comp (reflectedFourierL2).continuous

theorem measurable_fourierSeq38 : Measurable fourierSeq38 :=
  continuous_fourierSeq38.measurable

/-- The physical `H^m` as the carrier `h^m` through the isometry `𝓕`; cleaned (value `0` off `H^m`). -/
def physH38 (m : ℕ) (u : PhysicalL2) : SobolevCarrier38 (m : ℝ) :=
  Function.extend (carrierCoe38 (m : ℝ)) id (fun _ => 0) (fourierSeq38 u)

theorem physH38_of_mem (m : ℕ) (u : PhysicalL2) (hu : fourierSeq38 u ∈ seqSobolev38 (m : ℝ)) :
    physH38 m u = carrierMk38 (m : ℝ) (fourierSeq38 u) hu :=
  (carrierCoe38_injective (m : ℝ)).extend_apply id (fun _ => 0) (carrierMk38 (m : ℝ) _ hu)

theorem physH38_of_not_mem (m : ℕ) (u : PhysicalL2) (hu : fourierSeq38 u ∉ seqSobolev38 (m : ℝ)) :
    physH38 m u = 0 := by
  refine Function.extend_apply' _ _ _ ?_
  rintro ⟨a, ha⟩
  exact hu (ha ▸ carrierCoe38_mem _ a)

theorem measurable_physH38 (m : ℕ) [MeasurableSpace (SobolevCarrier38 (m : ℝ))]
    [BorelSpace (SobolevCarrier38 (m : ℝ))] : Measurable (physH38 m) :=
  ((measurableEmbedding_carrierCoe38 (m : ℝ)).measurable_extend measurable_id
    measurable_const).comp measurable_fourierSeq38

theorem measurable_comp_physH38 (m : ℕ) (F : SobolevCarrier38 (m : ℝ) →ᵇ ℝ) :
    Measurable (fun u : PhysicalL2 => F (physH38 m u)) := by
  let _ : MeasurableSpace (SobolevCarrier38 (m : ℝ)) := borel _
  have : BorelSpace (SobolevCarrier38 (m : ℝ)) := ⟨rfl⟩
  exact F.continuous.measurable.comp (measurable_physH38 m)

/-- On physical `H^m`, `physH38 m` has the physical norm `‖u‖_{H^m}`. -/
theorem norm_physH38 (m : ℕ) (u : PhysicalL2) (hu : SobolevSquareSummable (m : ℝ) (physicalFourier u)) :
    ‖physH38 m u‖ = ‖physicalSobolevL2 (m : ℝ) u hu‖ := by
  rw [physH38_of_mem m u ((fourierSeq38_mem_iff _ u).2 hu), norm_physicalSobolevL2_eq_carrier38]

/-- `physH38 m` is additive on `H^m`, hence distances are physical `H^m` distances. -/
theorem physH38_sub (m : ℕ) (u v : PhysicalL2) (hu : fourierSeq38 u ∈ seqSobolev38 (m : ℝ))
    (hv : fourierSeq38 v ∈ seqSobolev38 (m : ℝ)) :
    physH38 m u - physH38 m v = physH38 m (u - v) := by
  have h : fourierSeq38 (u - v) ∈ seqSobolev38 (m : ℝ) := by
    rw [fourierSeq38_sub]; exact seqSobolev38_sub hu hv
  rw [physH38_of_mem m u hu, physH38_of_mem m v hv, physH38_of_mem m _ h]
  exact carrierExt38 (by simp [fourierSeq38_sub]; rfl)

theorem physH38_surjective_on (m : ℕ) (x : SobolevCarrier38 (m : ℝ)) :
    ∃ u : PhysicalL2, fourierSeq38 u ∈ seqSobolev38 (m : ℝ) ∧ physH38 m u = x := by
  have h0 : carrierCoe38 (m : ℝ) x ∈ seqSobolev38 0 :=
    seqSobolev38_natCast_mono (carrierCoe38_mem _ x)
  refine ⟨physInv38 _ h0, ?_, ?_⟩
  · rw [fourierSeq38_physInv38]; exact carrierCoe38_mem _ x
  · rw [physH38_of_mem m _ (by rw [fourierSeq38_physInv38]; exact carrierCoe38_mem _ x)]
    exact carrierExt38 (by simp [fourierSeq38_physInv38])


namespace BirkhoffTop38

variable (B : BirkhoffTop38)

/-- `Φ⁻¹` into the physical `H^m` (as `h^m` through `𝓕`) is the cleaned carrier inverse `T⁻¹`. -/
theorem physH38_cleanΦinv (m : ℕ) (z : ℤ → ℂ) : physH38 m (B.cleanΦinv z) = B.cleanTinvC m z := by
  by_cases hz : z ∈ seqSobolev38 (m : ℝ)
  · have hz0 : z ∈ seqSobolev38 0 := seqSobolev38_natCast_mono hz
    have hm : fourierSeq38 (B.cleanΦinv z) ∈ seqSobolev38 (m : ℝ) := by
      rw [B.fourierSeq38_cleanΦinv z hz0]; exact B.mapsTo_Tinv m z hz
    rw [physH38_of_mem m _ hm, B.cleanTinvC_of_mem m z hz]
    exact carrierExt38 (by simp [B.fourierSeq38_cleanΦinv z hz0]; rfl)
  · rw [B.cleanTinvC_of_not_mem m z hz]
    by_cases hz0 : z ∈ seqSobolev38 0
    · apply physH38_of_not_mem
      rw [B.fourierSeq38_cleanΦinv z hz0]
      intro h
      apply hz
      have := B.mapsTo_T m _ h
      rwa [B.right_inv z hz0] at this
    · rw [show B.cleanΦinv z = 0 by unfold cleanΦinv; simp only [hz0, ↓reduceDIte]]
      rw [physH38_of_mem m 0 (by rw [fourierSeq38_zero]; exact (weightedSubmodule _).zero_mem)]
      exact carrierExt38 (by simp [fourierSeq38_zero]; rfl)

end BirkhoffTop38


/-! ## Finite-gap ensembles `ν̂_Λ`, `ν_Λ` in `z`-coordinates (v2 `A:eq:finiteenergy`, `A:eq:finitecanonical`) -/

/-- `𝓔_W(u) = (2/π) ∫_ℝ W(2λ) v(λ;u) dλ` (v2 `A:eq:finiteenergy`). -/
def energyW38 (c : ℕ → ℝ) (u : PhysicalL2) : ℝ :=
  (2 / Real.pi) * ∫ l : ℝ, weight c (2 * l) * actualGapHeightE02_38 u l

/-- A point of `ℂ^Λ` as a sequence with `z_n = 0` off `Λ`. -/
def extZero38 (Λ : Finset ℤ) (w : Λ → ℂ) : ℤ → ℂ :=
  fun n => if h : n ∈ Λ then w ⟨n, h⟩ else 0

theorem extZero38_apply_of_mem {Λ : Finset ℤ} (w : Λ → ℂ) {n : ℤ} (hn : n ∈ Λ) :
    extZero38 Λ w n = w ⟨n, hn⟩ := by simp [extZero38, hn]

theorem extZero38_apply_of_not_mem {Λ : Finset ℤ} (w : Λ → ℂ) {n : ℤ} (hn : n ∉ Λ) :
    extZero38 Λ w n = 0 := by simp [extZero38, hn]

theorem measurable_extZero38 (Λ : Finset ℤ) : Measurable (extZero38 Λ) := by
  refine measurable_pi_iff.2 (fun n => ?_)
  by_cases hn : n ∈ Λ
  · simp only [extZero38, hn, ↓reduceDIte]
    exact measurable_pi_apply _
  · simp only [extZero38, hn, ↓reduceDIte]
    exact measurable_const

theorem projFin38_eq_extZero38 (Λ : Finset ℤ) (z : ℤ → ℂ) :
    projFin38 Λ z = extZero38 Λ (Λ.restrict z) := by
  funext n
  by_cases hn : n ∈ Λ
  · rw [projFin38_apply_of_mem hn, extZero38_apply_of_mem _ hn]; rfl
  · rw [projFin38_apply_of_not_mem hn, extZero38_apply_of_not_mem _ hn]

theorem projFin38_extZero38 (Λ : Finset ℤ) (w : Λ → ℂ) :
    projFin38 Λ (extZero38 Λ w) = extZero38 Λ w := by
  funext n
  by_cases hn : n ∈ Λ
  · rw [projFin38_apply_of_mem hn]
  · rw [projFin38_apply_of_not_mem hn, extZero38_apply_of_not_mem _ hn]

theorem measurable_projFin38 (Λ : Finset ℤ) : Measurable (projFin38 Λ) := by
  rw [show projFin38 Λ = fun z => extZero38 Λ (Λ.restrict z) from funext (projFin38_eq_extZero38 Λ)]
  exact (measurable_extZero38 Λ).comp (Finset.measurable_restrict Λ)

theorem projFin38_mem_Omega038 (c : ℕ → ℝ) (Λ : Finset ℤ) (z : ℤ → ℂ) :
    projFin38 Λ z ∈ Omega038 c := by
  refine ⟨fun m => ?_, ?_⟩
  · exact (mem_seqSobolev38_iff _ _).1
      (finiteSupport_mem_seqSobolev38 _ _ (finite_support_projFin38 Λ z))
  · refine summable_of_ne_finset_zero (s := Λ) (fun n hn => ?_)
    rw [projFin38_apply_of_not_mem hn]; simp

/-- For a field with finitely many open gaps the energy integrand `W(2λ) v(λ;u)` is integrable
(continuous with compact support in the union of the finitely many closed gaps). -/
theorem integrable_energyIntegrand38 (c : ℕ → ℝ) (hW : Continuous (weight c)) (u : PhysicalL2)
    (hfin : {n : ℤ | actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n}.Finite) :
    Integrable (fun l : ℝ => weight c (2 * l) * actualGapHeightE02_38 u l) := by
  have hc : Continuous (fun l : ℝ => weight c (2 * l) * actualGapHeightE02_38 u l) :=
    (hW.comp (continuous_const.mul continuous_id)).mul (continuous_actualGapHeightE02_38 u)
  set K : Set ℝ := ⋃ n ∈ hfin.toFinset, Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n)
    with hK
  have hKc : IsCompact K := (hfin.toFinset).isCompact_biUnion (fun n _ => isCompact_Icc)
  refine hc.integrable_of_hasCompactSupport (HasCompactSupport.intro hKc (fun x hx => ?_))
  by_contra hne
  have h0 : actualGapHeightE02_38 u x ≠ 0 := fun h => hne (by simp [h])
  obtain ⟨n, hn⟩ := actualGapHeight_mem_gap_of_ne_zero_E02_38 u x h0
  exact hx (Set.mem_biUnion (x := n) (by simpa using hn.1.trans hn.2) ⟨hn.1.le, hn.2.le⟩)

/-- The rate `a_n = W(2πn)` on the finite index type `Λ`. -/
def rateΛ38 (c : ℕ → ℝ) (Λ : Finset ℤ) (i : Λ) : ℝ := fullWeightRate c (i : ℤ)

/-- `γ_Λ = ∏_{n∈Λ} (a_n/π) e^{-a_n|z_n|²} d²z_n` (the finite product of complex Gaussians). -/
def gammaΛ38 (c : ℕ → ℝ) (Λ : Finset ℤ) : Measure (Λ → ℂ) :=
  finiteComplexGaussian (rateΛ38 c Λ)

theorem gammaΛ38_eq_map (c : ℕ → ℝ) (Λ : Finset ℤ) :
    (fullWeightSequenceGaussian c).map Λ.restrict = gammaΛ38 c Λ := by
  unfold fullWeightSequenceGaussian countableComplexGaussian gammaΛ38 finiteComplexGaussian
  rw [Measure.infinitePi_map_restrict]
  rfl


namespace BirkhoffTop38

variable (B : BirkhoffTop38)

/-- The finite-gap field `Φ⁻¹(z)`, `z_n = 0` off `Λ`, with `z ∈ ℂ^Λ`. -/
def finiteGapField38 (Λ : Finset ℤ) (w : Λ → ℂ) : PhysicalL2 := B.cleanΦinv (extZero38 Λ w)

theorem measurable_finiteGapField38 (Λ : Finset ℤ) : Measurable (B.finiteGapField38 Λ) :=
  B.measurable_cleanΦinv.comp (measurable_extZero38 Λ)

/-- **`𝓔_W = R_W + ∑_{n∈Λ} a_n |z_n|²`** on finite-gap fields (v2 `A:eq:rates`). -/
theorem energy_proj38 (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) (Λ : Finset ℤ) (z : ℤ → ℂ) :
    energyW38 c (B.cleanΦinv (projFin38 Λ z)) =
      B.Rbar38 c (projFin38 Λ z) + ∑ n ∈ Λ, fullWeightRate c n * ‖z n‖ ^ 2 := by
  rw [B.Rbar38_of_mem c (projFin38_mem_Omega038 c Λ z)]
  have h := (B.remainder38_finiteGap_proj lower upper c hlower hbound hupper Λ z).2.1
  unfold energyW38
  linarith

/-- The unnormalised finite-gap density `e^{-𝓔_W(Φ⁻¹ z)}` on `ℂ^Λ`. -/
def densΛ38 (c : ℕ → ℝ) (Λ : Finset ℤ) (w : Λ → ℂ) : ℝ :=
  Real.exp (-(energyW38 c (B.finiteGapField38 Λ w)))

/-- `𝒵_Λ = ∫ e^{-𝓔_W(Φ⁻¹ z)} ∏ d²z_n` (v2 `A:eq:finitecanonical`). -/
def ZcalΛ38 (c : ℕ → ℝ) (Λ : Finset ℤ) : ℝ :=
  ∫ w, B.densΛ38 c Λ w ∂(finiteComplexVolume Λ)

/-- `Z_Λ = 𝒵_Λ / ∏_{n∈Λ} (π/a_n)` (v2 `A:eq:relativefinite`). -/
def ZΛ38 (c : ℕ → ℝ) (Λ : Finset ℤ) : ℝ :=
  B.ZcalΛ38 c Λ / ∏ i : Λ, (Real.pi / rateΛ38 c Λ i)

/-- `ν̂_Λ = 𝒵_Λ⁻¹ e^{-𝓔_W(Φ⁻¹ z)} ∏ d²z_n` (v2 `A:eq:finitecanonical`), on `ℂ^Λ`. -/
def nuHat38 (c : ℕ → ℝ) (Λ : Finset ℤ) : Measure (Λ → ℂ) :=
  (finiteComplexVolume Λ).withDensity
    (fun w => ENNReal.ofReal (B.densΛ38 c Λ w / B.ZcalΛ38 c Λ))

/-- `ν_Λ = (Φ⁻¹)_# ν̂_Λ`, the finite-gap ensemble on fields. -/
def nu38 (c : ℕ → ℝ) (Λ : Finset ℤ) : Measure PhysicalL2 :=
  (B.nuHat38 c Λ).map (B.finiteGapField38 Λ)

/-- The Gaussian density `∏ (a_n/π) e^{-a_n |z_n|²}`. -/
def gaussDensΛ38 (c : ℕ → ℝ) (Λ : Finset ℤ) (w : Λ → ℂ) : ℝ :=
  ∏ i : Λ, (rateΛ38 c Λ i / Real.pi) * Real.exp (-(rateΛ38 c Λ i) * ‖w i‖ ^ 2)

theorem Rbar38_extZero38_proj (c : ℕ → ℝ) (Λ : Finset ℤ) (w : Λ → ℂ) :
    B.Rbar38 c (projFin38 Λ (extZero38 Λ w)) = B.Rbar38 c (extZero38 Λ w) := by
  rw [projFin38_extZero38]

theorem densΛ38_eq (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) (Λ : Finset ℤ) (w : Λ → ℂ) :
    B.densΛ38 c Λ w = (∏ i : Λ, Real.pi / rateΛ38 c Λ i) *
      (gaussDensΛ38 c Λ w * Real.exp (-(B.Rbar38 c (extZero38 Λ w)))) := by
  have hq : ∀ i : Λ, 0 < rateΛ38 c Λ i := fun i => fullWeightRate_pos lower upper c hlower hbound hupper _
  have h1 := B.energy_proj38 lower upper c hlower hbound hupper Λ (extZero38 Λ w)
  rw [projFin38_extZero38] at h1
  have hS : ∑ n ∈ Λ, fullWeightRate c n * ‖extZero38 Λ w n‖ ^ 2 =
      ∑ i : Λ, rateΛ38 c Λ i * ‖w i‖ ^ 2 := by
    rw [← Finset.sum_coe_sort Λ]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [extZero38_apply_of_mem w i.2]
    rfl
  unfold densΛ38 finiteGapField38
  rw [h1, hS, neg_add, Real.exp_add, gaussDensΛ38]
  have e2 : Real.exp (-∑ i : Λ, rateΛ38 c Λ i * ‖w i‖ ^ 2) =
      ∏ i : Λ, Real.exp (-(rateΛ38 c Λ i) * ‖w i‖ ^ 2) := by
    rw [← Real.exp_sum, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have e3 : (∏ i : Λ, Real.pi / rateΛ38 c Λ i) * ∏ i : Λ, (rateΛ38 c Λ i / Real.pi) *
      Real.exp (-(rateΛ38 c Λ i) * ‖w i‖ ^ 2) = ∏ i : Λ, Real.exp (-(rateΛ38 c Λ i) * ‖w i‖ ^ 2) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have := (hq i).ne'
    field_simp
  rw [e2, mul_comm (Real.exp (-B.Rbar38 c (extZero38 Λ w))), ← mul_assoc, e3]


/-! ### Gibbs-density integrals for a probability reference measure -/

theorem integral_withDensity_exp_neg38 {α : Type*} [MeasurableSpace α] (γ : Measure α)
    (R : α → ℝ) (hR : Measurable R) (Z : ℝ) (hZ : 0 < Z) (f : α → ℝ) :
    ∫ x, f x ∂(γ.withDensity (fun x => ENNReal.ofReal (Real.exp (-(R x)) / Z))) =
      (∫ x, Real.exp (-(R x)) * f x ∂γ) / Z := by
  have hm : Measurable (fun x => ENNReal.ofReal (Real.exp (-(R x)) / Z)) :=
    ((Real.measurable_exp.comp hR.neg).div_const Z).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hm (Filter.Eventually.of_forall
    (fun _ => ENNReal.ofReal_lt_top))]
  rw [← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hZ.le)]
  ring


end BirkhoffTop38

theorem tendsto_integral_abs_sub38 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (fN : ℕ → α → ℝ) (f : α → ℝ) (K : ℝ)
    (hmeas : ∀ N, Measurable (fN N)) (hf : Measurable f)
    (hb : ∀ᶠ N in atTop, ∀ x, |fN N x| ≤ K) (hbf : ∀ x, |f x| ≤ K)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun N => fN N x) atTop (𝓝 (f x))) :
    Tendsto (fun N : ℕ => ∫ x, |fN N x - f x| ∂μ) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
    (F := fun N x => |fN N x - f x|) (f := fun _ => (0 : ℝ)) (fun _ => 2 * K)
    (Filter.Eventually.of_forall (fun N => ((hmeas N).sub hf).abs.aestronglyMeasurable))
    (hb.mono (fun N hN => Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_abs]
      calc |fN N x - f x| ≤ |fN N x| + |f x| := abs_sub _ _
        _ ≤ K + K := add_le_add (hN x) (hbf x)
        _ = 2 * K := by ring)))
    (integrable_const _)
    (hlim.mono (fun x hx => by
      have := (hx.sub_const (f x)).abs
      simpa using this))
  simpa using h

theorem exp_neg_integral_pos_le_one38 {α : Type*} [MeasurableSpace α] (γ : Measure α)
    [IsProbabilityMeasure γ] (R : α → ℝ) (hR : Measurable R) (h0 : ∀ x, 0 ≤ R x) :
    0 < ∫ x, Real.exp (-(R x)) ∂γ ∧ ∫ x, Real.exp (-(R x)) ∂γ ≤ 1 := by
  have hle : ∀ x, Real.exp (-(R x)) ≤ 1 := fun x => by
    rw [Real.exp_le_one_iff]; linarith [h0 x]
  have hi : Integrable (fun x => Real.exp (-(R x))) γ :=
    Integrable.of_bound (Real.measurable_exp.comp hR.neg).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hle x)
  refine ⟨?_, ?_⟩
  · rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) hi]
    have : Function.support (fun x => Real.exp (-(R x))) = Set.univ :=
      Set.eq_univ_of_forall fun x => (Real.exp_pos _).ne'
    rw [this]; simp
  · calc ∫ x, Real.exp (-(R x)) ∂γ ≤ ∫ _x, (1 : ℝ) ∂γ :=
          integral_mono hi (integrable_const _) hle
      _ = 1 := by simp

theorem isProbabilityMeasure_withDensity_exp_neg38 {α : Type*} [MeasurableSpace α]
    (γ : Measure α) [IsProbabilityMeasure γ] (R : α → ℝ) (hR : Measurable R)
    (h0 : ∀ x, 0 ≤ R x) :
    IsProbabilityMeasure (γ.withDensity
      (fun x => ENNReal.ofReal (Real.exp (-(R x)) / ∫ y, Real.exp (-(R y)) ∂γ))) := by
  obtain ⟨hZ, hZ1⟩ := exp_neg_integral_pos_le_one38 γ R hR h0
  have hi : Integrable (fun x => Real.exp (-(R x))) γ :=
    Integrable.of_bound (Real.measurable_exp.comp hR.neg).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]; linarith [h0 x])
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _)
      (Filter.Eventually.of_forall fun x => div_nonneg (Real.exp_pos _).le hZ.le),
    integral_div]
  rw [div_self hZ.ne']; simp

namespace BirkhoffTop38

variable (B : BirkhoffTop38)

/-- Pathwise convergence of `T⁻¹(P_{Λ_N} z) → T⁻¹ z` in `h^m` for `z ∈ Ω₀`. -/
theorem tendsto_cleanTinvC_proj38 (m : ℕ) {z : ℤ → ℂ} (c : ℕ → ℝ) (hz : z ∈ Omega038 c) {Λ : ℕ → Finset ℤ}
    (hΛ : IsExhaustion38 Λ) :
    Tendsto (fun N : ℕ => B.cleanTinvC m (projFin38 (Λ N) z)) atTop (𝓝 (B.cleanTinvC m z)) := by
  have hzm : z ∈ seqSobolev38 (m : ℝ) := mem_seqSobolev38_of_Omega038 c hz m
  have hP : ∀ N : ℕ, projFin38 (Λ N) z ∈ seqSobolev38 (m : ℝ) := fun N =>
    finiteSupport_mem_seqSobolev38 _ _ (finite_support_projFin38 (Λ N) z)
  rw [B.cleanTinvC_of_mem m z hzm]
  refine ((B.continuous_TinvC m).tendsto _).comp (tendsto_carrier_proj38 (m : ℝ) z hzm hΛ) |>.congr
    (fun N => ?_)
  rw [B.cleanTinvC_of_mem m _ (hP N)]
  rfl

theorem finiteGapStructure_fin38 (Λ : Finset ℤ) (z : ℤ → ℂ) :
    {n : ℤ | actualGapLowerAllE02_38 (B.cleanΦinv (projFin38 Λ z)) n <
      actualGapUpperAllE02_38 (B.cleanΦinv (projFin38 Λ z)) n}.Finite :=
  (B.finiteGap_structure38 Λ z).2.1

section Finite

variable (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
  (hupper : ∀ j : ℕ, c j ≤ upper)

include hlower hbound hupper

theorem measurable_Rext38 (Λ : Finset ℤ) :
    Measurable (fun w : Λ → ℂ => B.Rbar38 c (extZero38 Λ w)) :=
  (B.measurable_Rbar38 lower upper c hlower hbound hupper).comp (measurable_extZero38 Λ)

theorem gaussDensΛ38_nonneg (Λ : Finset ℤ) (w : Λ → ℂ) : 0 ≤ gaussDensΛ38 c Λ w :=
  Finset.prod_nonneg (fun i _ => normalizedGaussianKernel_nonneg _
    (fullWeightRate_pos lower upper c hlower hbound hupper _) (w i))

theorem gammaΛ38_density (Λ : Finset ℤ) :
    gammaΛ38 c Λ = (finiteComplexVolume Λ).withDensity
      (fun w => ENNReal.ofReal (gaussDensΛ38 c Λ w)) :=
  finiteComplexGaussian_density (rateΛ38 c Λ)
    (fun _ => fullWeightRate_pos lower upper c hlower hbound hupper _)

theorem integral_gammaΛ38 (Λ : Finset ℤ) (f : (Λ → ℂ) → ℝ) :
    ∫ w, f w ∂(gammaΛ38 c Λ) = ∫ w, gaussDensΛ38 c Λ w * f w ∂(finiteComplexVolume Λ) := by
  have hm : Measurable (fun w : Λ → ℂ => ENNReal.ofReal (gaussDensΛ38 c Λ w)) :=
    (measurable_finiteGaussianPDF (rateΛ38 c Λ)).ennreal_ofReal
  rw [gammaΛ38_density lower upper c hlower hbound hupper Λ,
    integral_withDensity_eq_integral_toReal_smul hm (Filter.Eventually.of_forall
        (fun _ => ENNReal.ofReal_lt_top))]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (gaussDensΛ38_nonneg lower upper c hlower hbound hupper Λ w)]

theorem ZcalΛ38_eq (Λ : Finset ℤ) :
    B.ZcalΛ38 c Λ = (∏ i : Λ, Real.pi / rateΛ38 c Λ i) *
      ∫ w, Real.exp (-(B.Rbar38 c (extZero38 Λ w))) ∂(gammaΛ38 c Λ) := by
  rw [integral_gammaΛ38 lower upper c hlower hbound hupper, ← integral_const_mul]
  unfold ZcalΛ38
  refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
  simp only
  rw [B.densΛ38_eq lower upper c hlower hbound hupper Λ w]

theorem prod_pi_div_rate_pos (Λ : Finset ℤ) : 0 < ∏ i : Λ, Real.pi / rateΛ38 c Λ i :=
  Finset.prod_pos (fun _ _ => div_pos Real.pi_pos
    (fullWeightRate_pos lower upper c hlower hbound hupper _))

theorem ZΛ38_eq_integral (Λ : Finset ℤ) :
    B.ZΛ38 c Λ = ∫ w, Real.exp (-(B.Rbar38 c (extZero38 Λ w))) ∂(gammaΛ38 c Λ) := by
  unfold ZΛ38
  rw [B.ZcalΛ38_eq lower upper c hlower hbound hupper Λ]
  have := (prod_pi_div_rate_pos lower upper c hlower hbound hupper Λ).ne'
  field_simp

theorem ZΛ38_eq_integral_global (Λ : Finset ℤ) :
    B.ZΛ38 c Λ = ∫ z, Real.exp (-(B.Rbar38 c (projFin38 Λ z))) ∂(fullWeightSequenceGaussian c) := by
  rw [B.ZΛ38_eq_integral lower upper c hlower hbound hupper Λ, ← gammaΛ38_eq_map,
    integral_map (Finset.measurable_restrict Λ).aemeasurable
      (Real.measurable_exp.comp (B.measurable_Rext38 lower upper c hlower hbound hupper Λ).neg
        ).aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  simp only [projFin38_eq_extZero38]


instance (Λ : Finset ℤ) : IsProbabilityMeasure (gammaΛ38 c Λ) := by
  unfold gammaΛ38; infer_instance

theorem Rext_nonneg38 (Λ : Finset ℤ) (w : Λ → ℂ) : 0 ≤ B.Rbar38 c (extZero38 Λ w) :=
  B.Rbar38_nonneg lower upper c hlower hbound hupper _

/-- **`0 < Z_Λ ≤ 1`** (v2 `A:eq:relativefinite`). -/
theorem ZΛ38_pos_le_one (Λ : Finset ℤ) : 0 < B.ZΛ38 c Λ ∧ B.ZΛ38 c Λ ≤ 1 := by
  rw [B.ZΛ38_eq_integral lower upper c hlower hbound hupper Λ]
  exact exp_neg_integral_pos_le_one38 _ _ (B.measurable_Rext38 lower upper c hlower hbound hupper Λ)
    (B.Rext_nonneg38 lower upper c hlower hbound hupper Λ)

/-- **`0 < 𝒵_Λ ≤ ∏_{n∈Λ} π/a_n < ∞`** (v2 `A:eq:finitecanonical`). -/
theorem ZcalΛ38_pos_le (Λ : Finset ℤ) :
    0 < B.ZcalΛ38 c Λ ∧ B.ZcalΛ38 c Λ ≤ ∏ i : Λ, Real.pi / rateΛ38 c Λ i := by
  have hK := prod_pi_div_rate_pos lower upper c hlower hbound hupper Λ
  obtain ⟨h1, h2⟩ := B.ZΛ38_pos_le_one lower upper c hlower hbound hupper Λ
  have e : B.ZcalΛ38 c Λ = B.ZΛ38 c Λ * ∏ i : Λ, Real.pi / rateΛ38 c Λ i := by
    unfold ZΛ38; field_simp
  rw [e]
  exact ⟨mul_pos h1 hK, by nlinarith⟩

/-- **Relative form** (v2 `A:eq:relativefinite`): `ν̂_Λ = Z_Λ⁻¹ e^{-R_W(Φ⁻¹ z)} γ_Λ`. -/
theorem nuHat38_eq_relative (Λ : Finset ℤ) :
    B.nuHat38 c Λ = (gammaΛ38 c Λ).withDensity
      (fun w => ENNReal.ofReal (Real.exp (-(B.Rbar38 c (extZero38 Λ w))) / B.ZΛ38 c Λ)) := by
  obtain ⟨hZ, -⟩ := B.ZΛ38_pos_le_one lower upper c hlower hbound hupper Λ
  have hK := prod_pi_div_rate_pos lower upper c hlower hbound hupper Λ
  have hm1 : Measurable (fun w : Λ → ℂ => ENNReal.ofReal (gaussDensΛ38 c Λ w)) :=
    (measurable_finiteGaussianPDF (rateΛ38 c Λ)).ennreal_ofReal
  have hm2 : Measurable (fun w : Λ → ℂ =>
      ENNReal.ofReal (Real.exp (-(B.Rbar38 c (extZero38 Λ w))) / B.ZΛ38 c Λ)) :=
    ((Real.measurable_exp.comp (B.measurable_Rext38 lower upper c hlower hbound hupper Λ).neg
      ).div_const _).ennreal_ofReal
  rw [gammaΛ38_density lower upper c hlower hbound hupper Λ, ← withDensity_mul _ hm1 hm2]
  unfold nuHat38
  congr 1
  funext w
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (gaussDensΛ38_nonneg lower upper c hlower hbound hupper Λ w)]
  congr 1
  have hZc : B.ZcalΛ38 c Λ = B.ZΛ38 c Λ * ∏ i : Λ, Real.pi / rateΛ38 c Λ i := by
    unfold ZΛ38; field_simp
  rw [B.densΛ38_eq lower upper c hlower hbound hupper Λ w, hZc]
  field_simp

/-- `ν̂_Λ` is a probability measure (v2 `A:eq:finitecanonical`: "well-defined probability"). -/
theorem isProbabilityMeasure_nuHat38 (Λ : Finset ℤ) : IsProbabilityMeasure (B.nuHat38 c Λ) := by
  rw [B.nuHat38_eq_relative lower upper c hlower hbound hupper Λ]
  have := isProbabilityMeasure_withDensity_exp_neg38 (gammaΛ38 c Λ) _
    (B.measurable_Rext38 lower upper c hlower hbound hupper Λ)
    (B.Rext_nonneg38 lower upper c hlower hbound hupper Λ)
  rwa [← B.ZΛ38_eq_integral lower upper c hlower hbound hupper Λ] at this

theorem isProbabilityMeasure_nu38 (Λ : Finset ℤ) : IsProbabilityMeasure (B.nu38 c Λ) := by
  have := B.isProbabilityMeasure_nuHat38 lower upper c hlower hbound hupper Λ
  unfold nu38
  exact (Measure.isProbabilityMeasure_map_iff (B.measurable_finiteGapField38 Λ).aemeasurable).2 this

/-- **Integral identity on the full product** (v2 displayed formula before `A:eq:weakconvergence`):
for measurable `g`, `∫ g dν_Λ = ∫ g(Φ⁻¹ P_Λ z) e^{-R_W(Φ⁻¹ P_Λ z)} dγ_W / ∫ e^{-R_W(Φ⁻¹ P_Λ z)} dγ_W`. -/
theorem integral_nu38 (Λ : Finset ℤ) (g : PhysicalL2 → ℝ) (hg : Measurable g) :
    ∫ u, g u ∂(B.nu38 c Λ) =
      (∫ z, g (B.cleanΦinv (projFin38 Λ z)) * Real.exp (-(B.Rbar38 c (projFin38 Λ z)))
        ∂(fullWeightSequenceGaussian c)) /
      ∫ z, Real.exp (-(B.Rbar38 c (projFin38 Λ z))) ∂(fullWeightSequenceGaussian c) := by
  obtain ⟨hZ, -⟩ := B.ZΛ38_pos_le_one lower upper c hlower hbound hupper Λ
  rw [← B.ZΛ38_eq_integral_global lower upper c hlower hbound hupper Λ]
  unfold nu38
  rw [integral_map (B.measurable_finiteGapField38 Λ).aemeasurable hg.aestronglyMeasurable,
    B.nuHat38_eq_relative lower upper c hlower hbound hupper Λ,
    integral_withDensity_exp_neg38 _ _ (B.measurable_Rext38 lower upper c hlower hbound hupper Λ) _ hZ,
    ← gammaΛ38_eq_map,
    integral_map (Finset.measurable_restrict Λ).aemeasurable]
  · congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [finiteGapField38, projFin38_eq_extZero38]
    ring
  · exact (((Real.measurable_exp.comp (B.measurable_Rext38 lower upper c hlower hbound hupper Λ).neg).mul
      (hg.comp (B.measurable_finiteGapField38 Λ)))).aestronglyMeasurable


/-! ### Pathwise limits along an exhaustion -/

theorem tendsto_Rbar_proj38 {z : ℤ → ℂ} (hz : z ∈ Omega038 c) {Λ : ℕ → Finset ℤ}
    (hΛ : IsExhaustion38 Λ) :
    Tendsto (fun N : ℕ => B.Rbar38 c (projFin38 (Λ N) z)) atTop (𝓝 (B.Rbar38 c z)) := by
  have h := (B.remainder_tendsto_pathwise38 lower upper c hlower hbound hupper z hz hΛ).2.2.1
  rw [B.Rbar38_of_mem c hz]
  refine h.congr (fun N => ?_)
  rw [B.Rbar38_of_mem c (projFin38_mem_Omega038 c (Λ N) z)]


theorem tendsto_numerator38 (m : ℕ) (F : SobolevCarrier38 (m : ℝ) →ᵇ ℝ) {Λ : ℕ → Finset ℤ}
    (hΛ : IsExhaustion38 Λ) :
    Tendsto (fun N : ℕ => ∫ z, F (B.cleanTinvC m (projFin38 (Λ N) z)) *
        Real.exp (-(B.Rbar38 c (projFin38 (Λ N) z))) ∂(fullWeightSequenceGaussian c)) atTop
      (𝓝 (∫ z, F (B.cleanTinvC m z) * Real.exp (-(B.Rbar38 c z)) ∂(fullWeightSequenceGaussian c))) := by
  let _ : MeasurableSpace (SobolevCarrier38 (m : ℝ)) := borel _
  have : BorelSpace (SobolevCarrier38 (m : ℝ)) := ⟨rfl⟩
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖F‖) (fun N => ?_) (integrable_const _)
    (fun N => Filter.Eventually.of_forall (fun z => ?_)) ?_
  · exact ((F.continuous.measurable.comp ((B.measurable_cleanTinvC m).comp (measurable_projFin38 (Λ N)))).mul
      (Real.measurable_exp.comp ((B.measurable_Rbar38 lower upper c hlower hbound hupper).comp
        (measurable_projFin38 (Λ N))).neg)).aestronglyMeasurable
  · rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
    calc ‖F (B.cleanTinvC m (projFin38 (Λ N) z))‖ * Real.exp (-(B.Rbar38 c (projFin38 (Λ N) z)))
        ≤ ‖F‖ * 1 := mul_le_mul (F.norm_coe_le_norm _)
          (B.exp_neg_Rbar38_le_one lower upper c hlower hbound hupper _) (Real.exp_pos _).le
          (norm_nonneg _)
      _ = ‖F‖ := mul_one _
  · filter_upwards [ae_mem_Omega038 lower upper c hlower hbound hupper] with z hz
    exact ((F.continuous.tendsto _).comp (B.tendsto_cleanTinvC_proj38 m c hz hΛ)).mul
      ((Real.continuous_exp.tendsto _).comp
        (B.tendsto_Rbar_proj38 lower upper c hlower hbound hupper hz hΛ).neg)

theorem tendsto_denominator38 {Λ : ℕ → Finset ℤ} (hΛ : IsExhaustion38 Λ) :
    Tendsto (fun N : ℕ => B.ZΛ38 c (Λ N)) atTop (𝓝 (B.ZW38 c)) := by
  have h := B.tendsto_numerator38 lower upper c hlower hbound hupper 0
    (BoundedContinuousFunction.const (SobolevCarrier38 ((0 : ℕ) : ℝ)) 1) hΛ
  simp only [BoundedContinuousFunction.const_apply, one_mul] at h
  unfold ZW38
  refine h.congr (fun N => ?_)
  rw [B.ZΛ38_eq_integral_global lower upper c hlower hbound hupper]


/-- `∫ F dμ_W` in `γ_W`-coordinates (v2 `A:eq:limitmeasure`). -/
theorem integral_muW38 (m : ℕ) (F : SobolevCarrier38 (m : ℝ) →ᵇ ℝ) :
    ∫ u, F (physH38 m u) ∂(B.muW38 c) =
      (∫ z, F (B.cleanTinvC m z) * Real.exp (-(B.Rbar38 c z)) ∂(fullWeightSequenceGaussian c)) /
        B.ZW38 c := by
  obtain ⟨hZ, -⟩ := B.ZW38_pos_le_one lower upper c hlower hbound hupper
  unfold muW38
  rw [integral_map B.measurable_cleanΦinv.aemeasurable (measurable_comp_physH38 m F).aestronglyMeasurable]
  unfold muHatW38
  rw [integral_withDensity_exp_neg38 _ _ (B.measurable_Rbar38 lower upper c hlower hbound hupper) _ hZ]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  simp only [physH38_cleanΦinv]
  ring

/-- `∫ F dν_Λ` in `γ_W`-coordinates, for the finite-gap law. -/
theorem integral_nu38_physH38 (m : ℕ) (F : SobolevCarrier38 (m : ℝ) →ᵇ ℝ) (Λ : Finset ℤ) :
    ∫ u, F (physH38 m u) ∂(B.nu38 c Λ) =
      (∫ z, F (B.cleanTinvC m (projFin38 Λ z)) * Real.exp (-(B.Rbar38 c (projFin38 Λ z)))
        ∂(fullWeightSequenceGaussian c)) / B.ZΛ38 c Λ := by
  rw [B.integral_nu38 lower upper c hlower hbound hupper Λ _ (measurable_comp_physH38 m F),
    ← B.ZΛ38_eq_integral_global lower upper c hlower hbound hupper Λ]
  simp only [physH38_cleanΦinv]

/-- **S04.04 / v2 `A:eq:weakconvergence`.** For every increasing exhaustion `Λ_N ↑ ℤ`,
`Z_{Λ_N} → Z_W > 0` and `ν_{Λ_N} ⇀ μ_W` on `H^m` for every `m ≥ 0`: for every bounded continuous
`F` on `H^m` (the physical `H^m`, identified with `h^m` by the isometry `𝓕`, see `physH38`),
`∫ F dν_{Λ_N} → ∫ F dμ_W`. -/
theorem weak_convergence_S04_38 {Λ : ℕ → Finset ℤ} (hΛ : IsExhaustion38 Λ) :
    (Tendsto (fun N : ℕ => B.ZΛ38 c (Λ N)) atTop (𝓝 (B.ZW38 c)) ∧ 0 < B.ZW38 c) ∧
    ∀ (m : ℕ) (F : SobolevCarrier38 (m : ℝ) →ᵇ ℝ),
      Tendsto (fun N : ℕ => ∫ u, F (physH38 m u) ∂(B.nu38 c (Λ N))) atTop
        (𝓝 (∫ u, F (physH38 m u) ∂(B.muW38 c))) := by
  obtain ⟨hZ, -⟩ := B.ZW38_pos_le_one lower upper c hlower hbound hupper
  refine ⟨⟨B.tendsto_denominator38 lower upper c hlower hbound hupper hΛ, hZ⟩, fun m F => ?_⟩
  rw [B.integral_muW38 lower upper c hlower hbound hupper m F]
  simp_rw [B.integral_nu38_physH38 lower upper c hlower hbound hupper m F]
  exact (B.tendsto_numerator38 lower upper c hlower hbound hupper m F hΛ).div
    (B.tendsto_denominator38 lower upper c hlower hbound hupper hΛ) hZ.ne'


/-- **L¹ convergence of the reweighted full-product densities** (v2, after
`A:eq:weakconvergence`): `e^{-R(Φ⁻¹P_{Λ_N}z)}/Z_{Λ_N} → e^{-R(Φ⁻¹z)}/Z_W` in `L¹(γ_W)`.
(This is not total-variation convergence of the field laws; v2 notes they are mutually singular.) -/
theorem l1_density_convergence38 {Λ : ℕ → Finset ℤ} (hΛ : IsExhaustion38 Λ) :
    Tendsto (fun N : ℕ => ∫ z, |Real.exp (-(B.Rbar38 c (projFin38 (Λ N) z))) / B.ZΛ38 c (Λ N) -
        Real.exp (-(B.Rbar38 c z)) / B.ZW38 c| ∂(fullWeightSequenceGaussian c)) atTop (𝓝 0) := by
  obtain ⟨hZ, hZ1⟩ := B.ZW38_pos_le_one lower upper c hlower hbound hupper
  have hden := B.tendsto_denominator38 lower upper c hlower hbound hupper hΛ
  have hev : ∀ᶠ N in atTop, B.ZW38 c / 2 ≤ B.ZΛ38 c (Λ N) :=
    hden.eventually (Ici_mem_nhds (by linarith : B.ZW38 c / 2 < B.ZW38 c))
  refine tendsto_integral_abs_sub38 _ _ _ (2 / B.ZW38 c) (fun N => ?_) ?_ ?_ (fun z => ?_) ?_
  · exact ((Real.measurable_exp.comp ((B.measurable_Rbar38 lower upper c hlower hbound hupper).comp
      (measurable_projFin38 (Λ N))).neg).div_const _)
  · exact (Real.measurable_exp.comp (B.measurable_Rbar38 lower upper c hlower hbound hupper).neg).div_const _
  · filter_upwards [hev] with N hN z
    obtain ⟨hZN, -⟩ := B.ZΛ38_pos_le_one lower upper c hlower hbound hupper (Λ N)
    rw [abs_of_nonneg (div_nonneg (Real.exp_pos _).le hZN.le), div_le_div_iff₀ hZN hZ]
    calc Real.exp (-(B.Rbar38 c (projFin38 (Λ N) z))) * B.ZW38 c ≤ 1 * B.ZW38 c :=
          mul_le_mul_of_nonneg_right (B.exp_neg_Rbar38_le_one lower upper c hlower hbound hupper _) hZ.le
      _ ≤ 2 * B.ZΛ38 c (Λ N) := by linarith
  · rw [abs_of_nonneg (div_nonneg (Real.exp_pos _).le hZ.le), div_le_div_iff₀ hZ hZ]
    calc Real.exp (-(B.Rbar38 c z)) * B.ZW38 c ≤ 1 * B.ZW38 c :=
          mul_le_mul_of_nonneg_right (B.exp_neg_Rbar38_le_one lower upper c hlower hbound hupper _) hZ.le
      _ ≤ 2 * B.ZW38 c := by linarith
  · filter_upwards [ae_mem_Omega038 lower upper c hlower hbound hupper] with z hz
    exact (((Real.continuous_exp.tendsto _).comp
      (B.tendsto_Rbar_proj38 lower upper c hlower hbound hupper hz hΛ).neg)).div hden hZ.ne'


/-- `𝓔_W(Φ⁻¹ P_Λ z)` is a genuine (integrable) integral: the energy integrand is integrable. -/
theorem integrable_energy_proj38 (Λ : Finset ℤ) (z : ℤ → ℂ) :
    Integrable (fun l : ℝ => weight c (2 * l) *
      actualGapHeightE02_38 (B.cleanΦinv (projFin38 Λ z)) l) :=
  integrable_energyIntegrand38 c (weight_continuous38 hlower hbound hupper) _
    (B.finiteGapStructure_fin38 Λ z)

/-- **S04.01-S04.03 (v2 `A:eq:limitmeasure` and l.406-411).**
S04.01: `R̄_W` is a measurable (everywhere defined) version of `z ↦ R_W(Φ⁻¹ z)`, equal to the
series of `A:eq:remainder` on the measurable probability-one set `Ω₀` and to `0` (an arbitrary
value) on the `γ_W`-null set `Ω₀ᶜ`; it is nonnegative.
S04.02: `0 < e^{-R̄_W} ≤ 1` and `0 < Z_W ≤ 1`.
S04.03: `μ̂_W = Z_W⁻¹ e^{-R̄_W} γ_W` is a probability measure, `μ_W = (Φ⁻¹)_# μ̂_W` is a probability
measure on `PhysicalL2`, `Φ⁻¹` is the actual inverse `μ̂_W`-a.e. -/
theorem S04_01_03_38 :
    (Measurable (B.Rbar38 c) ∧ MeasurableSet (Omega038 c) ∧
      fullWeightSequenceGaussian c (Omega038 c)ᶜ = 0 ∧
      (∀ z ∈ Omega038 c, Summable (fun n : ℤ => remainderSummand38 c (B.cleanΦinv z) n) ∧
        B.Rbar38 c z = remainder38 c (B.cleanΦinv z)) ∧
      (∀ z ∉ Omega038 c, B.Rbar38 c z = 0) ∧ (∀ z, 0 ≤ B.Rbar38 c z)) ∧
    ((∀ z, 0 < Real.exp (-(B.Rbar38 c z)) ∧ Real.exp (-(B.Rbar38 c z)) ≤ 1) ∧
      0 < B.ZW38 c ∧ B.ZW38 c ≤ 1) ∧
    (IsProbabilityMeasure (B.muHatW38 c) ∧
      B.muHatW38 c = (fullWeightSequenceGaussian c).withDensity
        (fun z => ENNReal.ofReal (Real.exp (-(B.Rbar38 c z)) / B.ZW38 c)) ∧
      (B.muHatW38 c ≪ fullWeightSequenceGaussian c ∧ fullWeightSequenceGaussian c ≪ B.muHatW38 c) ∧
      IsProbabilityMeasure (B.muW38 c) ∧ B.muW38 c = (B.muHatW38 c).map B.cleanΦinv ∧
      ∀ᵐ z ∂(B.muHatW38 c), ∃ hz : z ∈ seqSobolev38 0,
        B.cleanΦinv z = B.Φinv z hz ∧ B.Φ (B.cleanΦinv z) = z) := by
  refine ⟨⟨B.measurable_Rbar38 lower upper c hlower hbound hupper,
      measurableSet_Omega038 lower upper c hlower hbound hupper,
      fullWeightSequenceGaussian_Omega038_compl lower upper c hlower hbound hupper,
      fun z hz => ⟨(B.remainder_tendsto_pathwise38 lower upper c hlower hbound hupper z hz
        isExhaustion_stdExh38).1, B.Rbar38_of_mem c hz⟩,
      fun z hz => B.Rbar38_of_not_mem c hz,
      B.Rbar38_nonneg lower upper c hlower hbound hupper⟩,
    ⟨fun z => ⟨B.exp_neg_Rbar38_pos c z, B.exp_neg_Rbar38_le_one lower upper c hlower hbound hupper z⟩,
      (B.ZW38_pos_le_one lower upper c hlower hbound hupper).1,
      (B.ZW38_pos_le_one lower upper c hlower hbound hupper).2⟩,
    B.isProbabilityMeasure_muHatW38 lower upper c hlower hbound hupper, rfl,
    B.muHatW38_equivalent lower upper c hlower hbound hupper,
    B.isProbabilityMeasure_muW38 lower upper c hlower hbound hupper, rfl,
    B.ae_cleanΦinv_eq_Φinv38 lower upper c hlower hbound hupper⟩

end Finite

end BirkhoffTop38

end NlsGge.Birkhoff
