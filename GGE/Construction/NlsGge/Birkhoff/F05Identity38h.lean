import NlsGge.Birkhoff.F05Identity38g
import NlsGge.Birkhoff.S04Moments38

/-! # F05, file h: the finite-gap relative partition functions and `Z_m = lim Z_{m,Λ_N}` (v2 l.668-669)

"This is the limit of the canonical finite-gap ensembles with energy `E_m`: couple them by
`z ↦ P_N z` under `γ_m` and use continuity of `Φ⁻¹` and `R_m`, followed by domination by one."

The canonical finite-gap ensemble with energy `E_m` on `ℂ^Λ` has density `e^{-E_m(Φ⁻¹ z)}`
against `∏ d²z_n`; its relative partition function is `Z_{m,Λ} = 𝒵_{m,Λ} / ∏_{n∈Λ}(π/a_{m,n})`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.HierarchyRiccati.Core NlsGge.Ramer.General Filter Topology
open scoped ENNReal

section FiniteGap

variable (B : BirkhoffInput38) (m : ℕ) (β : ℕ → ℝ)

/-- The Fourier carrier (in `H^m`) of the finite-gap field `Φ⁻¹(z)`, `z ∈ ℂ^Λ` extended by zero. -/
def fgField38 (Λ : Finset ℤ) (w : Λ → ℂ) : SobolevHilbert (m : ℝ) :=
  ofCarrier38 _ (reflC38 _ (B.cleanTinvC m (extZero38 Λ w)))

/-- `E_m(Φ⁻¹ z)` on finite-gap fields. -/
def EmFG38 (Λ : Finset ℤ) (w : Λ → ℂ) : ℝ := energySobolev38 m β (fgField38 B m Λ w)

/-- The rate `a_{m,n}` on the finite index type `Λ`. -/
def rateΛM38 (Λ : Finset ℤ) (i : Λ) : ℝ := finiteHierarchyRate38 m β (i : ℤ)

/-- `γ_{m,Λ} = ∏_{n∈Λ} (a_{m,n}/π) e^{-a_{m,n}|z_n|²} d²z_n`. -/
def gammaΛM38 (Λ : Finset ℤ) : Measure (Λ → ℂ) := finiteComplexGaussian (rateΛM38 m β Λ)

/-- `𝒵_{m,Λ} = ∫ e^{-E_m(Φ⁻¹ z)} ∏ d²z_n`. -/
def ZcalΛM38 (Λ : Finset ℤ) : ℝ :=
  ∫ w, Real.exp (-(EmFG38 B m β Λ w)) ∂(finiteComplexVolume Λ)

/-- `Z_{m,Λ} = 𝒵_{m,Λ} / ∏_{n∈Λ} π/a_{m,n}`: the finite-gap relative partition function. -/
def ZΛM38 (Λ : Finset ℤ) : ℝ := ZcalΛM38 B m β Λ / ∏ i : Λ, (Real.pi / rateΛM38 m β Λ i)

theorem gammaΛM38_eq_map (Λ : Finset ℤ) :
    (gammaM38 m β).map Λ.restrict = gammaΛM38 m β Λ := by
  unfold gammaM38 countableComplexGaussian gammaΛM38 finiteComplexGaussian
  rw [Measure.infinitePi_map_restrict]
  rfl


variable (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

theorem finite_support_extZero05 (Λ : Finset ℤ) (w : Λ → ℂ) :
    {n : ℤ | extZero38 Λ w n ≠ 0}.Finite :=
  Λ.finite_toSet.subset fun n hn => by
    by_contra h
    exact hn (extZero38_apply_of_not_mem w h)

include hm hβ in
/-- **Finite-gap energy identity** `E_m(Φ⁻¹ z) = ∑_{n∈Λ} a_{m,n}|z_n|² + R_m(Φ⁻¹ z)` (F04, F04's
`first equality` with `|Φ_n|² = I_n`). -/
theorem energy_fg05 (Λ : Finset ℤ) (w : Λ → ℂ) :
    EmFG38 B m β Λ w = ∑ i : Λ, rateΛM38 m β Λ i * ‖w i‖ ^ 2 +
      Rm38 m β (B.PhiInvX38 m (extZero38 Λ w)) := by
  set z := extZero38 Λ w with hz
  have hfin := finite_support_extZero05 Λ w
  have hzm : ∀ r : ℝ, z ∈ seqSobolev38 r := fun r => finiteSupport_mem_seqSobolev38 r z hfin
  have hz0 : z ∈ seqSobolev38 0 := hzm 0
  set y : SobolevHilbert (m : ℝ) := fgField38 B m Λ w with hy
  set y' : Hm1 m := B.PhiInvX38 m z with hy'
  have hyc : ∀ n, (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n = -B.Tinv z (-n) := by
    intro n
    show -(carrierCoe38 _ (B.cleanTinvC m z) (-n)) = _
    rw [B.cleanTinvC_of_mem m z (hzm _)]
    rfl
  have hy'c : ∀ n, (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from y') n =
      -B.Tinv z (-n) := by
    intro n
    show -(carrierCoe38 _ (B.cleanTinvC (m - 1) z) (-n)) = _
    rw [B.cleanTinvC_of_mem (m - 1) z (hzm _)]
    rfl
  have hyy : ∀ n, (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n =
      (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from y') n := fun n => by
    rw [hyc, hy'c]
  obtain ⟨hs1, hs2, hE, -, -, -⟩ := (F04_spectral_lemma38 m hm β hβ).2.2 y
  have hu : sobolevToL2_38 m y = sobolevToL2_38 (m - 1) y' := by
    apply physical_ext38
    intro n
    rw [sobolevToL2_38_fourier, sobolevToL2_38_fourier, hyy]
  have hF : fourierSeq38 (sobolevToL2_38 m y) = B.Tinv z := by
    funext n
    rw [fourierSeq38_apply, sobolevToL2_38_fourier, hyc]
    simp
  have hH1 : SobolevSquareSummable 1 (physicalFourier (sobolevToL2_38 m y)) :=
    sobolevSquareSummable_restrict 1 (m : ℝ) (by exact_mod_cast (by omega : 1 ≤ m)) _
      (sobolevToL2_38_sobolev m y)
  have hI : ∀ n, actualGapActionAllE02_38 (sobolevToL2_38 m y) n = ‖z n‖ ^ 2 := fun n => by
    rw [← B.action _ hH1 n, hF, B.right_inv z hz0]
  have hR : Rm38 m β y' = ∑' n : ℤ, gapRemainderTermE02_38 (finiteWeightE02_38 m β)
      ((sobolevToL2_38 m) y) n := by
    unfold Rm38; rw [hu]
  have hsum : ∑' n : ℤ, finiteHierarchyRate38 m β n * actualGapActionAllE02_38
      (sobolevToL2_38 m y) n = ∑ i : Λ, rateΛM38 m β Λ i * ‖w i‖ ^ 2 := by
    have e1 : ∀ n : ℤ, finiteHierarchyRate38 m β n * actualGapActionAllE02_38
        (sobolevToL2_38 m y) n = finiteHierarchyRate38 m β n * ‖z n‖ ^ 2 := fun n => by
      rw [hI]
    simp only [e1]
    rw [tsum_eq_sum (s := Λ)]
    · rw [← Finset.sum_coe_sort Λ]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hz, extZero38_apply_of_mem w i.2]
      rfl
    · intro n hn
      rw [hz, extZero38_apply_of_not_mem w hn]; simp
  unfold EmFG38
  rw [hE, hR]
  · rw [← hsum]
    rfl


/-- The Gaussian density `∏ (a_{m,n}/π) e^{-a_{m,n}|z_n|²}`. -/
def gaussDensΛM38 (Λ : Finset ℤ) (w : Λ → ℂ) : ℝ :=
  ∏ i : Λ, (rateΛM38 m β Λ i / Real.pi) * Real.exp (-(rateΛM38 m β Λ i) * ‖w i‖ ^ 2)

include hm hβ

theorem rateΛM38_pos (Λ : Finset ℤ) (i : Λ) : 0 < rateΛM38 m β Λ i :=
  rate_pos38 m β (by omega) (fun j hj => (hβ j hj).le) (hβ 0 (Nat.zero_le _)) (hβ m le_rfl) _

theorem measurable_RFG38 (Λ : Finset ℤ) :
    Measurable (fun w : Λ → ℂ => Rm38 m β (B.PhiInvX38 m (extZero38 Λ w))) :=
  ((continuous_Rm38 hm hβ).measurable.comp (B.measurable_PhiInvX38 m)).comp
    (measurable_extZero38 Λ)

theorem RFG38_nonneg (Λ : Finset ℤ) (w : Λ → ℂ) :
    0 ≤ Rm38 m β (B.PhiInvX38 m (extZero38 Λ w)) := Rm38_nonneg hm hβ _

theorem gaussDensΛM38_nonneg (Λ : Finset ℤ) (w : Λ → ℂ) : 0 ≤ gaussDensΛM38 m β Λ w :=
  Finset.prod_nonneg (fun i _ => normalizedGaussianKernel_nonneg _
    (rateΛM38_pos m β hm hβ Λ i) (w i))

theorem prod_pi_div_rateM_pos (Λ : Finset ℤ) : 0 < ∏ i : Λ, Real.pi / rateΛM38 m β Λ i :=
  Finset.prod_pos (fun i _ => div_pos Real.pi_pos (rateΛM38_pos m β hm hβ Λ i))

theorem densΛM38_eq (Λ : Finset ℤ) (w : Λ → ℂ) :
    Real.exp (-(EmFG38 B m β Λ w)) = (∏ i : Λ, Real.pi / rateΛM38 m β Λ i) *
      (gaussDensΛM38 m β Λ w * Real.exp (-(Rm38 m β (B.PhiInvX38 m (extZero38 Λ w))))) := by
  rw [energy_fg05 B m β hm hβ Λ w, neg_add, Real.exp_add, gaussDensΛM38]
  have e2 : Real.exp (-∑ i : Λ, rateΛM38 m β Λ i * ‖w i‖ ^ 2) =
      ∏ i : Λ, Real.exp (-(rateΛM38 m β Λ i) * ‖w i‖ ^ 2) := by
    rw [← Real.exp_sum, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have e3 : (∏ i : Λ, Real.pi / rateΛM38 m β Λ i) * ∏ i : Λ, (rateΛM38 m β Λ i / Real.pi) *
      Real.exp (-(rateΛM38 m β Λ i) * ‖w i‖ ^ 2) =
      ∏ i : Λ, Real.exp (-(rateΛM38 m β Λ i) * ‖w i‖ ^ 2) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have := (rateΛM38_pos m β hm hβ Λ i).ne'
    field_simp
  rw [e2, ← mul_assoc, e3]

theorem gammaΛM38_density (Λ : Finset ℤ) :
    gammaΛM38 m β Λ = (finiteComplexVolume Λ).withDensity
      (fun w => ENNReal.ofReal (gaussDensΛM38 m β Λ w)) :=
  finiteComplexGaussian_density (rateΛM38 m β Λ) (rateΛM38_pos m β hm hβ Λ)

theorem integral_gammaΛM38 (Λ : Finset ℤ) (f : (Λ → ℂ) → ℝ) :
    ∫ w, f w ∂(gammaΛM38 m β Λ) =
      ∫ w, gaussDensΛM38 m β Λ w * f w ∂(finiteComplexVolume Λ) := by
  have hmeas : Measurable (fun w : Λ → ℂ => ENNReal.ofReal (gaussDensΛM38 m β Λ w)) :=
    (measurable_finiteGaussianPDF (rateΛM38 m β Λ)).ennreal_ofReal
  rw [gammaΛM38_density m β hm hβ Λ,
    integral_withDensity_eq_integral_toReal_smul hmeas (Filter.Eventually.of_forall
        (fun _ => ENNReal.ofReal_lt_top))]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (gaussDensΛM38_nonneg m β hm hβ Λ w)]

theorem ZcalΛM38_eq (Λ : Finset ℤ) :
    ZcalΛM38 B m β Λ = (∏ i : Λ, Real.pi / rateΛM38 m β Λ i) *
      ∫ w, Real.exp (-(Rm38 m β (B.PhiInvX38 m (extZero38 Λ w)))) ∂(gammaΛM38 m β Λ) := by
  rw [integral_gammaΛM38 m β hm hβ, ← integral_const_mul]
  unfold ZcalΛM38
  refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
  simp only
  rw [densΛM38_eq B m β hm hβ Λ w]

theorem ZΛM38_eq_integral (Λ : Finset ℤ) :
    ZΛM38 B m β Λ = ∫ w, Real.exp (-(Rm38 m β (B.PhiInvX38 m (extZero38 Λ w))))
      ∂(gammaΛM38 m β Λ) := by
  unfold ZΛM38
  rw [ZcalΛM38_eq B m β hm hβ Λ]
  have := (prod_pi_div_rateM_pos m β hm hβ Λ).ne'
  field_simp

theorem ZΛM38_eq_integral_global (Λ : Finset ℤ) :
    ZΛM38 B m β Λ = ∫ z, Real.exp (-(Rm38 m β (B.PhiInvX38 m (projFin38 Λ z)))) ∂(gammaM38 m β) := by
  rw [ZΛM38_eq_integral B m β hm hβ Λ, ← gammaΛM38_eq_map,
    integral_map (Finset.measurable_restrict Λ).aemeasurable
      (Real.measurable_exp.comp (measurable_RFG38 B m β hm hβ Λ).neg).aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  simp only [projFin38_eq_extZero38]

/-- **`0 < Z_{m,Λ} ≤ 1`.** -/
theorem ZΛM38_pos_le_one (Λ : Finset ℤ) : 0 < ZΛM38 B m β Λ ∧ ZΛM38 B m β Λ ≤ 1 := by
  rw [ZΛM38_eq_integral_global B m β hm hβ Λ]
  have : IsProbabilityMeasure (gammaM38 m β) := inferInstance
  exact exp_neg_integral_pos_le_one38 _ _
    (((continuous_Rm38 hm hβ).measurable.comp (B.measurable_PhiInvX38 m)).comp
      (measurable_projFin38 Λ))
    (fun z => Rm38_nonneg hm hβ _)

/-- **v2 l.668-669: `Z_m = lim_N Z_{m,Λ_N}`** (`Λ_N = {-N,…,N}`), the limit of the finite-gap
relative partition functions of the canonical finite-gap ensembles with energy `E_m`. -/
theorem tendsto_ZΛM38 :
    Tendsto (fun N : ℕ => ZΛM38 B m β (stdExh38 N)) atTop (𝓝 (ZM38 B m β)) := by
  have hrw : ∀ N, ZΛM38 B m β (stdExh38 N) = ∫ z, Real.exp (-(Rm38 m β
      (B.PhiInvX38 m (projFin38 (stdExh38 N) z)))) ∂(gammaM38 m β) := fun N =>
    ZΛM38_eq_integral_global B m β hm hβ _
  simp only [hrw]
  unfold ZM38
  have hRc := continuous_Rm38 hm hβ
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ (integrable_const _) ?_ ?_
  · intro N
    exact (((Real.measurable_exp.comp (hRc.measurable.comp (B.measurable_PhiInvX38 m)
      |>.comp (measurable_projFin38 (stdExh38 N))).neg))).aestronglyMeasurable
  · intro N
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact B.expNegR38_le_one hm hβ _
  · have hae := ae_summable38 (m := m) (β := β) (by omega) (fun j hj => (hβ j hj).le)
      (hβ 0 (Nat.zero_le _)) (hβ m le_rfl)
    filter_upwards [hae] with z hz
    have hz' : z ∈ seqSobolev38 ((m - 1 : ℕ) : ℝ) := (mem_seqSobolev38_iff _ _).2 hz
    have hP : ∀ N : ℕ, projFin38 (stdExh38 N) z ∈ seqSobolev38 ((m - 1 : ℕ) : ℝ) := fun N =>
      finiteSupport_mem_seqSobolev38 _ _ (finite_support_projFin38 (stdExh38 N) z)
    have h1 : Tendsto (fun N : ℕ => B.PhiInvX38 m (projFin38 (stdExh38 N) z)) atTop
        (𝓝 (B.PhiInvX38 m z)) := by
      have h0 := ((B.continuous_TinvC (m - 1)).tendsto _).comp
        (tendsto_carrier_proj38 ((m - 1 : ℕ) : ℝ) z hz' isExhaustion_stdExh38)
      have h2 := ((continuous_ofCarrier38 _).comp (continuous_reflC38 _)).tendsto _ |>.comp h0
      unfold BirkhoffInput38.PhiInvX38
      rw [B.cleanTinvC_of_mem _ z hz']
      refine h2.congr (fun N => ?_)
      simp only [Function.comp]
      rw [B.cleanTinvC_of_mem _ _ (hP N)]
    exact (Real.continuous_exp.tendsto _).comp ((hRc.tendsto _).comp h1).neg

end FiniteGap

end NlsGge.Birkhoff
