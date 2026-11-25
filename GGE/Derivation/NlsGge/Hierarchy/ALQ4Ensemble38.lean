import NlsGge.Hierarchy.ALSampling38
import NlsGge.Hierarchy.ALFiniteMeasure38

/-! # L06a: the actual AL ensemble through `Q₄` (`C:eq:ALmeasure`, paper/v2.tex l.2093-2141)

Polynomial weight `W(r) = β₀ + β₁ r² + β₂ r⁴`, lattice `L = 2N+1`, `h = alh38 N = 1/L`.
Reuses L05 (`alh38`, `alRh38`, `alSymbol38`, `alDFT38`) and L03 (`alGaussianNormalizer38`). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section

namespace NlsGge.AblowitzLadik

open Finset MeasureTheory NlsGge.HierarchyRiccati.Core

section Energy

/-- Coefficient sequence `c` with `NlsGge.coefficient c = (β₀, β₁, β₂, 0, …)`, i.e. `c_j = β_j (j!)⁴`. -/
def alQ4Coef38 (β₀ β₁ β₂ : ℝ) : ℕ → ℝ := fun j =>
  if j = 0 then β₀ else if j = 1 then β₁ else if j = 2 then 16 * β₂ else 0

theorem alQ4Coef_coefficient38 (β₀ β₁ β₂ : ℝ) (j : ℕ) :
    NlsGge.coefficient (alQ4Coef38 β₀ β₁ β₂) j =
      if j = 0 then β₀ else if j = 1 then β₁ else if j = 2 then β₂ else 0 := by
  unfold NlsGge.coefficient alQ4Coef38
  rcases Nat.lt_or_ge j 3 with h | h
  · interval_cases j <;> simp [Nat.factorial] <;> norm_num
  · have h0 : j ≠ 0 := by omega
    have h1 : j ≠ 1 := by omega
    have h2 : j ≠ 2 := by omega
    simp [h0, h1, h2]

theorem alQ4_weight38 (β₀ β₁ β₂ r : ℝ) :
    NlsGge.Weights.weight (alQ4Coef38 β₀ β₁ β₂) r = β₀ + β₁ * r ^ 2 + β₂ * r ^ 4 := by
  unfold NlsGge.Weights.weight
  rw [tsum_eq_sum (s := range 3)]
  · simp [Finset.sum_range_succ, NlsGge.weightTerm, alQ4Coef_coefficient38]
  · intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    unfold NlsGge.weightTerm
    rw [alQ4Coef_coefficient38]
    have h0 : j ≠ 0 := by omega
    have h1 : j ≠ 1 := by omega
    have h2 : j ≠ 2 := by omega
    simp [h0, h1, h2]


/-- The polynomial lattice energy `β₀/h·M_d + β₁/h³·H_d + β₂/h⁵·K_d` of `C:eq:ALmeasure`. -/
def alQ4Energy38 (β₀ β₁ β₂ : ℝ) (N : ℕ) (α : ZMod (2 * N + 1) → ℂ) : ℝ :=
  β₀ / alh38 N * alMd α + β₁ / alh38 N ^ 3 * alHd α + β₂ / alh38 N ^ 5 * alKd α

/-- The polynomial energy is the `D:eq:ALfullenergy` energy `E_{W,h}` for `W = β₀ + β₁r² + β₂r⁴`. -/
theorem alEnergy38_poly38 (β₀ β₁ β₂ : ℝ) {N : ℕ} (hN : 1 ≤ N) {α : ZMod (2 * N + 1) → ℂ}
    (hα : IsALField38 α) :
    alEnergy38 (alQ4Coef38 β₀ β₁ β₂) (alh38 N) α = alQ4Energy38 β₀ β₁ β₂ N α := by
  have hL : 3 ≤ 2 * N + 1 := by omega
  unfold alEnergy38
  rw [tsum_eq_sum (s := range 3)]
  · simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      alEnergyTerm38, alQ38, alQ4Coef_coefficient38, alMomentK38_eq_alK38,
      alK38_zero, alK38_one_eq_alHd hL hα, alK38_two_eq_alKd hL hα, alQ4Energy38]
    simp only [alMd_eq_alMass38]
    norm_num [inv_pow]
    rw [← alMd_eq_alMass38]
    field_simp
  · intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    unfold alEnergyTerm38
    rw [alQ4Coef_coefficient38]
    have h0 : j ≠ 0 := by omega
    have h1 : j ≠ 1 := by omega
    have h2 : j ≠ 2 := by omega
    simp [h0, h1, h2]

/-- `alRate38` of the polynomial weight is the symbol `a_{h,k}` of `C:eq:asymbol`. -/
theorem alRate38_poly38 (β₀ β₁ β₂ : ℝ) (N : ℕ) (k : ℤ) :
    alRate38 (alQ4Coef38 β₀ β₁ β₂) (alh38 N) k = alSymbol38 β₀ β₁ β₂ N k := by
  unfold alRate38 alSymbol38
  rw [alQ4_weight38, show alOmega38 (alh38 N) k = alomega38 N k from rfl]
  ring


end Energy

section Measure

theorem meas_alMd38 {L : ℕ} [NeZero L] : Measurable (alMd (L := L)) := by
  unfold alMd alR
  refine (Finset.measurable_sum _ fun j _ => ?_).neg
  have : Measurable fun α : ZMod L → ℂ => ‖α j‖ := (measurable_pi_apply j).norm
  exact Real.measurable_log.comp (by fun_prop)

theorem meas_alC1_38 {L : ℕ} [NeZero L] : Measurable (alC1 (L := L)) := by
  unfold alC1
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (measurable_pi_apply j).mul (Complex.continuous_conj.measurable.comp (measurable_pi_apply (j - 1)))

theorem meas_alC2_38 {L : ℕ} [NeZero L] : Measurable (alC2 (L := L)) := by
  unfold alC2
  refine Measurable.sub (Finset.measurable_sum _ fun j _ => ?_) (measurable_const.mul
    (Finset.measurable_sum _ fun j _ => ?_))
  · have hr : Measurable fun α : ZMod L → ℂ => ((alR α (j - 1) : ℝ) : ℂ) := by
      unfold alR
      have : Measurable fun α : ZMod L → ℂ => ‖α (j - 1)‖ := (measurable_pi_apply (j - 1)).norm
      exact Complex.measurable_ofReal.comp (by fun_prop)
    exact ((measurable_pi_apply j).mul
      (Complex.continuous_conj.measurable.comp (measurable_pi_apply (j - 2)))).mul
      (measurable_const.sub hr)
  · exact ((measurable_pi_apply j).mul
      (Complex.continuous_conj.measurable.comp (measurable_pi_apply (j - 1)))).pow_const 2

theorem meas_alHd38 {L : ℕ} [NeZero L] : Measurable (alHd (L := L)) := by
  unfold alHd
  exact (measurable_const.mul meas_alMd38).sub
    (measurable_const.mul (Complex.measurable_re.comp meas_alC1_38))

theorem meas_alKd38 {L : ℕ} [NeZero L] : Measurable (alKd (L := L)) := by
  unfold alKd
  exact (((measurable_const.mul meas_alMd38).sub
    (measurable_const.mul (Complex.measurable_re.comp meas_alC1_38))).add
    (measurable_const.mul (Complex.measurable_re.comp meas_alC2_38)))

theorem meas_alQ4Energy38 (β₀ β₁ β₂ : ℝ) (N : ℕ) :
    Measurable (alQ4Energy38 β₀ β₁ β₂ N) := by
  unfold alQ4Energy38
  exact (((measurable_const.mul meas_alMd38).add (measurable_const.mul meas_alHd38)).add
    (measurable_const.mul meas_alKd38))


open Classical in
/-- The Liouville density of `C:eq:ALmeasure` (unnormalised, on the open polydisk, `0` outside):
`exp(-β₀M_d/h - β₁H_d/h³ - β₂K_d/h⁵) ∏_j (1-r_j)⁻¹`. -/
def alQ4Density38 (β₀ β₁ β₂ : ℝ) (N : ℕ) (α : ZMod (2 * N + 1) → ℂ) : ℝ :=
  if IsALField38 α then Real.exp (-alQ4Energy38 β₀ β₁ β₂ N α) * ∏ j, (1 - ‖α j‖ ^ 2)⁻¹ else 0

/-- `𝒵_h = ∫ exp(-E) ∏ (1-r_j)⁻¹ d²α` over the polydisk. -/
def alQ4Partition38 (β₀ β₁ β₂ : ℝ) (N : ℕ) : ℝ :=
  ∫ α : ZMod (2 * N + 1) → ℂ, alQ4Density38 β₀ β₁ β₂ N α

theorem alIntegrand_poly38 (β₀ β₁ β₂ : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    alIntegrand38 (L := 2 * N + 1) (alQ4Coef38 β₀ β₁ β₂) (alh38 N) = alQ4Density38 β₀ β₁ β₂ N := by
  classical
  funext α
  unfold alIntegrand38 alQ4Density38
  by_cases hα : IsALField38 α
  · simp only [hα, ite_true, alEnergy38_poly38 β₀ β₁ β₂ hN hα]
  · simp [hα]

theorem alQ4Partition_eq38 (β₀ β₁ β₂ : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    alQ4Partition38 β₀ β₁ β₂ N =
      alPartition38 (2 * N + 1) (alQ4Coef38 β₀ β₁ β₂) (alh38 N) := by
  have hpart : alPartition38 (2 * N + 1) (alQ4Coef38 β₀ β₁ β₂) (alh38 N) =
      ∫ α, alIntegrand38 (L := 2 * N + 1) (alQ4Coef38 β₀ β₁ β₂) (alh38 N) α := rfl
  rw [hpart, alIntegrand_poly38 β₀ β₁ β₂ hN]
  rfl

theorem alQ4Density_nonneg38 (β₀ β₁ β₂ : ℝ) (N : ℕ) (α : ZMod (2 * N + 1) → ℂ) :
    0 ≤ alQ4Density38 β₀ β₁ β₂ N α := by
  classical
  unfold alQ4Density38
  split_ifs with hα
  · refine mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun j _ => inv_nonneg.2 ?_)
    have := hα j; nlinarith [norm_nonneg (α j)]
  · exact le_rfl

theorem meas_alQ4Density38 (β₀ β₁ β₂ : ℝ) (N : ℕ) :
    Measurable (alQ4Density38 β₀ β₁ β₂ N) := by
  classical
  have hprod : Measurable (fun α : ZMod (2 * N + 1) → ℂ => ∏ j, (1 - ‖α j‖ ^ 2)⁻¹) := by
    refine Finset.measurable_prod _ fun j _ => ?_
    have : Measurable fun α : ZMod (2 * N + 1) → ℂ => ‖α j‖ := (measurable_pi_apply j).norm
    fun_prop
  unfold alQ4Density38
  exact Measurable.ite (measurableSet_alDisk38 (L := 2 * N + 1))
    (((meas_alQ4Energy38 β₀ β₁ β₂ N).neg.exp).mul hprod) measurable_const

/-- On the disk, `E ≥ β₀ M_d / h`. -/
theorem alQ4Energy_ge38 {β₀ β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (N : ℕ)
    {α : ZMod (2 * N + 1) → ℂ} (hα : IsALField38 α) :
    β₀ / alh38 N * alMd α ≤ alQ4Energy38 β₀ β₁ β₂ N α := by
  have hh := alh38_pos N
  unfold alQ4Energy38
  have h1 : 0 ≤ β₁ / alh38 N ^ 3 * alHd α :=
    mul_nonneg (div_nonneg hβ₁ (by positivity)) (alHd_nonneg α hα)
  have h2 : 0 ≤ β₂ / alh38 N ^ 5 * alKd α :=
    mul_nonneg (div_nonneg hβ₂ (by positivity)) (alKd_nonneg α hα)
  linarith

theorem alQ4Density_le38 {β₀ β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (N : ℕ)
    (α : ZMod (2 * N + 1) → ℂ) :
    alQ4Density38 β₀ β₁ β₂ N α ≤ ∏ j, diskProf38 (β₀ / alh38 N) ‖α j‖ := by
  classical
  by_cases hα : IsALField38 α
  · have hpos : ∀ j, 0 < 1 - ‖α j‖ ^ 2 := fun j => by
      have := hα j; nlinarith [norm_nonneg (α j)]
    have hs := alQ4Energy_ge38 (β₀ := β₀) hβ₁ hβ₂ N hα
    have e1 : Real.exp (-alQ4Energy38 β₀ β₁ β₂ N α) ≤
        ∏ j, (1 - ‖α j‖ ^ 2) ^ (β₀ / alh38 N) := by
      calc Real.exp (-alQ4Energy38 β₀ β₁ β₂ N α)
          ≤ Real.exp (-(β₀ / alh38 N * alMd α)) := Real.exp_le_exp.2 (by linarith)
        _ = ∏ j, (1 - ‖α j‖ ^ 2) ^ (β₀ / alh38 N) := by
            unfold alMd alR
            rw [show -(β₀ / alh38 N * -∑ j : ZMod (2 * N + 1), Real.log (1 - ‖α j‖ ^ 2)) =
              ∑ j : ZMod (2 * N + 1), Real.log (1 - ‖α j‖ ^ 2) * (β₀ / alh38 N) by
                rw [mul_neg, neg_neg, Finset.mul_sum]
                exact Finset.sum_congr rfl fun j _ => by ring, Real.exp_sum]
            exact Finset.prod_congr rfl fun j _ => (Real.rpow_def_of_pos (hpos j) _).symm
    unfold alQ4Density38
    simp only [hα, ite_true]
    have e2 : ∏ j, diskProf38 (β₀ / alh38 N) ‖α j‖ =
        ∏ j, (1 - ‖α j‖ ^ 2) ^ (β₀ / alh38 N) * (1 - ‖α j‖ ^ 2)⁻¹ := by
      refine Finset.prod_congr rfl fun j _ => ?_
      have : ‖α j‖ < 1 := hα j
      simp only [diskProf38, this, ite_true]
      rw [Real.rpow_sub_one (hpos j).ne', div_eq_mul_inv]
    rw [e2, Finset.prod_mul_distrib]
    exact mul_le_mul_of_nonneg_right e1 (Finset.prod_nonneg fun j _ => (inv_pos.2 (hpos j)).le)
  · rw [show alQ4Density38 β₀ β₁ β₂ N α = 0 by unfold alQ4Density38; simp [hα]]
    exact Finset.prod_nonneg fun j _ => diskProf_nonneg38 _ (norm_nonneg _)

theorem alQ4Density_integrable38 {β₀ β₁ β₂ : ℝ} (hβ₀ : 0 < β₀) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (N : ℕ) : Integrable (alQ4Density38 β₀ β₁ β₂ N) := by
  have hs : 0 < β₀ / alh38 N := div_pos hβ₀ (alh38_pos N)
  have hG : Integrable (fun α : ZMod (2 * N + 1) → ℂ => ∏ j, diskProf38 (β₀ / alh38 N) ‖α j‖)
      (Measure.pi fun _ : ZMod (2 * N + 1) => (volume : Measure ℂ)) :=
    Integrable.fintype_prod (fun j => diskProf_integrable38 hs)
  refine Integrable.mono' hG (meas_alQ4Density38 β₀ β₁ β₂ N).aestronglyMeasurable
    (Filter.Eventually.of_forall fun α => ?_)
  rw [Real.norm_of_nonneg (alQ4Density_nonneg38 β₀ β₁ β₂ N α)]
  exact alQ4Density_le38 hβ₁ hβ₂ N α

/-- `𝒵_h` is finite, positive and `≤ (πh/β₀)^L`. -/
theorem alQ4Partition_bounds38 {β₀ β₁ β₂ : ℝ} (hβ₀ : 0 < β₀) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (N : ℕ) :
    Integrable (alQ4Density38 β₀ β₁ β₂ N) ∧
    (∫⁻ α, ENNReal.ofReal (alQ4Density38 β₀ β₁ β₂ N α)) < ⊤ ∧
    0 < alQ4Partition38 β₀ β₁ β₂ N ∧
    alQ4Partition38 β₀ β₁ β₂ N ≤ (Real.pi * alh38 N / β₀) ^ (2 * N + 1) := by
  have hh := alh38_pos N
  have hs : 0 < β₀ / alh38 N := div_pos hβ₀ hh
  have hint := alQ4Density_integrable38 hβ₀ hβ₁ hβ₂ N
  refine ⟨hint, hint.lintegral_lt_top, ?_, ?_⟩
  · unfold alQ4Partition38
    rw [integral_pos_iff_support_of_nonneg (alQ4Density_nonneg38 β₀ β₁ β₂ N) hint]
    have hsupp : Function.support (alQ4Density38 β₀ β₁ β₂ N) = alDisk38 (2 * N + 1) := by
      classical
      ext α
      simp only [Function.mem_support, ne_eq, alDisk38, Set.mem_ofPred_eq]
      unfold alQ4Density38
      by_cases hα : IsALField38 α
      · simp only [hα, ite_true, iff_true]
        refine mul_ne_zero (Real.exp_pos _).ne' (Finset.prod_ne_zero_iff.2 fun j _ => inv_ne_zero ?_)
        have := hα j; nlinarith [norm_nonneg (α j)]
      · simp [hα]
    rw [hsupp]
    exact (isOpen_alDisk38 (L := 2 * N + 1)).measure_pos _ ⟨0, fun j => by simp⟩
  · have hG : Integrable (fun α : ZMod (2 * N + 1) → ℂ => ∏ j, diskProf38 (β₀ / alh38 N) ‖α j‖)
        (Measure.pi fun _ : ZMod (2 * N + 1) => (volume : Measure ℂ)) :=
      Integrable.fintype_prod (fun j => diskProf_integrable38 hs)
    unfold alQ4Partition38
    calc ∫ α, alQ4Density38 β₀ β₁ β₂ N α
        ≤ ∫ α : ZMod (2 * N + 1) → ℂ, ∏ j, diskProf38 (β₀ / alh38 N) ‖α j‖ :=
          integral_mono hint hG (alQ4Density_le38 hβ₁ hβ₂ N)
      _ = ∏ j : ZMod (2 * N + 1), ∫ z : ℂ, diskProf38 (β₀ / alh38 N) ‖z‖ :=
          integral_fintype_prod_eq_prod
            (fun (j : ZMod (2 * N + 1)) (z : ℂ) => diskProf38 (β₀ / alh38 N) ‖z‖)
      _ = (Real.pi * alh38 N / β₀) ^ (2 * N + 1) := by
          simp only [diskProf_integral38 hs, Finset.prod_const, Finset.card_univ, ZMod.card]
          congr 1
          field_simp


/-- The energy-weighted Liouville measure `exp(-E) ∏ d²α_j/(1-r_j)` on the polydisk. -/
def alQ4Weighted38 (β₀ β₁ β₂ : ℝ) (N : ℕ) : Measure (ZMod (2 * N + 1) → ℂ) :=
  (alLiouvilleMeasure38 (2 * N + 1)).withDensity
    fun α => ENNReal.ofReal (Real.exp (-alQ4Energy38 β₀ β₁ β₂ N α))

/-- **`C:eq:ALmeasure`**: `η_h = 𝒵_h⁻¹ exp[-β₀M_d/h - β₁H_d/h³ - β₂K_d/h⁵] ∏ d²α_j/(1-r_j)`
on `|α_j| < 1`. -/
def alQ4Eta38 (β₀ β₁ β₂ : ℝ) (N : ℕ) : Measure (ZMod (2 * N + 1) → ℂ) :=
  ENNReal.ofReal (alQ4Partition38 β₀ β₁ β₂ N)⁻¹ • alQ4Weighted38 β₀ β₁ β₂ N

theorem alQ4Weighted_univ38 {β₀ β₁ β₂ : ℝ} (hβ₀ : 0 < β₀) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (N : ℕ) :
    alQ4Weighted38 β₀ β₁ β₂ N Set.univ = ENNReal.ofReal (alQ4Partition38 β₀ β₁ β₂ N) := by
  classical
  have hint := alQ4Density_integrable38 hβ₀ hβ₁ hβ₂ N
  unfold alQ4Weighted38 alLiouvilleMeasure38
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_withDensity_eq_lintegral_mul _
      (f := fun α => ENNReal.ofReal (alRho38 α))
      (ENNReal.measurable_ofReal.comp (measurable_alRho38 (L := 2 * N + 1)))
      (g := fun α => ENNReal.ofReal (Real.exp (-alQ4Energy38 β₀ β₁ β₂ N α)))
      (ENNReal.measurable_ofReal.comp (meas_alQ4Energy38 β₀ β₁ β₂ N).neg.exp)]
  unfold alQ4Partition38
  rw [ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (alQ4Density_nonneg38 β₀ β₁ β₂ N))]
  have hsupp : Function.support (fun α => ENNReal.ofReal (alQ4Density38 β₀ β₁ β₂ N α)) ⊆
      alDisk38 (2 * N + 1) := by
    intro α hα
    by_contra hn
    apply hα
    have : alQ4Density38 β₀ β₁ β₂ N α = 0 := by
      unfold alQ4Density38; simp [show ¬ IsALField38 α from hn]
    simp [this]
  rw [← setLIntegral_eq_of_support_subset hsupp]
  refine setLIntegral_congr_fun measurableSet_alDisk38 fun α hα => ?_
  have h1 : IsALField38 α := hα
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (by exact (Finset.prod_nonneg fun j _ => inv_nonneg.2 (by
    have := h1 j; nlinarith [norm_nonneg (α j)])))]
  unfold alQ4Density38
  simp only [h1, ite_true]
  rw [mul_comm]; rfl

/-- `η_h` is a probability measure, well defined for every `N` and every `β₀ > 0`, `β₁, β₂ ≥ 0`. -/
theorem isProbabilityMeasure_alQ4Eta38 {β₀ β₁ β₂ : ℝ} (hβ₀ : 0 < β₀) (hβ₁ : 0 ≤ β₁)
    (hβ₂ : 0 ≤ β₂) (N : ℕ) : IsProbabilityMeasure (alQ4Eta38 β₀ β₁ β₂ N) := by
  have hpos := (alQ4Partition_bounds38 hβ₀ hβ₁ hβ₂ N).2.2.1
  refine ⟨?_⟩
  unfold alQ4Eta38
  rw [Measure.smul_apply, alQ4Weighted_univ38 hβ₀ hβ₁ hβ₂, smul_eq_mul,
    ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hpos.ne', ENNReal.ofReal_one]


end Measure

section Fourier

theorem alh38_eq_inv (N : ℕ) : alh38 N = (((2 * N + 1 : ℕ) : ℝ))⁻¹ := by
  unfold alh38; push_cast; rw [one_div]

/-- L05's DFT coordinate `z_k = h Σ_j v_j e^{-2πikjh}` of `v = h⁻¹ α` is the (unnormalised)
`ZMod` DFT `Σ_j α_j e(-jk/L)` of `α`, at the representative `k.valMinAbs`. -/
theorem alDFT_eq_dft38 (N : ℕ) (α : ZMod (2 * N + 1) → ℂ) (k : ZMod (2 * N + 1)) :
    alDFT38 N (fun j => ((alh38 N : ℝ) : ℂ)⁻¹ * α j) k.valMinAbs = ZMod.dft α k := by
  have hh : ((alh38 N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (alh38_pos N).ne'
  unfold alDFT38
  rw [ZMod.dft_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : -(j * k) = ((-((j.val : ℤ) * k.valMinAbs) : ℤ) : ZMod (2 * N + 1)) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [e, stdAddChar_int38, smul_eq_mul]
  have e2 : Complex.exp (-(2 * Real.pi * Complex.I * ((k.valMinAbs : ℤ) : ℂ) * (alt38 N j : ℂ))) =
      Complex.exp (((2 * Real.pi * ((-((j.val : ℤ) * k.valMinAbs) : ℤ) : ℝ) /
        ((2 * N + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) := by
    congr 1
    unfold alt38
    rw [alh38_eq_inv]
    push_cast
    ring
  rw [e2]
  field_simp

/-- The sum over `ZMod L` at `k.valMinAbs` equals the sum over `|ν| ≤ N`. -/
theorem sum_valMinAbs_eq_Icc38 (N : ℕ) (F : ℤ → ℝ) :
    ∑ k : ZMod (2 * N + 1), F k.valMinAbs = ∑ ν ∈ Finset.Icc (-(N : ℤ)) N, F ν := by
  have hmem : ∀ k : ZMod (2 * N + 1), k.valMinAbs ∈ Finset.Icc (-(N : ℤ)) N := by
    intro k
    have h1 := ZMod.natAbs_valMinAbs_le k
    have h2 : (2 * N + 1) / 2 = N := by omega
    rw [h2] at h1
    rw [Finset.mem_Icc]; omega
  have himg : (Finset.univ : Finset (ZMod (2 * N + 1))).image ZMod.valMinAbs =
      Finset.Icc (-(N : ℤ)) N := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hx
      exact hmem k
    · rw [Finset.card_image_of_injective _ ZMod.injective_valMinAbs]
      simp [ZMod.card]
      omega
  rw [← himg, Finset.sum_image (fun a _ b _ h => ZMod.injective_valMinAbs h)]

end Fourier

section Remainder

theorem alQ4_weight_sum38 (β₀ β₁ β₂ r : ℝ) :
    NlsGge.Weights.weight (alQ4Coef38 β₀ β₁ β₂) r =
      ∑ j ∈ Finset.range 3, NlsGge.weightTerm (alQ4Coef38 β₀ β₁ β₂) r j := by
  unfold NlsGge.Weights.weight
  refine tsum_eq_sum fun j hj => ?_
  simp only [Finset.mem_range, not_lt] at hj
  unfold NlsGge.weightTerm
  rw [alQ4Coef_coefficient38]
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  have h2 : j ≠ 2 := by omega
  simp [h0, h1, h2]

/-- The three quadratic parts of the energy. -/
theorem alQ4_quad38 (β₀ β₁ β₂ : ℝ) (N : ℕ) (α : ZMod (2 * N + 1) → ℂ) :
    ∑ k : ZMod (2 * N + 1), NlsGge.Weights.weight (alQ4Coef38 β₀ β₁ β₂)
        (alOmega38 (alh38 N) k.valMinAbs) * ‖ZMod.dft α k‖ ^ 2 =
      β₀ * ((alh38 N)⁻¹ ^ 1 * ∑ i, ‖α i‖ ^ 2)
      + β₁ * ((alh38 N)⁻¹ ^ 3 * ∑ i, ‖α i - α (i - 1)‖ ^ 2)
      + β₂ * ((alh38 N)⁻¹ ^ 5 * ∑ i, ‖α (i + 1) - 2 * α i + α (i - 1)‖ ^ 2) := by
  have hh := alh38_eq_inv N
  have key : ∀ j : ℕ, ∑ k : ZMod (2 * N + 1), NlsGge.weightTerm (alQ4Coef38 β₀ β₁ β₂)
      (alOmega38 (alh38 N) k.valMinAbs) j * ‖ZMod.dft α k‖ ^ 2 =
      alEnergyQuadTerm38 (alQ4Coef38 β₀ β₁ β₂) (alh38 N) α j :=
    fun j => (alEnergyQuadTerm_eq38 α hh j).symm
  simp_rw [alQ4_weight_sum38, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [key, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  simp only [alEnergyQuadTerm38, alQ4Coef_coefficient38]
  have s1 : ∑ i, ‖(alDelta38^[2] α) i‖ ^ 2 = ∑ i, ‖α (i + 1) - 2 * α i + α (i - 1)‖ ^ 2 := by
    have e : ∀ i, (alDelta38^[2] α) i = α i - 2 * α (i - 1) + α (i - 1 - 1) := by
      intro i; simp [alDelta38]; ring_nf
    simp_rw [e]
    have := Equiv.sum_comp (Equiv.addRight (1 : ZMod (2 * N + 1)))
      (fun i => ‖α i - 2 * α (i - 1) + α (i - 1 - 1)‖ ^ 2)
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
  have s2 : ∑ i, ‖(alDelta38^[1] α) i‖ ^ 2 = ∑ i, ‖α i - α (i - 1)‖ ^ 2 := by
    simp [alDelta38]
  simp only [Function.iterate_zero, id, s1, s2]
  norm_num

theorem alKd_ge_delta2_38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    ∑ j, ‖α (j + 1) - 2 * α j + α (j - 1)‖ ^ 2 ≤ alKd α := by
  rw [alKd_squares]
  have hl : 0 ≤ ∑ j, (-Real.log (1 - alR α j) - alR α j - (1 / 2) * alR α j ^ 2) :=
    Finset.sum_nonneg fun j _ => alEll_sq_nonneg (by unfold alR; positivity) (alR_lt_one α hα j)
  have a2 : 0 ≤ ∑ j, (alR α (j + 1) - alR α j) ^ 2 :=
    Finset.sum_nonneg fun j _ => by positivity
  have a3 : 0 ≤ ∑ j, alR α j * ‖α (j + 1) - α (j - 1)‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (by unfold alR; positivity) (by positivity)
  have a4 : 0 ≤ ∑ j, ((α j * (starRingEnd ℂ) (α (j - 1))).im) ^ 2 :=
    Finset.sum_nonneg fun j _ => by positivity
  have : (0:ℝ) ≤ 3 / 2 * ∑ j, (alR α (j + 1) - alR α j) ^ 2 := by positivity
  show _ ≤ _ + _ + _ + 2 * ∑ j, ((α j * (starRingEnd ℂ) (α (j - 1))).im) ^ 2 + _
  linarith

/-- **Exact form of the nonlinear remainder** (consequence of `C:eq:Msplit`–`C:eq:Ksquares`):
`R_h = (β₀/h - 1 + 2β₁/h³) Σ ℓ(r_j) + (β₂/h⁵)(K_d - Σ|α_{j+1}-2α_j+α_{j-1}|²)`, in `L03`'s
Fourier-coordinate form `alRemainder38`. -/
theorem alQ4Remainder_eq38 (β₀ β₁ β₂ : ℝ) {N : ℕ} (hN : 1 ≤ N) {α : ZMod (2 * N + 1) → ℂ}
    (hα : IsALField38 α) :
    alRemainder38 (alQ4Coef38 β₀ β₁ β₂) (alh38 N) (ZMod.dft α) =
      (β₀ / alh38 N - 1 + 2 * β₁ / alh38 N ^ 3) * ∑ j, alEll (alR α j)
      + β₂ / alh38 N ^ 5 * (alKd α - ∑ j, ‖α (j + 1) - 2 * α j + α (j - 1)‖ ^ 2) := by
  have hh0 := (alh38_pos N).ne'
  have hrate := alRate_quadratic38 (c := alQ4Coef38 β₀ β₁ β₂) α (alh38_eq_inv N)
  unfold alRemainder38
  rw [ZMod.dft.symm_apply_apply, alEnergy38_poly38 β₀ β₁ β₂ hN hα, ← hrate, alQ4_quad38]
  have hM : alMass38 (2 * N + 1) α = alMd α := rfl
  rw [hM]
  unfold alQ4Energy38
  have e1 := alMd_split α
  have e2 := alHd_split α
  have e3 : ∑ j, alR α j = ∑ j, ‖α j‖ ^ 2 := rfl
  rw [e3] at e1
  rw [e2] at *
  rw [e1] at *
  field_simp
  ring

end Remainder

section Rh

/-- The mass shift `C:eq:massshift`: `-(β₀/h)M_d + M_d = -((β₀-h)/h) M_d`. -/
theorem alMassShift38 (β₀ : ℝ) (N : ℕ) (M : ℝ) :
    -(β₀ / alh38 N * M) + M = -((β₀ - alh38 N) / alh38 N * M) := by
  have := (alh38_pos N).ne'
  field_simp
  ring

/-- Symbol positivity `a_{h,k} > 0` for `h < β₀` (`C:eq:asymbol`). -/
theorem alSymbol38_pos {β₀ β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (N : ℕ)
    (hh : alh38 N < β₀) (k : ℤ) : 0 < alSymbol38 β₀ β₁ β₂ N k := by
  unfold alSymbol38
  have h1 : 0 ≤ β₁ * alomega38 N k ^ 2 := by positivity
  have h2 : 0 ≤ β₂ * alomega38 N k ^ 4 := by positivity
  linarith

theorem alQ4Rate_pos38 {β₀ β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (N : ℕ)
    (hh : alh38 N < β₀) (k : ℤ) : 0 < alRate38 (alQ4Coef38 β₀ β₁ β₂) (alh38 N) k := by
  rw [alRate38_poly38]; exact alSymbol38_pos hβ₁ hβ₂ N hh k

/-- Interpolation: `v = h⁻¹ α`. -/
def alQ4V38 (N : ℕ) (û : ZMod (2 * N + 1) → ℂ) : ZMod (2 * N + 1) → ℂ :=
  fun j => ((alh38 N : ℝ) : ℂ)⁻¹ * ZMod.dft.symm û j

theorem alQ4V_mul38 (N : ℕ) (α : ZMod (2 * N + 1) → ℂ) :
    (fun j => ((alh38 N : ℝ) : ℂ) * (((alh38 N : ℝ) : ℂ)⁻¹ * α j)) = α := by
  have hh : ((alh38 N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (alh38_pos N).ne'
  funext j; field_simp

/-- **`R_h` of L05 in Fourier coordinates is L03's remainder**: for `α` in the polydisk and
`v = h⁻¹ α`, `alRh38 β N v = alRemainder38 c h (dft α)`. -/
theorem alRh38_eq_alRemainder38 (β₀ β₁ β₂ : ℝ) {N : ℕ} (hN : 1 ≤ N) {α : ZMod (2 * N + 1) → ℂ}
    (hα : IsALField38 α) :
    alRh38 β₀ β₁ β₂ N (fun j => ((alh38 N : ℝ) : ℂ)⁻¹ * α j) =
      alRemainder38 (alQ4Coef38 β₀ β₁ β₂) (alh38 N) (ZMod.dft α) := by
  have hh0 := (alh38_pos N).ne'
  unfold alRh38 alRemainder38
  rw [alQ4V_mul38, ZMod.dft.symm_apply_apply, alEnergy38_poly38 β₀ β₁ β₂ hN hα]
  have hsum : ∑ k ∈ Finset.Icc (-(N : ℤ)) N, alSymbol38 β₀ β₁ β₂ N k *
        ‖alDFT38 N (fun j => ((alh38 N : ℝ) : ℂ)⁻¹ * α j) k‖ ^ 2 =
      ∑ k : ZMod (2 * N + 1), alRate38 (alQ4Coef38 β₀ β₁ β₂) (alh38 N) k.valMinAbs *
        ‖ZMod.dft α k‖ ^ 2 := by
    rw [← sum_valMinAbs_eq_Icc38 N (fun ν => alSymbol38 β₀ β₁ β₂ N ν *
      ‖alDFT38 N (fun j => ((alh38 N : ℝ) : ℂ)⁻¹ * α j) ν‖ ^ 2)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [alDFT_eq_dft38, alRate38_poly38]
  rw [hsum]
  have hM : alMass38 (2 * N + 1) α = alMd α := rfl
  rw [hM]
  unfold alQ4Energy38
  field_simp
  ring

/-- **`C:eq:Rhpositive`**: `R_h(v) ≥ 0` if `h < β₀` and `h|v_j| < 1` for all `j`. -/
theorem alRh38_nonneg {β₀ β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) {N : ℕ} (hN : 1 ≤ N)
    (hh : alh38 N < β₀) (v : ZMod (2 * N + 1) → ℂ) (hv : ∀ j, alh38 N * ‖v j‖ < 1) :
    0 ≤ alRh38 β₀ β₁ β₂ N v := by
  have hh0 := alh38_pos N
  have hhc : ((alh38 N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hh0.ne'
  set α : ZMod (2 * N + 1) → ℂ := fun j => ((alh38 N : ℝ) : ℂ) * v j with hαdef
  have hα : IsALField38 α := by
    intro j
    simp only [hαdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh0]
    exact hv j
  have hv' : v = fun j => ((alh38 N : ℝ) : ℂ)⁻¹ * α j := by
    funext j; simp only [hαdef]; field_simp
  rw [hv', alRh38_eq_alRemainder38 β₀ β₁ β₂ hN hα, alQ4Remainder_eq38 β₀ β₁ β₂ hN hα]
  have hc : 0 ≤ β₀ / alh38 N - 1 + 2 * β₁ / alh38 N ^ 3 := by
    have : 1 ≤ β₀ / alh38 N := (one_le_div hh0).2 hh.le
    have : 0 ≤ 2 * β₁ / alh38 N ^ 3 := by positivity
    linarith
  have hl : 0 ≤ ∑ j, alEll (alR α j) :=
    Finset.sum_nonneg fun j _ => alEll_nonneg (by unfold alR; positivity) (alR_lt_one α hα j)
  have hk := alKd_ge_delta2_38 hα
  have : 0 ≤ β₂ / alh38 N ^ 5 := by positivity
  have := mul_nonneg hc hl
  have := mul_nonneg ‹0 ≤ β₂ / alh38 N ^ 5› (sub_nonneg.2 hk)
  linarith

end Rh

section Weight

open Classical in
/-- **`C:eq:latticeweight`**: `f_h(v) = 1_{h max_j |v_j| < 1} e^{-R_h(v)}`, `R_h = alRh38`. -/
def alQ4F38 (β₀ β₁ β₂ : ℝ) (N : ℕ) (v : ZMod (2 * N + 1) → ℂ) : ℝ :=
  if ∀ j, alh38 N * ‖v j‖ < 1 then Real.exp (-alRh38 β₀ β₁ β₂ N v) else 0

/-- `0 ≤ f_h ≤ 1` (`C:eq:latticeweight`). -/
theorem alQ4F_nonneg38 (β₀ β₁ β₂ : ℝ) (N : ℕ) (v : ZMod (2 * N + 1) → ℂ) :
    0 ≤ alQ4F38 β₀ β₁ β₂ N v := by
  unfold alQ4F38; split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

theorem alQ4F_le_one38 {β₀ β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) {N : ℕ} (hN : 1 ≤ N)
    (hh : alh38 N < β₀) (v : ZMod (2 * N + 1) → ℂ) : alQ4F38 β₀ β₁ β₂ N v ≤ 1 := by
  unfold alQ4F38; split_ifs with hv
  · rw [Real.exp_le_one_iff]
    have := alRh38_nonneg hβ₁ hβ₂ hN hh v hv
    linarith
  · exact zero_le_one

theorem alIsAL_iff_V38 (N : ℕ) (û : ZMod (2 * N + 1) → ℂ) :
    IsALField38 (ZMod.dft.symm û) ↔ ∀ j, alh38 N * ‖alQ4V38 N û j‖ < 1 := by
  have hh0 := alh38_pos N
  have : ∀ j, alh38 N * ‖alQ4V38 N û j‖ = ‖ZMod.dft.symm û j‖ := by
    intro j
    unfold alQ4V38
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh0]
    field_simp
  simp only [this]
  rfl

/-- `L03`'s reweighting `alReweight38 c h` is `f_h` evaluated at `v = h⁻¹ 𝓕⁻ û`. -/
theorem alReweight_eq_alQ4F38 (β₀ β₁ β₂ : ℝ) {N : ℕ} (hN : 1 ≤ N) (û : ZMod (2 * N + 1) → ℂ) :
    alReweight38 (alQ4Coef38 β₀ β₁ β₂) (alh38 N) û = alQ4F38 β₀ β₁ β₂ N (alQ4V38 N û) := by
  classical
  unfold alReweight38 alQ4F38
  by_cases hα : IsALField38 (ZMod.dft.symm û)
  · have hv := (alIsAL_iff_V38 N û).1 hα
    rw [if_pos hα, if_pos hv]
    congr 1
    have := alRh38_eq_alRemainder38 β₀ β₁ β₂ hN hα
    rw [ZMod.dft.apply_symm_apply] at this
    unfold alQ4V38
    rw [this]
  · have hv : ¬ ∀ j, alh38 N * ‖alQ4V38 N û j‖ < 1 := fun h => hα ((alIsAL_iff_V38 N û).2 h)
    rw [if_neg hα, if_neg hv]

/-- The Gaussian `γ_h` on the Fourier coordinates `z_k`: independent proper complex Gaussians with
rates `a_{h,k} = alSymbol38 β N k` (`C:eq:asymbol`). -/
def alQ4Gauss38 (β₀ β₁ β₂ : ℝ) (N : ℕ) : Measure (ZMod (2 * N + 1) → ℂ) :=
  alGauss38 (L := 2 * N + 1) (alQ4Coef38 β₀ β₁ β₂) (alh38 N)

/-- `Z_h = E_{γ_h} f_h`. -/
def alQ4Z38 (β₀ β₁ β₂ : ℝ) (N : ℕ) : ℝ :=
  ∫ û, alQ4F38 β₀ β₁ β₂ N (alQ4V38 N û) ∂(alQ4Gauss38 β₀ β₁ β₂ N)

instance alQ4Gauss_prob38 (β₀ β₁ β₂ : ℝ) (N : ℕ) : IsProbabilityMeasure (alQ4Gauss38 β₀ β₁ β₂ N) := by
  unfold alQ4Gauss38 alGauss38
  infer_instance

theorem alQ4Z_eq_alZ38 (β₀ β₁ β₂ : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    alQ4Z38 β₀ β₁ β₂ N = alZ38 (L := 2 * N + 1) (alQ4Coef38 β₀ β₁ β₂) (alh38 N) := by
  unfold alQ4Z38 alZ38 alQ4Gauss38
  refine integral_congr_ae (Filter.Eventually.of_forall fun û => ?_)
  exact (alReweight_eq_alQ4F38 β₀ β₁ β₂ hN û).symm

theorem meas_alQ4F_V38 (β₀ β₁ β₂ : ℝ) (N : ℕ) :
    Measurable (fun û : ZMod (2 * N + 1) → ℂ => alQ4F38 β₀ β₁ β₂ N (alQ4V38 N û)) := by
  classical
  have hs := measurable_synth38 (L := 2 * N + 1)
  have hc := alh38_pos N
  have hV : Measurable (alQ4V38 N) := by
    unfold alQ4V38
    exact measurable_pi_iff.2 fun j => measurable_const.mul ((measurable_pi_apply j).comp hs)
  have hR : Measurable (alRh38 β₀ β₁ β₂ N) := by
    unfold alRh38
    have hα : Measurable fun v : ZMod (2 * N + 1) → ℂ => fun j => ((alh38 N : ℝ) : ℂ) * v j :=
      measurable_pi_iff.2 fun j => measurable_const.mul (measurable_pi_apply j)
    have hD : ∀ k : ℤ, Measurable fun v : ZMod (2 * N + 1) → ℂ => alDFT38 N v k := by
      intro k
      unfold alDFT38
      refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
      exact (measurable_pi_apply j).mul measurable_const
    refine ((((measurable_const.mul (meas_alMd38.comp hα)).add
      (measurable_const.mul (meas_alHd38.comp hα))).add
      (measurable_const.mul (meas_alKd38.comp hα)))).sub
      (Finset.measurable_sum _ fun k _ => measurable_const.mul ?_)
    exact ((hD k).norm).pow_const 2
  unfold alQ4F38
  refine Measurable.ite ?_ ((hR.comp hV).neg.exp) measurable_const
  have : {û : ZMod (2 * N + 1) → ℂ | ∀ j, alh38 N * ‖alQ4V38 N û j‖ < 1} =
      ⋂ j, {û | alh38 N * ‖alQ4V38 N û j‖ < 1} := by ext; simp
  rw [this]
  refine MeasurableSet.iInter fun j => ?_
  exact measurableSet_lt (measurable_const.mul (((measurable_pi_apply j).comp hV).norm))
    measurable_const

theorem integrable_alQ4F_V38 {β₀ β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) {N : ℕ} (hN : 1 ≤ N)
    (hh : alh38 N < β₀) :
    Integrable (fun û : ZMod (2 * N + 1) → ℂ => alQ4F38 β₀ β₁ β₂ N (alQ4V38 N û))
      (alQ4Gauss38 β₀ β₁ β₂ N) := by
  refine Integrable.of_bound (meas_alQ4F_V38 β₀ β₁ β₂ N).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun û => ?_)
  rw [Real.norm_of_nonneg (alQ4F_nonneg38 _ _ _ _ _)]
  exact alQ4F_le_one38 hβ₁ hβ₂ hN hh _

theorem alQ4Z_le_one38 {β₀ β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) {N : ℕ} (hN : 1 ≤ N)
    (hh : alh38 N < β₀) : alQ4Z38 β₀ β₁ β₂ N ≤ 1 := by
  unfold alQ4Z38
  calc _ ≤ ∫ û : ZMod (2 * N + 1) → ℂ, (1 : ℝ) ∂(alQ4Gauss38 β₀ β₁ β₂ N) :=
        integral_mono (integrable_alQ4F_V38 hβ₁ hβ₂ hN hh) (integrable_const _)
          fun û => alQ4F_le_one38 hβ₁ hβ₂ hN hh _
    _ = 1 := by simp

end Weight

section Normalizer

/-- **`C:eq:ALnormalizer`**: `𝒵_h = h^L ∏_{|k|≤N} (π/a_{h,k}) Z_h` for the polynomial weight
(`L03`'s `alGaussianNormalizer38` at the coefficients `alQ4Coef38`; no class hypothesis needed). -/
theorem alQ4Normalizer38 {β₀ β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) {N : ℕ} (hN : 1 ≤ N)
    (hh : alh38 N < β₀) :
    alQ4Partition38 β₀ β₁ β₂ N =
      alh38 N ^ (2 * N + 1) *
        (∏ ν ∈ Finset.Icc (-(N : ℤ)) N, Real.pi / alSymbol38 β₀ β₁ β₂ N ν) *
        alQ4Z38 β₀ β₁ β₂ N := by
  have key := alGaussianNormalizer38 (L := 2 * N + 1) (alQ4Coef38 β₀ β₁ β₂)
    (alh38_eq_inv N) (alQ4Rate_pos38 hβ₁ hβ₂ N hh)
  rw [alQ4Partition_eq38 β₀ β₁ β₂ hN, key, ← alQ4Z_eq_alZ38 β₀ β₁ β₂ hN]
  congr 2
  rw [← prod_valMinAbs_eq_Icc38 N (fun ν => Real.pi / alSymbol38 β₀ β₁ β₂ N ν)]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [alRate38_poly38]

/-- Bundled: for `0 < β₀`, `0 ≤ β₁, β₂`, `N ≥ 1`, `h < β₀`: `η_h` is a probability measure, `𝒵_h` is
finite with `0 < 𝒵_h ≤ (πh/β₀)^L`, all rates positive, `f_h` measurable with `0 ≤ f_h ≤ 1`,
`0 < Z_h ≤ 1`, and `𝒵_h = h^L ∏ (π/a) Z_h`. -/
theorem alQ4Ensemble38 {β₀ β₁ β₂ : ℝ} (hβ₀ : 0 < β₀) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) {N : ℕ}
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
  have hh0 := alh38_pos N
  obtain ⟨hint, -, hpos, hle⟩ := alQ4Partition_bounds38 hβ₀ hβ₁ hβ₂ N
  have hsym := alSymbol38_pos hβ₁ hβ₂ N hh
  have hid := alQ4Normalizer38 hβ₁ hβ₂ hN hh
  have hP : 0 < alh38 N ^ (2 * N + 1) *
      ∏ ν ∈ Finset.Icc (-(N : ℤ)) N, Real.pi / alSymbol38 β₀ β₁ β₂ N ν :=
    mul_pos (pow_pos hh0 _) (Finset.prod_pos fun ν _ => div_pos Real.pi_pos (hsym ν))
  have hZ : 0 < alQ4Z38 β₀ β₁ β₂ N := by
    by_contra hZ
    push Not at hZ
    have := mul_nonpos_of_nonneg_of_nonpos hP.le hZ
    rw [← hid] at this
    linarith
  exact ⟨isProbabilityMeasure_alQ4Eta38 hβ₀ hβ₁ hβ₂ N, hint, hpos, hle, hsym,
    meas_alQ4F_V38 β₀ β₁ β₂ N,
    fun v => ⟨alQ4F_nonneg38 _ _ _ _ _, alQ4F_le_one38 hβ₁ hβ₂ hN hh v⟩,
    integrable_alQ4F_V38 hβ₁ hβ₂ hN hh, hZ, alQ4Z_le_one38 hβ₁ hβ₂ hN hh, hid⟩

end Normalizer

section Law

theorem alQ4Weighted_eq38 (β₀ β₁ β₂ : ℝ) (N : ℕ) :
    alQ4Weighted38 β₀ β₁ β₂ N =
      (volume : Measure (ZMod (2 * N + 1) → ℂ)).withDensity
        fun α => ENNReal.ofReal (alQ4Density38 β₀ β₁ β₂ N α) := by
  classical
  unfold alQ4Weighted38 alLiouvilleMeasure38
  have hf : Measurable fun α : ZMod (2 * N + 1) → ℂ => ENNReal.ofReal (alRho38 α) :=
    ENNReal.measurable_ofReal.comp (measurable_alRho38 (L := 2 * N + 1))
  have hg : Measurable fun α : ZMod (2 * N + 1) → ℂ =>
      ENNReal.ofReal (Real.exp (-alQ4Energy38 β₀ β₁ β₂ N α)) :=
    ENNReal.measurable_ofReal.comp (meas_alQ4Energy38 β₀ β₁ β₂ N).neg.exp
  rw [← withDensity_mul _ hf hg,
    ← withDensity_indicator (measurableSet_alDisk38 (L := 2 * N + 1))]
  congr 1
  funext α
  by_cases hα : α ∈ alDisk38 (2 * N + 1)
  · have h1 : IsALField38 α := hα
    rw [Set.indicator_of_mem hα]
    unfold alQ4Density38
    simp only [h1, ite_true]
    rw [Pi.mul_apply, ← ENNReal.ofReal_mul (show 0 ≤ alRho38 α from Finset.prod_nonneg fun j _ => inv_nonneg.2 (by
      have := h1 j; nlinarith [norm_nonneg (α j)])), mul_comm]
    rfl
  · rw [Set.indicator_of_notMem hα]
    have : ¬ IsALField38 α := hα
    unfold alQ4Density38
    simp [this]

/-- **Law of the interpolant.** For every test function `φ` of the Fourier coordinates
`z = 𝓕α` (`z_k = h Σ_j v_j e^{-2πikjh}`, `v = h⁻¹α`),
`E_{η_h} φ(z) = Z_h⁻¹ E_{γ_h}[φ f_h]`: the Fourier-coordinate law of `η_h` is the normalised
reweighting of `γ_h` by `f_h`. Both sides are Lebesgue/Bochner integrals identified without
integrability assumptions (all steps are measure identities). -/
theorem alQ4Eta_integral38 {β₀ β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) {N : ℕ} (hN : 1 ≤ N)
    (hh : alh38 N < β₀) (φ : (ZMod (2 * N + 1) → ℂ) → ℝ) :
    ∫ α, φ (ZMod.dft α) ∂(alQ4Eta38 β₀ β₁ β₂ N) =
      (alQ4Z38 β₀ β₁ β₂ N)⁻¹ *
        ∫ û, φ û * alQ4F38 β₀ β₁ β₂ N (alQ4V38 N û) ∂(alQ4Gauss38 β₀ β₁ β₂ N) := by
  classical
  have hh0 := alh38_pos N
  have hid := alQ4Normalizer38 hβ₁ hβ₂ hN hh
  have hLne : (((2 * N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  set a : ZMod (2 * N + 1) → ℝ := fun k =>
    alRate38 (alQ4Coef38 β₀ β₁ β₂) (alh38 N) k.valMinAbs with ha
  have hapos : ∀ k, 0 < a k := fun k => alQ4Rate_pos38 hβ₁ hβ₂ N hh _
  -- the weighted measure as a density
  have hW : ∫ α, φ (ZMod.dft α) ∂(alQ4Weighted38 β₀ β₁ β₂ N) =
      ∫ α, alQ4Density38 β₀ β₁ β₂ N α * φ (ZMod.dft α) := by
    have hm : Measurable fun α : ZMod (2 * N + 1) → ℂ =>
        ENNReal.ofReal (alQ4Density38 β₀ β₁ β₂ N α) :=
      ENNReal.measurable_ofReal.comp (meas_alQ4Density38 β₀ β₁ β₂ N)
    rw [alQ4Weighted_eq38, integral_withDensity_eq_integral_toReal_smul hm
      (Filter.Eventually.of_forall fun α => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun α => ?_)
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (alQ4Density_nonneg38 β₀ β₁ β₂ N α)]
  -- Fourier coordinates
  have hF : ∫ α, alQ4Density38 β₀ β₁ β₂ N α * φ (ZMod.dft α) =
      (alh38 N) ^ (2 * N + 1) * ∫ û, Real.exp (-∑ k, a k * ‖û k‖ ^ 2) *
        (φ û * alQ4F38 β₀ β₁ β₂ N (alQ4V38 N û)) := by
    rw [integral_synth38]
    have hJ : ((((2 * N + 1 : ℕ) : ℝ)) ^ (2 * N + 1))⁻¹ = (alh38 N) ^ (2 * N + 1) := by
      rw [alh38_eq_inv, inv_pow]
    rw [hJ]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun û => ?_)
    simp only [ZMod.dft.apply_symm_apply]
    have e := alIntegrand_synth38 (L := 2 * N + 1) (alQ4Coef38 β₀ β₁ β₂) (alh38 N) û
    rw [alIntegrand_poly38 β₀ β₁ β₂ hN, alReweight_eq_alQ4F38 β₀ β₁ β₂ hN] at e
    rw [e]; ring
  have hG : ∫ û, φ û * alQ4F38 β₀ β₁ β₂ N (alQ4V38 N û) ∂(alQ4Gauss38 β₀ β₁ β₂ N) =
      (∏ k, a k / Real.pi) * ∫ û, Real.exp (-∑ k, a k * ‖û k‖ ^ 2) *
        (φ û * alQ4F38 β₀ β₁ β₂ N (alQ4V38 N û)) := by
    unfold alQ4Gauss38 alGauss38
    exact integral_gauss_pi38 a hapos _
  unfold alQ4Eta38
  rw [integral_smul_measure, hW, hF, hG]
  have hprod : (∏ k, a k / Real.pi) = (∏ k, Real.pi / a k)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [inv_div]
  have hP : (∏ k : ZMod (2 * N + 1), Real.pi / a k) =
      ∏ ν ∈ Finset.Icc (-(N : ℤ)) N, Real.pi / alSymbol38 β₀ β₁ β₂ N ν := by
    rw [← prod_valMinAbs_eq_Icc38 N (fun ν => Real.pi / alSymbol38 β₀ β₁ β₂ N ν)]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [ha, alRate38_poly38]
  have hPpos : 0 < ∏ k : ZMod (2 * N + 1), Real.pi / a k :=
    Finset.prod_pos fun k _ => div_pos Real.pi_pos (hapos k)
  have hZpos : 0 < alQ4Z38 β₀ β₁ β₂ N := by
    by_contra hZ
    push Not at hZ
    have hP2 : 0 < alh38 N ^ (2 * N + 1) * ∏ k : ZMod (2 * N + 1), Real.pi / a k :=
      mul_pos (pow_pos hh0 _) hPpos
    have := mul_nonpos_of_nonneg_of_nonpos hP2.le hZ
    have hpart := (alQ4Partition_bounds38 (β₀ := β₀) (by linarith) hβ₁ hβ₂ N).2.2.1
    rw [hid, ← hP] at hpart
    rw [mul_assoc] at hpart
    nlinarith
  rw [hprod]
  have hpart : alQ4Partition38 β₀ β₁ β₂ N =
      alh38 N ^ (2 * N + 1) * (∏ k : ZMod (2 * N + 1), Real.pi / a k) * alQ4Z38 β₀ β₁ β₂ N := by
    rw [hid, hP]
  rw [hpart, ENNReal.toReal_ofReal
    (inv_nonneg.2 (mul_pos (mul_pos (pow_pos hh0 _) hPpos) hZpos).le)]
  simp only [smul_eq_mul]
  have := hPpos.ne'
  have := hZpos.ne'
  have := hh0.ne'
  field_simp

end Law

end NlsGge.AblowitzLadik
