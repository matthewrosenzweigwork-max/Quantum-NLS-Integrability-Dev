import Mathlib
import QuantumNLS.FullMass

/-!
# R-043AB9AA `prop:root-full-mass` (part 2): weak continuity on all of `L²` including `u = 0` and zero coupling; the Born-product-law limit

Source: `ROOT_measure_extensions.tex`, `prop:root-full-mass`.  Routing: no EXT-025 contract (GP-10 not used); see the header of `FullMass`.

* `continuous_Mfin`: `(κ, u) ↦ M_{κ,u} ∈ FiniteMeasure ℝ` is continuous on `[0,∞) × L²(𝕋_L)` for the topology of weak convergence of finite measures
  (tested against bounded continuous functions).  This contains continuity of `u ↦ M_{κ,u}` for each `κ ≥ 0` on all of `L²`, continuity at `u = 0`
  (`|∫h dM_{κ,u}| ≤ ‖h‖∞‖u‖²`), the joint approach to zero mass and zero coupling, and (with `FullMass.Mmeas_zero_coupling`) the continuous extension
  `M_{0,u} = Σ|û(n)|²δ_{2πn/L}` at zero coupling.  The proof is the printed one: joint continuity of `μ_{λ,v}` (`ParamContinuity.tendsto_muKappa_joint`),
  multiplication by the converging masses.
* `lpEDist_smul_le`, `lpDist_smul_le`: `d_LP(s ρ, s ρ') ≤ max(1,s) d_LP(ρ,ρ')` for the Lévy–Prokhorov distance of finite measures.
* `born_product_limit`: for `u ≠ 0`, `m = ‖u‖²`, `v = u/√m`, coupling `c = κm/N` (`λ = κm`): `ν_N → μ_{κm,v}` weakly in probability under the actual
  Born law of `v^{⊗N}` (`IsLimitingRapidityMeasure`) and the random finite measures `(m/N)Σδ_{q_j} = m ν_N` converge in probability, in the Lévy–Prokhorov
  distance of finite measures, to `M_{κ,u}`; `born_product_unique`: `M_{κ,u}` is the only finite measure with this property.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal NNReal

noncomputable section

open Classical

namespace QuantumNLS.FullMassLimit

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.FreeLimit (freeMeasure freeProb muKappa muKappa_spec)
open QuantumNLS.FullMass (Mmeas Mfin Mmeas_of_ne Mmeas_zero Mmeas_univ unitDir norm_unitDir smul_unitDir isFinite_Mmeas)
open QuantumNLS.BulkResponseActual (IsLimitingRapidityMeasure physBasis empiricalProb)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BornConvergence (TendstoInProbability)

variable {L : ℝ} [Fact (0 < L)]

theorem muKappa_congr {u u' : L2T L} (h : u = u') (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) (κ : ℝ) :
    muKappa u hu κ = muKappa u' hu' κ := by
  subst h; rfl

theorem integral_Mmeas_of_ne (κ : ℝ) {u : L2T L} (h : u ≠ 0) (f : ℝ → ℝ) :
    ∫ x, f x ∂(Mmeas κ u) =
      ‖u‖ ^ 2 * ∫ x, f x ∂(muKappa (unitDir u) (norm_unitDir h) (κ * ‖u‖ ^ 2) : Measure ℝ) := by
  rw [Mmeas_of_ne κ h, integral_smul_measure, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]

/-! ### Weak continuity on `[0,∞) × L²` -/

theorem continuous_Mfin :
    Continuous (fun p : {κ : ℝ // 0 ≤ κ} × L2T L => Mfin p.1.1 p.2) := by
  refine continuous_iff_seqContinuous.2 (fun p q hpq => ?_)
  rw [FiniteMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hκ : Tendsto (fun j => (p j).1.1) atTop (𝓝 q.1.1) :=
    ((continuous_subtype_val.comp continuous_fst).tendsto q).comp hpq
  have hu : Tendsto (fun j => (p j).2) atTop (𝓝 q.2) := (continuous_snd.tendsto q).comp hpq
  have hnorm : Tendsto (fun j => ‖(p j).2‖ ^ 2) atTop (𝓝 (‖q.2‖ ^ 2)) :=
    ((continuous_norm.tendsto _).comp hu).pow 2
  by_cases h0 : q.2 = 0
  · -- zero input
    have hint : ∫ x, f x ∂(Mfin q.1.1 q.2 : Measure ℝ) = 0 := by
      show ∫ x, f x ∂(Mmeas q.1.1 q.2) = 0
      rw [h0, Mmeas_zero]; simp
    rw [hint, tendsto_zero_iff_norm_tendsto_zero]
    have hb : Tendsto (fun j => ‖f‖ * ‖(p j).2‖ ^ 2) atTop (𝓝 0) := by
      have := hnorm.const_mul ‖f‖
      simpa [h0] using this
    refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) hb
    have := norm_integral_le_of_norm_le_const (μ := (Mfin (p j).1.1 (p j).2 : Measure ℝ)) (f := f)
      (C := ‖f‖) (Eventually.of_forall fun x => f.norm_coe_le_norm x)
    refine this.trans (le_of_eq ?_)
    congr 1
    show (Mmeas (p j).1.1 (p j).2).real Set.univ = _
    rw [measureReal_def, Mmeas_univ, ENNReal.toReal_ofReal (sq_nonneg _)]
  · -- nonzero input
    have hq : 0 < ‖q.2‖ := norm_pos_iff.2 h0
    have hev : ∀ᶠ j in atTop, (p j).2 ≠ 0 := hu.eventually (isOpen_ne.mem_nhds h0)
    let vs : ℕ → L2T L := fun j => if h : (p j).2 = 0 then unitDir q.2 else unitDir (p j).2
    have hvs : ∀ j, ‖vs j‖ = 1 := by
      intro j
      by_cases h : (p j).2 = 0
      · simp only [vs, dif_pos h]; exact norm_unitDir h0
      · simp only [vs, dif_neg h]; exact norm_unitDir h
    let lams : ℕ → ℝ := fun j => (p j).1.1 * ‖(p j).2‖ ^ 2
    have hlams : ∀ j, 0 ≤ lams j := fun j => mul_nonneg (p j).1.2 (sq_nonneg _)
    have hlim : Tendsto lams atTop (𝓝 (q.1.1 * ‖q.2‖ ^ 2)) := hκ.mul hnorm
    have hvl : Tendsto vs atTop (𝓝 (unitDir q.2)) := by
      have hs : Tendsto (fun j => (((‖(p j).2‖⁻¹ : ℝ)) : ℂ) • (p j).2) atTop
          (𝓝 (((‖q.2‖⁻¹ : ℝ) : ℂ) • q.2)) := by
        have h1 : Tendsto (fun j => ‖(p j).2‖⁻¹) atTop (𝓝 ‖q.2‖⁻¹) :=
          ((continuous_norm.tendsto _).comp hu).inv₀ hq.ne'
        exact ((Complex.continuous_ofReal.tendsto _).comp h1).smul hu
      refine hs.congr' ?_
      filter_upwards [hev] with j hj
      simp only [vs, dif_neg hj]
      rfl
    have hjoint := QuantumNLS.ParamContinuity.tendsto_muKappa_joint hlim hlams (mul_nonneg q.1.2 (sq_nonneg _))
      vs hvs (norm_unitDir h0) hvl
    have hI := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hjoint) f
    have hlimint : ∫ x, f x ∂(Mfin q.1.1 q.2 : Measure ℝ) =
        ‖q.2‖ ^ 2 * ∫ x, f x ∂(muKappa (unitDir q.2) (norm_unitDir h0) (q.1.1 * ‖q.2‖ ^ 2) : Measure ℝ) :=
      integral_Mmeas_of_ne q.1.1 h0 f
    rw [hlimint]
    refine (hnorm.mul hI).congr' ?_
    filter_upwards [hev] with j hj
    show _ = ∫ x, f x ∂(Mmeas (p j).1.1 (p j).2)
    rw [integral_Mmeas_of_ne (p j).1.1 hj f]
    congr 2
    exact congrArg (fun μ : ProbabilityMeasure ℝ => (μ : Measure ℝ))
      (muKappa_congr (by simp only [vs, dif_neg hj]) (hvs j) (norm_unitDir hj) (lams j))

/-! ### Lipschitz scaling in the Lévy–Prokhorov distance -/

theorem lpEDist_smul_le (s : ℝ≥0) (ρ ρ' : Measure ℝ) [IsFiniteMeasure ρ] [IsFiniteMeasure ρ'] :
    levyProkhorovEDist ((s : ℝ≥0∞) • ρ) ((s : ℝ≥0∞) • ρ') ≤
      max 1 (s : ℝ≥0∞) * levyProkhorovEDist ρ ρ' := by
  set K : ℝ≥0∞ := max 1 (s : ℝ≥0∞) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK0 : K ≠ 0 := (zero_lt_one.trans_le hK1).ne'
  have hKt : K ≠ ∞ := (max_lt ENNReal.one_lt_top ENNReal.coe_lt_top).ne
  apply levyProkhorovEDist_le_of_forall
  intro ε B hδε hεt hB
  set d := levyProkhorovEDist ρ ρ' with hd
  have hdl : d < ε / K := by
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl hK0) (Or.inl hKt)]
    rwa [mul_comm] at hδε
  have hε1 : ε / K ≤ ε := ENNReal.div_le_of_le_mul (le_mul_of_one_le_right' hK1)
  have thick : Metric.thickening (ε / K).toReal B ⊆ Metric.thickening ε.toReal B :=
    Metric.thickening_mono (ENNReal.toReal_mono hεt.ne hε1) B
  have hsK : (s : ℝ≥0∞) * (ε / K) ≤ ε := by
    calc (s : ℝ≥0∞) * (ε / K) ≤ K * (ε / K) := mul_le_mul' (le_max_right _ _) le_rfl
      _ = ε := ENNReal.mul_div_cancel hK0 hKt
  constructor
  · have h1 := left_measure_le_of_levyProkhorovEDist_lt hdl hB
    calc ((s : ℝ≥0∞) • ρ) B = s * ρ B := by simp [Measure.smul_apply]
      _ ≤ s * (ρ' (Metric.thickening (ε / K).toReal B) + ε / K) := mul_le_mul' le_rfl h1
      _ = s * ρ' (Metric.thickening (ε / K).toReal B) + s * (ε / K) := mul_add _ _ _
      _ ≤ s * ρ' (Metric.thickening ε.toReal B) + ε :=
          add_le_add (mul_le_mul' le_rfl (measure_mono thick)) hsK
      _ = ((s : ℝ≥0∞) • ρ') (Metric.thickening ε.toReal B) + ε := by simp [Measure.smul_apply]
  · have h1 := right_measure_le_of_levyProkhorovEDist_lt hdl hB
    calc ((s : ℝ≥0∞) • ρ') B = s * ρ' B := by simp [Measure.smul_apply]
      _ ≤ s * (ρ (Metric.thickening (ε / K).toReal B) + ε / K) := mul_le_mul' le_rfl h1
      _ = s * ρ (Metric.thickening (ε / K).toReal B) + s * (ε / K) := mul_add _ _ _
      _ ≤ s * ρ (Metric.thickening ε.toReal B) + ε :=
          add_le_add (mul_le_mul' le_rfl (measure_mono thick)) hsK
      _ = ((s : ℝ≥0∞) • ρ) (Metric.thickening ε.toReal B) + ε := by simp [Measure.smul_apply]

theorem lpDist_smul_le (s : ℝ≥0) (ρ ρ' : Measure ℝ) [IsFiniteMeasure ρ] [IsFiniteMeasure ρ'] :
    levyProkhorovDist ((s : ℝ≥0∞) • ρ) ((s : ℝ≥0∞) • ρ') ≤
      (max 1 (s : ℝ≥0∞)).toReal * levyProkhorovDist ρ ρ' := by
  have hKt : max 1 (s : ℝ≥0∞) ≠ ∞ := (max_lt ENNReal.one_lt_top ENNReal.coe_lt_top).ne
  unfold levyProkhorovDist
  rw [← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hKt (levyProkhorovEDist_ne_top _ _))
    (lpEDist_smul_le s ρ ρ')

theorem toReal_max_pos (s : ℝ≥0) : 0 < (max 1 (s : ℝ≥0∞)).toReal := by
  have hK1 : 1 ≤ max 1 (s : ℝ≥0∞) := le_max_left _ _
  have hKt : max 1 (s : ℝ≥0∞) ≠ ∞ := (max_lt ENNReal.one_lt_top ENNReal.coe_lt_top).ne
  exact ENNReal.toReal_pos (zero_lt_one.trans_le hK1).ne' hKt

/-! ### Closed-set equality from vanishing Lévy–Prokhorov distance -/

theorem eq_of_lpEDist_eq_zero (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : levyProkhorovEDist μ ν = 0) : μ = ν := by
  have hclosed : ∀ s : Set ℝ, IsClosed s → μ s = ν s := fun s hs =>
    measure_eq_measure_of_levyProkhorovEDist_eq_zero_of_isClosed h hs
      ⟨1, one_pos, measure_ne_top _ _⟩ ⟨1, one_pos, measure_ne_top _ _⟩
  exact MeasureTheory.ext_of_generate_finite {s : Set ℝ | IsClosed s} borel_eq_generateFrom_isClosed
    isPiSystem_isClosed (fun s hs => hclosed s hs) (hclosed _ isClosed_univ)

/-! ### The Born-product-law limit -/

/-- The random finite measure `m ν_N = (m/N)Σδ_{q_j}` (here `ρ = ν_N`). -/
def scaledFin (m : ℝ) (ρ : ProbabilityMeasure ℝ) : FiniteMeasure ℝ :=
  ⟨ENNReal.ofReal m • (ρ : Measure ℝ), ⟨by
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    exact ENNReal.ofReal_lt_top⟩⟩

theorem toMeasure_scaledFin (m : ℝ) (ρ : ProbabilityMeasure ℝ) :
    (scaledFin m ρ : Measure ℝ) = ENNReal.ofReal m • (ρ : Measure ℝ) := rfl

theorem Mfin_eq_scaledFin {κ : ℝ} {u : L2T L} (h : u ≠ 0) :
    Mfin κ u = scaledFin (‖u‖ ^ 2) (muKappa (unitDir u) (norm_unitDir h) (κ * ‖u‖ ^ 2)) :=
  Subtype.ext (Mmeas_of_ne κ h)

/-- **Born-product-law limit** (`prop:root-full-mass`, third clause). -/
theorem born_product_limit {κ : ℝ} (hκ : 0 < κ) {u : L2T L} (h : u ≠ 0) :
    IsLimitingRapidityMeasure L (κ * ‖u‖ ^ 2) (mul_pos hκ (pow_pos (norm_pos_iff.2 h) 2)) (unitDir u)
      (norm_unitDir h) (muKappa (unitDir u) (norm_unitDir h) (κ * ‖u‖ ^ 2)) ∧
    TendstoInProbability
      (fun N => bornMeasure (physBasis L (mul_pos hκ (pow_pos (norm_pos_iff.2 h) 2)) N) (unitDir u)
        (norm_unitDir h))
      (fun N (ω : MArr N) => (LevyProkhorov.ofMeasure
        (scaledFin (‖u‖ ^ 2) (empiricalProb L (κ * ‖u‖ ^ 2) N ω)) : LevyProkhorov (FiniteMeasure ℝ)))
      (LevyProkhorov.ofMeasure (Mfin κ u)) := by
  have hlam : 0 < κ * ‖u‖ ^ 2 := mul_pos hκ (pow_pos (norm_pos_iff.2 h) 2)
  have hv := norm_unitDir h
  have hspec := muKappa_spec (unitDir u) hv hlam
  refine ⟨hspec, ?_⟩
  intro ε hε
  set s : ℝ≥0 := (‖u‖ ^ 2).toNNReal with hs
  have hsr : ENNReal.ofReal (‖u‖ ^ 2) = (s : ℝ≥0∞) := rfl
  set Kr : ℝ := (max 1 (s : ℝ≥0∞)).toReal with hKr
  have hKpos : 0 < Kr := toReal_max_pos s
  have hlim := hspec (ε / Kr) (by positivity)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) (fun N => ?_)
  refine measure_mono (fun ω hω => ?_)
  simp only [Set.mem_setOf_eq] at hω ⊢
  rw [Mfin_eq_scaledFin h] at hω
  have hd : dist (LevyProkhorov.ofMeasure
      (scaledFin (‖u‖ ^ 2) (empiricalProb L (κ * ‖u‖ ^ 2) N ω)))
      (LevyProkhorov.ofMeasure (scaledFin (‖u‖ ^ 2) (muKappa (unitDir u) hv (κ * ‖u‖ ^ 2)))) =
      levyProkhorovDist (ENNReal.ofReal (‖u‖ ^ 2) • (empiricalProb L (κ * ‖u‖ ^ 2) N ω : Measure ℝ))
        (ENNReal.ofReal (‖u‖ ^ 2) • (muKappa (unitDir u) hv (κ * ‖u‖ ^ 2) : Measure ℝ)) := rfl
  rw [hd, hsr] at hω
  have hle := lpDist_smul_le s (empiricalProb L (κ * ‖u‖ ^ 2) N ω : Measure ℝ)
    (muKappa (unitDir u) hv (κ * ‖u‖ ^ 2) : Measure ℝ)
  have h1 : ε < Kr * levyProkhorovDist (empiricalProb L (κ * ‖u‖ ^ 2) N ω : Measure ℝ)
      (muKappa (unitDir u) hv (κ * ‖u‖ ^ 2) : Measure ℝ) := lt_of_lt_of_le hω hle
  have h2 : ε / Kr < levyProkhorovDist (empiricalProb L (κ * ‖u‖ ^ 2) N ω : Measure ℝ)
      (muKappa (unitDir u) hv (κ * ‖u‖ ^ 2) : Measure ℝ) := by
    rw [div_lt_iff₀ hKpos]; linarith
  exact h2

/-- **Uniqueness of the finite-measure limit**: `M_{κ,u}` is the only finite measure that is the limit in probability (Lévy–Prokhorov distance of finite
measures) of `m ν_N` under the Born law of `v^{⊗N}`. -/
theorem born_product_unique {κ : ℝ} (hκ : 0 < κ) {u : L2T L} (h : u ≠ 0) (M' : FiniteMeasure ℝ)
    (hM' : TendstoInProbability
      (fun N => bornMeasure (physBasis L (mul_pos hκ (pow_pos (norm_pos_iff.2 h) 2)) N) (unitDir u)
        (norm_unitDir h))
      (fun N (ω : MArr N) => (LevyProkhorov.ofMeasure
        (scaledFin (‖u‖ ^ 2) (empiricalProb L (κ * ‖u‖ ^ 2) N ω)) : LevyProkhorov (FiniteMeasure ℝ)))
      (LevyProkhorov.ofMeasure M')) :
    M' = Mfin κ u := by
  set hP := (born_product_limit hκ h).2 with hPdef
  set X := (fun N (ω : MArr N) => (LevyProkhorov.ofMeasure
        (scaledFin (‖u‖ ^ 2) (empiricalProb L (κ * ‖u‖ ^ 2) N ω)) : LevyProkhorov (FiniteMeasure ℝ))) with hX
  -- both are limits, so their distance is zero
  have hz : dist (LevyProkhorov.ofMeasure M') (LevyProkhorov.ofMeasure (Mfin κ u)) = 0 := by
    by_contra hne
    have hd : 0 < dist (LevyProkhorov.ofMeasure M') (LevyProkhorov.ofMeasure (Mfin κ u)) :=
      lt_of_le_of_ne dist_nonneg (Ne.symm hne)
    set ε := dist (LevyProkhorov.ofMeasure M') (LevyProkhorov.ofMeasure (Mfin κ u)) / 3 with hε
    have hε0 : 0 < ε := by positivity
    have h1 := hM' ε hε0
    have h2 := hP ε hε0
    have hsum := h1.add h2
    rw [add_zero] at hsum
    have hge : ∀ N, (1 : ℝ≥0∞) ≤
        (bornMeasure (physBasis L (mul_pos hκ (pow_pos (norm_pos_iff.2 h) 2)) N) (unitDir u) (norm_unitDir h))
          {ω | ε < dist (X N ω) (LevyProkhorov.ofMeasure M')} +
        (bornMeasure (physBasis L (mul_pos hκ (pow_pos (norm_pos_iff.2 h) 2)) N) (unitDir u) (norm_unitDir h))
          {ω | ε < dist (X N ω) (LevyProkhorov.ofMeasure (Mfin κ u))} := by
      intro N
      have hcov : (Set.univ : Set (MArr N)) ⊆ {ω | ε < dist (X N ω) (LevyProkhorov.ofMeasure M')} ∪
          {ω | ε < dist (X N ω) (LevyProkhorov.ofMeasure (Mfin κ u))} := by
        intro ω _
        by_contra hcon
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hcon
        have := dist_triangle_left (LevyProkhorov.ofMeasure M') (LevyProkhorov.ofMeasure (Mfin κ u)) (X N ω)
        linarith [hcon.1, hcon.2]
      calc (1 : ℝ≥0∞) = _ := (measure_univ).symm
        _ ≤ _ := measure_mono hcov
        _ ≤ _ := measure_union_le _ _
    have hlim : (1 : ℝ≥0∞) ≤ 0 := ge_of_tendsto' hsum hge
    simp at hlim
  have hedist : levyProkhorovEDist (M' : Measure ℝ) (Mfin κ u : Measure ℝ) = 0 := by
    have h0 : levyProkhorovDist (M' : Measure ℝ) (Mfin κ u : Measure ℝ) = 0 := hz
    unfold levyProkhorovDist at h0
    rcases (ENNReal.toReal_eq_zero_iff _).1 h0 with h1 | h1
    · exact h1
    · exact absurd h1 (levyProkhorovEDist_ne_top _ _)
  exact Subtype.ext (eq_of_lpEDist_eq_zero (M' : Measure ℝ) (Mfin κ u : Measure ℝ) hedist)

end QuantumNLS.FullMassLimit

#print axioms QuantumNLS.FullMassLimit.continuous_Mfin
#print axioms QuantumNLS.FullMassLimit.lpEDist_smul_le
#print axioms QuantumNLS.FullMassLimit.eq_of_lpEDist_eq_zero
#print axioms QuantumNLS.FullMassLimit.born_product_limit
#print axioms QuantumNLS.FullMassLimit.born_product_unique
