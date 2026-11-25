import Mathlib
import QuantumNLS.TotalVariation
import QuantumNLS.DiscParamContinuity
import QuantumNLS.RootDensityIdentification
import QuantumNLS.PhysicalL2Normalization
import QuantumNLS.FullMassLimit

/-!
# R-0C33082D `prop:D05-total-variation` (`D05.tex:4`)

Source statement: assuming `thm:root-spectral-density` (R-7E0532E7, `RootDensityIdentification.root_density`) and `prop:root-full-mass` (R-043AB9AA, `FullMass`,
`FullMassLimit`): for fixed `L > 0`, the map `(κ,u) ↦ M_{κ,u}` is continuous from `(0,∞) × L²(𝕋_L)` to finite measures for `‖σ‖_TV = |σ|(ℝ)`; for fixed nonzero `u`,
the weak limit `M_{κ,u} ⇀ M_{0,u}` (`κ ↓ 0`) satisfies `‖M_{κ,u} - M_{0,u}‖_TV = 2‖u‖₂²` (`κ > 0`); hence the weak convergence does not hold in total variation.

Formalization (`M_{κ,u} = FullMass.Mmeas κ u`, `‖·‖_TV = TotalVariation.tvNorm`, Mathlib's Jordan total variation of the signed measure `μ - ν`):
* `tv_continuousAt`: for `κ₀ > 0` and every `u₀`, `tvNorm (M_{κ,u}) (M_{κ₀,u₀}) → 0` as `(κ,u) → (κ₀,u₀)` in `ℝ × L²` (continuity at every point of the domain `(0,∞) × L²`,
  including `u₀ = 0`).  Proof as printed: `ρ = dens` is the density of `M` (`root_density`), `ρ_{κ,u}(t) → ρ_{κ₀,u₀}(t)` by joint continuity of the discriminant
  (`DiscParamContinuity`, Gronwall in `L¹`), `∫ρ_{κ,u} = ‖u‖²`, `‖M - M'‖_TV ≤ ∫|ρ - ρ'| = ‖u‖² + ‖u₀‖² - 2∫ min(ρ,ρ')` and dominated convergence for `min(ρ,ρ') ≤ ρ'`.
* `tv_zero_coupling`: `tvNorm (M_{κ,u}) (M_{0,u}) = 2 ‖u‖²` for `κ > 0`, `u ≠ 0` (`M_{κ,u}` absolutely continuous, `M_{0,u} = freeMeasure` atomic on the null set `2πℤ/L`; mutually singular).
* `weak_limit_zero_coupling`: the weak limit `M_{κ,u} → M_{0,u}` as `κ → 0` (from `FullMassLimit.continuous_Mfin`).
* `not_tendsto_tv_zero_coupling`: consequently `tvNorm (M_{κ,u}) (M_{0,u})` does not tend to `0` as `κ ↓ 0`: the weak convergence is not in total variation.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace QuantumNLS.D05TotalVariation

open QuantumNLS.TotalVariation (tvNorm tvNorm_mutuallySingular tvNorm_zero_right tvNorm_le_density)
open QuantumNLS.FullMass (Mmeas Mmeas_univ Mmeas_zero Mmeas_zero_coupling Mfin)
open QuantumNLS.RootDensityIdentification (dens continuous_dens dens_nonneg root_density measure_absolutelyContinuous)
open QuantumNLS.FreeLimit (freeMeasure)
open QuantumNLS.PhysicalTensor (L2T)

variable {L : ℝ} [Fact (0 < L)]

theorem tvNorm_congr {μ ν ν' : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (h : ν = ν') : tvNorm μ ν = tvNorm μ ν' := by
  subst h; rfl

/-! ### The density of `M_{κ,u}` -/

theorem Mmeas_density {κ : ℝ} (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) :
    Mmeas κ u = volume.withDensity (fun t => ENNReal.ofReal (dens κ u t)) := by
  rw [← QuantumNLS.PhysicalL2Normalization.measure_eq_Mmeas hκ u]
  exact root_density hκ hu

theorem integrable_dens {κ : ℝ} (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) :
    Integrable (dens κ u) volume ∧ ∫ t, dens κ u t = ‖u‖ ^ 2 := by
  have h1 := Mmeas_univ κ u
  rw [Mmeas_density hκ hu, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  have hint : Integrable (dens κ u) volume := by
    refine (lintegral_ofReal_ne_top_iff_integrable (continuous_dens κ u).aestronglyMeasurable
      (Eventually.of_forall (dens_nonneg hκ u))).1 ?_
    rw [h1]; exact ENNReal.ofReal_ne_top
  refine ⟨hint, ?_⟩
  have := ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (dens_nonneg hκ u))
  rw [h1] at this
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (dens_nonneg hκ u)) (sq_nonneg _)).1 this

theorem tendsto_dens {κ0 : ℝ} (hκ0 : 0 < κ0) (u0 : L2T L) (t : ℝ) :
    Tendsto (fun p : ℝ × L2T L => dens p.1 p.2 t) (𝓝 (κ0, u0)) (𝓝 (dens κ0 u0 t)) := by
  unfold dens
  have hD := QuantumNLS.DiscParamContinuity.continuous_discriminant_param (L := L) (t : ℂ)
  have hh : Continuous fun p : ℝ × L2T L =>
      QuantumNLS.RootDensity.hfun |(QuantumNLS.L2SpatialTransfer.discriminant p.1 p.2 (t : ℂ)).re| :=
    QuantumNLS.RootDensity.continuous_hfun.comp (continuous_abs.comp (Complex.continuous_re.comp hD))
  have hinv : ContinuousAt (fun p : ℝ × L2T L => (Real.pi * p.1)⁻¹) (κ0, u0) :=
    ContinuousAt.inv₀ (by fun_prop) (by positivity)
  exact (hinv.mul hh.continuousAt).tendsto

/-! ### Continuity in total variation -/

theorem tv_continuousAt_ne {κ0 : ℝ} (hκ0 : 0 < κ0) {u0 : L2T L} (hu0 : u0 ≠ 0) :
    Tendsto (fun p : ℝ × L2T L => tvNorm (Mmeas p.1 p.2) (Mmeas κ0 u0)) (𝓝 (κ0, u0)) (𝓝 0) := by
  set ρ0 : ℝ → ℝ := dens κ0 u0 with hρ0
  obtain ⟨hρ0i, hρ0m⟩ := integrable_dens hκ0 hu0
  have hev : ∀ᶠ p : ℝ × L2T L in 𝓝 (κ0, u0), 0 < p.1 ∧ p.2 ≠ 0 :=
    ((continuous_fst.tendsto _).eventually (lt_mem_nhds hκ0)).and
      ((continuous_snd.tendsto _).eventually (eventually_ne_nhds hu0))
  have hmin : Tendsto (fun p : ℝ × L2T L => ∫ t, min (dens p.1 p.2 t) (ρ0 t)) (𝓝 (κ0, u0))
      (𝓝 (∫ t, ρ0 t)) := by
    refine tendsto_integral_filter_of_dominated_convergence ρ0 ?_ ?_ hρ0i ?_
    · exact Eventually.of_forall fun p =>
        ((continuous_dens p.1 p.2).min (continuous_dens κ0 u0)).aestronglyMeasurable
    · filter_upwards [hev] with p hp
      refine Eventually.of_forall fun t => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (dens_nonneg hp.1 _ t) (dens_nonneg hκ0 _ t))]
      exact min_le_right _ _
    · refine Eventually.of_forall fun t => ?_
      have := (tendsto_dens hκ0 u0 t).min (tendsto_const_nhds (x := ρ0 t))
      rw [show min (dens κ0 u0 t) (ρ0 t) = ρ0 t from min_self _] at this
      exact this
  have hmass : Tendsto (fun p : ℝ × L2T L => ‖p.2‖ ^ 2) (𝓝 (κ0, u0)) (𝓝 (‖u0‖ ^ 2)) :=
    ((continuous_norm.comp continuous_snd).pow 2).continuousAt.tendsto
  set g : ℝ × L2T L → ℝ := fun p => ‖p.2‖ ^ 2 + (∫ t, ρ0 t) - 2 * ∫ t, min (dens p.1 p.2 t) (ρ0 t) with hg
  have hgT : Tendsto g (𝓝 (κ0, u0)) (𝓝 0) := by
    have h := (hmass.add_const (∫ t, ρ0 t)).sub (hmin.const_mul 2)
    have hρ0m' : ∫ t, ρ0 t = ‖u0‖ ^ 2 := hρ0m
    have e : (‖u0‖ ^ 2 + ∫ t, ρ0 t) - 2 * ∫ t, ρ0 t = 0 := by rw [hρ0m']; ring
    rw [e] at h
    exact h
  have hgeq : ∀ p : ℝ × L2T L, 0 < p.1 → p.2 ≠ 0 → ∫ t, |dens p.1 p.2 t - ρ0 t| = g p := by
    intro p hp1 hp2
    obtain ⟨hpi, hpm⟩ := integrable_dens hp1 hp2
    have hmini : Integrable (fun t => min (dens p.1 p.2 t) (ρ0 t)) volume := by
      refine hρ0i.mono' ((continuous_dens p.1 p.2).min (continuous_dens κ0 u0)).aestronglyMeasurable
        (Eventually.of_forall fun t => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (dens_nonneg hp1 _ t) (dens_nonneg hκ0 _ t))]
      exact min_le_right _ _
    have hfun : (fun t => |dens p.1 p.2 t - ρ0 t|) =
        fun t => (dens p.1 p.2 t + ρ0 t) - 2 * min (dens p.1 p.2 t) (ρ0 t) := by
      funext t
      rcases le_total (dens p.1 p.2 t) (ρ0 t) with h | h
      · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
      · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
    have hsum : Integrable (fun t => dens p.1 p.2 t + ρ0 t) volume := hpi.add hρ0i
    have hm2 : Integrable (fun t => 2 * min (dens p.1 p.2 t) (ρ0 t)) volume := hmini.const_mul 2
    rw [hfun, integral_sub hsum hm2, integral_add hpi hρ0i, integral_const_mul, hpm]
  have hle : ∀ᶠ p : ℝ × L2T L in 𝓝 (κ0, u0),
      tvNorm (Mmeas p.1 p.2) (Mmeas κ0 u0) ≤ ENNReal.ofReal (g p) := by
    filter_upwards [hev] with p hp
    obtain ⟨hpi, -⟩ := integrable_dens hp.1 hp.2
    rw [← hgeq p hp.1 hp.2]
    exact tvNorm_le_density (m := volume) (dens_nonneg hp.1 _) (dens_nonneg hκ0 _) hpi hρ0i _ _
      (Mmeas_density hp.1 hp.2) (Mmeas_density hκ0 hu0)
  have hup : Tendsto (fun p : ℝ × L2T L => ENNReal.ofReal (g p)) (𝓝 (κ0, u0)) (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hgT
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => bot_le) hle

theorem tv_continuousAt_zero (κ0 : ℝ) :
    Tendsto (fun p : ℝ × L2T L => tvNorm (Mmeas p.1 p.2) (Mmeas κ0 (0 : L2T L))) (𝓝 (κ0, 0)) (𝓝 0) := by
  have e : ∀ p : ℝ × L2T L, tvNorm (Mmeas p.1 p.2) (Mmeas κ0 (0 : L2T L)) =
      ENNReal.ofReal (‖p.2‖ ^ 2) := by
    intro p
    rw [tvNorm_congr (Mmeas_zero κ0), tvNorm_zero_right, Mmeas_univ]
  simp_rw [e]
  have hc : Continuous fun p : ℝ × L2T L => ‖p.2‖ ^ 2 := (continuous_norm.comp continuous_snd).pow 2
  have := ENNReal.tendsto_ofReal (hc.continuousAt (x := ((κ0, 0) : ℝ × L2T L))).tendsto
  simpa using this

/-- **Continuity of `(κ,u) ↦ M_{κ,u}` in total variation at every point of `(0,∞) × L²(𝕋_L)`** (including `u₀ = 0`). -/
theorem tv_continuousAt {κ0 : ℝ} (hκ0 : 0 < κ0) (u0 : L2T L) :
    Tendsto (fun p : ℝ × L2T L => tvNorm (Mmeas p.1 p.2) (Mmeas κ0 u0)) (𝓝 (κ0, u0)) (𝓝 0) := by
  by_cases hu0 : u0 = 0
  · subst hu0; exact tv_continuousAt_zero κ0
  · exact tv_continuousAt_ne hκ0 hu0

/-! ### Zero coupling: mutual singularity, `‖M_{κ,u} - M_{0,u}‖_TV = 2‖u‖²` -/

theorem tv_zero_coupling {κ : ℝ} (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) :
    tvNorm (Mmeas κ u) (Mmeas 0 u) = 2 * ENNReal.ofReal (‖u‖ ^ 2) := by
  set S : Set ℝ := Set.range (fun n : ℤ => 2 * Real.pi * n / L) with hS
  have hSc : S.Countable := Set.countable_range _
  have hSm : MeasurableSet S := hSc.measurableSet
  have hac : Mmeas κ u ≪ volume := by
    rw [← QuantumNLS.PhysicalL2Normalization.measure_eq_Mmeas hκ u]
    exact measure_absolutelyContinuous hκ hu
  have hμS : Mmeas κ u S = 0 := hac (hSc.measure_zero _)
  have hνS : freeMeasure L u Sᶜ = 0 := by
    unfold freeMeasure
    rw [Measure.sum_apply _ hSm.compl]
    refine ENNReal.tsum_eq_zero.2 fun n => ?_
    rw [Measure.smul_apply, Measure.dirac_apply' _ hSm.compl]
    have : (2 * Real.pi * (n : ℝ) / L) ∈ S := ⟨n, rfl⟩
    simp [this]
  have hms : Mmeas κ u ⟂ₘ freeMeasure L u := ⟨S, hSm, hμS, hνS⟩
  have : IsFiniteMeasure (freeMeasure L u) := by
    rw [← Mmeas_zero_coupling]; infer_instance
  rw [tvNorm_congr (Mmeas_zero_coupling u), tvNorm_mutuallySingular _ _ hms, Mmeas_univ]
  have : freeMeasure L u Set.univ = ENNReal.ofReal (‖u‖ ^ 2) := by
    rw [← Mmeas_zero_coupling, Mmeas_univ]
  rw [this, two_mul]

/-- The weak limit `M_{κ,u} → M_{0,u}` as `κ → 0` (continuity of `Mfin` on `[0,∞) × L²`, R-043AB9AA). -/
theorem weak_limit_zero_coupling (u : L2T L) :
    Tendsto (fun x : {κ : ℝ // 0 ≤ κ} => Mfin x.1 u) (𝓝 ⟨0, le_rfl⟩) (𝓝 (Mfin 0 u)) := by
  have h := (QuantumNLS.FullMassLimit.continuous_Mfin (L := L)).comp
    (Continuous.prodMk continuous_id (continuous_const (y := u)))
  exact h.tendsto ⟨0, le_rfl⟩

/-- **The weak convergence `M_{κ,u} ⇀ M_{0,u}` does not hold in total variation** (`u ≠ 0`). -/
theorem not_tendsto_tv_zero_coupling {u : L2T L} (hu : u ≠ 0) :
    ¬ Tendsto (fun κ : ℝ => tvNorm (Mmeas κ u) (Mmeas 0 u)) (𝓝[>] 0) (𝓝 0) := by
  intro h
  have hev : ∀ᶠ κ : ℝ in 𝓝[>] 0, tvNorm (Mmeas κ u) (Mmeas 0 u) = 2 * ENNReal.ofReal (‖u‖ ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with κ hκ
    exact tv_zero_coupling hκ hu
  have h2 : Tendsto (fun κ : ℝ => tvNorm (Mmeas κ u) (Mmeas 0 u)) (𝓝[>] 0) (𝓝 (2 * ENNReal.ofReal (‖u‖ ^ 2))) :=
    tendsto_const_nhds.congr' (hev.mono fun κ hκ => hκ.symm)
  have := tendsto_nhds_unique h2 h
  have hpos : 0 < ‖u‖ ^ 2 := by positivity
  have hne : 2 * ENNReal.ofReal (‖u‖ ^ 2) ≠ 0 := by
    simp [hpos, hu]
  exact hne this

/-- **`prop:D05-total-variation`** (all three clauses). -/
theorem prop_D05_total_variation :
    (∀ κ0 : ℝ, 0 < κ0 → ∀ u0 : L2T L,
      Tendsto (fun p : ℝ × L2T L => tvNorm (Mmeas p.1 p.2) (Mmeas κ0 u0)) (𝓝 (κ0, u0)) (𝓝 0)) ∧
    (∀ u : L2T L, u ≠ 0 →
      Tendsto (fun x : {κ : ℝ // 0 ≤ κ} => Mfin x.1 u) (𝓝 ⟨0, le_rfl⟩) (𝓝 (Mfin 0 u)) ∧
      (∀ κ : ℝ, 0 < κ → tvNorm (Mmeas κ u) (Mmeas 0 u) = 2 * ENNReal.ofReal (‖u‖ ^ 2)) ∧
      ¬ Tendsto (fun κ : ℝ => tvNorm (Mmeas κ u) (Mmeas 0 u)) (𝓝[>] 0) (𝓝 0)) :=
  ⟨fun κ0 hκ0 u0 => tv_continuousAt hκ0 u0, fun u hu =>
    ⟨weak_limit_zero_coupling u, fun κ hκ => tv_zero_coupling hκ hu, not_tendsto_tv_zero_coupling hu⟩⟩

end QuantumNLS.D05TotalVariation

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.D05TotalVariation.tv_continuousAt
#print axioms QuantumNLS.D05TotalVariation.tv_zero_coupling
#print axioms QuantumNLS.D05TotalVariation.weak_limit_zero_coupling
#print axioms QuantumNLS.D05TotalVariation.not_tendsto_tv_zero_coupling
#print axioms QuantumNLS.D05TotalVariation.prop_D05_total_variation
