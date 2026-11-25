import NlsGge.Hierarchy.FullEnergySpectralIdentification38
import NlsGge.Hierarchy.RiccatiUnitPeriodIntervalToPhysicalHaar
import NlsGge.Weights.SpatialJensen
import NlsGge.Measure.ComplexGaussian
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Tactic

/-! Batch 38, W01 (`C:prop:full-existence`, paper/v2.tex l.941-978): remaining
assertions on top of W1/W2.
* local uniform convergence of `E_W = Σ_j β_j Q_{2j}` on each finite plane;
* `Q₀ = Σ_i |z_i|²` and the mass lower bound `E_W ≥ c₋ Σ|z_i|²`;
* `0 < 𝒵_{W,N} = ∫ e^{-E_W} < ∞` for every `N ≥ 0` (integrability proved first;
  explicit upper bound `(π/c₋)^{2N+1}`). -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot NlsGge.Measure MeasureTheory Filter
open scoped ContDiff Topology

/-- `Q₀` on the plane: `∫₀¹ |u|² = Σ_i |z_i|²` (Parseval). -/
theorem localCharge38_zero_plane (N : ℕ) (z : FourierPlane N) :
    localCharge38 (planeReal N z) 0 = ∑ i : Fin (2 * N + 1), ‖z i‖ ^ 2 := by
  have hpt : ∀ x : ℝ, riccatiJetEvaluation (planeReal N z) x (formalChargeIntegrand 0) =
      ((‖planeField N z (x : PhysicalCircle)‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    simp [formalChargeIntegrand, riccatiJetEvaluation, riccatiJetFunction, polynomialEvaluation,
      p, planeReal, Complex.mul_conj', mul_comm]
  unfold localCharge38
  simp_rw [hpt]
  rw [intervalIntegral.integral_ofReal, Complex.ofReal_re,
    unitIntervalIntegral_lift_eq_spatialHaar (fun y : PhysicalCircle => ‖planeField N z y‖ ^ 2),
    NlsGge.Weights.plane_mass_integral_eq_sum]

/-- Mass lower bound `E_W ≥ c₋ Σ_i |z_i|²` (uses `Q_{2j} ≥ 0`, via the trace formula). -/
theorem fullEnergy38_ge_lower_mass {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ)
    (z : FourierPlane N) :
    lo * ∑ i : Fin (2 * N + 1), ‖z i‖ ^ 2 ≤ fullEnergy38 c N z := by
  have h := fullEnergy38_ge_mass c N z
  rw [localCharge38_zero_plane] at h
  have hc := (c.property.2.2 0).1
  have hs : 0 ≤ ∑ i : Fin (2 * N + 1), ‖z i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  nlinarith

theorem exp_neg_fullEnergy38_le {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ)
    (z : FourierPlane N) :
    Real.exp (-fullEnergy38 c N z) ≤ ∏ i, Real.exp (-lo * ‖z i‖ ^ 2) := by
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  have := fullEnergy38_ge_lower_mass c N z
  rw [Finset.mul_sum] at this
  simp only [neg_mul, Finset.sum_neg_distrib]
  linarith

/-- Integrability of the full-energy Boltzmann factor on every finite plane. -/
theorem integrable_exp_neg_fullEnergy38 {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ) :
    Integrable (fun z => Real.exp (-fullEnergy38 c N z)) (planeVolume N) := by
  have hlo := c.property.1
  have hdom : Integrable (fun z : FourierPlane N => ∏ i, Real.exp (-lo * ‖z i‖ ^ 2))
      (planeVolume N) :=
    Integrable.fintype_prod (fun _ => integrable_complexGaussianKernel lo hlo)
  refine hdom.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact (Real.continuous_exp.comp (continuous_fullEnergy38 c N).neg).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact exp_neg_fullEnergy38_le c N z

/-- `0 < 𝒵_{W,N} ≤ (π/c₋)^{2N+1}` for every `N ≥ 0`. -/
theorem partition38_pos_le {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ) :
    0 < ∫ z, Real.exp (-fullEnergy38 c N z) ∂(planeVolume N) ∧
      (∫ z, Real.exp (-fullEnergy38 c N z) ∂(planeVolume N)) ≤
        (Real.pi / lo) ^ (2 * N + 1) := by
  have hlo := c.property.1
  constructor
  · have : NeZero (planeVolume N) := by unfold planeVolume; infer_instance
    exact integral_exp_pos (integrable_exp_neg_fullEnergy38 c N)
  · calc (∫ z, Real.exp (-fullEnergy38 c N z) ∂(planeVolume N))
        ≤ ∫ z, ∏ i, Real.exp (-lo * ‖z i‖ ^ 2) ∂(planeVolume N) :=
          integral_mono (integrable_exp_neg_fullEnergy38 c N)
            (Integrable.fintype_prod (fun _ => integrable_complexGaussianKernel lo hlo))
            (fun z => exp_neg_fullEnergy38_le c N z)
      _ = ∏ _i : Fin (2 * N + 1), (Real.pi / lo) := by
          unfold planeVolume
          rw [integral_fintype_prod_eq_prod (fun _ (w : ℂ) => Real.exp (-lo * ‖w‖ ^ 2)),
            integral_complexGaussianKernel lo hlo]
      _ = (Real.pi / lo) ^ (2 * N + 1) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Local uniform convergence of the energy series on each finite plane. -/
theorem tendstoLocallyUniformly_fullEnergy38 {lo up : ℝ} (c : BoundedCoefficients lo up)
    (N : ℕ) :
    TendstoLocallyUniformly
      (fun n (z : FourierPlane N) => ∑ j ∈ Finset.range n,
        c.val j / ((j.factorial : ℝ)) ^ 4 * localCharge38 (planeReal N z) j)
      (fullEnergy38 c N) atTop := by
  refine tendstoLocallyUniformly_of_forall_exists_nhds fun z₀ => ?_
  refine ⟨Metric.ball z₀ 1, Metric.ball_mem_nhds z₀ one_pos, ?_⟩
  set A' := (2 * N + 1 : ℝ) * (‖z₀‖ + 1)
  set K' := max 1 (max (2 * Real.pi * N) A')
  have hu := summable_majorant38 up A' K'
  refine tendstoUniformlyOn_tsum_nat hu (fun j z hz => ?_)
  rw [Real.norm_eq_abs]
  have hA : planeAmp38 z ≤ A' := planeAmp38_le_of_ball z₀ z hz
  exact fullEnergy_term_le_majorant38 c N z j A' K' hA (planeK38_mono N z A' hA)

/-- Bochner form of the auxiliary lower bound (`C:eq:Zlower`): for `N ≥ 1` and
`1 ≤ c_j ≤ 2`, `𝒵_{W,N} ≥ e^{-CN²}` with an absolute `C`. -/
theorem partition_lower_bochner38 :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ c : BoundedCoefficients 1 2,
      Real.exp (-(C * (N : ℝ) ^ 2)) ≤
        ∫ z, Real.exp (-fullEnergy38 c N z) ∂(planeVolume N) := by
  obtain ⟨C, hC, h⟩ := partition_lower38
  refine ⟨C, hC, fun N hN c => ?_⟩
  have hl := h N hN c
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_fullEnergy38 c N)
    (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le)] at hl
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun z => (Real.exp_pos _).le)).mp hl

end NlsGge.HierarchyRiccati.Core

end
