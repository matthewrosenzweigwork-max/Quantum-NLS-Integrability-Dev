import Mathlib
import QuantumNLS.RootPoissonDensity
import QuantumNLS.PhysicalPhaseHeightBoundary
import QuantumNLS.RootTraceSymbolFinal
import QuantumNLS.RootSpectralDensityFinal
import QuantumNLS.BulkResponseActual

/-!
# R-7E0532E7 item (3): identification `dμ_{κ,u}/dt = rootDensity κ Δ_u` (`eq:root-explicit-density`)

Source: `ROOT_spectral_density.tex`, `thm:root-spectral-density`, from "Fix `t ∈ ℝ` and let `z → t` from above" through "proves (eq:root-explicit-density)".

Inputs, all imported read-only (nothing re-proved, no EXT-025 contract):
* Sol's `PhysicalPhaseHeightBoundary.uniform_boundary_height` (locally uniform `Im γ(t+iη) → hfun|Δ(t)|`), whose only analytic premise is
  `PhysicalTraceSymbolDependency.TraceSymbolIdentity L κ u`;
* sonnet_fourier's `RootTraceSymbolFinal.traceSymbolIdentity` (which discharges that premise for every physical `u`);
* `RootPoissonDensity.measure_eq_withDensity` (Poisson inversion: finite `M`, continuous `ρ ≥ 0`, `poisson η M / π → ρ` locally uniformly ⟹ `M = ρ dt`);
* the R-09E1EAE9 canonical measure `PhysicalQuantumMeasure.measure` (`= μ_{κ,u}` for `‖u‖ = 1`, `M_{κ,u}` in general).

Results (`Δ` := `L2SpatialTransfer.discriminant κ u`, entire, real on `ℝ`):
* `poisson_eq_height`: `poisson η M x = (Im γ(x+iη) − Lη/2)/κ` for `γ = Lz/2 − κG_M` (the source's `−Im g = (y − Lη/2)/κ`);
* `root_density_cond`: for `u ≠ 0`, conditional ONLY on `TraceSymbolIdentity L κ u`,
  `measure hκ u = volume.withDensity (ofReal ∘ (t ↦ (πκ)⁻¹ hfun |Re Δ(t)|))`;
* `root_density`: the same, unconditionally;
* `root_density_rep`: for a continuous `L`-periodic representative `uf` (`BulkResponseActual.IsPeriodicRepresentative`), `HasRootDensity L κ uf (measure hκ u)`, i.e. the density
  `rootDensityFormula L κ uf` of `BulkResponseActual`, and the structural conclusions (absolute continuity, bound, support `= closure {|Δ| > 2}`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped Real ENNReal

noncomputable section

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace QuantumNLS.RootDensityIdentification

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.PhysicalQuantumMeasure (measure)
open QuantumNLS.SpatialTransfer (boundaryPhase)
open QuantumNLS.EmpiricalRapidity (cauchyTransform)
open QuantumNLS.CauchyUniqueness (poisson pk)
open QuantumNLS.RootDensity (hfun continuous_hfun hfun_nonneg rootDensity)
open QuantumNLS.BulkResponseActual (rootDensityFormula HasRootDensity IsPeriodicRepresentative)

variable {L κ : ℝ} [Fact (0 < L)]

/-! ### The L² discriminant of a periodic representative -/

theorem disc_eq_rep {u : L2T L} {uf : ℝ → ℂ} (hrep : IsPeriodicRepresentative L u uf) (κ : ℝ) (z : ℂ) :
    QuantumNLS.L2SpatialTransfer.discriminant κ u z = QuantumNLS.SpatialTransfer.discriminant L κ uf z := by
  have hL : 0 < L := Fact.out
  obtain ⟨hcont, -, hae⟩ := hrep
  have h1 := QuantumNLS.L2SpatialTransfer.profile_ae_of_representative u
    (v := fun x : AddCircle L => uf ((AddCircle.equivIco L 0 x : ℝ))) hae.symm
  have hne : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) L)), x ≠ L :=
    ae_restrict_of_ae (by
      filter_upwards [(Set.countable_singleton L).ae_notMem (volume : Measure ℝ)] with x hx
      simpa using hx)
  have h2 : (fun x : ℝ => uf ((AddCircle.equivIco L 0 (x : AddCircle L) : ℝ))) =ᵐ[volume.restrict (Icc (0 : ℝ) L)] uf := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, hne] with x hx hx'
    have : (AddCircle.equivIco L 0 (x : AddCircle L) : ℝ) = x :=
      AddCircle.equivIco_coe_of_mem (by simpa using ⟨hx.1, lt_of_le_of_ne hx.2 hx'⟩)
    rw [this]
  have h3 : QuantumNLS.L2SpatialTransfer.profile u =ᵐ[volume.restrict (Icc (0 : ℝ) L)] uf := h1.symm.trans h2
  unfold QuantumNLS.L2SpatialTransfer.discriminant QuantumNLS.L2SpatialTransfer.spatialTransfer
  have hA : QuantumNLS.SpatialTransfer.balCoef κ (QuantumNLS.L2SpatialTransfer.profile u) z
      =ᵐ[volume.restrict (Icc (0 : ℝ) L)] QuantumNLS.SpatialTransfer.balCoef κ uf z := by
    filter_upwards [h3] with s hs
    simp only [QuantumNLS.SpatialTransfer.balCoef, QuantumNLS.SpatialTransfer.coef, hs]
  rw [QuantumNLS.L1SpatialTransfer.transfer_eq_of_ae hL.le hA ⟨hL.le, le_rfl⟩]
  have := QuantumNLS.L2SpatialTransfer.transfer_eq_frozen (L := L) κ hcont z ⟨hL.le, le_rfl⟩
  unfold QuantumNLS.SpatialTransfer.discriminant
  rw [this]

/-! ### Poisson smoothing and the phase height -/

theorem im_cauchy (M : Measure ℝ) [IsFiniteMeasure M] (t : ℝ) {η : ℝ} (hη : 0 < η) :
    (cauchyTransform M ((t : ℂ) + η * Complex.I)).im = -poisson η M t := by
  have hz : ((t : ℂ) + η * Complex.I).im ≠ 0 := by simpa using hη.ne'
  have hint := QuantumNLS.EmpiricalRapidity.integrable_cauchyIntegrand M ((t : ℂ) + η * Complex.I) hz
  unfold cauchyTransform poisson
  have := Complex.imCLM.integral_comp_comm hint
  simp only [Complex.imCLM_apply] at this
  rw [← this, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only []
  rw [QuantumNLS.EmpiricalRapidity.im_cauchyIntegrand, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero, sub_zero]
  unfold pk
  have : (t - s) * (t - s) + η * η = η ^ 2 + (t - s) ^ 2 := by ring
  rw [this]
  ring

theorem im_phase (M : Measure ℝ) [IsFiniteMeasure M] (z : ℂ) :
    (boundaryPhase L κ M z).im = L * z.im / 2 - κ * (cauchyTransform M z).im := by
  unfold boundaryPhase
  simp [Complex.mul_im, Complex.sub_im]
  try ring

/-- `poisson η M x = (Im γ(x+iη) − Lη/2)/κ` (the source's `−Im g = (y − Lη/2)/κ`). -/
theorem poisson_eq_height (hκ : 0 < κ) (M : Measure ℝ) [IsFiniteMeasure M] (x : ℝ) {η : ℝ} (hη : 0 < η) :
    poisson η M x = ((boundaryPhase L κ M ((x : ℂ) + η * Complex.I)).im - L * η / 2) / κ := by
  have h := im_phase (L := L) (κ := κ) M ((x : ℂ) + η * Complex.I)
  rw [im_cauchy M x hη] at h
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_add] at h
  field_simp
  linarith

/-! ### The density -/

/-- The density `ρ(t) = (πκ)⁻¹ hfun |Re Δ(t)|` of the canonical measure for the `L²` discriminant. -/
def dens (κ : ℝ) (u : L2T L) (t : ℝ) : ℝ :=
  (Real.pi * κ)⁻¹ * hfun |(QuantumNLS.L2SpatialTransfer.discriminant κ u (t : ℂ)).re|

theorem continuous_dens (κ : ℝ) (u : L2T L) : Continuous (dens κ u) := by
  unfold dens
  have hd : Continuous fun t : ℝ => QuantumNLS.L2SpatialTransfer.discriminant κ u (t : ℂ) :=
    (QuantumNLS.PhysicalUpperTraceIdentity.entire_discriminant κ u).continuous.comp Complex.continuous_ofReal
  exact continuous_const.mul (continuous_hfun.comp (continuous_abs.comp (Complex.continuous_re.comp hd)))

theorem dens_nonneg (hκ : 0 < κ) (u : L2T L) (t : ℝ) : 0 ≤ dens κ u t := by
  unfold dens
  exact mul_nonneg (inv_nonneg.2 (by positivity)) (hfun_nonneg _)

/-- **Density identification, conditional only on the trace-symbol identity.** -/
theorem root_density_cond (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0)
    (htrace : QuantumNLS.PhysicalTraceSymbolDependency.TraceSymbolIdentity L κ u) :
    measure hκ u = volume.withDensity (fun t => ENNReal.ofReal (dens κ u t)) := by
  refine QuantumNLS.RootPoissonDensity.measure_eq_withDensity (measure hκ u) (dens κ u)
    (continuous_dens κ u) (dens_nonneg hκ u) ?_
  intro K hK
  have hunif := QuantumNLS.PhysicalPhaseHeightBoundary.uniform_boundary_height hκ hu htrace hK
  rw [Metric.tendstoUniformlyOn_iff] at hunif ⊢
  intro ε hε
  have hπκ : 0 < Real.pi * κ := by positivity
  have hε' : 0 < Real.pi * κ * ε / 2 := by positivity
  have hLη : ∀ᶠ η : ℝ in 𝓝[>] 0, L * η / 2 < Real.pi * κ * ε / 2 := by
    have : Tendsto (fun η : ℝ => L * η / 2) (𝓝[>] 0) (𝓝 (L * 0 / 2)) :=
      ((continuous_const.mul continuous_id).div_const 2).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    rw [mul_zero, zero_div] at this
    exact this.eventually (gt_mem_nhds hε')
  filter_upwards [hunif (Real.pi * κ * ε / 2) hε', hLη, self_mem_nhdsWithin] with η h1 h2 hη x hx
  have hη' : 0 < η := hη
  have hy := h1 x hx
  rw [Real.dist_eq] at hy ⊢
  rw [poisson_eq_height (L := L) hκ (measure hκ u) x hη']
  unfold dens
  have e : (Real.pi * κ)⁻¹ * hfun |(QuantumNLS.L2SpatialTransfer.discriminant κ u (x : ℂ)).re| -
      ((boundaryPhase L κ (measure hκ u) ((x : ℂ) + η * Complex.I)).im - L * η / 2) / κ / Real.pi =
      (hfun |(QuantumNLS.L2SpatialTransfer.discriminant κ u (x : ℂ)).re| -
        (boundaryPhase L κ (measure hκ u) ((x : ℂ) + η * Complex.I)).im + L * η / 2) / (Real.pi * κ) := by
    field_simp
    try ring
  have hL0 : 0 < L * η / 2 := by have := (Fact.out : 0 < L); positivity
  rw [e, abs_div, abs_of_pos hπκ, div_lt_iff₀ hπκ]
  have hy' := abs_lt.1 hy
  rw [abs_lt]
  constructor <;> linarith [hy'.1, hy'.2]

/-- **Density identification (`eq:root-explicit-density`), unconditional.** For every nonzero physical `u`, the canonical quantum measure is absolutely
continuous with the continuous density `(πκ)⁻¹ arcosh(|Δ_u(t)|/2)` on `{|Δ_u| > 2}` and `0` elsewhere. -/
theorem root_density (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) :
    measure hκ u = volume.withDensity (fun t => ENNReal.ofReal (dens κ u t)) :=
  root_density_cond hκ hu (QuantumNLS.RootTraceSymbolFinal.traceSymbolIdentity hκ.le u)

theorem measure_absolutelyContinuous (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) :
    measure hκ u ≪ volume := by
  rw [root_density hκ hu]
  exact withDensity_absolutelyContinuous _ _

/-! ### Continuous periodic representative: the printed formula -/

theorem norm_disc_eq {uf : ℝ → ℂ} (hcont : Continuous uf) (t : ℝ) :
    ‖QuantumNLS.SpatialTransfer.discriminant L κ uf (t : ℂ)‖ =
      |(QuantumNLS.SpatialTransfer.discriminant L κ uf (t : ℂ)).re| := by
  have hreal : (QuantumNLS.SpatialTransfer.discriminant L κ uf (t : ℂ)).im = 0 :=
    QuantumNLS.RootDiscriminant.discriminant_im_eq_zero L κ hcont t
  rw [Complex.norm_def, Complex.normSq_apply, hreal, mul_zero, add_zero, Real.sqrt_mul_self_eq_abs]

theorem rootDensityFormula_eq_rootDensity {uf : ℝ → ℂ} (hcont : Continuous uf) (t : ℝ) :
    rootDensityFormula L κ uf t = rootDensity κ (QuantumNLS.RootDiscriminant.discReal L κ uf) t := by
  unfold rootDensityFormula rootDensity QuantumNLS.RootDiscriminant.discReal hfun
  rw [norm_disc_eq hcont]
  split_ifs with h
  · rw [div_eq_inv_mul]
  · simp

theorem dens_eq_formula {u : L2T L} {uf : ℝ → ℂ} (hrep : IsPeriodicRepresentative L u uf) (t : ℝ) :
    dens κ u t = rootDensityFormula L κ uf t := by
  rw [rootDensityFormula_eq_rootDensity hrep.1]
  unfold dens rootDensity QuantumNLS.RootDiscriminant.discReal
  rw [disc_eq_rep hrep]

/-- **The printed statement**: `μ = volume.withDensity (rootDensityFormula)`, i.e. `HasRootDensity`. -/
theorem root_density_rep (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) {uf : ℝ → ℂ}
    (hrep : IsPeriodicRepresentative L u uf) : HasRootDensity L κ uf (measure hκ u) := by
  unfold HasRootDensity
  rw [root_density hκ hu]
  congr 1
  funext t
  rw [dens_eq_formula hrep]

/-- Structural conclusions for the canonical measure of a nonzero `u` with a continuous periodic representative: the bound `ρ ≤ ‖uf‖_{L¹}/(π√κ)`, and
`support = closure {|Δ| > 2}`. -/
theorem root_density_structure (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) {uf : ℝ → ℂ}
    (hrep : IsPeriodicRepresentative L u uf) :
    measure hκ u ≪ volume ∧
    (∀ t, dens κ u t ≤ (∫ x in (0 : ℝ)..L, ‖uf x‖) / (Real.pi * Real.sqrt κ)) ∧
    (measure hκ u).support = closure {t : ℝ | 2 < |QuantumNLS.RootDiscriminant.discReal L κ uf t|} := by
  have hL : 0 < L := Fact.out
  obtain ⟨-, -, hbound, -, -, -, hsupp⟩ := QuantumNLS.RootSpectralDensityFinal.root_density_structure_final L κ hL hκ hrep.1
  have hdens : ∀ t, dens κ u t = rootDensity κ (QuantumNLS.RootDiscriminant.discReal L κ uf) t := by
    intro t
    rw [dens_eq_formula hrep, rootDensityFormula_eq_rootDensity hrep.1 t]
  refine ⟨measure_absolutelyContinuous hκ hu, fun t => (hdens t) ▸ hbound t, ?_⟩
  rw [root_density hκ hu]
  have : (fun t => ENNReal.ofReal (dens κ u t)) = fun t => ENNReal.ofReal
      (rootDensity κ (QuantumNLS.RootDiscriminant.discReal L κ uf) t) := funext fun t => by rw [hdens]
  rw [this]
  exact hsupp

end QuantumNLS.RootDensityIdentification

#print axioms QuantumNLS.RootDensityIdentification.disc_eq_rep
#print axioms QuantumNLS.RootDensityIdentification.poisson_eq_height
#print axioms QuantumNLS.RootDensityIdentification.root_density_cond
#print axioms QuantumNLS.RootDensityIdentification.root_density
#print axioms QuantumNLS.RootDensityIdentification.root_density_rep
