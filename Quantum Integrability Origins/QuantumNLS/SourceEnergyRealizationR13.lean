import QuantumNLS.ArbitraryEnergyTraceR13
import QuantumNLS.PositiveSeriesR13

/-! Source interpretation: weighted spectral vectors may have their square-root
weights absorbed into the vectors. An arbitrary summable form-energy series
constructs the positive trace-class sandwich and its exact trace. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Filter Topology
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.SourceEnergyRealizationR13
open BoundedInverseR13 InverseSquareRootR13 ArbitraryEnergyTraceR13 PositiveSeriesR13
open TraceClass EnergyForm
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (h : LowerOne A)

/-- For any positive density decomposition in the form domain with summable
energy, construct the actual sandwich and identify its trace with the energy sum.
The decomposition is a source definition of finite expectation, not a supplied
sandwich or convergence conclusion. The family need not diagonalize A. -/
theorem energy_series (v : ι → (half A hA h).domain)
    (hv : Summable (fun i => ‖half A hA h (v i)‖^2))
    (ρ : E →L[ℂ] E)
    (hρ : HasSum (fun i => InnerProductSpace.rankOne ℂ (v i : E) (v i : E)) ρ) :
    ∃ B : E →L[ℂ] E, B.IsPositive ∧ IsTraceClass B ∧
      ρ = rootInv A hA h*B*rootInv A hA h ∧
      posTrace B = ∑' i, ENNReal.ofReal (‖half A hA h (v i)‖^2) ∧
      energyTraceNorm (rootInv A hA h) ρ = ∑' i, ENNReal.ofReal (‖half A hA h (v i)‖^2) := by
  let g := fun i => half A hA h (v i)
  let B := series g
  have hB : B.IsPositive := series_positive g hv
  have ht : IsTraceClass B := series_finite g hv
  have he : ρ = rootInv A hA h*B*rootInv A hA h := by
    have hs := (summable_rankOne g hv).hasSum
    have hc : Continuous (fun X : E →L[ℂ] E => rootInv A hA h*X*rootInv A hA h) := by fun_prop
    let F : (E →L[ℂ] E) →+ (E →L[ℂ] E) :=
      { toFun := fun X => rootInv A hA h*X*rootInv A hA h
        map_zero' := by simp
        map_add' := fun X Y => by simp only [mul_add,add_mul] }
    have hh := hs.map F hc
    have hi (i : ι) : rootInv A hA h*InnerProductSpace.rankOne ℂ (g i) (g i)*rootInv A hA h =
        InnerProductSpace.rankOne ℂ (v i : E) (v i : E) := (pure_spec A hA h (v i)).symm
    change HasSum (fun i => rootInv A hA h*InnerProductSpace.rankOne ℂ (g i) (g i)*rootInv A hA h)
      (rootInv A hA h*B*rootInv A hA h) at hh
    simp only [hi] at hh
    exact hρ.unique hh
  have htrace : posTrace B = ∑' i, ENNReal.ofReal (‖g i‖^2) := series_trace g hv
  refine ⟨B,hB,ht,he,htrace,?_⟩
  rw [energyTraceNorm_eq (rootInv_injective A hA h) (rootInv_dense A hA h) he,
    traceNorm_of_isPositive hB,htrace]

/-- Any such source decomposition gives a finite-energy density in the
arbitrary-A theorem's interface. -/
theorem finite_energy_of_series (v : ι → (half A hA h).domain)
    (hv : Summable (fun i => ‖half A hA h (v i)‖^2))
    (ρ : E →L[ℂ] E) (hp : ρ.IsPositive)
    (hρ : HasSum (fun i => InnerProductSpace.rankOne ℂ (v i : E) (v i : E)) ρ) :
    ρ.IsPositive ∧ energyTraceNorm (rootInv A hA h) ρ ≠ ⊤ := by
  obtain ⟨B,hB,ht,he,htrace,hnorm⟩ := energy_series A hA h v hv ρ hρ
  refine ⟨hp,?_⟩
  rw [hnorm,← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hv]
  exact ENNReal.ofReal_ne_top

/-- The source's positive trace-class density presented by its weighted
form-domain vectors, with square-root weights absorbed. -/
structure SourceDensity where
  density : E →L[ℂ] E
  positive : density.IsPositive
  vectors : ℕ → (half A hA h).domain
  finite_energy : Summable (fun i => ‖half A hA h (vectors i)‖^2)
  density_sum : HasSum (fun i => InnerProductSpace.rankOne ℂ (vectors i : E) (vectors i : E)) density

def sourceEnergy (ρ : SourceDensity A hA h) : ℝ := ∑' i, ‖half A hA h (ρ.vectors i)‖^2

def lift (ρ : SourceDensity A hA h) : FiniteEnergy A hA h :=
  ⟨ρ.density,finite_energy_of_series A hA h ρ.vectors ρ.finite_energy ρ.density ρ.positive ρ.density_sum⟩

theorem sourceEnergy_nonneg (ρ : SourceDensity A hA h) : 0 ≤ sourceEnergy A hA h ρ :=
  tsum_nonneg (fun i => sq_nonneg ‖half A hA h (ρ.vectors i)‖)

theorem lift_energy (ρ : SourceDensity A hA h) :
    energyTraceNorm (rootInv A hA h) (lift A hA h ρ).val = ENNReal.ofReal (sourceEnergy A hA h ρ) := by
  obtain ⟨B,hB,ht,he,htrace,hnorm⟩ :=
    energy_series A hA h ρ.vectors ρ.finite_energy ρ.density ρ.density_sum
  change energyTraceNorm (rootInv A hA h) ρ.density = _
  rw [hnorm,← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) ρ.finite_energy]
  rfl

/-- The source energy is independent of its positive density decomposition. -/
theorem sourceEnergy_independent (ρ σ : SourceDensity A hA h) (hd : ρ.density = σ.density) :
    sourceEnergy A hA h ρ = sourceEnergy A hA h σ := by
  have hρ := lift_energy A hA h ρ
  have hσ := lift_energy A hA h σ
  change energyTraceNorm (rootInv A hA h) ρ.density = _ at hρ
  change energyTraceNorm (rootInv A hA h) σ.density = _ at hσ
  have he := hρ.symm.trans ((congrArg (energyTraceNorm (rootInv A hA h)) hd).trans hσ)
  have hh := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (sourceEnergy_nonneg A hA h ρ),
    ENNReal.toReal_ofReal (sourceEnergy_nonneg A hA h σ)] using hh

/-- Source formulation, using the energy sum of the density decomposition.
No eigenvectors for A, spectral projections, or unbounded PVM are inputs. -/
theorem R_6EA807B1_source {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (f : T → (half A hA h).domain)
    (hf : Continuous (fun t => ((f t : E),half A hA h (f t))))
    (hunit : ∀ t, ‖(f t : E)‖ = 1)
    (ρ : ℕ → T → SourceDensity A hA h)
    (htrace : ∀ n t, posTrace (ρ n t).density = 1)
    (hconv : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, ∀ t,
      traceNorm ((ρ n t).density-InnerProductSpace.rankOne ℂ (f t : E) (f t : E)) ≤ ENNReal.ofReal ε)
    (henergy : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, ∀ t,
      |sourceEnergy A hA h (ρ n t)-‖half A hA h (f t)‖^2| ≤ ε) :
    Filter.Tendsto (fun n => ⨆ t,
      energyTraceNorm (rootInv A hA h)
        ((ρ n t).density-InnerProductSpace.rankOne ℂ (f t : E) (f t : E))) Filter.atTop (nhds 0) := by
  apply ArbitraryEnergyTraceR13.R_6EA807B1 A hA h f hf hunit
    (fun n t => lift A hA h (ρ n t)) htrace hconv
  intro ε hε
  filter_upwards [henergy ε hε] with n hn
  intro t
  simpa only [lift_energy,ENNReal.toReal_ofReal (sourceEnergy_nonneg A hA h (ρ n t))] using hn t
end QuantumNLS.SourceEnergyRealizationR13
