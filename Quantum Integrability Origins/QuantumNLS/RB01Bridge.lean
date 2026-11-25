import Mathlib
import QuantumNLS.RB01Matrix
import QuantumNLS.RootIndexedMasses

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01-8: the bridge from the interval carrier `L²(0,L;ℂ)` (on which
stages RB01-1..7 work) to the physical carrier `L²(𝕋_L)` (on which the DEF-014 discriminant
`L2SpatialTransfer.discriminant` and the root-indexed masses `RootIndexedMasses.masses` are defined).

The bridge is the accepted LOCAL-001 isometry `Local002Bridge.toInterval : L²(𝕋_L) ≃ₗᵢ L²(0,L)`; every spectral object
of the B01 chain depends only on the a.e. class of the potential (`Local002Bridge.*_congr`), and the interval class of
`toInterval v` is the DEF-001 representative `circleRep v` (`toInterval_coe`), which is *definitionally* the profile
`L2SpatialTransfer.profile v` entering the DEF-014 discriminant (`circleRep_eq_profile`).
* `analyticOnNhd_toInterval`: real analyticity on `B(toInterval v₀, ρ)` transfers to real analyticity of the composite on
  `B(v₀, ρ)`.
* `compressionMatrix_congr`, `dressedIntegral_congr`.
* **`tail_matrix_profile`**: `RB01Matrix.tail_matrix_analytic` on `L²(𝕋_L)`, all objects at the profile `circleRep v`.
* **`tail_entries_profile`**: `RB01Matrix.tail_entries_analytic` on `L²(𝕋_L)`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.RB01Bridge
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002Bridge QuantumNLS.PhysicalTensor
  QuantumNLS.RB01SquareSmall QuantumNLS.RB01Resolvent QuantumNLS.RB01Matrix

variable {L κ : ℝ}

/-- The DEF-001 representative is the DEF-014 profile. -/
theorem circleRep_eq_profile [Fact (0 < L)] (v : L2T L) :
    circleRep v = QuantumNLS.L2SpatialTransfer.profile v := rfl

theorem toInterval_mem_ball [Fact (0 < L)] {v₀ v : L2T L} {ρ : ℝ} (hv : v ∈ ball v₀ ρ) :
    toInterval L v ∈ ball (toInterval L v₀) ρ := by
  rw [mem_ball, dist_eq_norm, ← map_sub, norm_toInterval, ← dist_eq_norm]
  exact hv

theorem analyticOnNhd_toInterval [Fact (0 < L)] {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {F : Lp ℂ 2 (μI L) → X} {v₀ : L2T L} {ρ : ℝ} (hF : AnalyticOnNhd ℝ F (ball (toInterval L v₀) ρ)) :
    AnalyticOnNhd ℝ (fun v => F (toIntervalR L v)) (ball v₀ ρ) := fun v hv =>
  AnalyticAt.comp (g := F) (f := fun v => toIntervalR L v) (hF _ (toInterval_mem_ball hv))
    ((toIntervalR L).analyticAt v)

theorem compressionMatrix_congr {u u' : ℝ → ℂ} (h : u =ᵐ[μI L] u') (n : ℤ) (r : ℝ) :
    compressionMatrix L κ u n r = compressionMatrix L κ u' n r := by
  unfold compressionMatrix
  rw [perturbedProj_congr h]

theorem dressedIntegral_congr {u u' : ℝ → ℂ} (h : u =ᵐ[μI L] u') (n : ℤ) (r : ℝ) :
    dressedIntegral L κ u n r = dressedIntegral L κ u' n r := by
  unfold dressedIntegral
  simp only [resolvent_congr h]

/-- **The `ℓ²` matrix families on `L²(𝕋_L)`**: `RB01Matrix.tail_matrix_analytic` transported by `toInterval`, with
every spectral object taken at the DEF-001/DEF-014 profile `circleRep v`. -/
theorem tail_matrix_profile [Fact (0 < L)] (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L)
    (v₀ : L2T L) :
    ∃ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∃ Sf Kf Bf : L2T L → MS,
      AnalyticOnNhd ℝ Sf (ball v₀ ρ) ∧ AnalyticOnNhd ℝ Kf (ball v₀ ρ) ∧ AnalyticOnNhd ℝ Bf (ball v₀ ρ) ∧
      ∀ v ∈ ball v₀ ρ, ∀ n : ℤ,
        ((N : ℝ) < |(n : ℝ)| →
          SqSmall L κ r n (toInterval L v) ∧ ‖compressionMatrix L κ (circleRep v) n r - 1‖ ≤ 1 / 2 ∧
          (Sf v : ℤ → Mat) n = compressionMatrix L κ (circleRep v) n r - 1 ∧
          (Kf v : ℤ → Mat) n =
            ContinuousLinearMap.adjoint (embed L n) ∘L dressedIntegral L κ (circleRep v) n r ∘L embed L n ∧
          (Bf v : ℤ → Mat) n = invSqrtM (compressionMatrix L κ (circleRep v) n r) * (Kf v : ℤ → Mat) n *
            invSqrtM (compressionMatrix L κ (circleRep v) n r)) ∧
        (|(n : ℝ)| ≤ N → (Sf v : ℤ → Mat) n = 0 ∧ (Kf v : ℤ → Mat) n = 0 ∧ (Bf v : ℤ → Mat) n = 0) := by
  obtain ⟨N, ρ, hρ, Sf, Kf, Bf, hS, hK, hB, h⟩ := tail_matrix_analytic (κ := κ) hL hr hr2 (toInterval L v₀)
  refine ⟨N, ρ, hρ, fun v => Sf (toIntervalR L v), fun v => Kf (toIntervalR L v), fun v => Bf (toIntervalR L v),
    analyticOnNhd_toInterval hS, analyticOnNhd_toInterval hK, analyticOnNhd_toInterval hB,
    fun v hv n => ⟨fun hn => ?_, fun hn => (h _ (toInterval_mem_ball hv) n).2 hn⟩⟩
  have e := toInterval_coe L v
  have hC := compressionMatrix_congr (κ := κ) e n r
  have hD := dressedIntegral_congr (κ := κ) e n r
  rw [← hC, ← hD]
  exact (h _ (toInterval_mem_ball hv) n).1 hn

/-- **Entries of `B_n - p_n` on `L²(𝕋_L)`** (`b_n`, `a_n - p_n`, `b_n^♯` for `v = (1,0), j = 1`; `v = (1,0), j = 0`;
`v = (0,1), j = 0`), real analytic into `ℓ²(ℤ; ℂ)` near every `v₀`, at the profile `circleRep v`. -/
theorem tail_entries_profile [Fact (0 < L)] (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L)
    (v₀ : L2T L) :
    ∃ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∃ bf : E2 → Fin 2 → L2T L → lp (fun _ : ℤ => ℂ) 2,
      (∀ w j, AnalyticOnNhd ℝ (bf w j) (ball v₀ ρ)) ∧
      ∀ v ∈ ball v₀ ρ, ∀ n : ℤ, ∀ w j,
        ((N : ℝ) < |(n : ℝ)| →
          SqSmall L κ r n (toInterval L v) ∧ ‖compressionMatrix L κ (circleRep v) n r - 1‖ ≤ 1 / 2 ∧
          (bf w j v : ℤ → ℂ) n = ((invSqrtM (compressionMatrix L κ (circleRep v) n r) *
            (ContinuousLinearMap.adjoint (embed L n) ∘L dressedIntegral L κ (circleRep v) n r ∘L embed L n) *
            invSqrtM (compressionMatrix L κ (circleRep v) n r)) w) j) ∧
        (|(n : ℝ)| ≤ N → (bf w j v : ℤ → ℂ) n = 0) := by
  obtain ⟨N, ρ, hρ, bf, hb, h⟩ := tail_entries_analytic (κ := κ) hL hr hr2 (toInterval L v₀)
  refine ⟨N, ρ, hρ, fun w j v => bf w j (toIntervalR L v), fun w j => analyticOnNhd_toInterval (hb w j),
    fun v hv n w j => ⟨fun hn => ?_, fun hn => (h _ (toInterval_mem_ball hv) n w j).2 hn⟩⟩
  have e := toInterval_coe L v
  have hC := compressionMatrix_congr (κ := κ) e n r
  have hD := dressedIntegral_congr (κ := κ) e n r
  rw [← hC, ← hD]
  exact (h _ (toInterval_mem_ball hv) n w j).1 hn

end QuantumNLS.RB01Bridge
#print axioms QuantumNLS.RB01Bridge.circleRep_eq_profile
#print axioms QuantumNLS.RB01Bridge.analyticOnNhd_toInterval
#print axioms QuantumNLS.RB01Bridge.tail_matrix_profile
#print axioms QuantumNLS.RB01Bridge.tail_entries_profile
