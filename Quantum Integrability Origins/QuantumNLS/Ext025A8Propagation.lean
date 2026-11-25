import QuantumNLS.Ext025A8SourceHartree
import QuantumNLS.Ext025A8Global

/-! The classical GP-04 application in PROP-001: the literal bounded
autonomous interaction series has a unique global C1 unit-sphere solution. Neither a
global solution nor a local flow map is supplied as an assumption. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators InnerProductSpace NNReal
namespace QuantumNLS.Ext025A8
open TensorCarrier TensorPlacements
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H

theorem prop001_application
    (A : ∀ n : ℕ, SymSector ℂ H (n + 1) →L[ℂ] SymSector ℂ H (n + 1))
    (hA : ∀ n, IsSelfAdjoint (A n)) {a : ℝ} (ha : 0 < a)
    (hs : Summable (fun n => (n + 1 : ℕ) * ‖A n‖ * Real.exp (a * n)))
    {u : H} (hu : ‖u‖ = 1) :
    ∃ α : ℝ → H, α 0 = u ∧ ContDiff ℝ 1 α ∧
      (∀ t, ‖α t‖ = 1 ∧ HasDerivAt α (sourceHartreeField A (α t)) t) ∧
      (∀ β : ℝ → H, β 0 = u →
        (∀ t, ‖β t‖ = 1 ∧ HasDerivAt β (sourceHartreeField A (β t)) t) → β = α) := by
  let B := fun n => extendSymKernel (A n)
  have hB (n : ℕ) : IsSelfAdjoint (B n) := source_kernel_selfAdjoint (A n) (hA n)
  obtain ⟨S, hS, hv, hd⟩ := exponential_rank_margin ha (fun n => norm_nonneg (B n))
    (source_rank_summable A hs)
  have hS0 : 0 ≤ S := (zero_lt_one.trans hS).le
  obtain ⟨M, L, hM, hL⟩ := hartreeField_ball_bounds B hS0 hv hd
  obtain ⟨δ, hδ, hlocal⟩ := bounded_ball_picard hS hM hL
  let K : Set H := {x | ‖x‖ = 1}
  have hsub : K ⊆ closedBall (0 : H) S := by
    intro x hx
    rw [mem_closedBall_zero_iff, hx]
    exact hS.le
  have hlocalK : ∀ x ∈ K, ∃ γ : ℝ → H, γ 0 = x ∧
      SolOn (hartreeField B) K γ (Ioo (-δ) δ) := by
    intro x hx
    obtain ⟨γ, _, hγ0, hm, hγ⟩ := hlocal x (le_of_eq hx) 0
    have ht₀ : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
    have hγ' : ∀ t ∈ Ioo (-δ) δ, HasDerivAt γ (hartreeField B (γ t)) t := by
      simpa only [zero_sub, zero_add] using hγ
    have hmass := hartree_mass_on_interval B hB ht₀ hγ'
      (fun t _ => hartree_series_summable B hS0 hv (mem_closedBall_zero_iff.mp (hm t)))
    refine ⟨γ, hγ0, fun t ht => ⟨hγ' t ht, ?_⟩⟩
    change ‖γ t‖ = 1
    rw [hmass t ht, hγ0]
    exact hx
  obtain ⟨α, hα0, hα⟩ := uniform_invariant_global (hL.mono hsub) hδ hlocalK hu
  have hαcont : Continuous α := continuous_iff_continuousAt.mpr
    (fun t => (hα t).1.continuousAt)
  have hcont : Continuous (fun t => hartreeField B (α t)) :=
    hL.continuousOn.comp_continuous hαcont (fun t => hsub (hα t).2)
  have hC1 : ContDiff ℝ 1 α := contDiff_one_iff_deriv.mpr
    ⟨fun t => (hα t).1.differentiableAt, by
      have heq : deriv α = fun t => hartreeField B (α t) :=
        funext (fun t => (hα t).1.deriv)
      rw [heq]
      exact hcont⟩
  refine ⟨α, hα0, hC1, fun t => ⟨(hα t).2, (hα t).1⟩, ?_⟩
  intro β hβ0 hβ
  apply ODE_solution_unique_univ (fun _ => hL.mono hsub)
    (fun t => ⟨(hβ t).2, (hβ t).1⟩) hα
  exact hβ0.trans hα0.symm
end QuantumNLS.Ext025A8

#print axioms QuantumNLS.Ext025A8.prop001_application
