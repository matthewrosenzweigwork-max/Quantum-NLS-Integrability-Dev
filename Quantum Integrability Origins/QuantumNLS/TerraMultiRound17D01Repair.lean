import QuantumNLS.TerraMultiRound15D01Partial
import QuantumNLS.Ext025A6CompactFlow
import QuantumNLS.Ext025AFoundations

/-! R-B390B5E9 partial: analytic regularity of the actual field and local
solutions, under the printed reconstruction hypotheses. Completeness,
analytic dependence of the flow, and pullback identities are not asserted. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open Set Metric InnerProductSpace
namespace QuantumNLS.TerraMultiRound17D01Repair
open QuantumNLS.D01LocalPrimitive QuantumNLS.RealAnalyticDef

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def inverseW : (H →L[ℝ] ℝ) →L[ℝ] H :=
  LinearMap.mkContinuous
    { toFun := fun l => ((-Complex.I) / 2) • (toDual ℝ H).symm l
      map_add' := fun l m => by simp only [map_add, smul_add]
      map_smul' := fun c l => by
        change ((-Complex.I) / 2) • ((toDual ℝ H).symm (c • l)) =
          c • (((-Complex.I) / 2) • ((toDual ℝ H).symm l))
        rw [map_smul]
        exact smul_comm _ _ _ }
    (1 / 2) (fun l => by
      change ‖((-Complex.I) / 2) • ((toDual ℝ H).symm l)‖ ≤ (1 / 2) * ‖l‖
      rw [norm_smul, LinearIsometryEquiv.norm_map]
      have h : ‖(-Complex.I) / 2‖ = 1 / 2 := by simp
      rw [h])

private theorem inverseW_eq (l : H →L[ℝ] ℝ) : inverseW l = Winv l := by
  apply Winv_unique
  intro h
  exact QuantumNLS.Ext025A.gp06_hamiltonian_normalization l h

/-- The given vector field is analytic and has local integral curves, including
uniform existence times near each compact action segment. -/
theorem analytic_field_and_local_solutions (S : Hyp H) :
    (∀ u, AnalyticAt ℝ S.Y u) ∧
    (∀ (K : Set H), IsCompact K → K.Nonempty → ∀ b : ℝ,
      ∃ r > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x ∈ K, ∀ y ∈ closedBall x r,
        ∃ α : ℝ → H, α b = y ∧
          ∀ t ∈ Ioo (b - δ) (b + δ), HasDerivAt α (S.Y (α t)) t) := by
  have ha : ∀ u, AnalyticAt ℝ S.Y u := by
    intro u
    have h := (inverseW.analyticAt (S.abar u)).comp
      (analyticAt_of_isRealAnalyticPoly (S.abar_analytic u))
    convert h using 1
    funext x
    exact (inverseW_eq (S.abar x)).symm
  refine ⟨ha, ?_⟩
  intro K hK hn b
  exact QuantumNLS.Ext025A6.compact_common_local_solutions hK hn
    (fun x _ => (ha x).contDiffAt) b

#print axioms analytic_field_and_local_solutions
end QuantumNLS.TerraMultiRound17D01Repair
