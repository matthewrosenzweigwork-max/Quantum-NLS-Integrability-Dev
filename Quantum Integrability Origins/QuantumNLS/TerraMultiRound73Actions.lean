import QuantumNLS.TerraMultiRound73Difference

/-! Physical action specialization with an explicit higher-moment premise. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology ENNReal
namespace QuantumNLS.TerraMultiRound73Actions
open QuantumNLS.PhysicalTensor QuantumNLS.RootWeightedCellsR26
open QuantumNLS.TerraMultiRound73Difference

theorem physical_actions_lower_weight {L κ : ℝ} [Fact (0 < L)]
    (hκ : 0 < κ) (u : ℕ → L2T L) (v : L2T L) (p q B : ℝ)
    (hp : 0 ≤ p) (hpq : p < q) (hB : 0 ≤ B)
    (hu : Tendsto u atTop (𝓝 v))
    (hs : ∀ j, Summable (fun n : ℤ => (1+|momentum L n|)^q *
      (QuantumNLS.RootIndexedMasses.masses hκ (u j)).1 n))
    (hv : Summable (fun n : ℤ => (1+|momentum L n|)^q *
      (QuantumNLS.RootIndexedMasses.masses hκ v).1 n))
    (hb : ∀ j, (∑' n : ℤ, (1+|momentum L n|)^q *
      (QuantumNLS.RootIndexedMasses.masses hκ (u j)).1 n) ≤ B) :
    Tendsto (fun j => ∑' n : ℤ, (1+|momentum L n|)^p *
      |(QuantumNLS.RootIndexedMasses.masses hκ (u j)).1 n -
        (QuantumNLS.RootIndexedMasses.masses hκ v).1 n|) atTop (𝓝 0) := by
  let a := fun j => QuantumNLS.RootIndexedMasses.masses hκ (u j)
  let b := QuantumNLS.RootIndexedMasses.masses hκ v
  let w : ℤ → ℝ := fun n => 1 + |momentum L n|
  have hw : ∀ n, 1 ≤ w n := by intro n; dsimp [w]; linarith [abs_nonneg (momentum L n)]
  have hfs : ∀ j, Summable (fun n => |(a j).1 n - b.1 n|) := by
    intro j
    have h := (Memℓp.summable_of_one ((a j).1 - b.1).2).norm
    simpa only [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs] using h
  have hbase : Tendsto (fun j => ∑' n, |(a j).1 n - b.1 n|) atTop (𝓝 0) := by
    have hc := ((QuantumNLS.DEF014Continuity.continuous_physical_masses hκ).tendsto v).comp hu
    have hc' : Tendsto (fun j => (a j).1) atTop (𝓝 b.1) :=
      (continuous_subtype_val.tendsto b).comp hc
    have hn : Tendsto (fun j => ‖(a j).1 - b.1‖) atTop (𝓝 0) := by
      have h := (hc'.sub (tendsto_const_nhds (x := b.1))).norm
      simpa only [sub_self, norm_zero] using h
    have he : ∀ j, (∑' n, |(a j).1 n - b.1 n|) = ‖(a j).1 - b.1‖ := by
      intro j
      have h := lp.norm_rpow_eq_tsum (p := (1 : ℝ≥0∞)) (by norm_num) ((a j).1-b.1)
      simpa only [ENNReal.toReal_one, Real.rpow_one, lp.coeFn_sub, Pi.sub_apply,
        Real.norm_eq_abs] using h.symm
    exact hn.congr' (Filter.Eventually.of_forall fun j => (he j).symm)
  exact lower_weight_difference w (fun j n => (a j).1 n) (fun n => b.1 n) p q B hw
    (fun j n => (QuantumNLS.RootIndexedMasses.root_indexed_masses_proved_clauses hκ (u j)).2.1 n)
    (fun n => (QuantumNLS.RootIndexedMasses.root_indexed_masses_proved_clauses hκ v).2.1 n)
    hp hpq hB hbase hfs hs hv hb

#print axioms physical_actions_lower_weight
end QuantumNLS.TerraMultiRound73Actions
