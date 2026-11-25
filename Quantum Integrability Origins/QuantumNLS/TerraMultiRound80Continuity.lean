import QuantumNLS.TerraMultiRound80TailLemma

/-! Same-order convergence of the physical indexed actions. -/
set_option autoImplicit false
noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.RootWeightedCellsR26
namespace QuantumNLS.TerraMultiRound80Continuity
variable {L : ℝ} [Fact (0 < L)]

private theorem tail_real {ι : Type*} (f : ι → ℝ) (hf : ∀ n, 0 ≤ f n)
    (hs : Summable f) (P : ι → Prop) [DecidablePred P] (ε : ℝ) (hε : 0 < ε)
    (h : (∑' n, if P n then ENNReal.ofReal (f n) else 0) < ENNReal.ofReal ε) :
    (∑' n, if P n then f n else 0) < ε := by
  have hn : ∀ n, 0 ≤ (if P n then f n else 0) := by
    intro n; split_ifs; exact hf n; exact le_rfl
  have hsm : Summable (fun n => if P n then f n else 0) := by
    apply hs.of_nonneg_of_le hn
    intro n; split_ifs; exact le_rfl; exact hf n
  have heq : ENNReal.ofReal (∑' n, if P n then f n else 0) =
      ∑' n, if P n then ENNReal.ofReal (f n) else 0 := by
    rw [ENNReal.ofReal_tsum_of_nonneg hn hsm]
    apply tsum_congr
    intro n; split_ifs <;> simp
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mp (heq.trans_lt h)

/-- Same-order weighted absolute action differences converge to zero for
convergent Sobolev sequences, without a higher-order assumption. -/
theorem weighted_action_difference_tendsto (κ : ℝ) (hκ : 0 < κ) (s : ℝ)
    (hs0 : 0 < s) (hs2 : s ≤ 2) (u : ℕ → H02 L s) (v : H02 L s)
    (hu : Tendsto u atTop (𝓝 v)) :
    Tendsto (fun j => ∑' n : ℤ, (1+|momentum L n|)^(2*s) *
      |(QuantumNLS.RootIndexedMasses.masses hκ (u j).val).1 n -
       (QuantumNLS.RootIndexedMasses.masses hκ v.val).1 n|) atTop (𝓝 0) := by
  classical
  let w : ℤ → ℝ := fun n => (1+|momentum L n|)^(2*s)
  let a : ℕ → ℤ → ℝ := fun j n => (QuantumNLS.RootIndexedMasses.masses hκ (u j).val).1 n
  let b : ℤ → ℝ := fun n => (QuantumNLS.RootIndexedMasses.masses hκ v.val).1 n
  have hw : ∀ n, 0 ≤ w n := by intro n; dsimp [w]; positivity
  have ha : ∀ j n, 0 ≤ a j n := fun j n => (QuantumNLS.RootIndexedMasses.root_indexed_masses_proved_clauses hκ (u j).val).2.1 n
  have hb : ∀ n, 0 ≤ b n := fun n => (QuantumNLS.RootIndexedMasses.root_indexed_masses_proved_clauses hκ v.val).2.1 n
  have hsa : ∀ j, Summable (fun n => w n * a j n) := by
    intro j
    exact ((QuantumNLS.TerraMultiRound79Characterization.closed_interval_characterization κ hκ (u j).val s hs0.le hs2).2).mp
      (((QuantumNLS.TerraMultiRound79Characterization.closed_interval_characterization κ hκ (u j).val s hs0.le hs2).1).mp ⟨u j, rfl⟩)
  have hsb : Summable (fun n => w n * b n) := by
    exact ((QuantumNLS.TerraMultiRound79Characterization.closed_interval_characterization κ hκ v.val s hs0.le hs2).2).mp
      (((QuantumNLS.TerraMultiRound79Characterization.closed_interval_characterization κ hκ v.val s hs0.le hs2).1).mp ⟨v, rfl⟩)
  have hbs : ∀ j, Summable (fun n => |a j n - b n|) := by
    intro j
    have h := (Memℓp.summable_of_one ((QuantumNLS.RootIndexedMasses.masses hκ (u j).val).1 -
      (QuantumNLS.RootIndexedMasses.masses hκ v.val).1).2).norm
    simpa only [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs] using h
  have hbase : Tendsto (fun j => ∑' n, |a j n - b n|) atTop (𝓝 0) := by
    have ht : Tendsto (fun j => (u j).val) atTop (𝓝 v.val) :=
      ((H02.toL2 (L := L) hs0.le).continuous.tendsto v).comp hu
    have hc := ((QuantumNLS.DEF014Continuity.continuous_physical_masses hκ).tendsto v.val).comp ht
    have hc' : Tendsto (fun j => (QuantumNLS.RootIndexedMasses.masses hκ (u j).val).1) atTop
        (𝓝 (QuantumNLS.RootIndexedMasses.masses hκ v.val).1) :=
      (continuous_subtype_val.tendsto _).comp hc
    have hn := (hc'.sub (tendsto_const_nhds (x := (QuantumNLS.RootIndexedMasses.masses hκ v.val).1))).norm
    have he : ∀ j, (∑' n, |a j n - b n|) =
        ‖(QuantumNLS.RootIndexedMasses.masses hκ (u j).val).1 - (QuantumNLS.RootIndexedMasses.masses hκ v.val).1‖ := by
      intro j
      have h := lp.norm_rpow_eq_tsum (p := (1 : ℝ≥0∞)) (by norm_num)
        ((QuantumNLS.RootIndexedMasses.masses hκ (u j).val).1 - (QuantumNLS.RootIndexedMasses.masses hκ v.val).1)
      simpa only [ENNReal.toReal_one, Real.rpow_one, lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs] using h.symm
    have hn' : Tendsto (fun j => ‖(QuantumNLS.RootIndexedMasses.masses hκ (u j).val).1 -
        (QuantumNLS.RootIndexedMasses.masses hκ v.val).1‖) atTop (𝓝 0) := by simpa using hn
    exact hn'.congr' (Filter.Eventually.of_forall fun j => (he j).symm)
  apply QuantumNLS.TerraMultiRound80TailLemma.weighted_tendsto_of_tails w a b hw ha hb hbase hbs hsa hsb
  intro ε hε
  obtain ⟨R, hR⟩ := QuantumNLS.TerraMultiRound79IndexedTail.uniform_indexed_action_tail κ hκ s hs0 hs2 u v hu ε hε
  obtain ⟨S, hS⟩ := QuantumNLS.TerraMultiRound79IndexedTail.uniform_indexed_action_tail κ hκ s hs0 hs2 (fun _ => v) v tendsto_const_nhds ε hε
  let T := max R S
  refine ⟨fun n => T < |momentum L n|, inferInstance, (1+max T 0)^(2*s), by positivity, ?_, ?_, ?_⟩
  · intro n hn
    exact QuantumNLS.TerraMultiRound79ActionDifference.weight_bounded_on_cutoff s T hs0.le n (le_of_not_gt hn)
  · intro j
    apply tail_real (fun n => w n * a j n) (fun n => mul_nonneg (hw n) (ha j n)) (hsa j) _ ε hε
    apply lt_of_le_of_lt _ (hR j)
    apply ENNReal.tsum_le_tsum
    intro n
    dsimp only
    split_ifs with hT hR'
    · exact le_rfl
    · exfalso; exact hR' (lt_of_le_of_lt (le_max_left R S) hT)
    · exact zero_le
    · exact le_rfl
  · apply tail_real (fun n => w n * b n) (fun n => mul_nonneg (hw n) (hb n)) hsb _ ε hε
    apply lt_of_le_of_lt _ (hS 0)
    apply ENNReal.tsum_le_tsum
    intro n
    dsimp only
    split_ifs with hT hS'
    · exact le_rfl
    · exfalso; exact hS' (lt_of_le_of_lt (le_max_right R S) hT)
    · exact zero_le
    · exact le_rfl

#print axioms weighted_action_difference_tendsto
end QuantumNLS.TerraMultiRound80Continuity
