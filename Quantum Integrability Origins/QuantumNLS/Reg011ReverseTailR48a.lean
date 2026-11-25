import QuantumNLS.TerraMultiRound76MomentBridge
import QuantumNLS.TerraMultiRound79Characterization
import QuantumNLS.TerraMultiRound70WeightComparison

/-! Reverse confinement: weighted indexed tails control physical excess. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology
open QuantumNLS.PhysicalTensor QuantumNLS.RootWeightedCellsR26
open QuantumNLS.RootWeightedMomentsR26 QuantumNLS.TerraMultiRound60IndexedMoment
namespace QuantumNLS.Reg011ReverseTailR48a

/-- Eventual uniform tails follow from ℓ¹ convergence, at the same weight. -/
theorem eventual_lattice_tail (p : ℤ → ℝ) (a : ℕ → ℤ → ℝ) (b : ℤ → ℝ)
    (ha : ∀ j n, 0 ≤ a j n) (hb : ∀ n, 0 ≤ b n)
    (has : ∀ j, Summable (a j)) (hbs : Summable b)
    (hd : Tendsto (fun j => ∑' n, |a j n-b n|) atTop (𝓝 0)) :
    ∀ ε > 0, ∃ R : ℕ, ∀ᶠ j in atTop, (∑' n, if (R:ℝ) < |p n| then a j n else 0) < ε := by
  classical
  have ht : Tendsto (fun R : ℕ => ∑' n, if (R:ℝ) < |p n| then b n else 0) atTop (𝓝 0) := by
    have hp : ∀ n, Tendsto (fun R : ℕ => if (R:ℝ) < |p n| then b n else 0) atTop (𝓝 0) := by
      intro n
      apply tendsto_const_nhds.congr'
      filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (|p n|))] with R hR
      simp [not_lt_of_ge hR]
    have h := tendsto_tsum_of_dominated_convergence hbs hp
      (Filter.Eventually.of_forall fun R n => by split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hb n), hb n])
    simpa only [tsum_zero] using h
  intro ε hε
  obtain ⟨R,hR⟩ := (ht.eventually (gt_mem_nhds (show 0 < ε/2 by positivity))).exists
  refine ⟨R, ?_⟩
  filter_upwards [hd.eventually (gt_mem_nhds (show 0 < ε/2 by positivity))] with j hj
  have hs : Summable (fun n => if (R:ℝ) < |p n| then a j n else 0) := by
    exact (has j).of_nonneg_of_le (fun n => by split_ifs <;> simp_all) (fun n => by split_ifs <;> simp_all)
  have hbt : Summable (fun n => if (R:ℝ) < |p n| then b n else 0) := by
    exact hbs.of_nonneg_of_le (fun n => by split_ifs <;> simp_all) (fun n => by split_ifs <;> simp_all)
  have hle : (∑' n, if (R:ℝ) < |p n| then a j n else 0) ≤
      (∑' n, |a j n-b n|) + ∑' n, if (R:ℝ) < |p n| then b n else 0 := by
    rw [← ((has j).sub hbs).abs.tsum_add hbt]
    apply hs.tsum_le_tsum _ (((has j).sub hbs).abs.add hbt)
    intro n
    split_ifs
    · linarith [le_abs_self (a j n-b n)]
    · simpa only [add_zero] using abs_nonneg (a j n-b n)
  linarith

variable {L κ : ℝ} [Fact (0 < L)]

/-- No higher moment is used. The cutoff K is chosen after the common
confinement bound B and the indexed cutoff R. -/
theorem excess_le_indexed_tail (hκ : 0 < κ) (u : L2T L) (p R B K : ℝ)
    (hp : 0 < p) (_hR : 0 ≤ R) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hconf : 2 * Real.sqrt (κ * ‖u‖^2 / L) ≤ B) (hcut : (R+B)^p ≤ K)
    (hi : Summable (fun n : ℤ => (1+|momentum L n|)^p * (QuantumNLS.RootIndexedMasses.masses hκ u).1 n)) :
    |(∫ t : ℝ, |t|^p ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u) -
      (∫ t : ℝ, min (|t|^p) K ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u)| ≤
      (1+B)^p * ∑' n : ℤ, if R < |momentum L n| then
        (1+|momentum L n|)^p * (QuantumNLS.RootIndexedMasses.masses hκ u).1 n else 0 := by
  classical
  let μ := QuantumNLS.PhysicalQuantumMeasure.measure hκ u
  let wi := fun n : ℤ => if R < |momentum L n| then (1+|momentum L n|)^p else 0
  have hwi : ∀ n, 0 ≤ wi n := by intro n; dsimp [wi]; split_ifs <;> positivity
  have his : Summable (fun n => wi n * (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) := by
    apply hi.of_nonneg_of_le
    · intro n; exact mul_nonneg (hwi n) ((QuantumNLS.RootIndexedMasses.root_indexed_masses_proved_clauses hκ u).2.1 n)
    · intro n; dsimp [wi]; split_ifs
      · exact le_rfl
      · simp only [zero_mul]; exact mul_nonneg (by positivity) ((QuantumNLS.RootIndexedMasses.root_indexed_masses_proved_clauses hκ u).2.1 n)
  have hindex : Integrable wi (indexLaw hκ u) := by
    apply (integrable_indexLaw_iff hκ u wi).mpr
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hwi _), mul_comm] using his
  have hcell : Integrable (fun t => wi (cellIndex hκ u t)) μ :=
    (integrable_map_measure (μ := μ) (g := wi) Measurable.of_discrete.aestronglyMeasurable
      (measurable_cellIndex hκ u).aemeasurable).mp hindex
  have hmap : (∫ t, wi (cellIndex hκ u t) ∂μ) =
      ∑' n : ℤ, if R < |momentum L n| then
        (1+|momentum L n|)^p * (QuantumNLS.RootIndexedMasses.masses hκ u).1 n else 0 := by
    rw [← integral_map (measurable_cellIndex hκ u).aemeasurable Measurable.of_discrete.aestronglyMeasurable]
    change (∫ n, wi n ∂indexLaw hκ u) = _
    rw [integral_indexLaw hκ u wi hindex]
    apply tsum_congr
    intro n
    dsimp [wi]; split_ifs <;> ring
  have hm : Integrable (fun t : ℝ => |t|^p) μ := by
    have h := QuantumNLS.TerraMultiRound77ActionCriteria.physical_power_iff_indexed_actions hκ u (p/2) (by positivity)
    have he : 2*(p/2) = p := by ring
    rw [he] at h
    exact h.mpr hi
  have htr : Integrable (fun t : ℝ => min (|t|^p) K) μ := by
    apply hm.mono' ((continuous_abs.rpow_const (fun _ => Or.inr hp.le)).min continuous_const).aestronglyMeasurable
    apply ae_of_all
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by positivity) hK)]
    exact min_le_left _ _
  have hb : ∀ᵐ t ∂μ, |t|^p - min (|t|^p) K ≤ (1+B)^p * wi (cellIndex hκ u t) := by
    filter_upwards [displacement_bound_ae hκ u] with t ht
    have hdist : |t-cellMomentum hκ u t| ≤ B := ht.trans hconf
    by_cases hn : R < |cellMomentum hκ u t|
    · have hw := QuantumNLS.TerraMultiRound70WeightComparison.shifted_weight_le t (cellMomentum hκ u t) B p hB hp.le hdist
      have hl := Real.rpow_le_rpow (abs_nonneg t) (by linarith [abs_nonneg t] : |t| ≤ 1+|t|) hp.le
      have he : wi (cellIndex hκ u t) = (1+|cellMomentum hκ u t|)^p := by change (if R < |cellMomentum hκ u t| then (1+|cellMomentum hκ u t|)^p else 0) = _; simp [hn]
      rw [he]
      linarith [le_min (Real.rpow_nonneg (abs_nonneg t) p) hK]
    · have ha : |t| ≤ R+B := by
        have hh := abs_sub_abs_le_abs_sub t (cellMomentum hκ u t)
        linarith [le_abs_self (|t|-|cellMomentum hκ u t|), le_of_not_gt hn]
      have hk : |t|^p ≤ K := (Real.rpow_le_rpow (abs_nonneg t) ha hp.le).trans hcut
      have he : wi (cellIndex hκ u t) = 0 := by change (if R < |cellMomentum hκ u t| then (1+|cellMomentum hκ u t|)^p else 0) = _; simp [hn]
      rw [min_eq_left hk, sub_self, he, mul_zero]
  have hh := integral_mono_ae (hm.sub htr) (hcell.const_mul ((1+B)^p)) hb
  simp only [Pi.sub_apply] at hh
  rw [integral_sub hm htr, integral_const_mul, hmap] at hh
  rw [abs_of_nonneg (sub_nonneg.mpr (integral_mono htr hm (fun t => min_le_left _ _)))]
  exact hh

#print axioms eventual_lattice_tail
#print axioms excess_le_indexed_tail
end QuantumNLS.Reg011ReverseTailR48a

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg011ReverseTailR48a." ||
        n.toString.startsWith "_private.QuantumNLS.Reg011ReverseTailR48a." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Round48 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
