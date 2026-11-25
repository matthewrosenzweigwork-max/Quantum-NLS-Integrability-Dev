import QuantumNLS.Ext005MomentEnergyR108

/-! R109: lower semicontinuity and passage of actual number-moment bounds
to sectorwise limits. The uniform approximant estimate remains an explicit
premise: this module neither constructs an evolution nor supplies that
estimate for the PROP-022 solutions. -/
noncomputable section
set_option autoImplicit false
open scoped Topology
namespace QuantumNLS.Ext005MomentLimitR109
open Ext025B3PhysicalSectors Ext005Moments Ext005MomentEnergyR108
open BetheCoefficientTransform MeasureTheory Filter
variable {L : ℝ} [Fact (0 < L)]

def finiteEnergy (j : ℕ) (s : Finset ℕ) (x : Fock L) : ℝ :=
  ∑ n ∈ s, momentWeight j n * ‖x n‖ ^ 2

theorem finiteEnergy_le (j : ℕ) (s : Finset ℕ)
    (x : momentDomain (L := L) j) : finiteEnergy j s x.val ≤ energy j x.val := by
  exact Summable.sum_le_tsum s
    (fun n _ => mul_nonneg (momentWeight_nonneg j n) (sq_nonneg _))
    ((momentDomain_iff j x.val).1 x.property)

/-- Bounded finite subsums prove membership as well as the energy bound.
Thus the unrestricted real tsum is never used as a test for finiteness. -/
theorem bound_iff_finite (j : ℕ) (x : Fock L) (C : ℝ) :
    (x ∈ momentDomain (L := L) j ∧ energy j x ≤ C) ↔
      ∀ s : Finset ℕ, finiteEnergy j s x ≤ C := by
  constructor
  · rintro ⟨hx, hb⟩ s
    exact (finiteEnergy_le j s ⟨x, hx⟩).trans hb
  · intro h
    have hs : Summable (fun n => momentWeight j n * ‖x n‖ ^ 2) :=
      summable_of_sum_le
        (fun n => mul_nonneg (momentWeight_nonneg j n) (sq_nonneg _)) h
    exact ⟨(momentDomain_iff j x).2 hs, hs.tsum_le_of_sum_le h⟩

theorem finiteEnergy_continuous (j : ℕ) (s : Finset ℕ) :
    Continuous (finiteEnergy (L := L) j s) := by
  apply continuous_finsetSum
  intro n _
  exact continuous_const.mul
    (((lp.evalCLM ℂ (fun n => HN L n) 2 n).continuous.norm).pow 2)

/-- Each form-energy ball is closed in the physical Fock norm, although the
whole unbounded form domain need not be closed in that norm. -/
theorem energySublevel_closed (j : ℕ) (C : ℝ) :
    IsClosed {x : Fock L | x ∈ momentDomain (L := L) j ∧ energy j x ≤ C} := by
  have he : {x : Fock L | x ∈ momentDomain (L := L) j ∧ energy j x ≤ C} =
      ⋂ s : Finset ℕ, {x : Fock L | finiteEnergy j s x ≤ C} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact bound_iff_finite j x C
  rw [he]
  exact isClosed_iInter (fun s => isClosed_le (finiteEnergy_continuous j s) continuous_const)

/-- Fatou's argument in finite physical sectors. Only sectorwise norm
convergence is required; convergence in the full form norm is not assumed. -/
theorem sectorLimit_bound (j : ℕ) (u : ℕ → Fock L) (x : Fock L) (C : ℝ)
    (hu : ∀ m, u m ∈ momentDomain (L := L) j ∧ energy j (u m) ≤ C)
    (hx : ∀ n, Tendsto (fun m => u m n) atTop (𝓝 (x n))) :
    x ∈ momentDomain (L := L) j ∧ energy j x ≤ C := by
  apply (bound_iff_finite j x C).2
  intro s
  have ht : Tendsto (fun m => finiteEnergy j s (u m)) atTop
      (𝓝 (finiteEnergy j s x)) := by
    apply tendsto_finsetSum
    intro n _
    exact tendsto_const_nhds.mul ((hx n).norm.pow 2)
  exact le_of_tendsto ht (Eventually.of_forall fun m =>
    (finiteEnergy_le j s ⟨u m, (hu m).1⟩).trans (hu m).2)

theorem normLimit_bound (j : ℕ) (u : ℕ → Fock L) (x : Fock L) (C : ℝ)
    (hu : ∀ m, u m ∈ momentDomain (L := L) j ∧ energy j (u m) ≤ C)
    (hx : Tendsto u atTop (𝓝 x)) :
    x ∈ momentDomain (L := L) j ∧ energy j x ≤ C := by
  apply sectorLimit_bound j u x C hu
  intro n
  exact ((lp.evalCLM ℂ (fun n => HN L n) 2 n).continuous.tendsto x).comp hx

/-- A common cutoff-uniform estimate survives an a.e. sectorwise limit on
the same time interval. The common constant and convergence must be proved
by the evolution construction; they are not supplied by this theorem. -/
theorem ae_sectorLimit_bound (j : ℕ) (I : Set ℝ) (u : ℕ → ℝ → Fock L)
    (x : ℝ → Fock L) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ m, ∀ᵐ t ∂volume.restrict I,
      u m t ∈ momentDomain (L := L) j ∧ energy j (u m t) ≤ C)
    (hx : ∀ᵐ t ∂volume.restrict I,
      ∀ n, Tendsto (fun m => u m t n) atTop (𝓝 (x t n))) :
    EnergyBounded j I x := by
  refine ⟨C, hC, ?_⟩
  have hu' : ∀ᵐ t ∂volume.restrict I, ∀ m,
      u m t ∈ momentDomain (L := L) j ∧ energy j (u m t) ≤ C :=
    ae_all_iff.mpr hu
  filter_upwards [hu', hx] with t ht hl
  exact sectorLimit_bound j (fun m => u m t) (x t) C ht hl

theorem energy_sub_le (j : ℕ) (x y : momentDomain (L := L) j) :
    energy j ((x - y).val) ≤ 2 * (energy j x.val + energy j y.val) := by
  have h := norm_sub_le (momentRoot j x) (momentRoot j y)
  have hs := sq_nonneg (‖momentRoot j x‖ - ‖momentRoot j y‖)
  calc
    _ = ‖momentRoot j (x - y)‖ ^ 2 := energy_eq_root j (x - y)
    _ = ‖momentRoot j x - momentRoot j y‖ ^ 2 :=
      congrArg (fun z : Fock L => ‖z‖ ^ 2) ((momentRoot j).map_sub x y)
    _ ≤ 2 * (‖momentRoot j x‖ ^ 2 + ‖momentRoot j y‖ ^ 2) := by
      nlinarith [norm_nonneg (momentRoot j x - momentRoot j y),
        norm_nonneg (momentRoot j x), norm_nonneg (momentRoot j y)]
    _ = _ := congrArg₂ (fun a b : ℝ => 2 * (a + b))
      (energy_eq_root j x).symm (energy_eq_root j y).symm

/-- Differences of two D3 competitors retain an essential uniform form
bound. Norm continuity and the weak equation remain separate conditions. -/
theorem energyBounded_sub (j : ℕ) (I : Set ℝ) (x y : ℝ → Fock L)
    (hx : EnergyBounded j I x) (hy : EnergyBounded j I y) :
    EnergyBounded j I (fun t => x t - y t) := by
  obtain ⟨C, hC, hc⟩ := hx
  obtain ⟨D, hD, hd⟩ := hy
  refine ⟨2 * (C + D), by positivity, ?_⟩
  filter_upwards [hc, hd] with t ht hu
  refine ⟨Submodule.sub_mem _ ht.1 hu.1, ?_⟩
  have h := energy_sub_le j ⟨x t, ht.1⟩ ⟨y t, hu.1⟩
  change energy j (x t - y t) ≤ _ at h
  linarith

end QuantumNLS.Ext005MomentLimitR109
#print axioms QuantumNLS.Ext005MomentLimitR109.energySublevel_closed
#print axioms QuantumNLS.Ext005MomentLimitR109.sectorLimit_bound
#print axioms QuantumNLS.Ext005MomentLimitR109.ae_sectorLimit_bound
#print axioms QuantumNLS.Ext005MomentLimitR109.energyBounded_sub

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005MomentLimitR109." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005MomentLimitR109." then
      pending := pending.push n
  let roots := pending.size
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
  Lean.logInfo m!"R109 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
