import QuantumNLS.SourcePlacementCommutator

/-! Source commutator estimate and factorial-dominated uniform modulus. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
open Filter Topology
open scoped InnerProductSpace BigOperators
namespace QuantumNLS.SourceGeneratorBound
open TensorCarrier TensorPlacements PhysicalTensor KernelDefinition PlacementGrouping
open SourcePlacementCommutator LinearTailGenerator LinearTailKineticError
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Restriction is taken only after the full averages have been composed. -/
theorem sector_scaled_bound (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) (hN : 1 ≤ N)
    (A : BoundedSymmetricKernel H p) (hA : IsSelfAdjoint A)
    (J : BoundedSymmetricKernel H q) (v : SymSector ℂ H N)
    {e : ℝ} (he : 0 ≤ e)
    (hv : ∀ S : PlacementSubset p (N - p), ‖rawSubsetPlacement N p hp S A v.val‖ ≤ e) :
    ‖⟪v, (((N : ℂ) • genericU_N_r N p hp A) * genericU_N_r N q hq J -
      genericU_N_r N q hq J * ((N : ℂ) • genericU_N_r N p hp A)) v⟫_ℂ‖ ≤
        2 * e * ‖J‖ * ‖v‖ * (p * q : ℝ) := by
  have hh := average_bound N p q hp hq hN A hA J v.val he hv
  have hid : ⟪v, (((N : ℂ) • genericU_N_r N p hp A) * genericU_N_r N q hq J -
      genericU_N_r N q hq J * ((N : ℂ) • genericU_N_r N p hp A)) v⟫_ℂ =
      (N : ℂ) * ⟪v.val, (rawSubsetAverage N p hp A * rawSubsetAverage N q hq J -
        rawSubsetAverage N q hq J * rawSubsetAverage N p hp A) v.val⟫_ℂ := by
    rw [genericU_eq_rawSubsetAverageOnSector, genericU_eq_rawSubsetAverageOnSector]
    simp only [mul_apply_eq_comp, sub_apply, smul_apply, map_smul, inner_sub_right,
      inner_smul_right]
    change (N : ℂ) * ⟪v.val, rawSubsetAverage N p hp A (rawSubsetAverage N q hq J v.val)⟫_ℂ -
      (N : ℂ) * ⟪v.val, rawSubsetAverage N q hq J (rawSubsetAverage N p hp A v.val)⟫_ℂ = _
    ring
  rw [hid, norm_mul, Complex.norm_natCast]
  calc
    _ ≤ (N : ℝ) * (2 * e * ‖J‖ * ‖v‖ * ((p * q : ℝ) / N)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by
      have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      field_simp

omit [CompleteSpace H] in
/-- Linear combination of the actual scaled rank commutators. -/
theorem sum_bound {ι : Type*} (s : Finset ι) (c b : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (T : ι → H →L[ℂ] H) (J : H →L[ℂ] H)
    (N : ℕ) (v : H)
    (h : ∀ i ∈ s, ‖⟪v, (((N : ℂ) • T i) * J - J * ((N : ℂ) • T i)) v⟫_ℂ‖ ≤ b i) :
    ‖⟪v, (((N : ℂ) • ∑ i ∈ s, (c i : ℂ) • T i) * J -
      J * ((N : ℂ) • ∑ i ∈ s, (c i : ℂ) • T i)) v⟫_ℂ‖ ≤ ∑ i ∈ s, c i * b i := by
  have heq : ⟪v, (((N : ℂ) • ∑ i ∈ s, (c i : ℂ) • T i) * J -
      J * ((N : ℂ) • ∑ i ∈ s, (c i : ℂ) • T i)) v⟫_ℂ =
      ∑ i ∈ s, (c i : ℂ) * ⟪v, (((N : ℂ) • T i) * J - J * ((N : ℂ) • T i)) v⟫_ℂ := by
    simp only [Finset.smul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
      sum_apply, inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [mul_apply_eq_comp, sub_apply, smul_apply, map_smul, inner_sub_right, inner_smul_right]
    ring
  rw [heq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc i hi)]
  exact mul_le_mul_of_nonneg_left (h i hi) (hc i hi)

variable (L : ℝ) [Fact (0 < L)]

/-- Explicit source modulus; independent of N, the state, weights and time. -/
def epsilon (κ E : ℝ) (k R : ℕ) : ℝ :=
  (2 * k / L) * ∑' n : ℕ, ((n : ℝ) + 1) * κ ^ n * sourceError L n E R

theorem epsilon_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (E : ℝ) (k R : ℕ) :
    0 ≤ epsilon L κ E k R := by
  have hL : 0 < L := Fact.out
  unfold epsilon
  exact mul_nonneg (by positivity) (tsum_nonneg fun n => by
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hκ _)) (error_nonneg L n E R))

/-- Factorial dominated convergence for the constructed, rather than supplied, errors. -/
theorem epsilon_tendsto {κ E : ℝ} (hκ : 0 ≤ κ) (hE : 0 ≤ E) (k : ℕ) :
    Tendsto (epsilon L κ E k) atTop (𝓝 0) := by
  change Tendsto (fun R => (2 * k / L) * ∑' n : ℕ, ((n : ℝ) + 1) * κ ^ n * sourceError L n E R) atTop (𝓝 0)
  simpa only [mul_zero] using (source_error_series L hκ hE).2.const_mul (2 * k / L)

/-- Actual N-scaled generator estimate at a symmetric unit vector. The only
per-rank inputs are literal placement vector norms; cutoff_orbit supplies them. -/
theorem generator_bound (κ : ℝ) (hκ : 0 < κ) (N k : ℕ) (hN : 1 ≤ N) (hk : k ≤ N)
    (E : ℝ) (hE : 0 ≤ E) (R : ℕ) (a : Finset ℤ) (t : ℤ → ℝ)
    (J : BoundedSymmetricKernel (L2T L) k) (hJ : ‖J‖ ≤ 1)
    (v : SymSector ℂ (L2T L) N) (hnorm : ‖v‖ = 1)
    (hv : ∀ (n : ℕ) (hn : n + 1 ≤ N) (S : PlacementSubset (n + 1) (N - (n + 1))),
      ‖rawSubsetPlacement N (n + 1) hn S (finiteT L (n + 1) a t) v.val‖ ≤ sourceError L n E R) :
    ‖⟪v, (((N : ℂ) • genSum L κ N a t) * genericU_N_r N k hk J -
      genericU_N_r N k hk J * ((N : ℂ) • genSum L κ N a t)) v⟫_ℂ‖ ≤ epsilon L κ E k R := by
  classical
  have hL : 0 < L := Fact.out
  let c := fun j : Fin N => (1 / L) * κ ^ j.val * HighMomentsRank.fallR N (j.val + 1)
  let b := fun j : Fin N => 2 * sourceError L j.val E R * ‖J‖ * ‖v‖ * ((j.val + 1) * k : ℝ)
  have hc (j : Fin N) : 0 ≤ c j := by
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hκ.le _))
      (HighMomentsRank.fallR_bounds N (by omega) (j.val + 1) j.2).1
  rw [generator_identity L κ hκ N a t]
  have hb (j : Fin N) :
      ‖⟪v, (((N : ℂ) • genericU_N_r N (j.val + 1) j.2 (finiteT L (j.val + 1) a t)) * genericU_N_r N k hk J -
        genericU_N_r N k hk J * ((N : ℂ) • genericU_N_r N (j.val + 1) j.2 (finiteT L (j.val + 1) a t))) v⟫_ℂ‖ ≤ b j := by
    simpa only [b, Nat.cast_succ] using sector_scaled_bound N _ k j.2 hk hN _ (PhysicalPlacementError.finiteT_selfadjoint L _ a t)
      J v (error_nonneg L _ E R) (hv j.val j.2)
  refine (sum_bound Finset.univ c b (fun j _ => hc j) _ _ N v (fun j _ => hb j)).trans ?_
  have hterm (j : Fin N) : c j * b j ≤
      (2 * k / L) * (((j.val : ℝ) + 1) * κ ^ j.val * sourceError L j.val E R) := by
    have hf := (HighMomentsRank.fallR_bounds N (by omega) (j.val + 1) j.2).2.2
    have hj : ‖J‖ * HighMomentsRank.fallR N (j.val + 1) ≤ 1 := by
      calc
        _ ≤ 1 * 1 := mul_le_mul hJ hf
          (HighMomentsRank.fallR_bounds N (by omega) _ j.2).1 zero_le_one
        _ = 1 := one_mul 1
    have hm := mul_le_mul_of_nonneg_left hj
      (show 0 ≤ (2 * k / L) * (((j.val : ℝ) + 1) * κ ^ j.val * sourceError L j.val E R) by
        exact mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hκ.le _)) (error_nonneg L _ E R)))
    change (1 / L) * κ ^ j.val * HighMomentsRank.fallR N (j.val + 1) *
      (2 * sourceError L j.val E R * ‖J‖ * ‖v‖ * (((j.val : ℝ) + 1) * k)) ≤ _
    rw [hnorm]
    convert hm using 1 <;> ring
  refine (Finset.sum_le_sum fun j _ => hterm j).trans ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hs := (source_error_series L hκ.le hE).1 R
  rw [show (∑ i : Fin N, ((i.val : ℝ) + 1) * κ ^ i.val * sourceError L i.val E R) =
    ∑ n ∈ Finset.range N, ((n : ℝ) + 1) * κ ^ n * sourceError L n E R from
      Fin.sum_univ_eq_sum_range (fun n : ℕ => ((n : ℝ) + 1) * κ ^ n * sourceError L n E R) N]
  exact Summable.sum_le_tsum (Finset.range N) (fun n _ =>
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hκ.le _)) (error_nonneg L n E R)) hs

end QuantumNLS.SourceGeneratorBound

-- AUTHOR AUDITS
#print axioms QuantumNLS.SourceGeneratorBound.sector_scaled_bound
#print axioms QuantumNLS.SourceGeneratorBound.sum_bound
#print axioms QuantumNLS.SourceGeneratorBound.epsilon
#print axioms QuantumNLS.SourceGeneratorBound.epsilon_nonneg
#print axioms QuantumNLS.SourceGeneratorBound.epsilon_tendsto
#print axioms QuantumNLS.SourceGeneratorBound.generator_bound

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.SourceGeneratorBound." then
      pending := pending.push n
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
