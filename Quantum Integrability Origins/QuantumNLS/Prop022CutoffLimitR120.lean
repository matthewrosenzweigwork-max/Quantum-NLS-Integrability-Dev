import QuantumNLS.Prop022CutoffCauchyR120
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.UniformApproximation

/-! The actual cutoff limit, locally uniform Fock convergence, norm
continuity, initial trace and inherited number-moment estimates. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped InnerProductSpace Topology
open Set Filter ContinuousLinearMap
namespace QuantumNLS.Prop022CutoffLimitR120
open BetheCoefficientTransform Ext025B3PhysicalSectors Ext005Moments
open Ext005MomentEnergyR108 Ext005MomentLimitR109 Ext005FormCutoffR109
open Prop022CutoffEvolutionR119 Prop022CutoffCauchyR120 Prop022FactorialCoefficientsR115
open Prop022FactorialMajorantR115 Ext005PairCommutatorR108
variable {L : ℝ} [Fact (0 < L)]

lemma inverse_cutoff_tendsto : Tendsto (fun N : ℕ => ((N : ℝ)+1)⁻¹) atTop (𝓝 0) := by
  simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma overlapConstant_nonneg (M A T : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (x : momentDomain (L := L) 3) : 0 ≤ overlapConstant M A T x := by
  exact mul_nonneg (mul_nonneg (by norm_num)
    (mul_nonneg hM (add_nonneg (numberMajorant_nonneg A hA) (pairMajorant_nonneg A hA))))
    (radiusSq_nonneg M A T x)

theorem actual_uniform_cauchy (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (PhysicalTensor.L2T L))
    (s T : ℝ) (x : momentDomain (L := L) 3) :
    UniformCauchySeqOn (fun N => solution B M A hA hB hs u₀ N s x.val) atTop (Icc (s-T) (s+T)) := by
  have hp1 : Tendsto (fun p : ℕ × ℕ => p.1) atTop atTop := by
    rw [← prod_atTop_atTop_eq]; exact tendsto_fst
  have hp2 : Tendsto (fun p : ℕ × ℕ => p.2) atTop atTop := by
    rw [← prod_atTop_atTop_eq]; exact tendsto_snd
  have hi := (((cutoff_tendsto x.val).comp hp1).sub ((cutoff_tendsto x.val).comp hp2)).norm.pow 2
  have htail := ((((inverse_cutoff_tendsto.comp hp1).add
    (inverse_cutoff_tendsto.comp hp2)).const_mul (overlapConstant M A T x)).const_mul 2).mul_const T
  have he : Tendsto (fun p : ℕ × ℕ => ‖cutoff p.1 x.val-cutoff p.2 x.val‖^2+
      2*(overlapConstant M A T x * (((p.1 : ℝ)+1)⁻¹+((p.2 : ℝ)+1)⁻¹))*T) atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
      zero_add, mul_zero, zero_mul, add_zero] using hi.add htail
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop_prod_self'.mp (he.eventually (gt_mem_nhds (sq_pos_of_pos hε)))
  refine ⟨N, ?_⟩
  intro n hn k hk t ht
  have h := actual_square_distance B M A hM hA hB hs u₀ n k s T x t ht
  have hc : 0 ≤ 2*(overlapConstant M A T x * (((n : ℝ)+1)⁻¹+((k : ℝ)+1)⁻¹)) :=
    mul_nonneg (by norm_num) (mul_nonneg (overlapConstant_nonneg M A T hM hA x) (by positivity))
  have hst : |t-s| ≤ T := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hh := h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hst hc))
  have hsmall := hN n hn k hk
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (solution B M A hA hB hs u₀ n s x.val t-
    solution B M A hA hB hs u₀ k s x.val t)]

lemma actual_cauchy (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (PhysicalTensor.L2T L))
    (s : ℝ) (x : momentDomain (L := L) 3) (t : ℝ) :
    CauchySeq (fun N => solution B M A hA hB hs u₀ N s x.val t) := by
  apply (actual_uniform_cauchy B M A hM hA hB hs u₀ s |t-s| x).cauchySeq
  constructor <;> linarith [neg_abs_le (t-s), le_abs_self (t-s)]

/-- The physical cutoff limit selected from the proved Cauchy sequence. -/
def limit (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (PhysicalTensor.L2T L))
    (s : ℝ) (x : momentDomain (L := L) 3) (t : ℝ) : Fock L :=
  (cauchySeq_tendsto_of_complete (actual_cauchy B M A hM hA hB hs u₀ s x t)).choose

lemma limit_tendsto (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (PhysicalTensor.L2T L))
    (s : ℝ) (x : momentDomain (L := L) 3) (t : ℝ) :
    Tendsto (fun N => solution B M A hA hB hs u₀ N s x.val t) atTop
      (𝓝 (limit B M A hM hA hB hs u₀ s x t)) :=
  (cauchySeq_tendsto_of_complete (actual_cauchy B M A hM hA hB hs u₀ s x t)).choose_spec

lemma limit_uniform (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (PhysicalTensor.L2T L))
    (s T : ℝ) (x : momentDomain (L := L) 3) :
    TendstoUniformlyOn (fun N => solution B M A hA hB hs u₀ N s x.val)
      (limit B M A hM hA hB hs u₀ s x) atTop (Icc (s-T) (s+T)) :=
  (actual_uniform_cauchy B M A hM hA hB hs u₀ s T x).tendstoUniformlyOn_of_tendsto
    (fun t _ => limit_tendsto B M A hM hA hB hs u₀ s x t)

lemma limit_continuous (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (PhysicalTensor.L2T L))
    (s : ℝ) (x : momentDomain (L := L) 3) : Continuous (limit B M A hM hA hB hs u₀ s x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hc := (limit_uniform B M A hM hA hB hs u₀ s (|t-s|+1) x).continuousOn
    (Filter.Eventually.of_forall (fun N => (solution_continuous B M A hA hB hs u₀ N s x.val).continuousOn)).frequently
  apply hc.continuousAt
  apply Icc_mem_nhds <;> linarith [neg_abs_le (t-s), le_abs_self (t-s)]

lemma limit_initial (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (PhysicalTensor.L2T L))
    (s : ℝ) (x : momentDomain (L := L) 3) : limit B M A hM hA hB hs u₀ s x s = x.val := by
  exact tendsto_nhds_unique (limit_tendsto B M A hM hA hB hs u₀ s x s)
    (by simpa only [solution_initial] using cutoff_tendsto x.val)

lemma limit_norm (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (PhysicalTensor.L2T L))
    (s : ℝ) (x : momentDomain (L := L) 3) (t : ℝ) :
    ‖limit B M A hM hA hB hs u₀ s x t‖ = ‖x.val‖ := by
  have he : (fun N => ‖solution B M A hA hB hs u₀ N s x.val t‖) =
      (fun N => ‖cutoff N x.val‖) := by
    funext N
    exact propagator_norm B M A hA hB hs u₀ N s t (cutoff N x.val)
  have h := (limit_tendsto B M A hM hA hB hs u₀ s x t).norm
  rw [he] at h
  exact tendsto_nhds_unique h (cutoff_tendsto x.val).norm

/-- Every propagated initial number moment passes to the ACTUAL limit. -/
theorem limit_energy_envelope (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (PhysicalTensor.L2T L))
    (s : ℝ) (x : momentDomain (L := L) 3) (j : ℕ) (hj : 1 ≤ j)
    (hxj : x.val ∈ momentDomain (L := L) j) (t : ℝ) :
    limit B M A hM hA hB hs u₀ s x t ∈ momentDomain (L := L) j ∧
      energy j (limit B M A hM hA hB hs u₀ s x t) ≤
        energy j x.val * Real.exp (differenceConstant j*(M*pairMajorant A)*|t-s|) := by
  exact normLimit_bound j _ _ _
    (fun N => ⟨solution_momentDomain B M A hA hB hs u₀ N j s x.val t,
      solution_energy_envelope B M A hA hB hs u₀ N j hj s ⟨x.val, hxj⟩ t⟩)
    (limit_tendsto B M A hM hA hB hs u₀ s x t)

/-- D3-type local essential energy bound, derived for the actual limit. -/
theorem limit_energyBounded (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (PhysicalTensor.L2T L))
    (s T : ℝ) (x : momentDomain (L := L) 3) (j : ℕ) (hj : 1 ≤ j)
    (hxj : x.val ∈ momentDomain (L := L) j) :
    EnergyBounded j (Icc (s-T) (s+T)) (limit B M A hM hA hB hs u₀ s x) := by
  let c := differenceConstant j*(M*pairMajorant A)
  refine ⟨energy j x.val * Real.exp (c*T),
    mul_nonneg (energy_nonneg j x.val) (Real.exp_pos _).le, ?_⟩
  apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
  intro t ht
  have h := limit_energy_envelope B M A hM hA hB hs u₀ s x j hj hxj t
  refine ⟨h.1, h.2.trans ?_⟩
  have hst : |t-s| ≤ T := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hc : 0 ≤ c := mul_nonneg (differenceConstant_nonneg j)
    (mul_nonneg hM (pairMajorant_nonneg A hA))
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hst hc)) (energy_nonneg j x.val)

end QuantumNLS.Prop022CutoffLimitR120
#print axioms QuantumNLS.Prop022CutoffLimitR120.actual_uniform_cauchy
#print axioms QuantumNLS.Prop022CutoffLimitR120.limit_tendsto
#print axioms QuantumNLS.Prop022CutoffLimitR120.limit_continuous
#print axioms QuantumNLS.Prop022CutoffLimitR120.limit_norm
#print axioms QuantumNLS.Prop022CutoffLimitR120.limit_energyBounded

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022CutoffLimitR120." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022CutoffLimitR120." then
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
  Lean.logInfo m!"R120 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
