import QuantumNLS.Prop022FockPropagatorR122

/-! Moment preservation for arbitrary data in each moment domain, and strong
moment continuity with two additional initial moments. Estimates are proved
from the actual cutoff solutions, not supplied as evolution premises. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace Topology
open Set Filter ContinuousLinearMap MeasureTheory
namespace QuantumNLS.Prop022DomainR122
open BetheCoefficientTransform Ext025B3PhysicalSectors Ext005Moments Ext005MomentEnergyR108
open Ext005FormCutoffR109 Ext005MomentLimitR109 Ext005PairCommutatorR108
open Prop022FactorialCoefficientsR115 Prop022FactorialMajorantR115 Prop022CutoffEvolutionR119
open Prop022CutoffLimitR120 Prop022MomentTailR120 Prop022FockPropagatorR122
variable {L : ℝ} [Fact (0 < L)]
variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
  (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
  (u₀ : Prop001.Sphere (PhysicalTensor.L2T L))
local notation "V" => Prop022FockPropagatorR122.evolution B M A hM hA hB hs u₀

lemma solution_tendsto (s t : ℝ) (x : Fock L) :
    Tendsto (fun N => solution B M A hA hB hs u₀ N s x t) atTop (𝓝 (V s t x)) := by
  have herr : Tendsto (fun N => Prop022CutoffEvolutionR119.propagator B M A hA hB hs u₀ N s t (cutoff N x-x)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun N => (propagator_norm B M A hA hB hs u₀ N s t _).le)
    simpa only [sub_self, norm_zero] using
      ((cutoff_tendsto x).sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))).norm
  have hh := (cutoff_strong B M A hM hA hB hs u₀ s t x).add herr
  simpa only [solution, map_sub, add_sub_cancel, add_zero] using hh

/-- All positive integer moments propagate on their own full domain. -/
theorem evolution_energy (j : ℕ) (hj : 1 ≤ j) (s t : ℝ)
    (x : momentDomain (L := L) j) :
    V s t x.val ∈ momentDomain (L := L) j ∧
      energy j (V s t x.val) ≤ energy j x.val *
        Real.exp (differenceConstant j*(M*pairMajorant A)*|t-s|) := by
  exact normLimit_bound j _ _ _
    (fun N => ⟨solution_momentDomain B M A hA hB hs u₀ N j s x.val t,
      solution_energy_envelope B M A hA hB hs u₀ N j hj s x t⟩)
    (solution_tendsto B M A hM hA hB hs u₀ s t x.val)

/-- The essential energy bound used by the D3 class is a conclusion. -/
theorem evolution_energyBounded (j : ℕ) (hj : 1 ≤ j) (s T : ℝ)
    (x : momentDomain (L := L) j) :
    EnergyBounded j (Icc (s-T) (s+T)) (fun t => V s t x.val) := by
  let c := differenceConstant j*(M*pairMajorant A)
  refine ⟨energy j x.val * Real.exp (c*T),
    mul_nonneg (energy_nonneg j x.val) (Real.exp_pos _).le, ?_⟩
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro t ht
  have h := evolution_energy B M A hM hA hB hs u₀ j hj s t x
  refine ⟨h.1, h.2.trans ?_⟩
  have hst : |t-s| ≤ T := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hc : 0 ≤ c := mul_nonneg (differenceConstant_nonneg j)
    (mul_nonneg hM (pairMajorant_nonneg A hA))
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hst hc)) (energy_nonneg j x.val)

/-- Each moment domain is preserved in both directions by the actual unitary. -/
theorem evolution_domain_iff (j : ℕ) (hj : 1 ≤ j) (s t : ℝ) (x : Fock L) :
    V s t x ∈ momentDomain (L := L) j ↔ x ∈ momentDomain (L := L) j := by
  constructor
  · intro hx
    have hh := (evolution_energy B M A hM hA hB hs u₀ j hj t s ⟨V s t x,hx⟩).1
    simpa only [evolution_comp, evolution_self] using hh
  · intro hx
    exact (evolution_energy B M A hM hA hB hs u₀ j hj s t ⟨x,hx⟩).1

/-- Local uniform truncation in a lower moment norm. -/
lemma root_uniform (j : ℕ) (s T : ℝ) (x : momentDomain (L := L) (j+2)) :
    TendstoUniformlyOn (fun N t => rootCutoff j N (V s t x.val))
      (fun t => rootLift j (V s t x.val)) atTop (Icc (s-T) (s+T)) := by
  let C := energy (j+2) x.val * Real.exp (differenceConstant (j+2)*(M*pairMajorant A)*T)
  have hC : 0 ≤ C := mul_nonneg (energy_nonneg _ _) (Real.exp_pos _).le
  have hb (t : ℝ) (ht : t ∈ Icc (s-T) (s+T)) :
      ∃ hx : V s t x.val ∈ momentDomain (L := L) (j+2),
        ‖momentRoot (j+2) ⟨V s t x.val,hx⟩‖ ≤ Real.sqrt C := by
    have he := evolution_energy B M A hM hA hB hs u₀ (j+2) (by omega) s t x
    refine ⟨he.1, ?_⟩
    have hc : 0 ≤ differenceConstant (j+2)*(M*pairMajorant A) :=
      mul_nonneg (differenceConstant_nonneg _) (mul_nonneg hM (pairMajorant_nonneg A hA))
    have hst : |t-s| ≤ T := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hsq : ‖momentRoot (j+2) ⟨V s t x.val,he.1⟩‖^2 ≤ C := by
      have hn := energy_eq_root (j+2) (⟨V s t x.val,he.1⟩ : momentDomain (L := L) (j+2))
      exact hn.symm.le.trans (he.2.trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hst hc)) (energy_nonneg _ _)))
    nlinarith [Real.sq_sqrt hC, Real.sqrt_nonneg C, norm_nonneg (momentRoot (j+2) ⟨V s t x.val,he.1⟩)]
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hz := inverse_cutoff_tendsto.mul_const (Real.sqrt C)
  have hz' : Tendsto (fun N : ℕ => ((N : ℝ)+1)⁻¹*Real.sqrt C) atTop (𝓝 0) := by
    simpa only [zero_mul] using hz
  filter_upwards [hz'.eventually (gt_mem_nhds hε)] with N hN t ht
  obtain ⟨hx,hb⟩ := hb t ht
  have hh := (root_truncation_error j N ⟨V s t x.val,hx⟩).trans
    (mul_le_mul_of_nonneg_left hb (by positivity))
  rw [rootLift_eq j _ (domain_mono (by omega) hx), dist_eq_norm]
  exact hh.trans_lt hN

/-- Interpolation: Fock continuity and the proved higher moment estimate
imply strong continuity in each lower moment domain. -/
theorem evolution_root_continuous (j : ℕ) (s : ℝ)
    (x : momentDomain (L := L) (j+2)) :
    Continuous (fun t => rootLift j (V s t x.val)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hc := (root_uniform B M A hM hA hB hs u₀ j s (|t-s|+1) x).continuousOn
    (Eventually.of_forall (fun N =>
      ((rootCutoff j N).continuous.comp (evolution_continuous B M A hM hA hB hs u₀ s x.val)).continuousOn)).frequently
  apply hc.continuousAt
  apply Icc_mem_nhds <;> linarith [neg_abs_le (t-s), le_abs_self (t-s)]

end QuantumNLS.Prop022DomainR122
#print axioms QuantumNLS.Prop022DomainR122.evolution_energy
#print axioms QuantumNLS.Prop022DomainR122.evolution_domain_iff
#print axioms QuantumNLS.Prop022DomainR122.evolution_root_continuous

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022DomainR122." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022DomainR122." then
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
  Lean.logInfo m!"R122 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
