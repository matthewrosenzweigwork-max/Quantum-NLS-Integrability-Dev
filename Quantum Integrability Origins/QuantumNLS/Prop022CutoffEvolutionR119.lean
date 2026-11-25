import QuantumNLS.Prop022BoundedEvolutionR119
import QuantumNLS.Prop022CutoffCommutatorR119
import Mathlib.Analysis.ODE.Gronwall

/-! Actual nonautonomous PROP-022 cutoff solutions and their propagated
number moments. The envelope is independent of the cutoff. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace Topology ComplexConjugate
open ContinuousLinearMap
namespace QuantumNLS.Prop022CutoffEvolutionR119
open BetheCoefficientTransform PhysicalTensor Ext025B3PhysicalSectors Ext005Moments
open Ext005MomentEnergyR108 Ext005FormCutoffR109 Ext005PairCommutatorR108
open Prop022FactorialCoefficientsR115 Prop022ActualProfileR117 Prop022FactorialMajorantR115
open Prop022CutoffHamiltonianR115 Prop022PhysicalCommutatorR115
open Prop022CutoffCommutatorR119 Prop022BoundedEvolutionR119
variable {L : ℝ} [Fact (0 < L)]
local instance : NormedSpace ℝ (Fock L) := NormedSpace.restrictScalars ℝ ℂ (Fock L)

/-- Literal cutoff generator along the proved Hartree trajectory. -/
def generator (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L)) (N : ℕ) (t : ℝ) : Fock L →L[ℂ] Fock L :=
  cutoffHamiltonian (numberCoefficient B (profile B M A hA hB hs u₀ t))
    (pairCoefficient B (profile B M A hA hB hs u₀ t)) N

lemma generator_continuous (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L)) (N : ℕ) : Continuous (generator B M A hA hB hs u₀ N) := by
  have hc := actual_coefficients_continuous B M A hA hB hs u₀
  exact Prop022FormContinuityR119.cutoff_continuous _ _ hc.1 hc.2
    (fun t => numberCoefficient_adjoint B hs _) N

lemma generator_symmetric (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L)) (N : ℕ) (t : ℝ) :
    (generator B M A hA hB hs u₀ N t).IsSymmetric :=
  Prop022CutoffHamiltonianR115.cutoff_symmetric _ (numberCoefficient_adjoint B hs _) _ N

/-- Global bounded cutoff propagator; no evolution or norm estimate input. -/
def propagator (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L)) (N : ℕ) (s t : ℝ) : Fock L →L[ℂ] Fock L :=
  evolution (generator B M A hA hB hs u₀ N) (generator_continuous B M A hA hB hs u₀ N) s t

lemma propagator_derivative (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L)) (N : ℕ) (s : ℝ) (x : Fock L) (t : ℝ) :
    HasDerivAt (fun r => propagator B M A hA hB hs u₀ N s r x)
      ((-Complex.I) • generator B M A hA hB hs u₀ N t (propagator B M A hA hB hs u₀ N s t x)) t :=
  evolution_apply_derivative _ _ s x t

lemma propagator_norm (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L)) (N : ℕ) (s t : ℝ) (x : Fock L) :
    ‖propagator B M A hA hB hs u₀ N s t x‖ = ‖x‖ :=
  evolution_norm _ _ (generator_symmetric B M A hA hB hs u₀ N) s t x

/-- The actual cutoff propagator is a surjective complex linear isometry. -/
def propagatorEquiv (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L)) (N : ℕ) (s t : ℝ) : Fock L ≃ₗᵢ[ℂ] Fock L :=
  evolutionEquiv _ (generator_continuous B M A hA hB hs u₀ N)
    (generator_symmetric B M A hA hB hs u₀ N) s t

/-- The actual cutoff solution with projected initial datum. -/
def solution (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L)) (N : ℕ) (s : ℝ) (x : Fock L) (t : ℝ) : Fock L :=
  propagator B M A hA hB hs u₀ N s t (cutoff N x)

lemma solution_continuous (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L)) (N : ℕ) (s : ℝ) (x : Fock L) :
    Continuous (solution B M A hA hB hs u₀ N s x) :=
  continuous_iff_continuousAt.mpr (fun t =>
    (propagator_derivative B M A hA hB hs u₀ N s (cutoff N x) t).continuousAt)

lemma solution_initial (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L)) (N : ℕ) (s : ℝ) (x : Fock L) :
    solution B M A hA hB hs u₀ N s x s = cutoff N x := by
  exact congrArg (fun T : Fock L →L[ℂ] Fock L => T (cutoff N x)) (evolution_self _ _ s)

lemma solution_cutoff (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L)) (N : ℕ) (s : ℝ) (x : Fock L) (t : ℝ) :
    cutoff N (solution B M A hA hB hs u₀ N s x t) = solution B M A hA hB hs u₀ N s x t := by
  apply evolution_fixed _ _ (generator_symmetric B M A hA hB hs u₀ N) (cutoff N)
    (fun r y => ?_) s (cutoff N x) (cutoff_idempotent N x) t
  exact (cutoffHamiltonian_range _ _ N y).trans (cutoffHamiltonian_cutoff _ _ N y).symm

lemma solution_momentDomain (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L)) (N j : ℕ) (s : ℝ) (x : Fock L) (t : ℝ) :
    solution B M A hA hB hs u₀ N s x t ∈ momentDomain (L := L) j := by
  rw [← solution_cutoff B M A hA hB hs u₀ N s x t]
  exact cutoff_mem j N _

/-- Moment differentiation along the constructed cutoff solution, proved
from its equation and the literal finite-sector commutator identity. -/
theorem solution_energy_derivative (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L)) (N j : ℕ) (s : ℝ) (x : Fock L) (t : ℝ) :
    let ψ := solution B M A hA hB hs u₀ N s x
    HasDerivAt (fun r => energy j (ψ r))
      (physicalCommutator j (pairCoefficient B (profile B M A hA hB hs u₀ t)) (ψ t)).re t := by
  dsimp only
  have he := expectation_derivative _ (generator_continuous B M A hA hB hs u₀ N)
    (generator_symmetric B M A hA hB hs u₀ N) (momentCutoff j N) s t (cutoff N x)
  have hid := cutoff_commutator_identity
    (numberCoefficient B (profile B M A hA hB hs u₀ t))
    (pairCoefficient B (profile B M A hA hB hs u₀ t)) j N
    (solution B M A hA hB hs u₀ N s x t)
  change HasDerivAt (fun r => ⟪solution B M A hA hB hs u₀ N s x r,
    momentCutoff j N (solution B M A hA hB hs u₀ N s x r)⟫_ℂ)
    (Complex.I * ⟪solution B M A hA hB hs u₀ N s x t,
      (cutoffHamiltonian (numberCoefficient B (profile B M A hA hB hs u₀ t))
        (pairCoefficient B (profile B M A hA hB hs u₀ t)) N * momentCutoff (L := L) j N -
       momentCutoff (L := L) j N * cutoffHamiltonian (numberCoefficient B (profile B M A hA hB hs u₀ t))
        (pairCoefficient B (profile B M A hA hB hs u₀ t)) N)
          (solution B M A hA hB hs u₀ N s x t)⟫_ℂ) t at he
  rw [hid, solution_cutoff] at he
  have heq : (fun r => ⟪solution B M A hA hB hs u₀ N s x r,
    momentCutoff j N (solution B M A hA hB hs u₀ N s x r)⟫_ℂ) =
      (fun r => (energy j (solution B M A hA hB hs u₀ N s x r) : ℂ)) := by
    funext r
    rw [momentCutoff_pair, solution_cutoff]
  rw [heq] at he
  have hh := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t he
  simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using hh

/-- The differential inequality is derived on the actual solution and has
no cutoff in its coefficient. -/
theorem solution_energy_derivative_bound (B : ∀ m, HN L m →L[ℂ] HN L m)
    (M A : ℝ) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (L2T L))
    (N j : ℕ) (hj : 1 ≤ j) (s : ℝ) (x : Fock L) (t : ℝ) :
    let ψ := solution B M A hA hB hs u₀ N s x
    |deriv (fun r => energy j (ψ r)) t| ≤
      differenceConstant j * (M * pairMajorant A) * energy j (ψ t) := by
  dsimp only
  rw [(solution_energy_derivative B M A hA hB hs u₀ N j s x t).deriv]
  exact (Complex.abs_re_le_norm _).trans
    (factorialCommutator_bound B M A hA hB _
      ((profile_spec B M A hA hB hs u₀).2.2.1 t) j hj
      ⟨_, solution_momentDomain B M A hA hB hs u₀ N j s x t⟩)

/-- Scalar Gronwall on both sides of the initial time. -/
lemma real_gronwall (f : ℝ → ℝ) (hf : ∀ t, 0 ≤ f t) (hd : Differentiable ℝ f)
    (c : ℝ) (hb : ∀ t, |deriv f t| ≤ c * f t) (s t : ℝ) :
    f t ≤ f s * Real.exp (c * |t-s|) := by
  have forward (g : ℝ → ℝ) (hg : ∀ r, 0 ≤ g r) (hgd : Differentiable ℝ g)
      (hgb : ∀ r, |deriv g r| ≤ c * g r) (a b : ℝ) (hab : a ≤ b) :
      g b ≤ g a * Real.exp (c * (b-a)) := by
    have h := norm_le_gronwallBound_of_norm_deriv_right_le
      (f := g) (f' := deriv g) (δ := g a) (K := c) (ε := 0)
      hgd.continuous.continuousOn (fun r _ => (hgd r).hasDerivAt.hasDerivWithinAt)
      (by rw [Real.norm_eq_abs, abs_of_nonneg (hg a)])
      (fun r _ => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hg r), add_zero] using hgb r)
      b ⟨hab, le_rfl⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hg b), gronwallBound_ε0] using h
  by_cases hst : s ≤ t
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using forward f hf hd hb s t hst
  · have hg (r : ℝ) : HasDerivAt (fun q => f (-q)) (-deriv f (-r)) r := by
      simpa only [Function.comp_def, neg_one_smul] using
        ((hd (-r)).hasDerivAt.scomp r (hasDerivAt_id r).neg)
    have hgb (r : ℝ) : |deriv (fun q => f (-q)) r| ≤ c * f (-r) := by
      rw [(hg r).deriv, abs_neg]
      exact hb (-r)
    have h := forward (fun q => f (-q)) (fun q => hf (-q))
      (fun r => (hg r).differentiableAt) hgb (-s) (-t) (by linarith)
    simpa only [neg_neg, abs_of_neg (sub_neg.mpr (lt_of_not_ge hst)), neg_sub_neg,
      neg_sub] using h

/-- A cutoff-uniform propagated moment envelope, with initial energy and
Gronwall coefficient derived from the physical factorial coefficients. -/
theorem solution_energy_envelope (B : ∀ m, HN L m →L[ℂ] HN L m)
    (M A : ℝ) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (L2T L))
    (N j : ℕ) (hj : 1 ≤ j) (s : ℝ) (x : momentDomain (L := L) j) (t : ℝ) :
    energy j (solution B M A hA hB hs u₀ N s x.val t) ≤
      energy j x.val * Real.exp (differenceConstant j * (M * pairMajorant A) * |t-s|) := by
  have hd : Differentiable ℝ (fun r => energy j (solution B M A hA hB hs u₀ N s x.val r)) :=
    fun r => (solution_energy_derivative B M A hA hB hs u₀ N j s x.val r).differentiableAt
  have h := real_gronwall _ (fun r => energy_nonneg j _) hd _
    (solution_energy_derivative_bound B M A hA hB hs u₀ N j hj s x.val) s t
  rw [solution_initial] at h
  exact h.trans (mul_le_mul_of_nonneg_right (cutoff_energy_le j N x) (Real.exp_pos _).le)

/-- Every zero-particle datum has the proved all-order initial energy,
including the normalized physical vacuum. -/
theorem zero_sector_energy_envelope (B : ∀ m, HN L m →L[ℂ] HN L m)
    (M A : ℝ) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (L2T L))
    (N j : ℕ) (hj : 1 ≤ j) (s t : ℝ) (v : HN L 0) :
    energy j (solution B M A hA hB hs u₀ N s (inclusion L 0 v) t) ≤
      ‖v‖ ^ 2 * Real.exp (differenceConstant j * (M * pairMajorant A) * |t-s|) := by
  have hv := vacuum_sector_energy j v
  have he := solution_energy_envelope B M A hA hB hs u₀ N j hj s ⟨inclusion L 0 v, hv.1⟩ t
  simpa only [hv.2] using he

/-- On every finite centered interval the actual cutoff solution has the
D3-type essential energy bound, with one constant for all cutoffs. -/
theorem solution_energyBounded (B : ∀ m, HN L m →L[ℂ] HN L m)
    (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (L2T L))
    (j : ℕ) (hj : 1 ≤ j) (s T : ℝ) (x : momentDomain (L := L) j) (N : ℕ) :
    EnergyBounded j (Set.Icc (s-T) (s+T)) (solution B M A hA hB hs u₀ N s x.val) := by
  let c := differenceConstant j * (M * pairMajorant A)
  refine ⟨energy j x.val * Real.exp (c*T),
    mul_nonneg (energy_nonneg j x.val) (Real.exp_pos _).le, ?_⟩
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
  refine ⟨solution_momentDomain B M A hA hB hs u₀ N j s x.val t, ?_⟩
  have hst : |t-s| ≤ T := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hc : 0 ≤ c := mul_nonneg (differenceConstant_nonneg j)
    (mul_nonneg hM (pairMajorant_nonneg A hA))
  exact (solution_energy_envelope B M A hA hB hs u₀ N j hj s x t).trans
    (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hst hc)) (energy_nonneg j x.val))

end QuantumNLS.Prop022CutoffEvolutionR119

#print axioms QuantumNLS.Prop022CutoffEvolutionR119.generator_continuous

#print axioms QuantumNLS.Prop022CutoffEvolutionR119.propagator_derivative

#print axioms QuantumNLS.Prop022CutoffEvolutionR119.propagator_norm

#print axioms QuantumNLS.Prop022CutoffEvolutionR119.solution_cutoff

#print axioms QuantumNLS.Prop022CutoffEvolutionR119.solution_momentDomain

#print axioms QuantumNLS.Prop022CutoffEvolutionR119.solution_energy_derivative

#print axioms QuantumNLS.Prop022CutoffEvolutionR119.solution_energy_derivative_bound

#print axioms QuantumNLS.Prop022CutoffEvolutionR119.solution_energy_envelope

#print axioms QuantumNLS.Prop022CutoffEvolutionR119.solution_energyBounded

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022CutoffEvolutionR119." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022CutoffEvolutionR119." then
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
  Lean.logInfo m!"R119 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
