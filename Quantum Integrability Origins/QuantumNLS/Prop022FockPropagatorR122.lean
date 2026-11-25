import QuantumNLS.Prop022NativeCompetitorR121
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.MetricSpace.Equicontinuity

/-! The physical quadratic propagator on all Fock data, obtained by extending
its proved dense-domain cutoff limit. No propagator or evolution bound is an input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace Topology ComplexConjugate
open Set Filter ContinuousLinearMap
namespace QuantumNLS.Prop022FockPropagatorR122
open BetheCoefficientTransform Ext025B3PhysicalSectors Ext005Moments Ext005FormCutoffR109
open Prop022FactorialCoefficientsR115 Prop022CutoffEvolutionR119 Prop022CutoffLimitR120
open Prop022BoundedEvolutionR119
variable {L : ℝ} [Fact (0 < L)]

lemma moment_dense (j : ℕ) : DenseRange (momentDomain (L := L) j).subtype := by
  intro x
  apply mem_closure_of_tendsto (cutoff_tendsto x)
  exact Eventually.of_forall (fun N => ⟨⟨cutoff N x, cutoff_mem j N x⟩, rfl⟩)

variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
  (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
  (u₀ : Prop001.Sphere (PhysicalTensor.L2T L))

local notation "lim" => limit B M A hM hA hB hs u₀
local notation "PN" => propagator B M A hA hB hs u₀

lemma limit_add (s t : ℝ) (x y : momentDomain (L := L) 3) :
    lim s (x+y) t = lim s x t + lim s y t := by
  apply tendsto_nhds_unique (limit_tendsto B M A hM hA hB hs u₀ s (x+y) t)
  simpa only [solution, Submodule.coe_add, map_add] using
    (limit_tendsto B M A hM hA hB hs u₀ s x t).add
      (limit_tendsto B M A hM hA hB hs u₀ s y t)

lemma limit_smul (s t : ℝ) (c : ℂ) (x : momentDomain (L := L) 3) :
    lim s (c • x) t = c • lim s x t := by
  apply tendsto_nhds_unique (limit_tendsto B M A hM hA hB hs u₀ s (c • x) t)
  simpa only [solution, Submodule.coe_smul, map_smul] using
    (limit_tendsto B M A hM hA hB hs u₀ s x t).const_smul c

def denseMap (s t : ℝ) : momentDomain (L := L) 3 →ₗ[ℂ] Fock L where
  toFun x := lim s x t
  map_add' := limit_add B M A hM hA hB hs u₀ s t
  map_smul' c x := limit_smul B M A hM hA hB hs u₀ s t c x

/-- The bounded extension of the actual quadratic evolution. -/
def evolution (s t : ℝ) : Fock L →ₗᵢ[ℂ] Fock L :=
  (denseMap B M A hM hA hB hs u₀ s t).extendOfIsometry (moment_dense 3)
    (fun x => limit_norm B M A hM hA hB hs u₀ s x t)

local notation "V" => evolution B M A hM hA hB hs u₀

lemma evolution_on_domain (s t : ℝ) (x : momentDomain (L := L) 3) :
    V s t x.val = lim s x t :=
  LinearMap.extendOfIsometry_eq _ _ _ x

/-- Strong convergence of the unprojected cutoff unitaries on every Fock vector. -/
lemma cutoff_strong (s t : ℝ) (x : Fock L) :
    Tendsto (fun N => PN N s t x) atTop (𝓝 (V s t x)) := by
  refine isClosed_property (p := fun x : Fock L =>
    Tendsto (fun N => PN N s t x) atTop (𝓝 (V s t x))) (moment_dense (L := L) 3) ?_ ?_ x
  · apply Equicontinuous.isClosed_setOfPred_tendsto ?_ (V s t).continuous
    exact Metric.equicontinuous_of_continuity_modulus id (tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0))
      (fun N x => PN N s t x) (fun x y N => by
        rw [dist_eq_norm, ← map_sub, propagator_norm, dist_eq_norm]; rfl)
  · intro y
    have herr : Tendsto (fun N => PN N s t (y.val-cutoff N y.val)) atTop (𝓝 0) := by
      apply squeeze_zero_norm (fun N => (propagator_norm B M A hA hB hs u₀ N s t _).le)
      simpa only [sub_self, norm_zero] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => y.val) atTop (𝓝 y.val)).sub (cutoff_tendsto y.val)).norm
    have he := (limit_tendsto B M A hM hA hB hs u₀ s y t).add herr
    change Tendsto (fun N => PN N s t y.val) atTop (𝓝 (V s t y.val))
    rw [evolution_on_domain]
    simpa only [solution, map_sub, add_sub_cancel, add_zero] using he

lemma evolution_self (s : ℝ) (x : Fock L) : V s s x = x := by
  apply tendsto_nhds_unique (cutoff_strong B M A hM hA hB hs u₀ s s x)
  simpa only [propagator, Prop022BoundedEvolutionR119.evolution_self,
    one_apply_eq_self] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))

/-- Passing the exact bounded cocycle to the strong limit, with the moving
intermediate vector controlled by the cutoff isometry. -/
lemma evolution_comp (r s t : ℝ) (x : Fock L) :
    V s t (V r s x) = V r t x := by
  have herr : Tendsto (fun N => PN N s t (PN N r s x - V r s x)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun N => (propagator_norm B M A hA hB hs u₀ N s t _).le)
    simpa only [sub_self, norm_zero] using
      ((cutoff_strong B M A hM hA hB hs u₀ r s x).sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => V r s x) atTop (𝓝 (V r s x)))).norm
  have hh := (cutoff_strong B M A hM hA hB hs u₀ s t (V r s x)).add herr
  have he (N : ℕ) : PN N s t (V r s x) + PN N s t (PN N r s x - V r s x) = PN N r t x := by
    rw [map_sub, add_sub_cancel]
    exact congrArg (fun T : Fock L →L[ℂ] Fock L => T x)
      (Prop022BoundedEvolutionR119.evolution_comp _ _
        (generator_symmetric B M A hA hB hs u₀ N) r s t)
  simp only [he, add_zero] at hh
  exact tendsto_nhds_unique hh (cutoff_strong B M A hM hA hB hs u₀ r t x)

/-- The physical quadratic propagator is unitary, with inverse V(t,s). -/
def propagator (s t : ℝ) : Fock L ≃ₗᵢ[ℂ] Fock L :=
  LinearIsometryEquiv.ofSurjective (V s t) (by
    intro x
    refine ⟨V t s x, ?_⟩
    rw [evolution_comp, evolution_self])

lemma propagator_apply (s t : ℝ) (x : Fock L) :
    propagator B M A hM hA hB hs u₀ s t x = V s t x := rfl

/-- Strong continuity for every Fock datum follows by uniform approximation
by finite particle data and the isometry of the extended evolution. -/
theorem evolution_continuous (s : ℝ) (x : Fock L) : Continuous (fun t => V s t x) := by
  have hu : TendstoUniformly (fun N t => V s t (cutoff N x)) (fun t => V s t x) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    have hh := (cutoff_tendsto x).eventually (Metric.ball_mem_nhds x hε)
    filter_upwards [hh] with N hN t
    simpa only [Metric.mem_ball, dist_eq_norm, ← map_sub, LinearIsometry.norm_map, norm_sub_rev] using hN
  apply hu.continuous
  exact (Eventually.of_forall (fun N => by
    have hc := limit_continuous B M A hM hA hB hs u₀ s ⟨cutoff N x, cutoff_mem 3 N x⟩
    have he : (fun t => V s t (cutoff N x)) = lim s ⟨cutoff N x, cutoff_mem 3 N x⟩ :=
      funext (fun t => evolution_on_domain B M A hM hA hB hs u₀ s t ⟨cutoff N x, cutoff_mem 3 N x⟩)
    rw [he]
    exact hc)).frequently

end QuantumNLS.Prop022FockPropagatorR122
#print axioms QuantumNLS.Prop022FockPropagatorR122.propagator
#print axioms QuantumNLS.Prop022FockPropagatorR122.evolution_comp
#print axioms QuantumNLS.Prop022FockPropagatorR122.evolution_continuous

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022FockPropagatorR122." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022FockPropagatorR122." then
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
