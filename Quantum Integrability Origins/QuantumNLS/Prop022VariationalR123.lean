import QuantumNLS.Prop022RealEvolutionR123
import QuantumNLS.Prop022HessianR118
import QuantumNLS.Ext006KernelHilbertSchmidt

/-! The real derivative of the actual source Hartree vector field and its
nonautonomous variational evolution. No supplied linearized flow is used. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal
namespace QuantumNLS.Prop022VariationalR123
open PhysicalTensor BetheCoefficientTransform
open Prop022FactorialCoefficientsR115 Prop022ActualProfileR117
open Prop022GradientR118 Prop022HessianR118
open Ext006Blocks Ext006KernelHilbertSchmidt
variable {L : ℝ} [Fact (0 < L)]
local instance : Inner ℝ (L2T L) := Inner.rclikeToReal ℂ (L2T L)
local instance : AddCommGroup (L2T L) := (inferInstance : NormedAddCommGroup (L2T L)).toAddCommGroup

/-- Real Riesz inversion on the original physical Hilbert space. -/
def riesz : (L2T L →L[ℝ] ℝ) →L[ℝ] L2T L :=
  (InnerProductSpace.toDual ℝ (L2T L)).symm.toContinuousLinearEquiv.toContinuousLinearMap

lemma gradient_eq_riesz (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hs : ∀ m, (B m).adjoint = B m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (u : L2T L) :
    gradient B u = (1/2 : ℝ) • riesz (seriesD B u) := by
  apply ext_inner_right ℝ
  intro h
  rw [real_inner_smul_left]
  change (⟪gradient B u, h⟫_ℂ).re = (1/2 : ℝ) * ⟪(InnerProductSpace.toDual ℝ (L2T L)).symm (seriesD B u), h⟫_ℝ
  rw [InnerProductSpace.toDual_symm_apply, seriesD_eq_gradient B hs M A hA hB]
  ring

/-- The derivative follows from the full Hessian, including its proved
factorial summability. The factor one half is forced by dF=2 Re <grad F,·>. -/
def gradientDerivative (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) :
    L2T L →L[ℝ] L2T L := (1/2 : ℝ) • (riesz ∘L seriesHessian B u)

lemma gradient_hasFDerivAt (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hs : ∀ m, (B m).adjoint = B m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (u : L2T L) :
    HasFDerivAt (gradient B) (gradientDerivative B u) u := by
  have he : fderiv ℝ (Prop022ClassicalTimeR116.classicalSeries B) = seriesD B :=
    funext (fun v => (classicalSeries_hasFDerivAt B hs M A hA hB v).fderiv)
  have hd := classicalSeries_hasSecondFDerivAt B hs M A hA hB u
  rw [he] at hd
  have h := ((riesz (L := L)).hasFDerivAt.comp u hd).const_smul (1/2 : ℝ)
  have hg : gradient B = fun v => (1/2 : ℝ) • riesz (seriesD B v) :=
    funext (gradient_eq_riesz B hs M A hA hB)
  rw [hg]
  exact h

lemma gradientDerivative_continuous (B : ∀ m, HN L m →L[ℂ] HN L m)
    (M A : ℝ) (hA : 0 ≤ A) (hB : FactorialBound B M A) :
    Continuous (gradientDerivative B) := by
  have hh := seriesHessian_continuous B M A hA hB
  unfold gradientDerivative
  exact (continuous_const.clm_comp hh).const_smul (1/2 : ℝ)

/-- The Schrodinger rotation uses the original complex structure. -/
def rotation : L2T L →L[ℝ] L2T L :=
  ((-Complex.I) • ContinuousLinearMap.id ℂ (L2T L)).restrictScalars ℝ

def velocityDerivative (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) :
    L2T L →L[ℝ] L2T L := rotation ∘L gradientDerivative B u

lemma velocity_hasFDerivAt (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hs : ∀ m, (B m).adjoint = B m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (u : L2T L) :
    HasFDerivAt (velocity B) (velocityDerivative B u) u := by
  exact (rotation (L := L)).hasFDerivAt.comp u
    (gradient_hasFDerivAt B hs M A hA hB u)

lemma velocityDerivative_continuous (B : ∀ m, HN L m →L[ℂ] HN L m)
    (M A : ℝ) (hA : 0 ≤ A) (hB : FactorialBound B M A) :
    Continuous (velocityDerivative B) :=
  continuous_const.clm_comp (gradientDerivative_continuous B M A hA hB)

variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
  (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
  (u₀ : Prop001.Sphere (L2T L))

/-- The actual time-dependent derivative, evaluated along the proved source path. -/
def generator (t : ℝ) : L2T L →L[ℝ] L2T L :=
  velocityDerivative B (profile B M A hA hB hs u₀ t)

lemma generator_continuous : Continuous (generator B M A hA hB hs u₀) :=
  (velocityDerivative_continuous B M A hA hB).comp
    (profile_spec B M A hA hB hs u₀).2.1.continuous

/-- Conventional S(t,s): final time, then initial time. -/
def flow (t s : ℝ) : L2T L ≃L[ℝ] L2T L :=
  Prop022RealEvolutionR123.evolutionEquiv (generator B M A hA hB hs u₀)
    (generator_continuous B M A hA hB hs u₀) s t

lemma flow_self (s : ℝ) (x : L2T L) : flow B M A hA hB hs u₀ s s x = x := by
  change Prop022RealEvolutionR123.evolution _ _ s s x = x
  rw [Prop022RealEvolutionR123.evolution_self, one_apply_eq_self]

lemma flow_comp (r s t : ℝ) (x : L2T L) :
    flow B M A hA hB hs u₀ t s (flow B M A hA hB hs u₀ s r x) =
      flow B M A hA hB hs u₀ t r x := by
  exact congrArg (fun T : L2T L →L[ℝ] L2T L => T x)
    (Prop022RealEvolutionR123.evolution_comp _ _ r s t)

/-- A true variational equation: its coefficient is the proved Frechet
 derivative of the actual source vector field, at every signed time. -/
theorem flow_variational (s t : ℝ) (x : L2T L) :
    HasDerivAt (fun r => flow B M A hA hB hs u₀ r s x)
      (fderiv ℝ (velocity B) (profile B M A hA hB hs u₀ t)
        (flow B M A hA hB hs u₀ t s x)) t := by
  rw [(velocity_hasFDerivAt B hs M A hA hB _).fderiv]
  exact Prop022RealEvolutionR123.evolution_apply_derivative _ _ s x t

/-- Uniqueness among all differentiable solutions, with no supplied estimates. -/
theorem flow_unique (s : ℝ) (x : L2T L) (v : ℝ → L2T L)
    (hv : ∀ t, HasDerivAt v
      (fderiv ℝ (velocity B) (profile B M A hA hB hs u₀ t) (v t)) t)
    (hi : v s = x) : ∀ t, v t = flow B M A hA hB hs u₀ t s x := by
  have he := Prop022RealEvolutionR123.solution_unique
    (generator B M A hA hB hs u₀) (generator_continuous B M A hA hB hs u₀)
    v (fun t => flow B M A hA hB hs u₀ t s x)
    (fun t => by
      have h := hv t
      rw [(velocity_hasFDerivAt B hs M A hA hB _).fderiv] at h
      convert! h using 1)
    (Prop022RealEvolutionR123.evolution_apply_derivative _ _ s x) s
    (by rw [flow_self]; exact hi)
  exact congrFun he

/-- Original-complex-structure block; this is the same alpha as sourceP. -/
def alpha (t s : ℝ) : L2T L →L[ℂ] L2T L :=
  sourceP (flow B M A hA hB hs u₀ t s)

/-- The beta consumed by the reviewed BD-02 theorem, without a basis change. -/
def betaBlock (t s : ℝ) : L2T L →L[ℂ] L2T L :=
  beta (physicalBasis L) (flow B M A hA hB hs u₀ t s)

theorem flow_blocks (t s : ℝ) (x : L2T L) :
    flow B M A hA hB hs u₀ t s x = alpha B M A hA hB hs u₀ t s x +
      betaBlock B M A hA hB hs u₀ t s (conjugation (physicalBasis L) x) := by
  change _ = complexPart _ x + antilinearPart _ (conjugation _ (conjugation _ x))
  rw [conjugation_sq]
  exact (congrArg (fun T : L2T L →L[ℝ] L2T L => T x) (parts_sum _)).symm

theorem alpha_norm (t s : ℝ) :
    ‖alpha B M A hA hB hs u₀ t s‖ ≤ ‖(flow B M A hA hB hs u₀ t s).toContinuousLinearMap‖ := by
  unfold alpha sourceP
  rw [complexify_norm]
  exact complexPart_norm _

theorem betaBlock_norm (t s : ℝ) :
    ‖betaBlock B M A hA hB hs u₀ t s‖ ≤ ‖(flow B M A hA hB hs u₀ t s).toContinuousLinearMap‖ := by
  unfold betaBlock beta
  rw [antiRepresentative_norm]
  exact antilinearPart_norm _

end QuantumNLS.Prop022VariationalR123
#print axioms QuantumNLS.Prop022VariationalR123.velocity_hasFDerivAt
#print axioms QuantumNLS.Prop022VariationalR123.flow_variational
#print axioms QuantumNLS.Prop022VariationalR123.flow_blocks

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022VariationalR123." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022VariationalR123." then
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
  Lean.logInfo m!"R123 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
