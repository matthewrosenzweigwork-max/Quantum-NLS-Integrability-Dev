import QuantumNLS.Prop022VariationalR123

/-! Symplecticity of the actual source variational equation follows from the
proved real Hessian symmetry, with the original complex structure. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal
namespace QuantumNLS.Prop022SymplecticR123
open PhysicalTensor BetheCoefficientTransform Prop022FactorialCoefficientsR115
open Prop022GradientR118 Prop022HessianR118 Prop022ActualProfileR117
open Prop022VariationalR123 Ext006SymplecticKernel
variable {L : ℝ} [Fact (0 < L)]
local instance : Inner ℝ (L2T L) := Inner.rclikeToReal ℂ (L2T L)
local instance : AddCommGroup (L2T L) := (inferInstance : NormedAddCommGroup (L2T L)).toAddCommGroup

lemma hessian_symmetric (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hs : ∀ m, (B m).adjoint = B m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (u x y : L2T L) :
    seriesHessian B u x y = seriesHessian B u y x := by
  have he := (classicalSeries_hasSecondFDerivAt B hs M A hA hB u).fderiv
  have h := (((classicalSeries_C2 B hs M A hA hB).contDiffAt (x := u)).isSymmSndFDerivAt
    (by norm_num)).eq x y
  rw [he] at h
  exact h

lemma gradientDerivative_pairing (B : ∀ m, HN L m →L[ℂ] HN L m) (u x y : L2T L) :
    (⟪gradientDerivative B u x, y⟫_ℂ).re = (1/2 : ℝ) * seriesHessian B u x y := by
  change ⟪gradientDerivative B u x, y⟫_ℝ = _
  change ⟪(1/2 : ℝ) • riesz (seriesHessian B u x), y⟫_ℝ = _
  rw [real_inner_smul_left]
  change (1/2 : ℝ) * ⟪(InnerProductSpace.toDual ℝ (L2T L)).symm (seriesHessian B u x), y⟫_ℝ = _
  rw [InnerProductSpace.toDual_symm_apply]

lemma velocityDerivative_infinitesimal_symplectic
    (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hs : ∀ m, (B m).adjoint = B m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (u x y : L2T L) :
    (⟪velocityDerivative B u x, y⟫_ℂ + ⟪x, velocityDerivative B u y⟫_ℂ).im = 0 := by
  have hx := gradientDerivative_pairing B u x y
  have hy := gradientDerivative_pairing B u y x
  rw [hessian_symmetric B hs M A hA hB u y x] at hy
  have hi := inner_re_symm (𝕜 := ℂ) x (gradientDerivative B u y)
  change (⟪x, gradientDerivative B u y⟫_ℂ).re = (⟪gradientDerivative B u y, x⟫_ℂ).re at hi
  change (⟪(-Complex.I) • gradientDerivative B u x, y⟫_ℂ +
    ⟪x, (-Complex.I) • gradientDerivative B u y⟫_ℂ).im = 0
  simp only [inner_smul_left, inner_smul_right, map_neg, Complex.conj_I, neg_neg,
    Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.neg_im, zero_mul, one_mul, neg_mul, zero_add]
  linarith

/-- Preservation of the imaginary inner product for every initial and final
 time, with no symplecticity premise on the constructed flow. -/
theorem flow_symplectic (B : ∀ m, HN L m →L[ℂ] HN L m)
    (M A : ℝ) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (L2T L)) (t s : ℝ) :
    Symplectic (flow B M A hA hB hs u₀ t s).toContinuousLinearMap := by
  intro x y
  let S := flow B M A hA hB hs u₀
  have hd (v : L2T L) (r : ℝ) : HasDerivAt (fun z => S z s v)
      (velocityDerivative B (profile B M A hA hB hs u₀ r) (S r s v)) r :=
    Prop022RealEvolutionR123.evolution_apply_derivative _ _ s v r
  have hz (r : ℝ) : HasDerivAt (fun z => (⟪S z s x, S z s y⟫_ℂ).im) 0 r := by
    apply (Complex.imCLM.hasFDerivAt.comp_hasDerivAt r ((hd x r).inner ℂ (hd y r))).congr_deriv
    change (⟪S r s x, velocityDerivative B (profile B M A hA hB hs u₀ r) (S r s y)⟫_ℂ +
      ⟪velocityDerivative B (profile B M A hA hB hs u₀ r) (S r s x), S r s y⟫_ℂ).im = 0
    rw [add_comm]
    exact velocityDerivative_infinitesimal_symplectic B hs M A hA hB _ _ _
  have he := is_const_of_deriv_eq_zero (fun r => (hz r).differentiableAt)
    (fun r => (hz r).deriv) t s
  simpa only [S, flow_self] using! he

end QuantumNLS.Prop022SymplecticR123
#print axioms QuantumNLS.Prop022SymplecticR123.hessian_symmetric
#print axioms QuantumNLS.Prop022SymplecticR123.flow_symplectic

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022SymplecticR123." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022SymplecticR123." then
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
