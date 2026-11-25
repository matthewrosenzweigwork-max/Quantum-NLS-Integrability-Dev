import QuantumNLS.LinearFundamental
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Global nonautonomous bounded self-adjoint evolution. Existence follows
from the proved Dyson construction; conservation and uniqueness follow by
actual differentiation, without any propagated estimate as an input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped InnerProductSpace Topology
open ContinuousLinearMap
namespace QuantumNLS.Prop022BoundedEvolutionR119
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H
local instance opNormed : NormedAddCommGroup (H →L[ℂ] H) := inferInstance
local instance opGroup : AddCommGroup (H →L[ℂ] H) := opNormed.toAddCommGroup
local instance opTopology : TopologicalSpace (H →L[ℂ] H) := opNormed.toUniformSpace.toTopologicalSpace
local instance opRealNS : NormedSpace ℝ (H →L[ℂ] H) :=
  NormedSpace.restrictScalars ℝ ℂ _
local instance opRealModule : Module ℝ (H →L[ℂ] H) := opRealNS.toModule

omit [CompleteSpace H] in
lemma solution_norm (Q : ℝ → H →L[ℂ] H) (hs : ∀ t, (Q t).IsSymmetric)
    (x : ℝ → H) (hd : ∀ t, HasDerivAt x ((-Complex.I) • Q t (x t)) t) (s t : ℝ) :
    ‖x t‖ = ‖x s‖ := by
  have hzero (r : ℝ) : HasDerivAt (fun z => ⟪x z, x z⟫_ℂ) 0 r := by
    apply ((hd r).inner ℂ (hd r)).congr_deriv
    have hh := hs r (x r) (x r)
    change ⟪Q r (x r), x r⟫_ℂ = ⟪x r, Q r (x r)⟫_ℂ at hh
    simp only [inner_smul_left, inner_smul_right, map_neg, Complex.conj_I, neg_neg, hh]
    ring
  have he := is_const_of_deriv_eq_zero (fun r => (hzero r).differentiableAt)
    (fun r => (hzero r).deriv) t s
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at he
  have hn : ‖x t‖ ^ 2 = ‖x s‖ ^ 2 := by exact_mod_cast he
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hn

omit [CompleteSpace H] in
lemma solution_unique (Q : ℝ → H →L[ℂ] H) (hs : ∀ t, (Q t).IsSymmetric)
    (x y : ℝ → H) (hx : ∀ t, HasDerivAt x ((-Complex.I) • Q t (x t)) t)
    (hy : ∀ t, HasDerivAt y ((-Complex.I) • Q t (y t)) t)
    (s : ℝ) (hi : x s = y s) : x = y := by
  have hd (t : ℝ) : HasDerivAt (fun r => x r - y r)
      ((-Complex.I) • Q t (x t - y t)) t := by
    convert! (hx t).sub (hy t) using 1; simp only [map_sub, smul_sub]
  ext t
  have hn := solution_norm Q hs (fun r => x r-y r) hd s t
  rw [hi, sub_self, norm_zero] at hn
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- The bounded evolution is selected from the proved operator-valued Dyson
solution, shifted to its actual initial time. -/
def evolution (Q : ℝ → H →L[ℂ] H) (hQ : Continuous Q) (s t : ℝ) : H →L[ℂ] H :=
  (LinearFundamental.exists_fundamental
    (A := fun r => (-Complex.I) • Q (r+s))
    ((hQ.comp (continuous_id.add continuous_const)).const_smul (-Complex.I))).choose (t-s)

lemma evolution_self (Q : ℝ → H →L[ℂ] H) (hQ : Continuous Q) (s : ℝ) :
    evolution Q hQ s s = 1 := by
  unfold evolution
  rw [sub_self]
  exact (LinearFundamental.exists_fundamental
    (A := fun r => (-Complex.I) • Q (r+s))
    ((hQ.comp (continuous_id.add continuous_const)).const_smul (-Complex.I))).choose_spec.1

lemma evolution_derivative (Q : ℝ → H →L[ℂ] H) (hQ : Continuous Q) (s t : ℝ) :
    HasDerivAt (evolution Q hQ s) (((-Complex.I) • Q t) * evolution Q hQ s t) t := by
  have h := (LinearFundamental.exists_fundamental
    (A := fun r => (-Complex.I) • Q (r+s))
    ((hQ.comp (continuous_id.add continuous_const)).const_smul (-Complex.I))).choose_spec.2 (t-s)
  convert! h.scomp t ((hasDerivAt_id t).sub_const s) using 1
  simp only [evolution, sub_add_cancel, one_smul]

lemma evolution_apply_derivative (Q : ℝ → H →L[ℂ] H) (hQ : Continuous Q)
    (s : ℝ) (v : H) (t : ℝ) :
    HasDerivAt (fun r => evolution Q hQ s r v)
      ((-Complex.I) • Q t (evolution Q hQ s t v)) t := by
  let ev := (ContinuousLinearMap.apply ℂ H v).restrictScalars ℝ
  have he : HasDerivAt (fun r => ev (evolution Q hQ s r))
      (ev (((-Complex.I) • Q t) * evolution Q hQ s t)) t := by
    apply ev.hasFDerivAt.comp_hasDerivAt t
    convert! evolution_derivative Q hQ s t
  convert! he using 1


lemma evolution_continuous (Q : ℝ → H →L[ℂ] H) (hQ : Continuous Q) (s : ℝ) :
    Continuous (evolution Q hQ s) :=
  continuous_iff_continuousAt.mpr (fun t => (evolution_derivative Q hQ s t).continuousAt)

lemma evolution_norm (Q : ℝ → H →L[ℂ] H) (hQ : Continuous Q)
    (hs : ∀ t, (Q t).IsSymmetric) (s t : ℝ) (v : H) :
    ‖evolution Q hQ s t v‖ = ‖v‖ := by
  have h := solution_norm Q hs (fun r => evolution Q hQ s r v)
    (evolution_apply_derivative Q hQ s v) s t
  simpa only [evolution_self, one_apply_eq_self] using h

lemma evolution_comp (Q : ℝ → H →L[ℂ] H) (hQ : Continuous Q)
    (hs : ∀ t, (Q t).IsSymmetric) (r s t : ℝ) :
    evolution Q hQ s t * evolution Q hQ r s = evolution Q hQ r t := by
  apply ContinuousLinearMap.ext
  intro v
  have he := solution_unique Q hs
    (fun z => evolution Q hQ s z (evolution Q hQ r s v))
    (fun z => evolution Q hQ r z v)
    (evolution_apply_derivative Q hQ s _) (evolution_apply_derivative Q hQ r v) s
    (by simp only [evolution_self, one_apply_eq_self])
  exact congrFun he t

/-- The inverse is the evolution with exchanged initial/final times. -/
def evolutionEquiv (Q : ℝ → H →L[ℂ] H) (hQ : Continuous Q)
    (hs : ∀ t, (Q t).IsSymmetric) (s t : ℝ) : H ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (evolution Q hQ s t).toLinearMap
      norm_map' := evolution_norm Q hQ hs s t }
    (by
      intro v
      refine ⟨evolution Q hQ t s v, ?_⟩
      have hh := congrArg (fun T : H →L[ℂ] H => T v) (evolution_comp Q hQ hs t s t)
      change evolution Q hQ s t (evolution Q hQ t s v) = v
      simpa only [mul_apply_eq_comp, evolution_self, one_apply_eq_self] using hh)

/-- Actual differentiation of a bounded observable along the constructed
nonautonomous solution, including the physical Schrodinger sign. -/
lemma expectation_derivative (Q : ℝ → H →L[ℂ] H) (hQ : Continuous Q)
    (hs : ∀ t, (Q t).IsSymmetric) (J : H →L[ℂ] H) (s t : ℝ) (v : H) :
    HasDerivAt (fun r => ⟪evolution Q hQ s r v, J (evolution Q hQ s r v)⟫_ℂ)
      (Complex.I * ⟪evolution Q hQ s t v,
        (Q t * J - J * Q t) (evolution Q hQ s t v)⟫_ℂ) t := by
  have hd := evolution_apply_derivative Q hQ s v t
  apply (hd.inner ℂ ((J.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd)).congr_deriv
  have hh := hs t (evolution Q hQ s t v) (J (evolution Q hQ s t v))
  change ⟪Q t (evolution Q hQ s t v), J (evolution Q hQ s t v)⟫_ℂ =
    ⟪evolution Q hQ s t v, Q t (J (evolution Q hQ s t v))⟫_ℂ at hh
  simp only [Function.comp_def, coe_restrictScalars', inner_smul_left, map_smul,
    inner_smul_right, map_neg, Complex.conj_I, neg_neg, sub_apply,
    mul_apply_eq_comp, inner_sub_right, hh]
  ring

lemma evolution_fixed (Q : ℝ → H →L[ℂ] H) (hQ : Continuous Q)
    (hs : ∀ t, (Q t).IsSymmetric) (P : H →L[ℂ] H)
    (hP : ∀ t x, P (Q t x) = Q t (P x)) (s : ℝ) (v : H) (hv : P v = v) (t : ℝ) :
    P (evolution Q hQ s t v) = evolution Q hQ s t v := by
  have hd (r : ℝ) : HasDerivAt (fun z => P (evolution Q hQ s z v))
      ((-Complex.I) • Q r (P (evolution Q hQ s r v))) r := by
    have h := (P.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r
      (evolution_apply_derivative Q hQ s v r)
    simpa only [Function.comp_def, coe_restrictScalars', map_smul, hP] using h
  have he := solution_unique Q hs (fun z => P (evolution Q hQ s z v))
    (fun z => evolution Q hQ s z v) hd (evolution_apply_derivative Q hQ s v) s
    (by simpa only [evolution_self, one_apply_eq_self] using hv)
  exact congrFun he t

end QuantumNLS.Prop022BoundedEvolutionR119

#print axioms QuantumNLS.Prop022BoundedEvolutionR119.solution_norm

#print axioms QuantumNLS.Prop022BoundedEvolutionR119.solution_unique

#print axioms QuantumNLS.Prop022BoundedEvolutionR119.evolution_apply_derivative

#print axioms QuantumNLS.Prop022BoundedEvolutionR119.evolution_norm

#print axioms QuantumNLS.Prop022BoundedEvolutionR119.evolution_comp

#print axioms QuantumNLS.Prop022BoundedEvolutionR119.evolutionEquiv

#print axioms QuantumNLS.Prop022BoundedEvolutionR119.expectation_derivative

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022BoundedEvolutionR119." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022BoundedEvolutionR119." then
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
