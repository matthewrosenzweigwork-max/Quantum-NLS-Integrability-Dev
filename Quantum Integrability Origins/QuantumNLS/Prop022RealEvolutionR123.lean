import QuantumNLS.LinearFundamental
import Mathlib.Analysis.ODE.ExistUnique

/-! Global real-linear evolution for continuous bounded coefficients.
The coefficient need not have a uniform bound on the entire real line. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped Topology NNReal
open Set ContinuousLinearMap
namespace QuantumNLS.Prop022RealEvolutionR123
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma solution_unique (G : ℝ → H →L[ℝ] H) (hG : Continuous G)
    (x y : ℝ → H) (hx : ∀ t, HasDerivAt x (G t (x t)) t)
    (hy : ∀ t, HasDerivAt y (G t (y t)) t)
    (s : ℝ) (hi : x s = y s) : x = y := by
  have hc : Continuous x := continuous_iff_continuousAt.mpr (fun t => (hx t).continuousAt)
  have hd : Continuous y := continuous_iff_continuousAt.mpr (fun t => (hy t).continuousAt)
  ext t
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := min s t) (b := max s t)).exists_bound_of_continuousOn hG.continuousOn
  let K : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hb (r : ℝ) (hr : r ∈ Icc (min s t) (max s t)) :
      LipschitzOnWith K (G r) (univ : Set H) := by
    apply (G r).lipschitzWith.lipschitzOnWith.weaken
    exact_mod_cast (hC r hr).trans (le_max_left C 0)
  rcases le_total s t with hst | hts
  · have he := ODE_solution_unique_of_mem_Icc_right
      (v := fun r z => G r z) (s := fun _ => univ)
      (fun r hr => hb r (by simpa [min_eq_left hst, max_eq_right hst] using ⟨hr.1, hr.2.le⟩))
      hc.continuousOn (fun r _ => (hx r).hasDerivWithinAt) (fun _ _ => mem_univ _)
      hd.continuousOn (fun r _ => (hy r).hasDerivWithinAt) (fun _ _ => mem_univ _) hi
    exact he ⟨hst, le_rfl⟩
  · have he := ODE_solution_unique_of_mem_Icc_left
      (v := fun r z => G r z) (s := fun _ => univ)
      (fun r hr => hb r (by simpa [min_eq_right hts, max_eq_left hts] using ⟨hr.1.le, hr.2⟩))
      hc.continuousOn (fun r _ => (hx r).hasDerivWithinAt) (fun _ _ => mem_univ _)
      hd.continuousOn (fun r _ => (hy r).hasDerivWithinAt) (fun _ _ => mem_univ _) hi
    exact he ⟨le_rfl, hts⟩

/-- Initial time precedes final time in this lower-level definition. -/
def evolution (G : ℝ → H →L[ℝ] H) (hG : Continuous G) (s t : ℝ) : H →L[ℝ] H :=
  (LinearFundamental.exists_fundamental
    (A := fun r => G (r+s)) (hG.comp (continuous_id.add continuous_const))).choose (t-s)

lemma evolution_self (G : ℝ → H →L[ℝ] H) (hG : Continuous G) (s : ℝ) :
    evolution G hG s s = 1 := by
  unfold evolution
  rw [sub_self]
  exact (LinearFundamental.exists_fundamental
    (A := fun r => G (r+s)) (hG.comp (continuous_id.add continuous_const))).choose_spec.1

lemma evolution_derivative (G : ℝ → H →L[ℝ] H) (hG : Continuous G) (s t : ℝ) :
    HasDerivAt (evolution G hG s) (G t * evolution G hG s t) t := by
  have h := (LinearFundamental.exists_fundamental
    (A := fun r => G (r+s)) (hG.comp (continuous_id.add continuous_const))).choose_spec.2 (t-s)
  convert! h.scomp t ((hasDerivAt_id t).sub_const s) using 1
  simp only [evolution, sub_add_cancel, one_smul]

lemma evolution_apply_derivative (G : ℝ → H →L[ℝ] H) (hG : Continuous G)
    (s : ℝ) (x : H) (t : ℝ) :
    HasDerivAt (fun r => evolution G hG s r x) (G t (evolution G hG s t x)) t := by
  exact (ContinuousLinearMap.apply ℝ H x).hasFDerivAt.comp_hasDerivAt t
    (evolution_derivative G hG s t)

lemma evolution_continuous (G : ℝ → H →L[ℝ] H) (hG : Continuous G) (s : ℝ) :
    Continuous (evolution G hG s) :=
  continuous_iff_continuousAt.mpr (fun t => (evolution_derivative G hG s t).continuousAt)

lemma evolution_comp (G : ℝ → H →L[ℝ] H) (hG : Continuous G) (r s t : ℝ) :
    evolution G hG s t * evolution G hG r s = evolution G hG r t := by
  ext x
  have he := solution_unique G hG
    (fun z => evolution G hG s z (evolution G hG r s x))
    (fun z => evolution G hG r z x)
    (evolution_apply_derivative G hG s _) (evolution_apply_derivative G hG r x) s
    (by simp only [evolution_self, one_apply_eq_self])
  exact congrFun he t

/-- Invertibility follows from the proved cocycle, for arbitrary signed times. -/
def evolutionEquiv (G : ℝ → H →L[ℝ] H) (hG : Continuous G) (s t : ℝ) : H ≃L[ℝ] H where
  toLinearEquiv :=
    { toLinearMap := (evolution G hG s t).toLinearMap
      invFun := evolution G hG t s
      left_inv := by
        intro x
        change evolution G hG t s (evolution G hG s t x) = x
        have h := congrArg (fun T : H →L[ℝ] H => T x) (evolution_comp G hG s t s)
        simpa only [mul_apply_eq_comp, evolution_self, one_apply_eq_self] using h
      right_inv := by
        intro x
        change evolution G hG s t (evolution G hG t s x) = x
        have h := congrArg (fun T : H →L[ℝ] H => T x) (evolution_comp G hG t s t)
        simpa only [mul_apply_eq_comp, evolution_self, one_apply_eq_self] using h }
  continuous_toFun := (evolution G hG s t).continuous
  continuous_invFun := (evolution G hG t s).continuous

end QuantumNLS.Prop022RealEvolutionR123
#print axioms QuantumNLS.Prop022RealEvolutionR123.evolutionEquiv
#print axioms QuantumNLS.Prop022RealEvolutionR123.solution_unique

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022RealEvolutionR123." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022RealEvolutionR123." then
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
