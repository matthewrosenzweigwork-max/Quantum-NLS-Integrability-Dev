import QuantumNLS.Ext006StoneGeneratorR44a
import Mathlib.Analysis.Calculus.MeanValue

/-! Stone characterization of the source exponential on the actual Fock
space. The generator is the proved self-adjoint closure of a*(f)+a(f).
Existence is constructed and uniqueness is proved, rather than postulated. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006SourceStoneR44a
open Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006SmoothOperatorsR34a
open Ext006StrongFieldR41a Ext006FieldBoundsR42a Ext006BoundedExponentialR43a
open Ext006FieldClosureR42a Ext006SelfAdjointR44a Ext006StoneGeneratorR44a
open Ext006SeriesIdentificationR43a Ext006ExponentialDerivativeR43a
open Ext006ExponentialContinuityR43a

/-- The full Stone characterization, with exact strong generator domain.
This is on the concrete completed occupation Fock space. -/
structure StoneFamily (h : H) where
  U : ℝ → Fock ≃ₗᵢ[ℂ] Fock
  zero : ∀ x, U 0 x=x
  add : ∀ s t x, U s (U t x)=U (s+t) x
  continuous : ∀ x, Continuous (fun t : ℝ => U t x)
  generator : ∀ x y, HasDerivAt (fun t : ℝ => U t x) (Complex.I • y) 0 ↔
    (x,y) ∈ (closureField h).graph

/-- Existence for this actual self-adjoint generator is constructed. -/
def constructed (h : H) : StoneFamily h where
  U := unitary h
  zero := unitary_zero h
  add := unitary_add h
  continuous := unitary_strong_continuous h
  generator := generator_iff h

lemma family_derivative (h : H) (V : StoneFamily h) (x y : Fock)
    (hxy : (x,y) ∈ closedFieldGraph h) (t : ℝ) :
    HasDerivAt (fun s : ℝ => V.U s x) (Complex.I • V.U t y) t := by
  have hg : (x,y) ∈ (closureField h).graph := by
    rw [closureField_graph,graph_mem_closed]
    exact hxy
  have hd0 := (V.generator x y).mpr hg
  have hshift := hd0.scomp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp)
  have hd := ((V.U t).toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hshift
  have he : (fun s : ℝ => V.U t (V.U (s-t) x)) = (fun s : ℝ => V.U s x) := by
    funext s
    rw [V.add]
    rw [show t+(s-t)=s by ring]
  change HasDerivAt (fun s : ℝ => V.U t (V.U (s-t) x))
    (V.U t ((1 : ℝ) • (Complex.I • y))) t at hd
  simpa only [he,one_smul,map_smul] using hd

lemma family_preserves_graph (h : H) (V : StoneFamily h) (x y : Fock)
    (hxy : (x,y) ∈ closedFieldGraph h) (t : ℝ) :
    (V.U t x,V.U t y) ∈ closedFieldGraph h := by
  have hg : (x,y) ∈ (closureField h).graph := by
    rw [closureField_graph,graph_mem_closed]
    exact hxy
  have hd0 := (V.generator x y).mpr hg
  have hd := ((V.U t).toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd0
  have he : (fun s : ℝ => V.U t (V.U s x)) = (fun s : ℝ => V.U s (V.U t x)) := by
    funext s
    rw [V.add,V.add,add_comm]
  change HasDerivAt (fun s : ℝ => V.U t (V.U s x)) (V.U t (Complex.I • y)) 0 at hd
  rw [he,map_smul] at hd
  have hg' := (V.generator (V.U t x) (V.U t y)).mp hd
  rwa [closureField_graph,graph_mem_closed] at hg'

/-- Uniqueness in Stone's characterization, proved by differentiating
matrix elements of two groups with the same actual self-adjoint generator. -/
theorem family_unique (h : H) (V : StoneFamily h) (t : ℝ) (x : Fock) :
    V.U t x=unitary h t x := by
  have hp (v w : Core) :
      inner ℂ (V.U t (inclusion v)) (unitary h t (inclusion w)) =
        inner ℂ (inclusion v) (inclusion w) := by
    have hvg : (inclusion v,(field h v.1).1) ∈ closedFieldGraph h := by
      have he := graph_smooth h v.1
      rwa [graph_mem_closed] at he
    have hwg : (inclusion w,(field h w.1).1) ∈ closedFieldGraph h := by
      have he := graph_smooth h w.1
      rwa [graph_mem_closed] at he
    have hd (s : ℝ) : HasDerivAt
        (fun u : ℝ => inner ℂ (V.U u (inclusion v)) (unitary h u (inclusion w))) 0 s := by
      have dv := family_derivative h V _ _ hvg s
      have dw := graph_hasDerivAt h _ _ hwg s
      have hs := closedFieldGraph_symmetric h
        (family_preserves_graph h V _ _ hvg s)
        (family_preserves_graph h (constructed h) _ _ hwg s)
      change inner ℂ (V.U s (field h v.1).1) (unitary h s (inclusion w)) =
        inner ℂ (V.U s (inclusion v)) (unitary h s (field h w.1).1) at hs
      have d := dv.inner ℂ dw
      convert d using 1
      rw [inner_smul_left,inner_smul_right,Complex.conj_I,← hs]
      ring
    have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
      (fun s => (hd s).deriv) t 0
    simpa only [V.zero,unitary_zero] using he
  have hall (a b : Fock) : inner ℂ (V.U t a) (unitary h t b)=inner ℂ a b := by
    exact core_dense.induction_on₂
      (p := fun a b => inner ℂ (V.U t a) (unitary h t b)=inner ℂ a b)
      (isClosed_eq (((V.U t).continuous.comp continuous_fst).inner
          ((unitary h t).continuous.comp continuous_snd))
        (continuous_fst.inner continuous_snd)) hp a b
  apply ext_inner_right ℂ
  intro z
  have he := hall x ((unitary h t).symm z)
  rw [LinearIsometryEquiv.apply_symm_apply] at he
  have hi := ((unitary h t).inner_map_map x ((unitary h t).symm z)).symm
  rw [LinearIsometryEquiv.apply_symm_apply] at hi
  exact he.trans hi

/-- The source's exponential defined by the unique Stone group of the
self-adjoint closure, with exact generator domain. -/
def sourceStone (h : H) : StoneFamily h := Classical.choice (show Nonempty (StoneFamily h) from ⟨constructed h⟩)

/-- Exact identification with the source convention W(f,fbar)=exp(i(a*+a)). -/
theorem sourceStone_eq (h : H) (t : ℝ) (x : Fock) :
    (sourceStone h).U t x=unitary h t x := family_unique h (sourceStone h) t x

end QuantumNLS.Ext006SourceStoneR44a
#print axioms QuantumNLS.Ext006SourceStoneR44a.family_unique
#print axioms QuantumNLS.Ext006SourceStoneR44a.sourceStone_eq

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006SourceStoneR44a." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
        throwError "Held identifier in dependency closure: {n}"
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
  Lean.logInfo m!"Round44a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
