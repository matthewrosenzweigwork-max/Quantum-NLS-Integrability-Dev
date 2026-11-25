import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Complex.Circle
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Group.Circle

/-! GP-15. The general compact abelian group statement applies in particular to
`ℤ → Circle`. Every continuous finite-support integer character is a monoid
homomorphism into `Circle`. Coordinate permutations, common-phase translations,
and conjugation are covered by invariance below. The occupation-configuration
and matrix-element sentences are descriptive prose about consumers. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Topology TopologicalSpace
namespace QuantumNLS.Ext025BHaar
local instance (α : Type*) : DecidableEq α := Classical.decEq α
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Normalization is by the whole compact group, so the mass is exactly one. -/
def normalizedHaar : Measure G := Measure.haarMeasure ⊤

instance : IsHaarMeasure (normalizedHaar : Measure G) := by
  unfold normalizedHaar
  infer_instance

instance : IsProbabilityMeasure (normalizedHaar : Measure G) :=
  ⟨by simpa [normalizedHaar] using
    (Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts G)))⟩

/-- GP-15 existence and uniqueness of normalized invariant Borel measure. -/
theorem «FIN-EXT025-GP-15» :
    ∃! μ : Measure G, IsProbabilityMeasure μ ∧ IsMulLeftInvariant μ := by
  refine ⟨normalizedHaar, ⟨inferInstance, inferInstance⟩, ?_⟩
  intro μ hμ
  let := hμ.1
  let := hμ.2
  let : IsHaarMeasure μ :=
    isHaarMeasure_of_isCompact_nonempty_interior μ Set.univ isCompact_univ
      (by simp) (by simp) (by simp)
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure μ normalizedHaar

/-- Inversion preserves normalized Haar, including circle conjugation. -/
theorem «FIN-EXT025-GP-15-inversion» :
    MeasurePreserving (Inv.inv : G → G) normalizedHaar normalizedHaar :=
  measurePreserving_inv normalizedHaar

/-- Continuous group automorphisms preserve normalized Haar. -/
theorem «FIN-EXT025-GP-15-automorphism» (e : G ≃ₜ* G) :
    MeasurePreserving e normalizedHaar normalizedHaar :=
  e.toMulEquiv.toMonoidHom.measurePreserving e.continuous e.surjective rfl

/-- All translations preserve the normalization. -/
theorem «FIN-EXT025-GP-15-translation» (g : G) :
    MeasurePreserving (fun x => g * x) normalizedHaar normalizedHaar :=
  measurePreserving_mul_left normalizedHaar g

/-- Character orthogonality, with the two possible integrals and no restriction
on how many coordinates the ambient compact group has. -/
theorem «FIN-EXT025-GP-15-character» (χ : G →* Circle) :
    (∫ x, (χ x : ℂ) ∂normalizedHaar) = if χ = 1 then 1 else 0 := by
  classical
  split_ifs with h
  · subst χ
    simp
  · have hex : ∃ g, χ g ≠ 1 := by
      by_contra hn
      apply h
      apply DFunLike.ext
      intro g
      exact not_not.mp (not_exists.mp hn g)
    obtain ⟨g, hg⟩ := hex
    have hc : (χ g : ℂ) ≠ 1 := by
      intro hc
      apply hg
      exact Subtype.ext hc
    have hi := integral_mul_left_eq_self (μ := (normalizedHaar : Measure G))
      (fun x => (χ x : ℂ)) g
    have hi' : (χ g : ℂ) * (∫ x, (χ x : ℂ) ∂normalizedHaar) =
        ∫ x, (χ x : ℂ) ∂normalizedHaar := by
      simpa only [map_mul, Circle.coe_mul, integral_const_mul] using hi
    exact eq_zero_of_mul_eq_self_left hc hi'

/-- Every finite-coordinate marginal is normalized Haar: apply this to the
surjective continuous coordinate projection onto a finite product of circles. -/
theorem «FIN-EXT025-GP-15-marginal» {J : Type*} [CommGroup J]
    [TopologicalSpace J] [IsTopologicalGroup J] [CompactSpace J] [T2Space J]
    [MeasurableSpace J] [BorelSpace J] (p : G →* J)
    (hc : Continuous p) (hs : Function.Surjective p) :
    MeasurePreserving p (normalizedHaar : Measure G) (normalizedHaar : Measure J) :=
  p.measurePreserving hc hs (by simp)

/-- The actual countable torus has the claimed compact product topology. -/
theorem «FIN-EXT025-GP-15-countable-torus» :
    IsCompact (Set.univ : Set (ℤ → Circle)) ∧ MetrizableSpace (ℤ → Circle) :=
  ⟨isCompact_univ, inferInstance⟩

/-- The literal infinite product of the normalized circle measures. -/
def productCircleHaar : Measure (ℤ → Circle) :=
  Measure.infinitePi (fun _ : ℤ => (normalizedHaar : Measure Circle))

instance : IsProbabilityMeasure productCircleHaar := by
  unfold productCircleHaar
  infer_instance

instance : IsMulLeftInvariant productCircleHaar := by
  constructor
  intro g
  change Measure.map (fun x i => g i * x i)
    (Measure.infinitePi (fun _ : ℤ => (normalizedHaar : Measure Circle))) = _
  simpa only [map_mul_left_eq_self, productCircleHaar] using
    (Measure.infinitePi_map_pi (fun _ : ℤ => (normalizedHaar : Measure Circle))
      (f := fun i x => g i * x) (fun i => measurable_const_mul (g i)))

/-- Identification of product Haar with the uniquely normalized invariant
measure; thus all the invariance/character results use the same normalization. -/
theorem «FIN-EXT025-GP-15-product» :
    productCircleHaar = (normalizedHaar : Measure (ℤ → Circle)) := by
  exact («FIN-EXT025-GP-15» (G := ℤ → Circle)).unique
    ⟨inferInstance, inferInstance⟩ ⟨inferInstance, inferInstance⟩

end QuantumNLS.Ext025BHaar

#print axioms QuantumNLS.Ext025BHaar.normalizedHaar
#print axioms QuantumNLS.Ext025BHaar.«FIN-EXT025-GP-15»
#print axioms QuantumNLS.Ext025BHaar.«FIN-EXT025-GP-15-inversion»
#print axioms QuantumNLS.Ext025BHaar.«FIN-EXT025-GP-15-automorphism»
#print axioms QuantumNLS.Ext025BHaar.«FIN-EXT025-GP-15-translation»
#print axioms QuantumNLS.Ext025BHaar.«FIN-EXT025-GP-15-character»
#print axioms QuantumNLS.Ext025BHaar.«FIN-EXT025-GP-15-marginal»
#print axioms QuantumNLS.Ext025BHaar.«FIN-EXT025-GP-15-countable-torus»

#print axioms QuantumNLS.Ext025BHaar.productCircleHaar
#print axioms QuantumNLS.Ext025BHaar.«FIN-EXT025-GP-15-product»

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants do
    if n.toString.startsWith "QuantumNLS.Ext025BHaar." then
      pending := pending.push n
      roots := roots + 1
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
  Lean.logInfo m!"Ext025BHaar audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
