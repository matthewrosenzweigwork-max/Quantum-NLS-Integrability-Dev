import Mathlib
import QuantumNLS.Ext025HGP17Compact
import QuantumNLS.Ext025HGP17Routes

/-! # EXT-025 GP-17 per-consumer lemmas (haiku_inventory, 2026-11-17)

Per-consumer checks required by the owner addendum (`ops/contracts/OWNER_DECISIONS_EXT025_GP14_GP04_GP17_2026-11-17.md`,
CHECKS ON EVERY USE): every application of GP-17 must be checked against the Riesz-rank convention.

Lean content, by consumer:
* R-EC25334D (route (ii)): `contourProj_continuous_of_joint` — if the resolvent on the contour is
  jointly norm-continuous in (parameter, contour point), the contour projection family is
  norm-continuous in the parameter; `consumer_route_ii` then propagates finite rank and rank from a
  base parameter (frozen `Ext025B3RankContinuation` through `Ext025HGP17Routes.route_ii`).
* LOCAL-007 (finite reduction): `finite_reduction_route_i` — in a finite-dimensional reduction every
  Riesz projection has finite-dimensional range, so the finite-rank hypothesis of route (i) holds
  automatically. The value two is the frozen `Local002Rank.proj_rank`, not re-proved here.
* LOCAL-009: no Lean module of the Quantum NLS tree imports the frozen `LOCAL009GP17`; the accepted
  LOCAL-009 use is scalar (see the review record). Route (iii) applies to it only through
  `Ext025HGP17Compact.route_iii_contour` once a full `ClosedResolvent` family is built; see the note.

No `sorry`, no new axioms. Author: haiku_inventory. -/

noncomputable section
set_option autoImplicit false

open Set Metric MeasureTheory intervalIntegral Complex Real Function
open QuantumNLS.Ext025HGP17Resolvent

namespace QuantumNLS.Ext025HGP17Consumers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- R-EC25334D route (ii), continuity: joint norm-continuity of the resolvent on the contour, in the
parameter `x` and the contour point, makes `x ↦ P x` norm-continuous. -/
theorem contourProj_continuous_of_joint {X : Type*} [TopologicalSpace X] {F : X → ℂ → E →L[ℂ] E}
    {c : ℂ} {r : ℝ} (hF : Continuous (fun p : X × ℝ => F p.1 (circleMap c r p.2))) :
    Continuous (fun x => contourProj (F x) c r) := by
  have hd : Continuous (fun θ : ℝ => deriv (circleMap c r) θ) := by
    simp only [deriv_circleMap]
    fun_prop
  have hint : Continuous (fun x => circleIntegral (F x) c r) := by
    unfold circleIntegral
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x θ => deriv (circleMap c r) θ • F x (circleMap c r θ))
      ((hd.comp continuous_snd).smul hF) 0 (2 * π)
  exact hint.const_smul ((2 * π * Complex.I)⁻¹ : ℂ)

/-- R-EC25334D route (ii), consumer statement: finite rank at a base parameter propagates to every
parameter, with the same rank, along a connected parameter space (frozen rank continuation). -/
theorem consumer_route_ii {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {F : X → ℂ → E →L[ℂ] E} {c : ℂ} {r : ℝ}
    (hF : Continuous (fun p : X × ℝ => F p.1 (circleMap c r p.2)))
    (hid : ∀ x, contourProj (F x) c r * contourProj (F x) c r = contourProj (F x) c r)
    (x₀ : X) [FiniteDimensional ℂ (LinearMap.range (contourProj (F x₀) c r).toLinearMap)] (x : X) :
    QuantumNLS.Ext025HGP17Routes.HasFiniteAlgMult (contourProj (F x) c r) ∧
      QuantumNLS.Ext025HGP17Routes.algMult (contourProj (F x) c r) =
        QuantumNLS.Ext025HGP17Routes.algMult (contourProj (F x₀) c r) := by
  have hc := contourProj_continuous_of_joint (c := c) (r := r) hF
  have hid' : ∀ (x : X) (v : E), contourProj (F x) c r (contourProj (F x) c r v) =
      contourProj (F x) c r v := fun x v => by
    rw [← ContinuousLinearMap.mul_apply, hid x]
  exact QuantumNLS.Ext025HGP17Routes.route_ii (fun x => contourProj (F x) c r) hc hid' x₀ x

/-- LOCAL-007 finite reduction: on a finite-dimensional space every Riesz projection has
finite-dimensional range, so the finite-rank hypothesis of route (i) holds automatically. -/
theorem finite_reduction_route_i [FiniteDimensional ℂ E] (P : E →L[ℂ] E) :
    QuantumNLS.Ext025HGP17Routes.HasFiniteAlgMult P := by
  unfold QuantumNLS.Ext025HGP17Routes.HasFiniteAlgMult
  infer_instance

/-- LOCAL-007 finite reduction, contour form: the contour projection of any resolvent family on a
finite-dimensional space has finite algebraic multiplicity under the Riesz-rank convention. -/
theorem finite_reduction_contour [FiniteDimensional ℂ E] (R : ℂ → E →L[ℂ] E) (c : ℂ) (r : ℝ) :
    QuantumNLS.Ext025HGP17Routes.HasFiniteAlgMult (contourProj R c r) :=
  finite_reduction_route_i _

end QuantumNLS.Ext025HGP17Consumers

#print axioms QuantumNLS.Ext025HGP17Consumers.contourProj_continuous_of_joint
#print axioms QuantumNLS.Ext025HGP17Consumers.consumer_route_ii
#print axioms QuantumNLS.Ext025HGP17Consumers.finite_reduction_route_i
