import QuantumNLS.FullWickH4
import QuantumNLS.ReconstructionInputsR33m
import QuantumNLS.UniformStaticR49b

/-! FullWickH5 (haiku_inventory, R-140AE34B `thm:full-wick`, Stage 3, instantiation).

Named inputs, used by reference and not restated:
  * AuditDynamic: `ReconstructionR33m.RD8362E5EBInput hκ F g` (exact printed R-8362E5EB, frozen by
    sol_multi r34; defined in ReconstructionInputsR33m.lean, sha256 cd4458c72acbc0d283f61ac9b94678676c206fb26121cbd9d2b1c24aaac45fe8).
    Its hierarchy enters only through the flow family `F` (the shared type HierarchyInputR25m
    supplies `F = flows hκ HierarchyInput` at the use site).
  * UniformStatic: the parameter predicate `UniformStaticR49b.UniformStatic hκ j q` (sha256 of
    UniformStaticR49b.lean c532f48e9bfe3e7e4e449c9e8fdbcf9c6c7285b9234e78ddc27dba78f87ddfdd), used
    on parameters (j, q) and discharged at the selected witnesses (`static_discharged`).

Lemmas:
  * `generator_pair`: for one fixed profile, time box and preparation, the generator `E_{ab}` with
    its adjoint is a uniform strong-symbol pair with symbol `z_a conj(z_b)`, where `z = w(u)`.
  * `phase_pair`: the same for `W_{ab}` with the positive-action normalization, under the printed
    hypotheses `a ≠ b` and positivity of the chart coordinates.

Standard axioms only.
-/

noncomputable section
open Filter Topology
open scoped ComplexConjugate
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace QuantumNLS.FullWickH5

open QuantumNLS.FullWickH4 QuantumNLS.ReconstructionR33m
open QuantumNLS.Def033HierarchyR24m (Smooth physical)
open QuantumNLS.BetheOccupationGauge (Gauge)
open QuantumNLS.ActualModelTargetR53a (HigherFlows)
open QuantumNLS.BetheCoefficientTransform (HN)

variable {L κ : ℝ} [Fact (0 < L)]

/-- **Generator pair** from the printed R-8362E5EB input, for one fixed profile `u`, time box
`TimeBox R lo hi`, preparation `ψ`, and labels `a, b`: the operator `E_{ab}` and its adjoint carry
the symbol `z_a conj(z_b)`, uniformly over the time box, with `z = w(u)`. -/
theorem generator_pair (hκ : 0 < κ) (F : HigherFlows L κ) (g : Gauge)
    (D : RD8362E5EBInput hκ F g) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (R : Finset ℕ) (lo hi : ↥R → ℝ) (ψ : ∀ n : ℕ, HN L (1 + n)) (hψ : Preparation u ψ)
    (a b : ℤ) :
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => E hκ g n a b) (fun n => (E hκ g n a b).adjoint)
      (Set.univ : Set Unit) (TimeBox R lo hi)
      (fun (_ : Unit) t n => U hκ R t n (ψ n))
      (fun (_ : Unit) t => w hκ F u R t a * (starRingEnd ℂ) (w hκ F u R t b)) := by
  have hs := (D u hu R lo hi ψ hψ a b).1
  constructor
  · intro ε hε
    filter_upwards [hs ε hε] with n hn
    intro _ _ t ht
    have h1 := (hn t ht).1
    simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul] using h1
  · intro ε hε
    filter_upwards [hs ε hε] with n hn
    intro _ _ t ht
    have h2 := (hn t ht).2
    simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul] using h2

/-- **Phase pair** from the printed R-8362E5EB input (the positive-action clause), under the
printed hypotheses `a ≠ b` and positivity of the chart coordinates of `physical u`. -/
theorem phase_pair (hκ : 0 < κ) (F : HigherFlows L κ) (g : Gauge)
    (D : RD8362E5EBInput hκ F g) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (R : Finset ℕ) (lo hi : ↥R → ℝ) (ψ : ∀ n : ℕ, HN L (1 + n)) (hψ : Preparation u ψ)
    (a b : ℤ) (hab : a ≠ b)
    (h1 : 0 < ‖(QuantumNLS.Def021ChartR41b.chart L κ hκ).Φ (physical u) a‖ ^ 2)
    (h2 : 0 < ‖(QuantumNLS.Def021ChartR41b.chart L κ hκ).Φ (physical u) b‖ ^ 2) :
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => W hκ g n a b) (fun n => (W hκ g n a b).adjoint)
      (Set.univ : Set Unit) (TimeBox R lo hi)
      (fun (_ : Unit) t n => U hκ R t n (ψ n))
      (fun (_ : Unit) t =>
        (w hκ F u R t a * (starRingEnd ℂ) (w hκ F u R t b))
          / ((Real.sqrt (‖w hκ F u R t a‖ ^ 2 * ‖w hκ F u R t b‖ ^ 2) : ℝ) : ℂ)) := by
  have hs := ((D u hu R lo hi ψ hψ a b).2 hab h1 h2)
  constructor
  · intro ε hε
    filter_upwards [hs ε hε] with n hn
    intro _ _ t ht
    have h1' := (hn t ht).1
    simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul] using h1'
  · intro ε hε
    filter_upwards [hs ε hε] with n hn
    intro _ _ t ht
    have h2' := (hn t ht).2
    simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul] using h2'

/-- The static predicate on parameters `(j, q)`, as printed (`UniformStaticR49b.UniformStatic`). -/
abbrev StaticClause (hκ : 0 < κ) (j : ℕ → ℕ) (q : UniformStaticR49b.SectorGauge) : Prop :=
  UniformStaticR49b.UniformStatic (L := L) hκ j q

/-- The static clause is discharged at the selected witnesses (sol_ext_b, reviewed conditional PASS
r259): some `(j, q)` satisfy it. Stage 3 uses the predicate on parameters, so this discharge is a
separate fact. -/
theorem static_discharged (hκ : 0 < κ) :
    ∃ (j : ℕ → ℕ) (q : UniformStaticR49b.SectorGauge), StaticClause (L := L) hκ j q :=
  ⟨_, _, UniformStaticR49b.selected_uniform_static (L := L) hκ⟩

end QuantumNLS.FullWickH5

#print axioms QuantumNLS.FullWickH5.generator_pair
#print axioms QuantumNLS.FullWickH5.phase_pair
#print axioms QuantumNLS.FullWickH5.static_discharged
