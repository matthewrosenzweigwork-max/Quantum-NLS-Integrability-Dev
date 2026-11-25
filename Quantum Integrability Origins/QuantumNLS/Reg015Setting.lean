import QuantumNLS.TerraMultiRound64REG004
import QuantumNLS.Reg014Main
import QuantumNLS.TerraMultiRound70ExtendedWeights
import QuantumNLS.Reg010LowFreeSobolev

/-! REG-015 (`CC:all-fractional:theorem`, `all_orders.tex:110`) pre-start setting.

This module fixes the vocabulary of the printed statement and states, as three clearly
named `Prop`s, the EXACT printed statements of the three predecessors still being authored:

* `Reg010LowOrdersInput`  — REG-010 `thm:regularity-low-orders` (`fractional_moments.tex:49`);
* `Reg011HomeomorphismInput` — REG-011 `thm:regularity-homeomorphism-low` (`:512`);
* `Reg013InductionInput` — REG-013 `lem:regularity-induction` (`:610`).

None of them is an axiom; they appear only as explicit hypotheses of intermediate theorems.
The accepted predecessors REG-004 and REG-014 are imported, never restated.

`Seq`, `toBase`, `Target`, `ExactModuli` are verbatim copies of the (not yet frozen)
review record round-48 REG-011 vocabulary (`Reg011SettingR48a`), so that the later bridge is
definitional. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.Fourier
open QuantumNLS.RootWeightedCellsR26 QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound64ExtendedMeasure
namespace QuantumNLS.Reg015Setting
variable {L κ : ℝ} [Fact (0 < L)]

abbrev Seq := lp (fun _ : ℤ => ℂ) 2

/-- Coordinate-preserving inclusion `h^s ↪ ℓ²` (verbatim REG-011 vocabulary). -/
def toBase (s : ℝ) (hs : 0 ≤ s) : h02 L s →L[ℂ] Seq :=
  (fourierL2 L).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((H02.toL2 hs).comp
      (fourierHs (L := L) (one_le_def002 L hs)).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem toBase_apply (s : ℝ) (hs : 0 ≤ s) (z : h02 L s) (n : ℤ) :
    toBase s hs z n = z.val n := by
  exact congrArg (fun q : h02 L s => q.val n)
    ((fourierHs (L := L) (one_le_def002 L hs)).apply_symm_apply z)

/-- `V ∩ h^s` with the subspace `h^s` topology (REG-011 vocabulary; `abbrev` so that the
subtype topology is found). -/
abbrev Target (V : Set Seq) (s : ℝ) (hs : 0 ≤ s) := {z : h02 L s // toBase s hs z ∈ V}

/-- The printed phase hypothesis `|Φ_n(u)|² = I_n(u)` (verbatim REG-011 vocabulary). -/
def ExactModuli {V : Set Seq} (e : L2T L ≃ₜ V) (hκ : 0 < κ) : Prop :=
  ∀ u n, ‖(e u).val n‖^2 = (QuantumNLS.RootIndexedMasses.masses hκ u).1 n

/-! ### The per-order clauses of the printed statements -/

/-- "Moment characterization" at order `s`: the printed three-way equivalence. -/
def MomentChar (hκ : 0 < κ) (s : ℝ) : Prop :=
  ∀ u : L2T L,
    ((∃ v : H02 L s, v.val = u) ↔
      Integrable (fun t : ℝ => (1+|t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) ∧
    (Integrable (fun t : ℝ => (1+|t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ↔
      Summable (fun n : ℤ => (1+|momentum L n|)^(2*s) *
        (QuantumNLS.RootIndexedMasses.masses hκ u).1 n))

/-- "Weighted-action continuity" at order `s`: the indexed action map is continuous from
`H^s` into the weighted `ℓ¹` space, realized isometrically in `ℓ¹` by the weighted
coordinates (the REG-010 carrier convention). -/
def WeightedCont (hκ : 0 < κ) (s : ℝ) : Prop :=
  ∃ A : H02 L s → lp (fun _ : ℤ => ℝ) 1,
    (∀ u n, A u n = (1+|momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n) ∧
    Continuous A

/-- The indexed action map at order `s` sends bounded sets to bounded sets. -/
def BoundedActions (hκ : 0 < κ) (s : ℝ) : Prop :=
  ∃ A : H02 L s → lp (fun _ : ℤ => ℝ) 1,
    (∀ u n, A u n = (1+|momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n) ∧
    ∀ B : Set (H02 L s), Bornology.IsBounded B → Bornology.IsBounded (A '' B)

/-- "Conditional homeomorphism statement" at order `s`: for every homeomorphism
`Φ : L² → V ⊂ ℓ²` onto its image with exact moduli, its restriction is a homeomorphism
`H^s → V ∩ h^s` (subspace `h^s` topology). No claim `V = ℓ²`. -/
def CondHomeo (hκ : 0 < κ) (s : ℝ) (hs0 : 0 ≤ s) : Prop :=
  ∀ (V : Set Seq) (e : L2T L ≃ₜ V), ExactModuli e hκ →
    ∃ F : H02 L s ≃ₜ Target (L := L) V s hs0, ∀ u n, (F u).val.val n = (e u.val).val n

/-- The three conclusions of REG-010/REG-011 that REG-013 propagates, at one order. -/
def OrderStatement (hκ : 0 < κ) (s : ℝ) : Prop :=
  MomentChar (L := L) hκ s ∧ WeightedCont (L := L) hκ s ∧ ∀ hs0 : 0 ≤ s, CondHomeo (L := L) hκ s hs0

/-- REG-013's first assertion at order `k`: for all `u ∈ L²`, `u ∈ H^{k+1}` iff
`𝓜_{2k+2}(u) < ∞`, and on `H^k` the extended identity `𝓜_{2k+2} = Q_{k+1} + R` with
`R : H^k → ℝ` continuous. Extended values use the REG-004 convention. -/
def IntegerAssertion (hκ : 0 < κ) (k : ℕ) (R : Hk L k → ℝ) : Prop :=
  (∀ u : L2T L, (∃ v : Hk L (k+1), v.val = u) ↔
      (∫⁻ t : ℝ, ENNReal.ofReal (t^(2*(k+1))) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) ≠ ⊤) ∧
  Continuous R ∧
  ∀ v : Hk L k,
    ennrealToWithTop (∫⁻ t : ℝ, ENNReal.ofReal (t^(2*(k+1)))
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v.val)) =
      ennrealToWithTop (∑' n : ℤ, ENNReal.ofReal ((momentum L n)^(2*(k+1)) *
        ‖QuantumNLS.Fourier.coeff L v.val n‖^2)) + ↑(R v)

/-- REG-013's second assertion at order `k`: fixed-`Y` continuity of `D_{k+1,u}(Y)` on `H^k`
and a bound uniform for large `Y` on every `H^k` bounded set (exactly the two clauses that
REG-014 supplies, in REG-014's own form with `r = k+1`). -/
def FiniteYAssertion (hκ : 0 < κ) (k : ℕ) : Prop :=
  (∀ Y : ℝ, 0 < Y → Continuous (fun u : Hk L k =>
      (∫ t : ℝ, Y ^ 2 * t ^ (2 * (k+1)) / (Y ^ 2 + t ^ 2)
          ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) -
        ∑' n : ℤ, Y ^ 2 * (momentum L n) ^ (2 * (k+1)) /
          (Y ^ 2 + (momentum L n) ^ 2) *
          ‖QuantumNLS.Fourier.coeff L u.val n‖ ^ 2)) ∧
  (∀ B : Set (Hk L k), Bornology.IsBounded B →
      ∃ C Y₀ : ℝ, 0 < C ∧ 0 < Y₀ ∧ ∀ u ∈ B, ∀ Y : ℝ, Y₀ ≤ Y →
        |(∫ t : ℝ, Y ^ 2 * t ^ (2 * (k+1)) / (Y ^ 2 + t ^ 2)
            ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) -
          ∑' n : ℤ, Y ^ 2 * (momentum L n) ^ (2 * (k+1)) /
            (Y ^ 2 + (momentum L n) ^ 2) *
            ‖QuantumNLS.Fourier.coeff L u.val n‖ ^ 2| ≤ C)

/-- REG-013's conditional bounded-set hypothesis: the lower moments `𝓜_{2s}`, `0 ≤ s ≤ k`,
are bounded on bounded subsets of `H^s`, and the correction `R` is bounded on bounded
subsets of `H^k`. -/
def LowerBounded (hκ : 0 < κ) (k : ℕ) (R : Hk L k → ℝ) : Prop :=
  (∀ s : ℝ, 0 ≤ s → s ≤ k → ∀ B : Set (H02 L s), Bornology.IsBounded B →
      ∃ C : ℝ, ∀ u ∈ B,
        (∫ t : ℝ, |t|^(2*s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) ≤ C) ∧
  (∀ B : Set (Hk L k), Bornology.IsBounded B → ∃ C : ℝ, ∀ u ∈ B, |R u| ≤ C)

/-! ### The three named predecessor inputs (exact printed statements) -/

/-- INPUT 1. EXACT printed REG-010 (`fractional_moments.tex:49`): for every `0 ≤ s ≤ 2`
and every L² field, the three finiteness conditions are equivalent; the indexed action map
is continuous into the weighted `ℓ¹` space and sends bounded sets to bounded sets.
(Verbatim the review record round-48 `Reg010LowOrdersInput`; same shape as terra_multi's draft
`TerraMultiRound80Final.REG010`.) -/
def Reg010LowOrdersInput (hκ : 0 < κ) : Prop :=
  ∀ s : ℝ, 0 ≤ s → s ≤ 2 →
    (∀ u : L2T L,
      ((∃ v : H02 L s, v.val = u) ↔
        Integrable (fun t : ℝ => (1+|t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) ∧
      (Integrable (fun t : ℝ => (1+|t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ↔
        Summable (fun n : ℤ => (1+|momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ u).1 n))) ∧
    ∃ A : H02 L s → lp (fun _ : ℤ => ℝ) 1,
      (∀ u n, A u n = (1+|momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n) ∧
      Continuous A ∧ ∀ B : Set (H02 L s), Bornology.IsBounded B → Bornology.IsBounded (A '' B)

/-- INPUT 2. EXACT printed REG-011 (`fractional_moments.tex:512`): for every homeomorphism
`Φ : L² → V ⊂ ℓ²` onto its image (subspace `ℓ²` topology on `V`) with `|Φ_n(u)|² = I_n(u)`,
and every `0 ≤ s ≤ 2`, the restriction of `Φ` is a homeomorphism `H^s → V ∩ h^s` with the
subspace `h^s` topology. (The conclusion of review record's `regularity_homeomorphism_lowInput`.) -/
def Reg011HomeomorphismInput (hκ : 0 < κ) : Prop :=
  ∀ (V : Set Seq) (e : L2T L ≃ₜ V), ExactModuli e hκ →
    ∀ s : ℝ, ∀ hs0 : 0 ≤ s, s ≤ 2 →
      ∃ F : H02 L s ≃ₜ Target (L := L) V s hs0, ∀ u n, (F u).val.val n = (e u.val).val n

/-- INPUT 3. EXACT printed REG-013 (`fractional_moments.tex:610`). Fix an integer `k ≥ 2`.
If the moment characterization, weighted-action continuity and conditional homeomorphism
statement hold through order `k` (every real `0 ≤ s ≤ k`), and the two assertions
(`IntegerAssertion` with its correction `R`, `FiniteYAssertion`) hold, then the same
conclusions hold for every `k < s ≤ k+1`; and if the lower moments and corrections are
bounded on bounded Sobolev sets (`LowerBounded`), the new weighted-action maps send bounded
sets to bounded sets as well. -/
def Reg013InductionInput (hκ : 0 < κ) : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    (∀ s : ℝ, 0 ≤ s → s ≤ k → OrderStatement (L := L) hκ s) →
    ∀ R : Hk L k → ℝ, IntegerAssertion hκ k R → FiniteYAssertion (L := L) hκ k →
      (∀ s : ℝ, (k:ℝ) < s → s ≤ (k:ℝ)+1 → OrderStatement (L := L) hκ s) ∧
      (LowerBounded hκ k R →
        ∀ s : ℝ, (k:ℝ) < s → s ≤ (k:ℝ)+1 → BoundedActions (L := L) hκ s)

/-! ### Elementary lemmas -/

theorem masses_nonneg (hκ : 0 < κ) (u : L2T L) (n : ℤ) :
    0 ≤ (QuantumNLS.RootIndexedMasses.masses hκ u).1 n :=
  (QuantumNLS.RootIndexedMasses.root_indexed_masses_proved_clauses hκ u).2.1 n

theorem lp_one_norm (a : lp (fun _ : ℤ => ℝ) 1) : ‖a‖ = ∑' n, |a n| := by
  have h := lp.hasSum_norm (p := (1 : ℝ≥0∞)) (by simp) a
  simp only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] at h
  exact h.tsum_eq.symm

/-- The `ℓ¹` norm of the weighted carrier is the weighted action sum. -/
theorem actions_norm (hκ : 0 < κ) (s : ℝ) (A : H02 L s → lp (fun _ : ℤ => ℝ) 1)
    (hA : ∀ u n, A u n = (1+|momentum L n|)^(2*s) *
      (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n) (u : H02 L s) :
    ‖A u‖ = ∑' n : ℤ, (1+|momentum L n|)^(2*s) *
      (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n := by
  rw [lp_one_norm]
  apply tsum_congr
  intro n
  rw [hA, abs_of_nonneg (mul_nonneg (by positivity) (masses_nonneg hκ u.val n))]

/-- Two carriers with the same weighted coordinates coincide. -/
theorem carrier_unique (hκ : 0 < κ) (s : ℝ) (A A' : H02 L s → lp (fun _ : ℤ => ℝ) 1)
    (hA : ∀ u n, A u n = (1+|momentum L n|)^(2*s) *
      (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n)
    (hA' : ∀ u n, A' u n = (1+|momentum L n|)^(2*s) *
      (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n) : A = A' :=
  funext fun u => lp.ext (funext fun n => by rw [hA, hA'])

/-- Root-label confinement, quantitatively (accepted weight comparison): the lower moment
is bounded by the confinement factor times the weighted action sum. -/
theorem moment_le_actions (hκ : 0 < κ) (u : L2T L) (s : ℝ) (hs : 0 ≤ s)
    (hint : Integrable (fun t : ℝ => (1+|t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u))
    (hsum : Summable (fun n : ℤ => (1+|momentum L n|)^(2*s) *
      (QuantumNLS.RootIndexedMasses.masses hκ u).1 n)) :
    (∫ t : ℝ, |t|^(2*s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) ≤
      (1 + 2 * Real.sqrt (κ * ‖u‖^2 / L))^(2*s) *
        ∑' n : ℤ, (1+|momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ u).1 n := by
  have hD : 0 ≤ 2 * Real.sqrt (κ * ‖u‖^2 / L) := by positivity
  have hp : (0:ℝ) ≤ 2*s := by linarith
  have h1 : (∫ t : ℝ, |t|^(2*s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) ≤
      ∫ t : ℝ, (1+|t|)^(2*s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u) := by
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => Real.rpow_nonneg (abs_nonneg t) _)) hint
    exact Filter.Eventually.of_forall (fun t =>
      Real.rpow_le_rpow (abs_nonneg t) (by linarith [abs_nonneg t]) hp)
  have hcmp := (QuantumNLS.TerraMultiRound70ExtendedWeights.extended_weight_comparison hκ u (2*s) hp).1
  have hw : ∀ n : ℤ, 0 ≤ (1+|momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ u).1 n :=
    fun n => mul_nonneg (by positivity) (masses_nonneg hκ u n)
  rw [← ENNReal.ofReal_tsum_of_nonneg hw hsum] at hcmp
  have hfm : AEStronglyMeasurable (fun t : ℝ => (1+|t|)^(2*s))
      (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) := hint.aestronglyMeasurable
  have hne : ENNReal.ofReal ((1 + 2 * Real.sqrt (κ * ‖u‖^2 / L))^(2*s)) *
      ENNReal.ofReal (∑' n : ℤ, (1+|momentum L n|)^(2*s) *
        (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have h := ENNReal.toReal_mono hne hcmp
  have hc0 : (0:ℝ) ≤ (1 + 2 * Real.sqrt (κ * ‖u‖^2 / L))^(2*s) :=
    Real.rpow_nonneg (by linarith) _
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0,
    ENNReal.toReal_ofReal (tsum_nonneg hw),
    ← integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall
      (fun t => Real.rpow_nonneg (by linarith [abs_nonneg t]) _)) hfm] at h
  exact h1.trans h

#print axioms toBase_apply
#print axioms lp_one_norm
#print axioms actions_norm
#print axioms carrier_unique
#print axioms moment_le_actions
end QuantumNLS.Reg015Setting

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg015Setting." ||
        n.toString.startsWith "_private.QuantumNLS.Reg015Setting." then
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
        if n.toString.endsWith "HeldGP14Tonelli" || n.toString.endsWith "RegularCut" then
          throwError "Held name in closure: {n}"
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Reg015Setting aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
