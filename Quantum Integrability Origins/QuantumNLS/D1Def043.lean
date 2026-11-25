import QuantumNLS.IndexedScalarMeasureCuts

/-!
# DEF-043, owner decision D1 realization (NEW module; frozen `IndexedScalarMeasure` and `IndexedScalarMeasureCuts` untouched)

Owner decision D1 (2026-11-16): the DEF-043/044 "regular cut" is EVERY `x ∉ supp μ` with `F(x)/(2π)` not an integer;
separation holds at every such `x`, with the unique integer `a` such that `2πa < F(x) < 2π(a+1)`.

Exact D1-faithful definition (Terra-B r51 "DEF-043 realization -- RESTATE"):
* the scalar fields are those of `IndexedScalarMeasure`: `0 < L`, `0 < κ`, a nonatomic probability measure `μ`, the
  boundary function `reG`, the boundary alternative (locally uniform or locally bounded/a.e.), and the `μ`-a.e.
  integer-valued `indexLabel`;
* `F = exteriorForce L κ μ`, `n = indexLabel L κ reG`;
* `regularCut L κ μ x ↔ x ∉ μ.support ∧ ∀ a : ℤ, F x / (2π) ≠ a`;
* separation is required at EVERY regular cut `x`, for every integer `a` with `2πa < F x < 2π(a+1)` (which exists and is
  unique, `regular_unique_index`): `n ≤ a` `μ`-a.e. on `t < x` and `n ≥ a + 1` `μ`-a.e. on `t > x`.
* there is no cut-set parameter.

Proved here: `regular_unique_index`, `bracket_regular`, the two-way conversion with the older `IndexedScalarMeasure`
(`D1ScalarMeasure.toFull`, `IndexedScalarMeasure.toD1`, round trips by `rfl`, and the carrier-level `d1Full`/`full_d1`
for an `IndexedScalarMeasureCuts` carrier plus the separation predicate `D1Sep`).
Not proved (not claimed): that any particular physical measure satisfies D1.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

open MeasureTheory Filter Topology Set
open QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts

namespace QuantumNLS.D1Def043

/-- D1 regular cut: `x ∉ supp μ` and `F(x)/(2π)` is not an integer. -/
def regularCut (L κ : ℝ) (μ : Measure ℝ) (x : ℝ) : Prop :=
  x ∉ μ.support ∧ ∀ a : ℤ, exteriorForce L κ μ x / (2 * Real.pi) ≠ (a : ℝ)

/-- D1 separation on the scalar data `(μ, reG)`: at EVERY regular cut `x` and integer `a` with
`2πa < F x < 2π(a+1)`, `n ≤ a` a.e. on `t < x` and `n ≥ a+1` a.e. on `t > x`. -/
def D1Separation (L κ : ℝ) (μ : Measure ℝ) (reG : ℝ → ℝ) : Prop :=
  ∀ x, regularCut L κ μ x → ∀ a : ℤ,
    2 * Real.pi * a < exteriorForce L κ μ x →
    exteriorForce L κ μ x < 2 * Real.pi * (a + 1) →
      (∀ᵐ t ∂μ, t < x → indexLabel L κ reG t ≤ a) ∧
      (∀ᵐ t ∂μ, x < t → (a : ℝ) + 1 ≤ indexLabel L κ reG t)

/-- **DEF-043, owner decision D1**: the indexed scalar measure with separation at every D1 regular cut. -/
structure D1ScalarMeasure (L κ : ℝ) where
  hL : 0 < L
  hκ : 0 < κ
  μ : Measure ℝ
  isProb : IsProbabilityMeasure μ
  noAtoms : NoAtoms μ
  reG : ℝ → ℝ
  boundary : LocallyUniformBoundary μ reG ∨ BoundedAEBoundary μ reG
  integer_ae : ∀ᵐ t ∂μ, ∃ k : ℤ, indexLabel L κ reG t = k
  separation : ∀ x, regularCut L κ μ x → ∀ a : ℤ,
    2 * Real.pi * a < exteriorForce L κ μ x →
    exteriorForce L κ μ x < 2 * Real.pi * (a + 1) →
      (∀ᵐ t ∂μ, t < x → indexLabel L κ reG t ≤ a) ∧
      (∀ᵐ t ∂μ, x < t → (a : ℝ) + 1 ≤ indexLabel L κ reG t)

variable {L κ : ℝ}

/-- Unique-index lemma: at every regular cut there is exactly one integer `a` with
`2πa < F x < 2π(a+1)` (the floor of `F x / (2π)`). -/
theorem regular_unique_index {μ : Measure ℝ} {x : ℝ} (hx : regularCut L κ μ x) :
    ∃! a : ℤ, 2 * Real.pi * a < exteriorForce L κ μ x ∧
      exteriorForce L κ μ x < 2 * Real.pi * (a + 1) := by
  let v := exteriorForce L κ μ x / (2 * Real.pi)
  have hp : 0 < 2 * Real.pi := by positivity
  have hl : ((⌊v⌋ : ℤ) : ℝ) < v :=
    lt_of_le_of_ne (Int.floor_le v) (Ne.symm (hx.2 ⌊v⌋))
  have hu : v < ((⌊v⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one v
  refine ⟨⌊v⌋, ?_, ?_⟩
  · constructor
    · have h := (lt_div_iff₀ hp).mp hl
      dsimp [v] at h
      nlinarith
    · have h := (div_lt_iff₀ hp).mp hu
      dsimp [v] at h
      nlinarith
  · intro a ha
    have hlow : (a : ℝ) < v := by
      apply (lt_div_iff₀ hp).mpr
      nlinarith [ha.1]
    have hupp : v < (a : ℝ) + 1 := by
      apply (div_lt_iff₀ hp).mpr
      nlinarith [ha.2]
    exact (Int.floor_eq_iff.mpr ⟨le_of_lt hlow, hupp⟩).symm

/-- Any exterior point with a strict adjacent-integer force bracket is a D1 regular cut. -/
theorem bracket_regular {μ : Measure ℝ} {x : ℝ} (hx : x ∉ μ.support)
    {a : ℤ} (h1 : 2 * Real.pi * a < exteriorForce L κ μ x)
    (h2 : exteriorForce L κ μ x < 2 * Real.pi * (a + 1)) : regularCut L κ μ x := by
  refine ⟨hx, ?_⟩
  intro b hb
  have hp : 0 < 2 * Real.pi := by positivity
  have he : exteriorForce L κ μ x = (b : ℝ) * (2 * Real.pi) := (div_eq_iff (ne_of_gt hp)).mp hb
  have hb1 : (a : ℝ) < (b : ℝ) := by nlinarith
  have hb2 : (b : ℝ) < (a : ℝ) + 1 := by nlinarith
  have hi1 : a < b := by exact_mod_cast hb1
  have hi2 : b < a + 1 := by exact_mod_cast hb2
  omega

/-- D1 regular cuts are exterior points. -/
theorem regularCut.not_mem_support {μ : Measure ℝ} {x : ℝ} (hx : regularCut L κ μ x) :
    x ∉ μ.support := hx.1

/-- The D1 structure gives the earlier full-exterior `IndexedScalarMeasure`. -/
def D1ScalarMeasure.toFull (S : D1ScalarMeasure L κ) : IndexedScalarMeasure L κ where
  hL := S.hL
  hκ := S.hκ
  μ := S.μ
  isProb := S.isProb
  noAtoms := S.noAtoms
  reG := S.reG
  boundary := S.boundary
  integer_ae := S.integer_ae
  separation := fun x hx a h1 h2 => S.separation x (bracket_regular hx h1 h2) a h1 h2

/-- The earlier `IndexedScalarMeasure` gives the D1 structure. -/
def _root_.QuantumNLS.IndexedScalarMeasure.IndexedScalarMeasure.toD1
    (S : IndexedScalarMeasure L κ) : D1ScalarMeasure L κ where
  hL := S.hL
  hκ := S.hκ
  μ := S.μ
  isProb := S.isProb
  noAtoms := S.noAtoms
  reG := S.reG
  boundary := S.boundary
  integer_ae := S.integer_ae
  separation := fun x hx a h1 h2 => S.separation x hx.1 a h1 h2

theorem toFull_toD1 (S : IndexedScalarMeasure L κ) : S.toD1.toFull = S := rfl

theorem toD1_toFull (S : D1ScalarMeasure L κ) : S.toFull.toD1 = S := rfl

/-- The scalar-cuts carrier of a D1 measure (cuts = full exterior; separation holds at every D1 cut). -/
def D1ScalarMeasure.toCuts (S : D1ScalarMeasure L κ) : IndexedScalarMeasureCuts L κ :=
  S.toFull.toCuts

/-- D1 separation as a predicate on an `IndexedScalarMeasureCuts` carrier (it does not read `S.cuts`). -/
def D1Sep (S : IndexedScalarMeasureCuts L κ) : Prop := D1Separation L κ S.μ S.reG

/-- Carrier-level conversion: scalar data in an `IndexedScalarMeasureCuts` carrier plus D1 separation
give the earlier `IndexedScalarMeasure`. -/
def d1Full (S : IndexedScalarMeasureCuts L κ) (hd : D1Sep S) : IndexedScalarMeasure L κ where
  hL := S.hL
  hκ := S.hκ
  μ := S.μ
  isProb := S.isProb
  noAtoms := S.noAtoms
  reG := S.reG
  boundary := S.boundary
  integer_ae := S.integer_ae
  separation := fun x hx a h1 h2 => hd x (bracket_regular hx h1 h2) a h1 h2

/-- Reverse implication: the carrier `S.toCuts` of an `IndexedScalarMeasure` satisfies D1 separation. -/
theorem full_d1 (S : IndexedScalarMeasure L κ) : D1Sep S.toCuts := by
  intro x hx a h1 h2
  exact S.separation x hx.1 a h1 h2

/-- The D1 structure's `toCuts` carrier satisfies `D1Sep`. -/
theorem D1ScalarMeasure.toCuts_d1 (S : D1ScalarMeasure L κ) : D1Sep S.toCuts :=
  full_d1 S.toFull

end QuantumNLS.D1Def043

#print axioms QuantumNLS.D1Def043.regular_unique_index
#print axioms QuantumNLS.D1Def043.bracket_regular
#print axioms QuantumNLS.D1Def043.d1Full
#print axioms QuantumNLS.D1Def043.full_d1
#print axioms QuantumNLS.D1Def043.toFull_toD1
#print axioms QuantumNLS.D1Def043.toD1_toFull
