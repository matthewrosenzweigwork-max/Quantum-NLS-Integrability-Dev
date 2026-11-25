import Mathlib

set_option autoImplicit false

namespace NlsGge.Atomic.KSTPath

/-- The `2k` internal lattice vertices in the KST path expansion. -/
abbrev Path (k : ℕ) := Fin (2 * k) → ℤ

/-- A near/far pattern on the `2k` internal vertices. `false` means near. -/
abbrev Pattern (k : ℕ) := Fin (2 * k) → Bool

def vertexIndex {k : ℕ} (hk : 0 < k) (i : ℕ) : Fin (2 * k) :=
  ⟨i % (2 * k), Nat.mod_lt _ (by omega)⟩

/-- On an in-range index the totalized vertex accessor is the source index. -/
theorem vertexIndex_eq_mk {k : ℕ} (hk : 0 < k) {i : ℕ} (hi : i < 2 * k) :
    vertexIndex hk i = ⟨i, hi⟩ := by
  apply Fin.ext
  simp [vertexIndex, Nat.mod_eq_of_lt hi]

/-- Source path argument in slot `j`: the left endpoint, an adjacent-vertex
sum, or the right endpoint. The source expansion has `k ≥ 1`. -/
def pathArgument {k : ℕ} (hk : 0 < k) (n : ℤ) (ℓ : Path k)
    (j : Fin (2 * k + 1)) : ℤ :=
  if j.val = 0 then
    n + ℓ (vertexIndex hk 0)
  else if j.val < 2 * k then
    ℓ (vertexIndex hk (j.val - 1)) + ℓ (vertexIndex hk j.val)
  else
    ℓ (vertexIndex hk (2 * k - 1)) + n

/-- The exact near/far cutoff from the source: `true` means
`|ℓᵢ-n| > |n|/2`, and `false` means the complementary near inequality. -/
noncomputable def nearFarBit (n : ℤ) (ℓi : ℤ) : Bool :=
  decide (((ℓi - n).natAbs : ℝ) > (n.natAbs : ℝ) / 2)

/-- Membership in the source summation lattice `I_{2k,n}`. -/
def admissiblePath {k : ℕ} (n : ℤ) (ℓ : Path k) : Prop :=
  ∀ i, ℓ i ≠ n

/-- The number of far vertices in a pattern. -/
def patternOnes {k : ℕ} (σ : Pattern k) : ℕ :=
  ∑ i : Fin (2 * k), if σ i then 1 else 0

/-- The number of adjacent pairs of far vertices. -/
def adjacentOnePairs {k : ℕ} (σ : Pattern k) : ℕ :=
  ∑ i : Fin (2 * k - 1),
    if σ ⟨i.val, by omega⟩ && σ ⟨i.val + 1, by omega⟩ then 1 else 0

/-- A source path-argument slot forced large by the adjacent pattern bits. -/
def forcedAt {k : ℕ} (hk : 0 < k) (σ : Pattern k)
    (j : Fin (2 * k + 1)) : Prop :=
  if j.val = 0 then σ ⟨0, by omega⟩ = false
  else if j.val < 2 * k then
    σ (vertexIndex hk (j.val - 1)) = false ∧ σ (vertexIndex hk j.val) = false
  else σ (vertexIndex hk (2 * k - 1)) = false

/-- Number of forced source argument slots. The `Fin` cardinal retains slot
multiplicity even if two integer arguments happen to have equal values. -/
noncomputable def forcedTailCount {k : ℕ} (hk : 0 < k) (σ : Pattern k) : ℕ :=
  by classical exact (Finset.univ.filter (forcedAt hk σ)).card

/-- Number of path-argument slots whose integer label has magnitude at least
`|n|`. -/
def actualLargeArgs {k : ℕ} (hk : 0 < k) (n : ℤ) (ℓ : Path k) : ℕ :=
  (Finset.univ.filter (fun j : Fin (2 * k + 1) =>
    n.natAbs ≤ (pathArgument hk n ℓ j).natAbs)).card

/-- The real absolute-value test represented by the Boolean pattern. -/
theorem nearFarBit_eq_true_iff (n ℓi : ℤ) :
    nearFarBit n ℓi = true ↔
      ((ℓi - n).natAbs : ℝ) > (n.natAbs : ℝ) / 2 := by
  simp [nearFarBit]

theorem nearFarBit_eq_false_iff (n ℓi : ℤ) :
    nearFarBit n ℓi = false ↔
      ((ℓi - n).natAbs : ℝ) ≤ (n.natAbs : ℝ) / 2 := by
  simp [nearFarBit]

/-- The left endpoint source argument `n + ℓ₁`. -/
theorem pathArgument_zero {k : ℕ} (hk : 0 < k) (n : ℤ) (ℓ : Path k) :
    pathArgument hk n ℓ ⟨0, by omega⟩ = n + ℓ ⟨0, by omega⟩ := by
  simp [pathArgument, vertexIndex]

/-- The right endpoint source argument `ℓ_(2k) + n`. -/
theorem pathArgument_last {k : ℕ} (hk : 0 < k) (n : ℤ) (ℓ : Path k) :
    pathArgument hk n ℓ ⟨2 * k, by omega⟩ = ℓ ⟨2 * k - 1, by omega⟩ + n := by
  have hlast : 2 * k - 1 < 2 * k := by omega
  have hne0 : ¬ 2 * k = 0 := by omega
  simp [pathArgument, hne0, Nat.lt_irrefl, vertexIndex_eq_mk hk hlast]

/-- Interior source arguments are the adjacent-vertex sums. -/
theorem pathArgument_interior {k : ℕ} (hk : 0 < k) (n : ℤ) (ℓ : Path k)
    (j : Fin (2 * k + 1)) (hj0 : 0 < j.val) (hjlast : j.val < 2 * k) :
    pathArgument hk n ℓ j =
      ℓ ⟨j.val - 1, by omega⟩ + ℓ ⟨j.val, by omega⟩ := by
  have hleft : j.val - 1 < 2 * k := by omega
  have hne0 : ¬ j.val = 0 := by omega
  simp [pathArgument, hne0, hjlast, vertexIndex_eq_mk hk hleft,
    vertexIndex_eq_mk hk hjlast]

end NlsGge.Atomic.KSTPath
