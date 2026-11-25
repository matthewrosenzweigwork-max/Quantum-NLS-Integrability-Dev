import QuantumNLS.IndexedMasses
import QuantumNLS.ActionTorus

/-!
DEF-014, faithful replacement interface for the frozen IndexedMasses interface.
Source: DEFINITIONS_LEDGER.md:291-299; ROOT_indexed_masses.tex:14-90.
Only the half-integer level sets must be singletons. Open gaps may be flat.
The singleton condition is sufficient; no equivalence with strict monotonicity
on a whole neighborhood is asserted for arbitrary continuous monotone functions.
The source's positive band derivative gives the stronger local property below.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace QuantumNLS.MonotoneIndexedMasses

abbrev level := QuantumNLS.IndexedMasses.level

/-- Strict increase on some open interval around every point at a separator level. -/
def LocallyStrictAtLevels (φ : ℝ → ℝ) : Prop :=
  ∀ n x, φ x = level n → ∃ a b, a < x ∧ x < b ∧ StrictMonoOn φ (Ioo a b)

/-- Nondecreasing, continuous, onto, with singleton half-integer level sets. -/
structure BoundaryPhase where
  φ : ℝ → ℝ
  monotone : Monotone φ
  continuous : Continuous φ
  onto : Function.Surjective φ
  level_injective : ∀ n x y, φ x = level n → φ y = level n → x = y

/-- Local strict increase at the levels suffices for their global uniqueness. -/
theorem level_injective_of_local {φ : ℝ → ℝ} (hm : Monotone φ)
    (hl : LocallyStrictAtLevels φ) :
    ∀ n x y, φ x = level n → φ y = level n → x = y := by
  have hn : ∀ n x y, φ x = level n → φ y = level n → x < y → False := by
    intro n x y hx hy hxy
    obtain ⟨a, b, hax, hxb, hs⟩ := hl n x hx
    obtain ⟨z, hxz, hzz⟩ := exists_between (lt_min hxy hxb)
    have hlt := hs ⟨hax, hxb⟩ ⟨hax.trans hxz, (lt_min_iff.mp hzz).2⟩ hxz
    have hle := hm (lt_min_iff.mp hzz).1.le
    rw [hx, hy] at *
    exact (not_lt_of_ge hle) hlt
  intro n x y hx hy
  rcases lt_trichotomy x y with h | h | h
  · exact (hn n x y hx hy h).elim
  · exact h
  · exact (hn n y x hy hx h).elim

/-- Constructor from the local band property, without global strict monotonicity. -/
def ofLocal (φ : ℝ → ℝ) (hm : Monotone φ) (hc : Continuous φ)
    (ho : Function.Surjective φ) (hl : LocallyStrictAtLevels φ) : BoundaryPhase :=
  ⟨φ, hm, hc, ho, level_injective_of_local hm hl⟩

namespace BoundaryPhase
variable (P : BoundaryPhase)

theorem exists_unique_separator (n : ℤ) : ∃! b : ℝ, P.φ b = level n := by
  obtain ⟨b, hb⟩ := P.onto (level n)
  exact ⟨b, hb, fun y hy => P.level_injective n y b hy hb⟩

def separator (n : ℤ) : ℝ := (P.exists_unique_separator n).exists.choose

theorem separator_spec (n : ℤ) : P.φ (P.separator n) = level n :=
  (P.exists_unique_separator n).exists.choose_spec

theorem separator_unique {n : ℤ} {x : ℝ} (hx : P.φ x = level n) : x = P.separator n :=
  P.level_injective n x (P.separator n) hx (P.separator_spec n)

theorem level_strictMono : StrictMono level :=
  QuantumNLS.IndexedMasses.BoundaryPhase.level_strictMono

/-- Order reflection at a separator only; no global order reflection is needed. -/
theorem lt_separator_iff (x : ℝ) (n : ℤ) : x < P.separator n ↔ P.φ x < level n := by
  constructor
  · intro hx
    have hle : P.φ x ≤ level n := (P.monotone hx.le).trans_eq (P.separator_spec n)
    exact lt_of_le_of_ne hle (fun he => (ne_of_lt hx) (P.separator_unique he))
  · intro hx
    by_contra hn
    have hle := P.monotone (le_of_not_gt hn)
    rw [P.separator_spec n] at hle
    exact (not_lt_of_ge hle) hx

theorem separator_lt_iff (x : ℝ) (n : ℤ) : P.separator n < x ↔ level n < P.φ x := by
  constructor
  · intro hx
    have hle : level n ≤ P.φ x := (P.separator_spec n).symm.trans_le (P.monotone hx.le)
    exact lt_of_le_of_ne hle (fun he => (ne_of_gt hx) (P.separator_unique he.symm))
  · intro hx
    by_contra hn
    have hle := P.monotone (le_of_not_gt hn)
    rw [P.separator_spec n] at hle
    exact (not_lt_of_ge hle) hx

theorem separator_strictMono : StrictMono P.separator := by
  intro m n h
  exact (P.lt_separator_iff _ n).mpr (by rw [P.separator_spec m]; exact level_strictMono h)

def indexedMass (M : Measure ℝ) (n : ℤ) : ℝ≥0∞ :=
  M (Ioo (P.separator (n - 1)) (P.separator n))

def indexedMassReal (M : Measure ℝ) (n : ℤ) : ℝ := (P.indexedMass M n).toReal

theorem indexedMassReal_nonneg (M : Measure ℝ) (n : ℤ) : 0 ≤ P.indexedMassReal M n :=
  ENNReal.toReal_nonneg

theorem pairwiseDisjoint_Ioo :
    Pairwise (Function.onFun Disjoint fun n : ℤ => Ioo (P.separator (n - 1)) (P.separator n)) := by
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with h | h
  · refine Set.disjoint_left.mpr fun x hx hy => ?_
    have h1 : P.separator m ≤ P.separator (n - 1) := P.separator_strictMono.monotone (by omega)
    linarith [hx.2, hy.1]
  · refine Set.disjoint_left.mpr fun x hx hy => ?_
    have h1 : P.separator n ≤ P.separator (m - 1) := P.separator_strictMono.monotone (by omega)
    linarith [hx.1, hy.2]

theorem tsum_indexedMass_le (M : Measure ℝ) : ∑' n, P.indexedMass M n ≤ M univ :=
  tsum_meas_le_meas_iUnion_of_disjoint M (fun _ => measurableSet_Ioo)
    P.pairwiseDisjoint_Ioo |>.trans (measure_mono (subset_univ _))

theorem summable_indexedMassReal (M : Measure ℝ) [IsFiniteMeasure M] :
    Summable (P.indexedMassReal M) := by
  exact ENNReal.summable_toReal
    (ne_top_of_le_ne_top (measure_ne_top M univ) (P.tsum_indexedMass_le M))

theorem indexedMass_zero (n : ℤ) : P.indexedMass (0 : Measure ℝ) n = 0 := by
  simp [indexedMass]

/-- Every point belongs either to a separator or to one of the mass intervals. -/
theorem mem_interval_or_separator (x : ℝ) :
    (∃ n, x ∈ Ioo (P.separator (n - 1)) (P.separator n)) ∨ x ∈ range P.separator := by
  let k : ℤ := ⌊P.φ x / Real.pi - 1 / 2⌋
  have hlo := Int.floor_le (P.φ x / Real.pi - 1 / 2)
  have hhi := Int.lt_floor_add_one (P.φ x / Real.pi - 1 / 2)
  have hdiv : P.φ x / Real.pi * Real.pi = P.φ x := div_mul_cancel₀ _ Real.pi_ne_zero
  have hk : level k ≤ P.φ x := by
    dsimp [level, QuantumNLS.IndexedMasses.level, k]
    nlinarith [mul_le_mul_of_nonneg_right hlo Real.pi_pos.le]
  rcases hk.eq_or_lt with he | he
  · exact Or.inr ⟨k, (P.separator_unique he.symm).symm⟩
  · left
    refine ⟨k + 1, ?_, ?_⟩
    · apply (P.separator_lt_iff x (k + 1 - 1)).mpr
      simpa using he
    · apply (P.lt_separator_iff x (k + 1)).mpr
      dsimp [level, QuantumNLS.IndexedMasses.level]
      push_cast
      change P.φ x < ((k : ℝ) + 1 + 1 / 2) * Real.pi
      dsimp [k]
      nlinarith [mul_lt_mul_of_pos_right hhi Real.pi_pos]

/-- The only omitted points are the separators. -/
theorem iUnion_intervals :
    (⋃ n : ℤ, Ioo (P.separator (n - 1)) (P.separator n)) = (range P.separator)ᶜ := by
  ext x
  constructor
  · intro hx ⟨n, hn⟩
    obtain ⟨m, hm⟩ := mem_iUnion.mp hx
    have h1 := (P.separator_lt_iff x (m - 1)).mp hm.1
    have h2 := (P.lt_separator_iff x m).mp hm.2
    rw [← hn, P.separator_spec n] at h1 h2
    have hn1 : m - 1 < n := level_strictMono.lt_iff_lt.mp h1
    have hn2 : n < m := level_strictMono.lt_iff_lt.mp h2
    omega
  · intro hx
    rcases P.mem_interval_or_separator x with ⟨n, hn⟩ | h
    · exact mem_iUnion.mpr ⟨n, hn⟩
    · exact (hx h).elim

/-- Exact total mass once the countable separator set has measure zero. -/
theorem tsum_indexedMass_eq (M : Measure ℝ) (hz : M (range P.separator) = 0) :
    ∑' n, P.indexedMass M n = M univ := by
  calc
    ∑' n, P.indexedMass M n = M (⋃ n : ℤ, Ioo (P.separator (n - 1)) (P.separator n)) :=
      (measure_iUnion P.pairwiseDisjoint_Ioo (fun _ => measurableSet_Ioo)).symm
    _ = M univ := by
      rw [P.iUnion_intervals]
      exact measure_of_measure_compl_eq_zero (by simpa using hz)

/-- In particular, atomless spectral measures lose no mass at separators. -/
theorem tsum_indexedMass_eq_of_noAtoms (M : Measure ℝ) [NullSingletonClass M] :
    ∑' n, P.indexedMass M n = M univ :=
  P.tsum_indexedMass_eq M ((Set.countable_range _).measure_zero M)

/-- The source's nonnegative ell1 carrier, usable without the frozen strict phase type. -/
def massVector (M : Measure ℝ) [IsFiniteMeasure M] : QuantumNLS.ActionTorus.PosL1 :=
  ⟨⟨P.indexedMassReal M, by
      apply memℓp_gen
      simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs,
        abs_of_nonneg (P.indexedMassReal_nonneg M _)] using P.summable_indexedMassReal M⟩,
    P.indexedMassReal_nonneg M⟩

/-- Real ell1 sum equals the full mass under the same null-separator hypothesis. -/
theorem tsum_indexedMassReal_eq (M : Measure ℝ) [IsFiniteMeasure M]
    (hz : M (range P.separator) = 0) :
    ∑' n, P.indexedMassReal M n = (M univ).toReal := by
  change (∑' n, (P.indexedMass M n).toReal) = (M univ).toReal
  calc
    (∑' n, (P.indexedMass M n).toReal) = (∑' n, P.indexedMass M n).toReal :=
      (ENNReal.tsum_toReal_eq (f := P.indexedMass M)
        (fun n => measure_ne_top M (Ioo (P.separator (n - 1)) (P.separator n)))).symm
    _ = (M univ).toReal := congrArg ENNReal.toReal (P.tsum_indexedMass_eq M hz)

/-- The mass-vector coordinates are exactly the interval masses. -/
theorem massVector_apply (M : Measure ℝ) [IsFiniteMeasure M] (n : ℤ) :
    (P.massVector M).1 n = P.indexedMassReal M n := rfl

end BoundaryPhase

/-- Every old strict phase transfers to the faithful interface, preserving its function. -/
def ofStrict (P : QuantumNLS.IndexedMasses.BoundaryPhase) : BoundaryPhase :=
  ⟨P.φ, P.strictMono.monotone, P.continuous, P.surjective,
    fun _ _ _ hx hy => P.strictMono.injective (hx.trans hy.symm)⟩

theorem separator_ofStrict (P : QuantumNLS.IndexedMasses.BoundaryPhase) (n : ℤ) :
    (ofStrict P).separator n = P.separator n :=
  P.separator_unique ((ofStrict P).separator_spec n)

theorem indexedMass_ofStrict (P : QuantumNLS.IndexedMasses.BoundaryPhase)
    (M : Measure ℝ) (n : ℤ) : (ofStrict P).indexedMass M n = P.indexedMass M n := by
  simp only [BoundaryPhase.indexedMass, QuantumNLS.IndexedMasses.BoundaryPhase.indexedMass,
    separator_ofStrict]

end QuantumNLS.MonotoneIndexedMasses

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.MonotoneIndexedMasses.level
#print axioms QuantumNLS.MonotoneIndexedMasses.LocallyStrictAtLevels
#print axioms QuantumNLS.MonotoneIndexedMasses.BoundaryPhase
#print axioms QuantumNLS.MonotoneIndexedMasses.level_injective_of_local
#print axioms QuantumNLS.MonotoneIndexedMasses.ofLocal
#print axioms QuantumNLS.MonotoneIndexedMasses.BoundaryPhase.exists_unique_separator
#print axioms QuantumNLS.MonotoneIndexedMasses.BoundaryPhase.separator
#print axioms QuantumNLS.MonotoneIndexedMasses.BoundaryPhase.separator_spec
#print axioms QuantumNLS.MonotoneIndexedMasses.BoundaryPhase.separator_unique
#print axioms QuantumNLS.MonotoneIndexedMasses.BoundaryPhase.level_strictMono
#print axioms QuantumNLS.MonotoneIndexedMasses.BoundaryPhase.lt_separator_iff
#print axioms QuantumNLS.MonotoneIndexedMasses.BoundaryPhase.separator_lt_iff
#print axioms QuantumNLS.MonotoneIndexedMasses.BoundaryPhase.separator_strictMono
#print axioms QuantumNLS.MonotoneIndexedMasses.BoundaryPhase.indexedMass
#print axioms QuantumNLS.MonotoneIndexedMasses.BoundaryPhase.indexedMassReal
#print axioms QuantumNLS.MonotoneIndexedMasses.BoundaryPhase.indexedMassReal_nonneg
#print axioms QuantumNLS.MonotoneIndexedMasses.BoundaryPhase.pairwiseDisjoint_Ioo
#print axioms QuantumNLS.MonotoneIndexedMasses.BoundaryPhase.tsum_indexedMass_le
#print axioms QuantumNLS.MonotoneIndexedMasses.BoundaryPhase.summable_indexedMassReal
#print axioms QuantumNLS.MonotoneIndexedMasses.BoundaryPhase.indexedMass_zero
#print axioms QuantumNLS.MonotoneIndexedMasses.BoundaryPhase.mem_interval_or_separator
#print axioms QuantumNLS.MonotoneIndexedMasses.BoundaryPhase.iUnion_intervals
#print axioms QuantumNLS.MonotoneIndexedMasses.BoundaryPhase.tsum_indexedMass_eq
#print axioms QuantumNLS.MonotoneIndexedMasses.BoundaryPhase.tsum_indexedMass_eq_of_noAtoms
#print axioms QuantumNLS.MonotoneIndexedMasses.BoundaryPhase.massVector
#print axioms QuantumNLS.MonotoneIndexedMasses.BoundaryPhase.tsum_indexedMassReal_eq
#print axioms QuantumNLS.MonotoneIndexedMasses.BoundaryPhase.massVector_apply
#print axioms QuantumNLS.MonotoneIndexedMasses.ofStrict
#print axioms QuantumNLS.MonotoneIndexedMasses.separator_ofStrict
#print axioms QuantumNLS.MonotoneIndexedMasses.indexedMass_ofStrict

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.MonotoneIndexedMasses." then
      pending := pending.push n
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
