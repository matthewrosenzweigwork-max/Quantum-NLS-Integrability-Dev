import QuantumNLS.Ext005SourceIntervalR32b

/-! Restriction and consecutive-interval uniqueness, plus a single global
both-directions theorem for locally energy-bounded weak solutions. This is
uniqueness for existing solutions, not a construction or an existence input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate ContDiff
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005PatchingR32b
open Ext005OperatorFormR113 Ext005SourceIntervalR32b Ext005HilbertEnergyR112
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Source assumptions restrict to a smaller closed interval. -/
def restrictSource (A : PositiveOperator H) (a b : ℝ) (S : SourceOn A a b)
    (c d : ℝ) (hac : a ≤ c) (hdb : d ≤ b) : SourceOn A c d where
  B := S.B
  domain := S.domain
  commute := S.commute
  hamiltonian := S.hamiltonian
  C := S.C
  constant_pos := S.constant_pos
  symmetric t ht := S.symmetric t ⟨hac.trans ht.1, ht.2.trans hdb⟩
  upper t ht := S.upper t ⟨hac.trans ht.1, ht.2.trans hdb⟩
  lower t ht := S.lower t ⟨hac.trans ht.1, ht.2.trans hdb⟩
  commutator t ht := S.commutator t ⟨hac.trans ht.1, ht.2.trans hdb⟩
  diagonalDerivative := S.diagonalDerivative
  derivative u t ht := (S.derivative u t ⟨hac.trans ht.1, ht.2.trans hdb⟩).mono
    (fun _ hs => ⟨hac.trans hs.1, hs.2.trans hdb⟩)
  derivative_bound u t ht := S.derivative_bound u t ⟨hac.trans ht.1, ht.2.trans hdb⟩

/-- The three D3 requirements restrict without a measurable-lift premise. -/
lemma D3On_restrict (A : PositiveOperator H) (a b : ℝ) (S : SourceOn A a b)
    (c d : ℝ) (hac : a ≤ c) (hdb : d ≤ b) (x : ℝ → H) (hx : D3On A a b S x) :
    D3On A c d (restrictSource A a b S c d hac hdb) x := by
  let : InnerProductSpace ℝ (FormDomain A) := InnerProductSpace.rclikeToReal ℂ (FormDomain A)
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  let i := (inclusion A).restrictScalars ℝ
  have hsub : Icc c d ⊆ Icc a b := fun _ ht => ⟨hac.trans ht.1, ht.2.trans hdb⟩
  refine ⟨hx.1.mono hsub, Ext005IntervalUniqueR32b.energy_mono i hx.2.1 hsub, ?_⟩
  intro v p hp hc hs
  exact hx.2.2 v p hp hc (hs.trans fun _ ht => ⟨hac.trans_lt ht.1, ht.2.trans_le hdb⟩)

/-- Patching uniqueness over any finite chain of consecutive compact
intervals. Each piece carries its own source hypotheses and D3 bounds. -/
theorem EXT005_D3_unique_chain (A : PositiveOperator H) (τ : ℕ → ℝ) (n : ℕ)
    (S : ∀ k : ℕ, SourceOn A (τ k) (τ (k + 1)))
    (hτ : ∀ k < n, τ k < τ (k + 1)) (x y : ℝ → H)
    (hx : ∀ k < n, D3On A (τ k) (τ (k + 1)) (S k) x)
    (hy : ∀ k < n, D3On A (τ k) (τ (k + 1)) (S k) y)
    (hinit : x (τ 0) = y (τ 0)) :
    ∀ k < n, ∀ t ∈ Icc (τ k) (τ (k + 1)), x t = y t := by
  have hend : ∀ k, k ≤ n → x (τ k) = y (τ k) := by
    intro k
    induction k with
    | zero => intro _; exact hinit
    | succ k ih =>
      intro hkn
      have hk : k < n := Nat.lt_of_succ_le hkn
      exact EXT005_D3_finite_interval_unique A _ _ (S k) (τ k) (hτ k hk)
        ⟨le_rfl, (hτ k hk).le⟩ x y (hx k hk) (hy k hk) (ih hk.le)
        (τ (k + 1)) ⟨(hτ k hk).le, le_rfl⟩
  intro k hk
  exact EXT005_D3_finite_interval_unique A _ _ (S k) (τ k) (hτ k hk)
    ⟨le_rfl, (hτ k hk).le⟩ x y (hx k hk) (hy k hk) (hend k hk.le)

/-- One theorem covering every finite positive and negative time: local
source and D3 hypotheses on each [-T,T] imply equality on the whole line.
The arbitrary-interval chain rule avoids changing variables in distributions. -/
theorem EXT005_D3_all_finite_times_unique (A : PositiveOperator H)
    (S : ∀ T : ℝ, 0 < T → SourceOn A (-T) T) (x y : ℝ → H)
    (hx : ∀ (T : ℝ) (hT : 0 < T), D3On A (-T) T (S T hT) x)
    (hy : ∀ (T : ℝ) (hT : 0 < T), D3On A (-T) T (S T hT) y)
    (hinit : x 0 = y 0) : x = y := by
  funext t
  let T := |t| + 1
  have hT : 0 < T := by dsimp [T]; positivity
  apply EXT005_D3_finite_interval_unique A (-T) T (S T hT) 0 (by linarith)
    (by constructor <;> linarith) x y (hx T hT) (hy T hT) hinit t
  constructor <;> dsimp [T] <;> linarith [le_abs_self t, neg_abs_le t]

end QuantumNLS.Ext005PatchingR32b
#print axioms QuantumNLS.Ext005PatchingR32b.EXT005_D3_unique_chain
#print axioms QuantumNLS.Ext005PatchingR32b.EXT005_D3_all_finite_times_unique

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005PatchingR32b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005PatchingR32b." then
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
  Lean.logInfo m!"R32b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
