import QuantumNLS.Bind7BDEF033H01
import QuantumNLS.Def033AdjacentR24m
import QuantumNLS.Def033SobolevR25m
import QuantumNLS.RB7BindFinal

/-!
# Bind7BDEF033H02: DEF-033 packaged at ALL printed clauses

PRINTED SOURCE: `source-text/chapters/definitions.tex`, lines 199-203 (`\begin{definition}` at 199, the text
`\DefinitionID{DEF-033}...` at 201, `\end{definition}` at 203; label `def:report-33`, "Adjacent quantum charge
difference"; `scope.json` `statement_location` file `chapters/definitions.tex`, line 199, offset 16663; file SHA-256
`abe7643be6830cf1601a2beed4c2635b22de769b77ef5918f6a0f09fbb8da6fc`).  The printed text is:

  "For the fixed smooth hierarchy of Definition~24, the active-coordinate frequency `ω_{r,n}(u)` is the real
   multiplier in `w_n(Φ_t^{(r)}u) = e^{-itω_{r,n}(u)} w_n(u)` when `a_n(u) > 0`.  Its existence is proved in
   Theorem~thm:hierarchy.  For `m_a ≥ 1`, the adjacent quantum difference of order `r` is
   `Λ_{N,r}(m - e_a + e_b) - Λ_{N,r}(m)`, receiver minus donor.  For fixed positive-action endpoints its target
   is `ω_{r,b}(u) - ω_{r,a}(u)`.  Each limit specifies the original Born law and its convention on the
   missing-donor sector."

CLAUSE MAP of the conclusion: the structure `DEF033Package hκ w` (one field per printed clause) and its
inhabitant `DEF033_package hκ w hw : DEF033Package hκ w` (the only declaration with hypotheses `hκ w hw`):
  (A) `a_n(u) = |w_n(u)|²`: `PrintedChart.moduli`, the printed chart normalization used by DEF-033;
  (B) "fixed smooth hierarchy of Definition 24": fields `flow`, `isFlow`, `hamiltonian_physical`, `flow_unique`,
      `flow_commute`, `flow_staged`: flows of the Hamiltonians `hamiltonian L κ r`, each equal to the real part of the
      physical Riccati charge `charge L κ · (r+1)` (`Def033AdjacentR24m.hamiltonian_is_physical`, reviewed in
      terra_review r232), unique (any smooth Hamiltonian flow coincides with it, so `ω` does not depend on a
      choice), one commuting family of orders `r ≥ 0`, orders 0, 1, 2 equal to the staged DEF-024 flows;
  (C) "`ω_{r,n}(u)` is the real multiplier ... when `a_n(u) > 0`; its existence is proved in thm:hierarchy": fields
      `ω`, `active`, `active_unique`: the selected function `ω r u n` is an `ActiveFrequency` along the SAME flow
      `flow r` at the positive-action coordinates, and any active frequency equals it (the existence and uniqueness
      of the frozen H01 theorem, repackaged as a selected function);
  (D) "adjacent quantum difference, `m_a ≥ 1`, `Λ_{N,r}(m - e_a + e_b) - Λ_{N,r}(m)`, receiver minus donor"
      (fields `shifted_eq`, `adjacent_eq`): the shifted array is `m - e_a + e_b` and `adjacentDifference` is the eigenvalue difference, for every
      occupied donor;
  (E) "for fixed positive-action endpoints its target is `ω_{r,b}(u) - ω_{r,a}(u)`" (field `target_eq`):
      `Def033CoreR24m.target` of the
      selected `ω r u` equals `ω r u b - ω r u a` for positive-action `a`, `b`;
  (F) "Each limit specifies the original Born law and its convention on the missing-donor sector" (fields
      `missing_occupied`, `missing_empty`, `born_probability`, `born_singleton`, `limit_iff`): the original
      physical product Born measure `originalBorn` at particle number `N+1` is a probability measure with the
      singleton weights `bornLaw`; the total random variable `withMissing` equals the adjacent difference on the
      occupied-donor sector and the caller-specified `missing m` on the empty-donor sector; and the printed limit
      `DifferenceLimit` is exactly convergence in probability of `|withMissing - target|` under `originalBorn`.
      NO adjacent limit is asserted: the printed definition asserts none (terra_review r232).
The definitions (D)-(F) are exactly the objects of `Def033CoreR24m`, `Def033AdjacentR24m` and
`TerraMultiRound12Definitions` reviewed in terra_review r232.

DERIVATION: the flows and (C) are obtained from the frozen `Bind7BDEF033H01.DEF033_bound` (bf408159), i.e.
`Def033BindingR25m.DEF033_intermediate` with the shared input discharged by
`RB7BindFinal.hierarchyInputR25m_unconditional`; flow uniqueness and the staged orders come from the same
shared input through `Def033HierarchyR24m.all_order_commuting` (the flow of H01 is identified with its unique
flow); (A), (B)-Hamiltonian, (D), (E), (F) are the r232-reviewed definition lemmas.  No new hypothesis beyond `hκ`, `w`, `hw : PrintedChart hκ w`.  No acceptance claim; R-7B122087 is
held for the owner ruling on the DEF-024 predecessor gate.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter MeasureTheory Topology
namespace QuantumNLS.Bind7BDEF033H02
open QuantumNLS.ClassicalCharges QuantumNLS.HierarchyFlow
open QuantumNLS.Def033HierarchyR24m QuantumNLS.Def033CoreR24m
open QuantumNLS.BetheLabels QuantumNLS.BetheCoefficientTransform QuantumNLS.BetheSpectralCharges
open QuantumNLS.TerraMultiRound12Definitions QuantumNLS.Def024Order2Joint QuantumNLS.Def024LowEquivariance
variable {L κ : ℝ} [Fact (0 < L)]

/-- DEF-033, all printed clauses, as one structure over the printed chart `w` (clause map in the module header).
The data are the selected flows `flow` and the selected active frequencies `ω`; every other field is a
property of them. -/
structure DEF033Package (hκ : 0 < κ)
    (w : QuantumNLS.PhysicalTensor.L2T L → QuantumNLS.REF88Chart.K) : Type where
  /-- (A) the active-coordinate action is the squared modulus of the chart coordinate. -/
  action_modulus : ∀ (v : QuantumNLS.PhysicalTensor.L2T L) (n : ℤ),
    ‖w v n‖ ^ 2 = (QuantumNLS.RootIndexedMasses.masses hκ v).1 n
  /-- (B) the fixed smooth hierarchy: `flow r` is the time map of the flow of `I_{r+1}^{(κ)}`. -/
  flow : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ)
  isFlow : ∀ r, IsHamFlow L (hamiltonian L κ r) (flow r)
  /-- (B) the Hamiltonian is the real part of the physical Riccati charge, for every order. -/
  hamiltonian_physical : ∀ r (u : Smooth L),
    ((hamiltonian L κ r u.val : ℝ) : ℂ) = charge L κ u.val (r + 1)
  /-- (B) it is THE flow: any smooth Hamiltonian flow of the same Hamiltonian coincides with it. -/
  flow_unique : ∀ r, UniqueHamFlow L (hamiltonian L κ r) (flow r)
  flow_commute : ∀ r s, ∀ u : Smooth L, ∀ t τ, flow r t (flow s τ u.val) = flow s τ (flow r t u.val)
  /-- (B) order-0, order-1 and order-2 conventions: the staged flows of DEF-024. -/
  flow_staged : ∀ r, r ≤ 2 → ∀ u : Smooth L, ∀ t, flow r t u.val = flowMap2 L κ r t u.val
  /-- (C) the selected active frequency `ω r u n = ω_{r,n}(u)`. -/
  ω : ℕ → Smooth L → ℤ → ℝ
  /-- (C) `w_n(Φ_t^{(r)} u) = e^{-itω_{r,n}(u)} w_n(u)` when `a_n(u) > 0`. -/
  active : ∀ r (u : Smooth L) n, 0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 n →
    ActiveFrequency (fun t => w (physical ⟨flow r t u.val, ((isFlow r u.val u.property).2.2 t).1⟩) n)
      (w (physical u) n) (ω r u n)
  /-- (C) the real multiplier is unique. -/
  active_unique : ∀ r (u : Smooth L) n, 0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 n →
    ∀ freq : ℝ, ActiveFrequency
      (fun t => w (physical ⟨flow r t u.val, ((isFlow r u.val u.property).2.2 t).1⟩) n)
      (w (physical u) n) freq → freq = ω r u n
  /-- (D) the shifted array is `m - e_a + e_b` for an occupied donor `m_a ≥ 1`. -/
  shifted_eq : ∀ (N : ℕ) (a b : ℤ) (m : MArr N) (h : QuantumNLS.Occupation.DonorOK a (marrArr N m).1),
    (marrArr N (shifted a b m h)).1 =
      (marrArr N m).1 - QuantumNLS.Occupation.e a + QuantumNLS.Occupation.e b
  /-- (D) the adjacent quantum difference `Λ_{N,r}(m - e_a + e_b) - Λ_{N,r}(m)`, receiver minus donor. -/
  adjacent_eq : ∀ (N r : ℕ) (a b : ℤ) (m : MArr N) (h : QuantumNLS.Occupation.DonorOK a (marrArr N m).1),
    adjacentDifference L κ N r a b m h =
      eigenvalue L N (κ / N) r (shifted a b m h) - eigenvalue L N (κ / N) r m
  /-- (E) the target at positive-action endpoints is `ω_{r,b}(u) - ω_{r,a}(u)`. -/
  target_eq : ∀ r (u : Smooth L) (a b : ℤ),
    0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 a →
    0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 b →
    Def033CoreR24m.target (ω r u) a b = ω r u b - ω r u a
  /-- (F) missing-donor convention: the total variable is the adjacent difference on the occupied sector ... -/
  missing_occupied : ∀ (N r : ℕ) (a b : ℤ) (missing : MArr N → ℝ) (m : MArr N)
    (h : QuantumNLS.Occupation.DonorOK a (marrArr N m).1),
    withMissing L κ N r a b missing m = adjacentDifference L κ N r a b m h
  /-- (F) ... and the caller-specified value on the empty-donor sector. -/
  missing_empty : ∀ (N r : ℕ) (a b : ℤ) (missing : MArr N → ℝ) (m : MArr N),
    ¬ QuantumNLS.Occupation.DonorOK a (marrArr N m).1 → withMissing L κ N r a b missing m = missing m
  /-- (F) the original physical product Born law, at particle number `N+1`, is a probability measure ... -/
  born_probability : ∀ (u : Smooth L) (hu : ‖physical u‖ = 1) (N : ℕ),
    IsProbabilityMeasure (originalBorn hκ (physical u) hu N)
  /-- (F) ... with the Born-law singleton weights. -/
  born_singleton : ∀ (u : Smooth L) (hu : ‖physical u‖ = 1) (N : ℕ) (m : MArr (N + 1)),
    originalBorn hκ (physical u) hu N {m} =
      ENNReal.ofReal (bornLaw
        (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L (N + 1) (by omega) hκ)
        (physical u) m)
  /-- (F) each printed limit is convergence in probability of `|total - target|` under the ORIGINAL law,
  with an explicitly specified missing-donor value; no limit is asserted. -/
  limit_iff : ∀ (u : Smooth L) (hu : ‖physical u‖ = 1) (r : ℕ) (a b : ℤ) (ω' : ℤ → ℝ)
    (missing : ∀ N, MArr (N + 1) → ℝ),
    DifferenceLimit hκ (physical u) hu r a b ω' missing ↔
      ∀ ε : ℝ, 0 < ε → Tendsto (fun N => originalBorn hκ (physical u) hu N
        {m | ε < |withMissing L κ (N + 1) r a b (missing N) m - Def033CoreR24m.target ω' a b|})
        atTop (𝓝 0)

/-- DEF-033, all printed clauses.  Derived from the frozen `Bind7BDEF033H01.DEF033_bound`
(active-frequency existence and uniqueness), the all-order commuting/unique flows of the same shared
hierarchy input, and the r232-reviewed definition lemmas. -/
def DEF033_package (hκ : 0 < κ)
    (w : QuantumNLS.PhysicalTensor.L2T L → QuantumNLS.REF88Chart.K)
    (hw : QuantumNLS.REF88PrintedChart.PrintedChart hκ w) : DEF033Package hκ w :=
  have hFull := QuantumNLS.RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ w hw
    (QuantumNLS.Def033SobolevR25m.sobolev_homeomorphisms hκ w hw)
    (QuantumNLS.HierarchyInputR25m.scalar_uniqueness hκ)
    (QuantumNLS.HierarchyInputR25m.scalar_moments hκ)
  have hAll := all_order_commuting (L := L) hκ.le w _
    (QuantumNLS.HierarchyInputR25m.conclusion_to_r24 w _ hFull)
  have hH01 := QuantumNLS.Bind7BDEF033H01.DEF033_bound (L := L) hκ w hw
  let Ψ := Classical.choose hH01
  let hΨ := Classical.choose (Classical.choose_spec hH01)
  have hcomm := (Classical.choose_spec (Classical.choose_spec hH01)).1
  have hfreq := (Classical.choose_spec (Classical.choose_spec hH01)).2
  have hex : ∀ (r : ℕ) (u : Smooth L) (n : ℤ), ∃ ωv : ℝ,
      0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 n →
        ActiveFrequency
          (fun t => w (physical ⟨Ψ r t u.val, ((hΨ r u.val u.property).2.2 t).1⟩) n)
          (w (physical u) n) ωv ∧
        ∀ freq : ℝ, ActiveFrequency
          (fun t => w (physical ⟨Ψ r t u.val, ((hΨ r u.val u.property).2.2 t).1⟩) n)
          (w (physical u) n) freq → freq = ωv := by
    intro r u n
    by_cases hpos : 0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 n
    · obtain ⟨ωv, hωv, huniq⟩ := hfreq r u n hpos
      exact ⟨ωv, fun _ => ⟨hωv, huniq⟩⟩
    · exact ⟨0, fun h => absurd h hpos⟩
  have hΨ'eq : ∀ (Ψ' : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ)),
      (∀ r, UniqueHamFlow L (hamiltonian L κ r) (Ψ' r)) →
      ∀ r (u : ℝ → ℂ), SmoothPeriodic L u → ∀ s, Ψ r s u = Ψ' r s u :=
    fun Ψ' hu r u hsm s => hu r (Ψ r) (hΨ r) u hsm s
  { action_modulus := hw.moduli
    flow := Ψ
    isFlow := hΨ
    hamiltonian_physical := fun r u =>
      QuantumNLS.Def033AdjacentR24m.hamiltonian_is_physical hκ u.property r
    flow_unique := fun r Θ hΘ u hu s => by
      obtain ⟨Ψ', _, huΨ', -⟩ := hAll
      exact (huΨ' r Θ hΘ u hu s).trans (hΨ'eq Ψ' huΨ' r u hu s).symm
    flow_commute := hcomm
    flow_staged := fun r hr u t => by
      obtain ⟨Ψ', _, huΨ', _, hlow⟩ := hAll
      exact (hΨ'eq Ψ' huΨ' r u.val u.property t).trans (hlow r hr u t)
    ω := fun r u n => Classical.choose (hex r u n)
    active := fun r u n hn => (Classical.choose_spec (hex r u n) hn).1
    active_unique := fun r u n hn => (Classical.choose_spec (hex r u n) hn).2
    shifted_eq := fun N a b m h => by
      simp only [shifted, Equiv.apply_symm_apply]
      rfl
    adjacent_eq := fun N r a b m h => rfl
    target_eq := fun r u a b _ _ => rfl
    missing_occupied := fun N r a b missing m h =>
      extendedDifference_occupied L κ N r a b missing m h
    missing_empty := fun N r a b missing m h =>
      extendedDifference_missing L κ N r a b missing m h
    born_probability := fun u hu N => inferInstance
    born_singleton := fun u hu N m => originalBorn_singleton hκ (physical u) hu N m
    limit_iff := fun u hu r a b ω' missing => Iff.rfl }

open Lean Meta in
/-- The package statement mentions every reviewed definition of the printed clauses. -/
private def mentionsAll (n : Name) (required : List Name) : MetaM (List Name) := do
  let env ← getEnv
  let some ci := env.find? n | throwError "missing {n}"
  let used := ci.type.getUsedConstants
  return required.filter fun c => !used.contains c

open Lean Meta in
/-- Transitive closure of a root constant: held names and non-standard axioms are rejected. -/
private def transitiveAudit (root : Name) : MetaM (Nat × Nat) := do
  let env ← getEnv
  let mut pending : Array Name := #[root]
  let mut seen : Std.HashSet Name := {}
  let mut axioms : Nat := 0
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 || (n.toString.splitOn "RegularCut").length > 1 then
        throwError "held identifier in closure: {n}"
      let some ci := env.find? n | throwError "missing constant {n}"
      match ci with
      | .axiomInfo _ =>
        unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
          throwError "nonstandard axiom in closure: {n}"
        axioms := axioms + 1
      | _ => pure ()
      pending := pending ++ ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then
        pending := pending ++ v.getUsedConstants
  return (seen.size, axioms)

end QuantumNLS.Bind7BDEF033H02

set_option maxHeartbeats 16000000 in
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let newN := ``QuantumNLS.Bind7BDEF033H02.DEF033_package
  let missing ← QuantumNLS.Bind7BDEF033H02.mentionsAll ``QuantumNLS.Bind7BDEF033H02.DEF033Package.mk
    [``QuantumNLS.Def033CoreR24m.ActiveFrequency, ``QuantumNLS.Def033CoreR24m.target,
     ``QuantumNLS.Def033CoreR24m.withMissing, ``QuantumNLS.Def033CoreR24m.originalBorn,
     ``QuantumNLS.Def033CoreR24m.DifferenceLimit,
     ``QuantumNLS.TerraMultiRound12Definitions.adjacentDifference,
     ``QuantumNLS.TerraMultiRound12Definitions.shifted,
     ``QuantumNLS.HierarchyFlow.hamiltonian, ``QuantumNLS.HierarchyFlow.IsHamFlow,
     ``QuantumNLS.ClassicalCharges.charge, ``QuantumNLS.BetheSpectralCharges.eigenvalue,
     ``QuantumNLS.RootIndexedMasses.masses]
  unless missing.isEmpty do throwError "package statement does not mention: {missing}"
  let missing2 ← QuantumNLS.Bind7BDEF033H02.mentionsAll newN
    [``QuantumNLS.REF88PrintedChart.PrintedChart, ``QuantumNLS.Bind7BDEF033H02.DEF033Package]
  unless missing2.isEmpty do throwError "DEF033_package type does not mention: {missing2}"
  let (nConst, nAx) ← QuantumNLS.Bind7BDEF033H02.transitiveAudit newN
  logInfo m!"Bind7BDEF033H02 PASS: statement mentions all reviewed printed-clause definitions; closure {nConst} constants, {nAx} standard axioms, no held identifiers."

#print axioms QuantumNLS.Bind7BDEF033H02.DEF033_package

end
