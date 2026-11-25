import QuantumNLS.Reg015Setting

/-! REG-015 (`CC:all-fractional:theorem`, `all_orders.tex:110`), pre-start assembly.

Proof of the printed theorem, following the printed proof:
* `0 ≤ s ≤ 2`: REG-010 and REG-011 (named inputs);
* every integer `r = k+1 ≥ 3`: REG-013 (named input) applied at `k = r-1 ≥ 2`, whose two
  assertions are discharged by the ACCEPTED REG-004 (`integer_assertion`) and the ACCEPTED
  REG-014 (`finiteY_assertion`), and whose conditional bounded-set clause is discharged by
  the REG-004 polynomial bound (`R_bounded`) and root-label confinement (`lower_moments_bounded`);
* induction over `k` (`orders_through`) and the final ceiling step (`REG015Input`).

No sorry, no axiom; the three unaccepted predecessors appear only as the explicit hypotheses
`reg010`, `reg011`, `reg013` of the INTERMEDIATE theorem `REG015Input`. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.Fourier
open QuantumNLS.RootWeightedCellsR26 QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound64ExtendedMeasure QuantumNLS.TerraMultiRound59RCompatibility
open QuantumNLS.Reg015Setting
namespace QuantumNLS.Reg015Assembly
variable {L κ : ℝ} [Fact (0 < L)]

/-- The accepted REG-004 supplies REG-013's first assertion at every `k ≥ 2`, with the
continuous polynomial correction `R = R_{k+1}` on `H^k`. -/
theorem integer_assertion (hκ : 0 < κ) (k : ℕ) (hk : 2 ≤ k) :
    IntegerAssertion (L := L) hκ k (Rfield (L := L) (k+1) (by omega) κ) := by
  have h4 := QuantumNLS.TerraMultiRound64REG004.REG004 L κ hκ
  refine ⟨fun u => ?_, (h4.2.1 (k+1) (by omega)).2, fun v => h4.2.2.2.1 (k+1) (by omega) v⟩
  have hpos : (0:ℝ) < ((k+1:ℕ):ℝ) := Nat.cast_pos.mpr (Nat.succ_pos k)
  exact ((QuantumNLS.Reg010LowFreeSobolev.free_power_integrable_iff_H02 u _ hpos).symm.trans
    (QuantumNLS.Reg010LowFreeSobolev.free_power_integrable_iff_hsq u _ hpos)).trans
    ((h4.1 (k+1) (by omega) u).1)

/-- The accepted REG-014 at `r = k+1` supplies REG-013's second assertion exactly. -/
theorem finiteY_assertion (hκ : 0 < κ) (k : ℕ) (hk : 2 ≤ k) :
    FiniteYAssertion (L := L) hκ k :=
  ⟨(QuantumNLS.Reg014Main.REG014 L κ hκ (k+1) (by omega)).2.1,
    (QuantumNLS.Reg014Main.REG014 L κ hκ (k+1) (by omega)).2.2⟩

/-- The REG-004 correction is a continuous real polynomial, hence bounded on bounded sets. -/
theorem R_bounded (hκ : 0 < κ) (k : ℕ) (hk : 2 ≤ k) (B : Set (Hk L k))
    (hB : Bornology.IsBounded B) :
    ∃ C : ℝ, ∀ u ∈ B, |Rfield (L := L) (k+1) (by omega) κ u| ≤ C := by
  obtain ⟨U, hU⟩ := isBounded_iff_forall_norm_le.mp hB
  obtain ⟨C, hC⟩ := QuantumNLS.Reg014Moments.RealPolynomial_bounded
    ((QuantumNLS.TerraMultiRound64REG004.REG004 L κ hκ).2.1 (k+1) (by omega)).1 U
  exact ⟨C, fun u hu => hC u (hU u hu)⟩

/-- Bounded weighted actions bound the lower moment on bounded Sobolev sets: root-label
confinement with the displacement `D(u) = 2√(κ m/L)`, `m ≤ ‖u‖²_{H^s}`. -/
theorem lower_moments_bounded (hκ : 0 < κ) (s : ℝ) (hs : 0 ≤ s)
    (hchar : MomentChar (L := L) hκ s) (hbdd : BoundedActions (L := L) hκ s)
    (B : Set (H02 L s)) (hB : Bornology.IsBounded B) :
    ∃ C : ℝ, ∀ u ∈ B,
      (∫ t : ℝ, |t|^(2*s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) ≤ C := by
  obtain ⟨A, hA, hAB⟩ := hbdd
  obtain ⟨K, hK⟩ := isBounded_iff_forall_norm_le.mp hB
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp (hAB B hB)
  have hL : 0 < L := Fact.out
  refine ⟨(1 + 2 * Real.sqrt (κ * K^2 / L))^(2*s) * M, fun u hu => ?_⟩
  have hint := ((hchar u.val).1).mp ⟨u, rfl⟩
  have hsum := ((hchar u.val).2).mp hint
  have h1 := moment_le_actions hκ u.val s hs hint hsum
  have hn : ‖u.val‖ ≤ K := (WField.norm_val_le (one_le_def002 L hs) u).trans (hK u hu)
  have hsq : κ * ‖u.val‖^2 / L ≤ κ * K^2 / L := by
    apply div_le_div_of_nonneg_right _ hL.le
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) hκ.le
  have hD : (1 + 2 * Real.sqrt (κ * ‖u.val‖^2 / L))^(2*s) ≤
      (1 + 2 * Real.sqrt (κ * K^2 / L))^(2*s) := by
    apply Real.rpow_le_rpow (by positivity) _ (by linarith)
    linarith [Real.sqrt_le_sqrt hsq]
  have hS : (∑' n : ℤ, (1+|momentum L n|)^(2*s) *
      (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n) ≤ M := by
    rw [← actions_norm hκ s A hA u]
    exact hM _ ⟨u, hu, rfl⟩
  have hS0 : 0 ≤ ∑' n : ℤ, (1+|momentum L n|)^(2*s) *
      (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n :=
    tsum_nonneg (fun n => mul_nonneg (by positivity) (masses_nonneg hκ u.val n))
  exact h1.trans (mul_le_mul hD hS hS0 (Real.rpow_nonneg (by positivity) _))

/-- Orders `0 ≤ s ≤ 2`: REG-010 and REG-011. -/
theorem base_orders (hκ : 0 < κ) (reg010 : Reg010LowOrdersInput (L := L) hκ)
    (reg011 : Reg011HomeomorphismInput (L := L) hκ) (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) :
    OrderStatement (L := L) hκ s ∧ BoundedActions (L := L) hκ s := by
  obtain ⟨hchar, A, hA, hcont, hbdd⟩ := reg010 s hs0 hs2
  exact ⟨⟨hchar, ⟨A, hA, hcont⟩, fun hs0' V e he => reg011 V e he s hs0' hs2⟩, ⟨A, hA, hbdd⟩⟩

/-- Induction over the integer orders: through every order `k ≥ 2`, all clauses hold,
including bounded-set preservation. -/
theorem orders_through (hκ : 0 < κ) (reg010 : Reg010LowOrdersInput (L := L) hκ)
    (reg011 : Reg011HomeomorphismInput (L := L) hκ) (reg013 : Reg013InductionInput (L := L) hκ) :
    ∀ k : ℕ, 2 ≤ k → ∀ s : ℝ, 0 ≤ s → s ≤ k →
      OrderStatement (L := L) hκ s ∧ BoundedActions (L := L) hκ s := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro s hs0 hs2
    exact base_orders hκ reg010 reg011 s hs0 (by exact_mod_cast hs2)
  | succ k hk ih =>
    intro s hs0 hsk
    obtain ⟨hnew, hbnew⟩ := reg013 k hk (fun s h0 h1 => (ih s h0 h1).1)
      (Rfield (L := L) (k+1) (by omega) κ) (integer_assertion hκ k hk) (finiteY_assertion hκ k hk)
    have hLB : LowerBounded (L := L) hκ k (Rfield (L := L) (k+1) (by omega) κ) :=
      ⟨fun s h0 h1 B hB => lower_moments_bounded hκ s h0 (ih s h0 h1).1.1 (ih s h0 h1).2 B hB,
        fun B hB => R_bounded hκ k hk B hB⟩
    by_cases hle : s ≤ (k:ℝ)
    · exact ih s hs0 hle
    · have hlt : (k:ℝ) < s := not_le.mp hle
      have hs' : s ≤ (k:ℝ) + 1 := by
        have h := hsk
        push_cast at h
        exact h
      exact ⟨hnew s hlt hs', hbnew hLB s hlt hs'⟩

/-- **REG-015, INTERMEDIATE form.** For every real `s ≥ 0`: the printed three-way
characterization on all of `L²`; the indexed action map is continuous from `H^s` into the
weighted `ℓ¹` space (realized isometrically in `ℓ¹` by its weighted coordinates) and sends
bounded sets to bounded sets; and for every homeomorphism `Φ : L² → V ⊂ ℓ²` onto its image
with `|Φ_n(u)|² = I_n(u)`, its restriction is a homeomorphism `H^s → V ∩ h^s` (subspace
`h^s` topology; no claim `V = ℓ²`).

The ONLY unaccepted inputs are the explicit hypotheses `reg010` (REG-010), `reg011`
(REG-011), `reg013` (REG-013), each the exact printed statement. REG-004 and REG-014 are
the accepted theorems themselves. The final theorem will replace the three hypotheses by
the accepted predecessor theorems. -/
theorem REG015Input (hκ : 0 < κ) (reg010 : Reg010LowOrdersInput (L := L) hκ)
    (reg011 : Reg011HomeomorphismInput (L := L) hκ) (reg013 : Reg013InductionInput (L := L) hκ) :
    ∀ s : ℝ, ∀ hs0 : 0 ≤ s,
      (∀ u : L2T L,
        ((∃ v : H02 L s, v.val = u) ↔
          Integrable (fun t : ℝ => (1+|t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) ∧
        (Integrable (fun t : ℝ => (1+|t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ↔
          Summable (fun n : ℤ => (1+|momentum L n|)^(2*s) *
            (QuantumNLS.RootIndexedMasses.masses hκ u).1 n))) ∧
      (∃ A : H02 L s → lp (fun _ : ℤ => ℝ) 1,
        (∀ u n, A u n = (1+|momentum L n|)^(2*s) *
          (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n) ∧
        Continuous A ∧
        ∀ B : Set (H02 L s), Bornology.IsBounded B → Bornology.IsBounded (A '' B)) ∧
      (∀ (V : Set Seq) (e : L2T L ≃ₜ V), ExactModuli e hκ →
        ∃ F : H02 L s ≃ₜ Target (L := L) V s hs0, ∀ u n, (F u).val.val n = (e u.val).val n) := by
  intro s hs0
  have hceil : s ≤ ((max 2 ⌈s⌉₊ : ℕ) : ℝ) := by
    have h1 := Nat.le_ceil s
    have h2 : ((⌈s⌉₊ : ℕ) : ℝ) ≤ ((max 2 ⌈s⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast le_max_right 2 ⌈s⌉₊
    linarith
  obtain ⟨⟨hchar, ⟨A, hA, hcont⟩, hhomeo⟩, ⟨A', hA', hbdd⟩⟩ :=
    orders_through hκ reg010 reg011 reg013 (max 2 ⌈s⌉₊) (le_max_left _ _) s hs0 hceil
  have hAA : A' = A := carrier_unique hκ s A' A hA' hA
  subst hAA
  exact ⟨hchar, ⟨A', hA, hcont, hbdd⟩, hhomeo hs0⟩

#print axioms integer_assertion
#print axioms finiteY_assertion
#print axioms R_bounded
#print axioms lower_moments_bounded
#print axioms base_orders
#print axioms orders_through
#print axioms REG015Input
end QuantumNLS.Reg015Assembly

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg015Assembly." ||
        n.toString.startsWith "_private.QuantumNLS.Reg015Assembly." ||
        n.toString.startsWith "QuantumNLS.Reg015Setting." ||
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
  Lean.logInfo m!"Reg015 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
