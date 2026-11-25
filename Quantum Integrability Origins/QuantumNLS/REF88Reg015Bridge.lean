import Mathlib
import QuantumNLS.REF88Reg015Input
import QuantumNLS.Reg015HFinal
import QuantumNLS.Reg015Setting

/-!
# REF88Reg015Bridge: `Reg015Input` from the conditional final `REG015_final` (haiku_inventory)

Bridge theorem `reg015Input_of_final (hκ : 0 < κ) : QuantumNLS.REF88Reg015.Reg015Input L κ hκ`,
derived from `QuantumNLS.Reg015HFinal.REG015_final`, with no extra hypothesis.

Clause correspondence (named input `Reg015Input` of `REF88Reg015Input`, versus `REG015_final`):
* (a) `MemHsLp L s u ↔ Integrable` and `Integrable ↔ Summable (sobolevWeight L s n * I_n u)`:
  from clause 1 of `REG015_final`, through `(∃ v : H02 L s, v.val = u) ↔ MemHsLp L s u`
  (`WField.summable`, `WField.mk`) and the definitional identity
  `sobolevWeight L s n = (1 + |momentum L n|)^(2s)`.
* (b) ε-δ continuity of `u ↦ (w_n I_n u)` in weighted `ℓ¹`: from `Continuous A` in `ℓ¹`, using
  `dist = ‖·‖`, `‖a‖ = ∑' |a n|` (`Reg015Setting.lp_one_norm`) and `|w_n (x_n - y_n)| = w_n |x_n - y_n|`.
* (c) bounded sets to bounded sums: from `IsBounded (A '' B)` (`isBounded_iff_forall_norm_le`) and
  `∑' |A u n| = ∑' w_n I_n u` (weights and masses nonnegative).
* (d) homeomorphism clause: take `V := Set.range Φ` and `e0 : L2T L ≃ₜ V` the embedding as a
  homeomorphism onto its range.  Its `ExactModuli` is exactly the hypothesis `‖Φ u n‖² = I_n u`.
  `Target V s hs = {z // toBase z ∈ range Φ}` is identified with `{w // ∃ u, Φ u = toK hs w}` by
  `toBase = toK` coordinatewise (`toBase_apply`, `toK_apply`) and `Homeomorph.ofEqSubtypes`.

Status: a Lean theorem with no hypotheses other than `hκ`.  Its scientific status is exactly that of
`REG015_final` (conditional on the REG-010, REG-011 and REG-013 chain, pending review; no acceptance of
REG-015 is claimed).  No sorry, admit, native_decide, or custom axiom.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ENNReal Topology
open MeasureTheory Filter

namespace QuantumNLS.REF88Reg015Bridge

open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight QuantumNLS.Fourier
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.REF88Chart (K)
open QuantumNLS.REF88Reg015 (toK toK_apply Reg015Input)
open QuantumNLS.Reg015Setting (lp_one_norm masses_nonneg ExactModuli toBase toBase_apply Target)

variable {L κ : ℝ} [Fact (0 < L)]

/-- `ℓ¹`-summability of the absolute coordinates of an `ℓ¹` element. -/
theorem summable_abs_lp_one (a : lp (fun _ : ℤ => ℝ) 1) : Summable (fun n : ℤ => |a n|) := by
  have h := lp.hasSum_norm (p := (1 : ENNReal)) (by simp) a
  simp only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] at h
  exact h.summable

/-- Membership bridge: the `H^s` field space is exactly `MemHsLp` at the `L²` level. -/
theorem exists_H02_iff_memHsLp (s : ℝ) (u : L2T L) :
    (∃ v : H02 L s, v.val = u) ↔ MemHsLp L s u := by
  constructor
  · rintro ⟨v, rfl⟩
    exact WField.summable v
  · intro h
    exact ⟨WField.mk u h, rfl⟩

/-- **Named input from the conditional final.**  `REF88Reg015Input.Reg015Input` follows from
`Reg015HFinal.REG015_final` for every `κ` with `0 < κ`. -/
theorem reg015Input_of_final (hκ : 0 < κ) : Reg015Input L κ hκ := by
  intro s hs
  obtain ⟨hA, ⟨A, hAdef, hAcont, hAbdd⟩, hD⟩ :=
    QuantumNLS.Reg015HFinal.REG015_final (L := L) hκ s hs
  -- the weighted coordinates of the action map, in the `sobolevWeight` form
  have hAn : ∀ (x : H02 L s) (n : ℤ),
      A x n = sobolevWeight L s n * (QuantumNLS.RootIndexedMasses.masses hκ x.val).1 n :=
    fun x n => hAdef x n
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- clause (a): the printed three-way characterization on all of `L²`
    intro u
    exact ⟨(exists_H02_iff_memHsLp (L := L) s u).symm.trans (hA u).1, (hA u).2⟩
  · -- clause (b): ε-δ continuity into weighted `ℓ¹`, from continuity of `A` into `ℓ¹`
    intro u₀ ε hε
    obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.1 hAcont u₀ ε hε
    refine ⟨δ, hδ, fun u hu => ?_⟩
    have hdist : dist (A u) (A u₀) < ε := hball u (by rwa [dist_eq_norm])
    have hterm : ∀ n : ℤ, |(A u - A u₀) n| =
        sobolevWeight L s n * |(QuantumNLS.RootIndexedMasses.masses hκ (H02.toL2 hs u)).1 n -
          (QuantumNLS.RootIndexedMasses.masses hκ (H02.toL2 hs u₀)).1 n| := by
      intro n
      rw [lp.coeFn_sub, Pi.sub_apply, hAn u n, hAn u₀ n, ← mul_sub, abs_mul,
        abs_of_nonneg (sobolevWeight_pos L s n).le]
      rfl
    have hsum : Summable (fun n : ℤ => sobolevWeight L s n *
        |(QuantumNLS.RootIndexedMasses.masses hκ (H02.toL2 hs u)).1 n -
          (QuantumNLS.RootIndexedMasses.masses hκ (H02.toL2 hs u₀)).1 n|) :=
      (summable_abs_lp_one (A u - A u₀)).congr hterm
    have htsum : ∑' n : ℤ, sobolevWeight L s n *
        |(QuantumNLS.RootIndexedMasses.masses hκ (H02.toL2 hs u)).1 n -
          (QuantumNLS.RootIndexedMasses.masses hκ (H02.toL2 hs u₀)).1 n| =
        ∑' n : ℤ, |(A u - A u₀) n| :=
      tsum_congr fun n => (hterm n).symm
    refine ⟨hsum, htsum.trans_lt ?_⟩
    rw [← lp_one_norm]
    rw [dist_eq_norm] at hdist
    exact hdist
  · -- clause (c): bounded sets go to bounded weighted sums
    intro B hB
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (hAbdd B hB)
    refine ⟨C, fun u hu => ?_⟩
    have h1 : ∑' n : ℤ, |A u n| ≤ C := by
      have := hC (A u) ⟨u, hu, rfl⟩
      rwa [lp_one_norm] at this
    refine (tsum_congr fun n => ?_).trans_le h1
    rw [hAn u n, abs_of_nonneg (mul_nonneg (sobolevWeight_pos L s n).le
      (masses_nonneg hκ u.val n))]
    rfl
  · -- clause (d): the conditional homeomorphism, with `V := range Φ`
    intro Φ hΦ hmod
    let e0 : L2T L ≃ₜ Set.range Φ := hΦ.toHomeomorph
    have hE : ExactModuli (κ := κ) e0 hκ := fun u n => hmod u n
    obtain ⟨F, hF⟩ := hD (Set.range Φ) e0 hE
    have hbk : ∀ z : h02 L s, toBase s hs z = toK hs z := fun z =>
      lp.ext (funext fun n => by rw [toBase_apply, toK_apply])
    have hpq : (fun z : h02 L s => toBase s hs z ∈ Set.range Φ) =
        (fun z : h02 L s => ∃ u : L2T L, Φ u = toK hs z) :=
      funext fun z => propext (show toBase s hs z ∈ Set.range Φ ↔
          ∃ u : L2T L, Φ u = toK hs z from by rw [hbk z]; exact Set.mem_range)
    let eS : Target (L := L) (Set.range Φ) s hs ≃ₜ
        {w : h02 L s // ∃ u : L2T L, Φ u = toK hs w} :=
      Homeomorph.ofEqSubtypes hpq
    refine ⟨F.trans eS, fun u => ?_⟩
    apply lp.ext
    funext n
    rw [toK_apply]
    exact hF u n

#print axioms summable_abs_lp_one
#print axioms exists_H02_iff_memHsLp
#print axioms reg015Input_of_final

end QuantumNLS.REF88Reg015Bridge

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.REF88Reg015Bridge." ||
        n.toString.startsWith "_private.QuantumNLS.REF88Reg015Bridge." then
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
  Lean.logInfo m!"REF88Reg015Bridge aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
