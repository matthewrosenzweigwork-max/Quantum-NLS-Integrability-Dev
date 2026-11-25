import QuantumNLS.Prop024WIdent
import QuantumNLS.Prop021RemainderInputR131

/-! PROP-024 final assembly, module H1 (haiku_inventory; prefix Prop024FinalH).

Printed source: `source-text/chapters/propagation/fluctuations.tex`, `Q7B:lem:remainder`
(lines 247-316).  Its standing setting is lines 14-60 (`Q7B:eq:kernel`: `M >= 1`, `A > 0`,
`B_m` bounded self-adjoint with `‖B_m‖ <= M A^m/√((2m)!)`; `Q7B:eq:manybody`: the maximal
direct-sum Hamiltonian `H_N`).  Its input is the two displayed estimates of `Q7B:eq:mgf`
(lines 195-200), and the constant is `C'_A = 2 S_B B^3 (32e)^{3/2}` with `B = √(2A)` and
`S_B = Σ_{l>=0} B^l/√(l!)` (proof, lines 262-275).

This module states the printed lemma as the Lean Prop `PrintedRemainder` and proves it.
Nothing here uses PROP-022, the flow bound `Q7B:eq:P`, or any R58 scaffold input.  The proof
is the frozen Prop024WIdent/Prop024WStepOne/Prop024WRemainder chain, with the constant
written in the printed form.  `PrintedRemainderPoly` is the same statement with the
exponential clause of `Q7B:eq:mgf` dropped (the printed domain and norm arguments use only
its polynomial clause); it is strictly stronger, and `printed_remainder` follows from it. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace ComplexConjugate Topology

namespace QuantumNLS.Prop024FinalH1

open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors Ext006PhysFockCoord
open Prop024WWeylPhysical Prop024WBlock Prop024WOrder Prop024WNorms Prop024WSeries Prop024WStepOne
open Prop024WConstant Prop024WLinear Prop024WQuadratic Prop024WRemainder
open Prop024ContractionsR54 Prop024PhysicalHamiltonianR54 Prop022FactorialCoefficientsR115
open Prop024HilbertConjugationR58 Prop022ClassicalTimeR116 Prop022StrongOperatorR125 Ext005Moments
open Ext006ModeDomainR33a
variable {L : ℝ} [Fact (0 < L)]

/-- The printed constant `C'_A` of `Q7B:eq:rembound`: `B = √(2A)`, `S_B = Σ_{l>=0} B^l/√(l!)`,
`C'_A = 2 S_B B^3 (32e)^{3/2}` (fluctuations.tex:262-275). -/
def printedConstant (A : ℝ) : ℝ :=
  2 * Prop024ScalarSeriesR52.factorialRootSeries (Real.sqrt (2 * A)) * (Real.sqrt (2 * A)) ^ 3 *
    (32 * Real.exp 1) ^ ((3 : ℝ) / 2)

lemma printedConstant_nonneg (A : ℝ) : 0 ≤ printedConstant A := by
  unfold printedConstant
  have hB0 : 0 ≤ Real.sqrt (2 * A) := Real.sqrt_nonneg _
  have hS := Prop024ScalarSeriesR52.factorialRootSeries_nonneg hB0
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hS) (pow_nonneg hB0 3))
    (Real.rpow_nonneg (by positivity) _)

lemma sqrt_cube_eq_rpow' (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x) ^ 3 = x ^ ((3 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- **Q7B:lem:remainder, the printed statement** (fluctuations.tex:247-316), written out.

Hypotheses, all printed: `A > 0`; `M >= 1` and `B_m` self-adjoint with `‖B_m‖ <= M A^m/√((2m)!)`
for `m >= 1` (`FactorialBound`, `Q7B:eq:kernel`); `N` natural with `256 e A Q <= N`, `Q >= 1`
(the parameter of `Q7B:eq:mgf`); `u` unit; `ξ` satisfies both displayed estimates of
`Q7B:eq:mgf` (`NumberMoments Q ξ`).

Conclusion: `W(√N u) ξ ∈ D(H_N)` (`H_N = Prop021ManyBodyR129.hamiltonian B N`, which is the
printed `Q7B:eq:manybody` by `Prop021RemainderInputR131.interaction_eq_hamiltonian`); and the
conjugation identity `H_N W(√N u) ξ = W(√N u)(lowOrders ξ + R)` holds in Hilbert norm for a vector
`R = R_N(u) ξ`, where `lowOrders` is `N F(u) ξ + √N{a*(∇F(u)) + a(∇F(u))}ξ + 𝕢(u)ξ` (fluctuations.tex
274-276).  Equivalently `W(√N u)^{-1} H_N W(√N u) ξ = lowOrders ξ + R` by unitarity of `W`.  Finally
`‖R_N(u) ξ‖ <= C'_A M N^{-1/2} Q^{3/2}` with `C'_A = printedConstant A`. -/
def PrintedRemainder : Prop :=
  ∀ (A : ℝ), 0 < A →
  ∀ (B : ∀ m, HN L m →L[ℂ] HN L m) (M : ℝ), 1 ≤ M → FactorialBound B M A →
  (∀ m, (B m).adjoint = B m) →
  ∀ (N : ℕ) (Q : ℝ), 1 ≤ Q → 256 * Real.exp 1 * A * Q ≤ N →
  ∀ u : L2T L, ‖u‖ = 1 → ∀ x : Fock L, Prop021RemainderInputR131.NumberMoments Q x →
    ∃ (hx : Smooth (Ext006PhysicalVacuum.coefficient x))
      (h₂ : x ∈ momentDomain (L := L) 2)
      (hd : Prop022OVacuum.printedWeyl ((Real.sqrt N : ℂ) • u) x ∈
        (Prop021ManyBodyR129.hamiltonian B N).domain) (R : Fock L),
      Prop021ManyBodyR129.hamiltonian B N ⟨Prop022OVacuum.printedWeyl ((Real.sqrt N : ℂ) • u) x, hd⟩ =
        Prop022OVacuum.printedWeyl ((Real.sqrt N : ℂ) • u)
          (Prop021RemainderInputR131.lowOrders B N u x hx h₂ + R) ∧
      ‖R‖ ≤ printedConstant A * M * (N : ℝ) ^ (-(1/2 : ℝ)) * Q ^ (3/2 : ℝ)

/-- The printed statement with the exponential clause of `Q7B:eq:mgf` removed: the hypothesis is
only the polynomial clause `PolyMoments Q ξ`.  The printed proof uses only this clause. -/
def PrintedRemainderPoly : Prop :=
  ∀ (A : ℝ), 0 < A →
  ∀ (B : ∀ m, HN L m →L[ℂ] HN L m) (M : ℝ), 1 ≤ M → FactorialBound B M A →
  (∀ m, (B m).adjoint = B m) →
  ∀ (N : ℕ) (Q : ℝ), 1 ≤ Q → 256 * Real.exp 1 * A * Q ≤ N →
  ∀ u : L2T L, ‖u‖ = 1 → ∀ x : Fock L, PolyMoments Q x →
    ∃ (hx : Smooth (Ext006PhysicalVacuum.coefficient x))
      (h₂ : x ∈ momentDomain (L := L) 2)
      (hd : Prop022OVacuum.printedWeyl ((Real.sqrt N : ℂ) • u) x ∈
        (Prop021ManyBodyR129.hamiltonian B N).domain) (R : Fock L),
      Prop021ManyBodyR129.hamiltonian B N ⟨Prop022OVacuum.printedWeyl ((Real.sqrt N : ℂ) • u) x, hd⟩ =
        Prop022OVacuum.printedWeyl ((Real.sqrt N : ℂ) • u)
          (Prop021RemainderInputR131.lowOrders B N u x hx h₂ + R) ∧
      ‖R‖ ≤ printedConstant A * M * (N : ℝ) ^ (-(1/2 : ℝ)) * Q ^ (3/2 : ℝ)

/-- The polynomial-only statement, proved from the frozen Round-249/Round-58 Wick chain. -/
theorem printed_remainder_poly : PrintedRemainderPoly (L := L) := by
  intro A hA B M hM hB hsB N Q hQ hNQ u hu x hpoly
  have hQ0 : 0 ≤ Q := by linarith
  have hNpos : 0 < N := by
    have h0 : (0 : ℝ) < 256 * Real.exp 1 * A * Q :=
      mul_pos (mul_pos (mul_pos (by norm_num) (Real.exp_pos 1)) hA) (by linarith)
    exact_mod_cast h0.trans_le hNQ
  have hsm : x ∈ physSmooth L := mem_physSmooth_of_polyMoments Q x hpoly
  obtain ⟨hx', h₂, hz, hid⟩ :=
    Prop024WIdent.stepOne_lowOrders N hNpos B hsB M A Q (by linarith) hA hQ hNQ hB u hu hsm hpoly
  have heq := Prop021RemainderInputR131.interaction_eq_hamiltonian B N
  have hW : physicalWeyl N u x = Prop022OVacuum.printedWeyl ((Real.sqrt (N : ℝ) : ℂ) • u) x :=
    Prop024WeylConventionR55.physicalWeyl_eq_printedWeyl N u x
  have hd : Prop022OVacuum.printedWeyl ((Real.sqrt (N : ℝ) : ℂ) • u) x ∈
      (Prop021ManyBodyR129.hamiltonian B N).domain := by
    rw [← heq, ← hW]; exact hz
  refine ⟨hx', h₂, hd, remVec N B u x, ?_, ?_⟩
  · have h1 : Prop021ManyBodyR129.hamiltonian B N
        ⟨Prop022OVacuum.printedWeyl ((Real.sqrt (N : ℝ) : ℂ) • u) x, hd⟩ =
        interaction N B ⟨physicalWeyl N u x, hz⟩ :=
      Prop024WIdent.pmap_apply_congr _ _ heq.symm _ _ hW.symm hd hz
    rw [h1, interaction_eq_physicalWeyl_pulled, hid]
    exact Prop024WeylConventionR55.physicalWeyl_eq_printedWeyl N u _
  · have hbd := norm_remVec_le N hNpos B M A Q (by linarith) hA hQ hNQ hB u hu ⟨x, hsm⟩ hpoly
    have hbd' : ‖remVec N B u x‖ ≤ 2 * Prop024ScalarSeriesR52.factorialRootSeries (Real.sqrt (2 * A)) *
        (Real.sqrt (2 * A)) ^ 3 * (Real.sqrt (32 * Real.exp 1)) ^ 3 * M * (Real.sqrt Q) ^ 3 /
          Real.sqrt (N : ℝ) := hbd
    have hc : (32 * Real.exp 1) ^ ((3 : ℝ) / 2) = (Real.sqrt (32 * Real.exp 1)) ^ 3 :=
      (sqrt_cube_eq_rpow' _ (by positivity)).symm
    unfold printedConstant
    rw [hc]
    refine hbd'.trans (le_of_eq ?_)
    rw [Prop024WIdent.sqrt_cube_eq Q hQ0, div_eq_mul_inv,
      Prop024WIdent.inv_sqrt_eq (N : ℝ) (Nat.cast_nonneg N)]
    ring

/-- **Q7B:lem:remainder, exact printed statement** (the NumberMoments form of `Q7B:eq:mgf`). -/
theorem printed_remainder : PrintedRemainder (L := L) := by
  intro A hA B M hM hB hsB N Q hQ hNQ u hu x hx
  exact printed_remainder_poly A hA B M hM hB hsB N Q hQ hNQ u hu x hx.2

/-- The printed statement as the PROP-021 `RemainderEstimate` with the printed constant. -/
theorem remainderEstimate_printed (A : ℝ) (hA : 0 < A) :
    Prop021RemainderInputR131.RemainderEstimate (L := L) A (printedConstant A) :=
  printed_remainder A hA

/-- Binding: the PROP-021 premise `Prop024RemainderInput` (R131), proved from the printed statement
with the explicit nonnegative constant `printedConstant`. -/
theorem prop024RemainderInput_printed : Prop021RemainderInputR131.Prop024RemainderInput (L := L) :=
  fun A hA => ⟨printedConstant A, printedConstant_nonneg A, printed_remainder A hA⟩

end QuantumNLS.Prop024FinalH1

#print axioms QuantumNLS.Prop024FinalH1.printed_remainder_poly
#print axioms QuantumNLS.Prop024FinalH1.printed_remainder
#print axioms QuantumNLS.Prop024FinalH1.remainderEstimate_printed
#print axioms QuantumNLS.Prop024FinalH1.prop024RemainderInput_printed

set_option maxHeartbeats 10000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024FinalH1." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024FinalH1." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any
          (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
        throwError "Held identifier in dependency closure: {n}"
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
  Lean.logInfo m!"H1 PROP-024 printed-statement audit PASS: {roots} own constants; {seen.size} transitive constants; standard axioms only."
