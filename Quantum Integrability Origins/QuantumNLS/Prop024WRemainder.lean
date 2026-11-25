import QuantumNLS.Prop024AssemblyR58
import QuantumNLS.Prop024WSeries

/-! PROP-024 operator-level Wick expansion, module 9 (Prop024WRemainder): the entire Wick remainder estimate for the ACTUAL remainder vector.

`norm_remVec_le`: for the remainder vector `remVec` of `Prop024WSeries` (all Wick cells of total degree `j ≥ 3`, all interaction orders), under the factorial kernel bound, the printed polynomial number-moment bounds and `N ≥ 256 e A Q`, `‖R_N(u) x‖ ≤ C_A' M N^{-1/2} Q^{3/2}` with the printed constant `C_A' = 2 S_B B³ (32e)^{3/2}`.  The proof is the triangle inequality for the Hilbert-norm convergent series, `norm_cellDeg_le_slice` (each slice is at most `N` times the frozen R54 `contractedSliceCell`), and the frozen R54 `contractedDoubleSeries_source_bound`. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace ComplexConjugate Topology
namespace QuantumNLS.Prop024WRemainder
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop024WWeylPhysical Prop024WBlock Prop024WOrder Prop024WNorms Prop024WSeries
open Prop024ContractionsR54 Prop024WickCellsR54 Prop024WickSeriesR54 Prop022FactorialCoefficientsR115
variable {L : ℝ} [Fact (0 < L)]

/-- **The entire Wick remainder estimate** `Q7B:eq:rembound` for the actual remainder vector:
`‖R_N(u) x‖ ≤ C_A' M N^{-1/2} Q^{3/2}` with the printed constant `C_A' = 2 S_B B³ (32e)^{3/2}`,
`B = √(2A)`, `S_B = ∑_l B^l/√(l!)`. -/
theorem norm_remVec_le (N : ℕ) (hN : 0 < N) (B : ∀ r, HN L r →L[ℂ] HN L r) (M A Q : ℝ)
    (hM : 0 ≤ M) (hA : 0 < A) (hQ : 1 ≤ Q) (hNQ : 256 * Real.exp 1 * A * Q ≤ N)
    (hB : FactorialBound B M A) (u : L2T L) (hu : ‖u‖ = 1) (x : physSmooth L)
    (hMom : PolyMoments Q x.1) :
    ‖remVec N B u x.1‖ ≤
      2 * Prop024ScalarSeriesR52.factorialRootSeries (Real.sqrt (2*A)) * (Real.sqrt (2*A))^3 *
        (Real.sqrt (32 * Real.exp 1))^3 * M * (Real.sqrt Q)^3 / Real.sqrt N := by
  have hs := summable_norm_remCell N hN B M A Q hM hA hQ hNQ hB u hu x hMom
  have hext := (summable_contractedSlice_ext B u hu M A Q N hM hA hQ hNQ hB).mul_left (N : ℝ)
  have h1 : ‖remVec N B u x.1‖ ≤ ∑' q : ℕ × ℕ, ‖remCell N B u x.1 q‖ :=
    norm_tsum_le_tsum_norm hs
  have h2 : ∑' q : ℕ × ℕ, ‖remCell N B u x.1 q‖ ≤
      ∑' q : ℕ × ℕ, (N : ℝ) * (if 3 ≤ q.2 ∧ q.2 ≤ 2 * q.1 then contractedSliceCell q.1 q.2 B u Q N else 0) := by
    refine Summable.tsum_le_tsum (fun q => ?_) hs hext
    unfold remCell
    split_ifs with h
    · exact norm_cellDeg_le_slice N q.1 q.2 hN h.1 B u x Q hQ hMom
    · simp
  have h3 : ∑' q : ℕ × ℕ, (N : ℝ) * (if 3 ≤ q.2 ∧ q.2 ≤ 2 * q.1 then contractedSliceCell q.1 q.2 B u Q N else 0) =
      (N : ℝ) * contractedDoubleSeries B u Q N := by
    rw [tsum_mul_left]
    congr 1
    unfold contractedDoubleSeries
    have := tsum_subtype ({q : ℕ × ℕ | 3 ≤ q.2 ∧ q.2 ≤ 2 * q.1}) (fun q : ℕ × ℕ => contractedSliceCell q.1 q.2 B u Q N)
    refine Eq.trans ?_ this.symm
    refine tsum_congr (fun q => ?_)
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  have h4 := contractedDoubleSeries_source_bound B u hu M A Q N hM hA hQ hNQ hB
  calc ‖remVec N B u x.1‖ ≤ _ := h1.trans h2
    _ = (N : ℝ) * contractedDoubleSeries B u Q N := h3
    _ ≤ _ := h4

end QuantumNLS.Prop024WRemainder

#print axioms QuantumNLS.Prop024WRemainder.norm_remVec_le

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024WRemainder." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024WRemainder." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
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
  Lean.logInfo m!"Prop024WRemainder aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard axioms only."
