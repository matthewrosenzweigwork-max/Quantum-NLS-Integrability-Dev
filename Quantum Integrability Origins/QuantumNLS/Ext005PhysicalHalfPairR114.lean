import QuantumNLS.Ext005PhysicalPairFormR114

/-! Bind the completed physical pair form to the literal one-half
coefficient in PROP-022, including its form-domain diagonal identity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005PhysicalHalfPairR114
open Ext005PhysicalPairFormR114 Ext005AlgebraicFormR114 Ext005ComplexRieszR113
open Ext005PairSector Ext005Moments Ext005FormScaleR109
open Ext025B3PhysicalSectors BetheCoefficientTransform
variable {L : ℝ} [Fact (0 < L)]

/-- The exact one-half creation/annihilation form in the report. -/
def halfPair (b : HN L 2) : Form (Fock L) := (1 / 2 : ℂ) • pairContinuous b

lemma halfPair_diagonal (b : HN L 2) (u : Fock L) :
    halfPair b u u = (1 / 2 : ℂ) * pairHamiltonian b ⟨embedding 1 u, embedding_mem 1 u⟩ := rfl

lemma halfPair_symmetric (b : HN L 2) (u v : Fock L) :
    starRingEnd ℂ (halfPair b u v) = halfPair b v u := by
  change starRingEnd ℂ ((1 / 2 : ℂ) * pairRaw b u v) = (1 / 2 : ℂ) * pairRaw b v u
  rw [map_mul, pairRaw_symmetric b u v]
  congr 1
  norm_num [map_ofNat]

/-- Exact diagonal coefficient on every actual first-moment-domain vector. -/
lemma halfPair_operatorDomain (b : HN L 2) (x : momentDomain (L := L) 1) :
    halfPair b (momentRoot 1 x) (momentRoot 1 x) = (1 / 2 : ℂ) * pairHamiltonian b x := by
  rw [halfPair_diagonal]
  have hx : (⟨embedding 1 (momentRoot 1 x), embedding_mem 1 (momentRoot 1 x)⟩ :
      momentDomain (L := L) 1) = x := Subtype.ext (embedding_root 1 x)
  rw [hx]

lemma halfPair_offDiagonal (b : HN L 2) (u v : Fock L) :
    halfPair b u v = (1 / 2 : ℂ) * ((∑' n, sectorTerm b u v n) +
      ∑' n, ⟪embedding 1 v (2 + n), creation b n (embedding 1 u n)⟫_ℂ) := by
  change (1 / 2 : ℂ) * pairContinuous b u v = _
  rw [pairContinuous_offDiagonal]

end QuantumNLS.Ext005PhysicalHalfPairR114
#print axioms QuantumNLS.Ext005PhysicalHalfPairR114.halfPair_operatorDomain
#print axioms QuantumNLS.Ext005PhysicalHalfPairR114.halfPair_offDiagonal

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005PhysicalHalfPairR114." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005PhysicalHalfPairR114." then
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
  Lean.logInfo m!"R114 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
