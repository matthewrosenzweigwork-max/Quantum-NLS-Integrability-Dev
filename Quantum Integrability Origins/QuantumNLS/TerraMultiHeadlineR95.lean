import QuantumNLS.TerraMultiPhysicalR94

/-! One assembled physical headline at the R94 named pair.  Positive sectors
are indexed by n, with physical particle number N = n+1. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
noncomputable section
open Set Filter Topology
open scoped ComplexConjugate
open QuantumNLS.PhysicalTensor QuantumNLS.BetheLabels QuantumNLS.Occupation
open QuantumNLS.OccupationHilbert QuantumNLS.FullOccupationAffinity QuantumNLS.FiniteCellGauge
open QuantumNLS.BetheCoefficientTransform QuantumNLS.TensorCarrier
open QuantumNLS.RetargetWeightsR48b QuantumNLS.RetargetStageR48b QuantumNLS.RetargetPhysicalR48b
open QuantumNLS.RetargetAnglesR48b QuantumNLS.RetargetCellR48b
namespace QuantumNLS.TerraMultiHeadlineR95
variable {L κ : ℝ} [Fact (0 < L)]

/-- The assembled R-D51987CA headline, with one named gauge and one
physical schedule throughout. The quantified H02 witness spells out the
rough unit H¹ ball. All formulas are on the complete occupation array. -/
theorem audit_gauge_retargeting (hκ : 0 < κ) :
    let s := RetargetSelectionR49b.sectorStage (L := L) hκ
    let q := RetargetSelectionR49b.sectorGauge (L := L) hκ
    let j := physicalSchedule s
    Monotone j ∧ Tendsto j atTop atTop ∧
    (∀ N (m : MArr N), ‖(gauge q N m).1‖ = 1) ∧
    (∀ n (a b : ℤ) (m : MArr (n+1)),
      let B := Def044D1SpectralR51a.basis (L := L) hκ n
      physical B (FiniteCellGauge.W (q n) a b) (B m) =
        if hd : DonorOK a m.val then
          let d := DynSeedGradingR47b.transfer a b m hd
          ((gauge q (n+1) m).1 * conj (gauge q (n+1) d).1) • B d
        else 0) ∧
    (∀ n (a b : ℤ) (m : MArr (n+1)),
      let B := Def044D1SpectralR51a.basis (L := L) hκ n
      physical B (cartesian (q n) a b) (B m) =
        if hd : DonorOK a m.val then
          ((q n (marrArr (n+1) m)).1 * conj (q n (shiftArr a b (marrArr (n+1) m) hd)).1 *
            (coef (n+1) a b (marrArr (n+1) m).1 : ℂ)) • B (DynSeedGradingR47b.transfer a b m hd)
        else 0) ∧
    (∀ n (a b : ℤ), cartesian (q n) a b =
      FiniteCellGauge.W (q n) a b ∘L weight (n+1) a b) ∧
    (∀ n (a b : ℤ), a ≠ b → ∀ m : MArr (n+1),
      coef (n+1) a b m.val = Real.sqrt (((m.val a : ℝ) / ((n+1 : ℕ) : ℝ)) *
        ((m.val b : ℝ) / ((n+1 : ℕ) : ℝ) + ((n+1 : ℕ) : ℝ)⁻¹))) ∧
    (∀ n (a : ℤ), physical (Def044D1SpectralR51a.basis (L := L) hκ n)
      (cartesian (q n) a a) = Prop010ContourBindingR11.B L hκ (Nat.succ_pos n) a) ∧
    (∀ n (a b i : ℤ) (m : MArr (n+1)) (hd : DonorOK a m.val),
      i ≠ a → i ≠ b → (DynSeedGradingR47b.transfer a b m hd).val i = m.val i) ∧
    (∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ u : L2T L,
      (‖u‖ = 1 ∧ ∃ v : Sobolev.H02 L 1, v.val = u ∧ ‖v‖ ≤ R) →
      ∀ a b : ↥(labels (j (n+1))),
        let ψ : HN L (n+1) := HighMomentsOps.wvec (n+1) u
        let B := Def044D1SpectralR51a.basis (L := L) hκ n
        let E := physical B (cartesian (q n) a.1 b.1)
        let z := coordinate hκ u a.1 * conj (coordinate hκ u b.1)
        ‖E ψ - z • ψ‖ + ‖E.adjoint ψ - conj z • ψ‖ ≤ ε) ∧
    (∀ R ρ ε : ℝ, 0 < ρ → 0 < ε → ∀ᶠ n in atTop, ∀ u : L2T L,
      (‖u‖ = 1 ∧ ∃ v : Sobolev.H02 L 1, v.val = u ∧ ‖v‖ ≤ R) →
      ∀ a b : ↥(labels (j (n+1))), a.1 ≠ b.1 →
        let ψ : HN L (n+1) := HighMomentsOps.wvec (n+1) u
        let B := Def044D1SpectralR51a.basis (L := L) hκ n
        let z := coordinate hκ u a.1
        let w := coordinate hκ u b.1
        let ζ := pairPhase z w
        let A := physical B (FiniteCellGauge.W (q n) a.1 b.1)
        ρ ≤ ‖z‖^2 → ρ ≤ ‖w‖^2 →
          ‖A ψ - ζ.1 • ψ‖ ≤ ε ∧ ‖A.adjoint ψ - conj ζ.1 • ψ‖ ≤ ε) ∧
    (∀ R ρ ε : ℝ, 0 < ρ → 0 < ε → ∀ᶠ n in atTop, ∀ u : L2T L,
      (‖u‖ = 1 ∧ ∃ v : Sobolev.H02 L 1, v.val = u ∧ ‖v‖ ≤ R) →
      ∀ a b : ↥(labels (j (n+1))), a.1 ≠ b.1 →
        let g := coefficients hκ n u
        let z := coordinate hκ u a.1
        let w := coordinate hκ u b.1
        let ζ := pairPhase z w
        ρ ≤ ‖z‖^2 → ρ ≤ ‖w‖^2 →
          ‖FiniteCellGauge.W (q n) a.1 b.1 g - ζ.1 • g‖ ≤ ε ∧
          ‖(FiniteCellGauge.W (q n) a.1 b.1).adjoint g - conj ζ.1 • g‖ ≤ ε ∧
          ExactShiftResidual.missing a.1 g ≤ ε ∧ ExactShiftResidual.missing b.1 g ≤ ε ∧
          |affinity a.1 b.1 g - 1| ≤ ε ∧ |defect a.1 b.1 (edgePhase (q n) a.1 b.1) ζ g| ≤ ε ∧
          ‖overlap a.1 b.1 (edgePhase (q n) a.1 b.1) g - ζ.1‖ ≤ ε) := by
  -- Each exact term checks that conjunct against its frozen interface type.
  -- The final conjunct is the complete directed R94 gauge interface.
  dsimp only
  refine ⟨TerraMultiPhysicalR94.named_schedule_monotone hκ,
    TerraMultiPhysicalR94.named_schedule_tendsto hκ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N m; exact (gauge _ N m).2
  · exact TerraMultiPhysicalR94.named_phase_ratio hκ
  · intro n a b m; exact cartesian_formula _ _ a b m
  · intro n a b; exact cartesian_factor _ a b
  · intro n a b hab m; exact cartesian_weight (Nat.succ_pos n) a b hab m
  · exact TerraMultiPhysicalR94.named_cartesian_diagonal hκ
  · intro n a b i m hd; exact exact_exterior a b i m hd
  · exact TerraMultiPhysicalR94.named_cartesian hκ
  · exact TerraMultiPhysicalR94.named_phase hκ
  · exact (FullWickO5.gauge_conclusion_named (L := L) hκ).2.2.2

#print axioms audit_gauge_retargeting
end QuantumNLS.TerraMultiHeadlineR95

set_option maxHeartbeats 20000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[``QuantumNLS.TerraMultiHeadlineR95.audit_gauge_retargeting]
  let mut seen : Std.HashSet Lean.Name := {}
  let mut axioms : Array Lean.Name := #[]
  let mut flags : Array Lean.Name := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          n.components.any (fun c => c.toString == "RegularCut") then
        flags := flags.push n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            axioms := axioms.push n
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"R95 audit: {seen.size} transitive constants; nonstandard axioms {axioms}; flagged identifiers {flags}"
  unless axioms.isEmpty do throwError "Nonstandard axioms found"
  unless flags.isEmpty do throwError "Flagged identifiers found"
