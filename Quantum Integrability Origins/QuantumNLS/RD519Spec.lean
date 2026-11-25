import QuantumNLS.TerraMultiHeadlineR95
/-! integrator-authored trusted spec for R-D51987CA thm:audit-gauge-retargeting (single assembled headline): headline statement(s) copied verbatim from TerraMultiHeadlineR95 (QuantumNLS.TerraMultiHeadlineR95). -/
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
namespace QuantumNLS.RD519Spec
open QuantumNLS.TerraMultiHeadlineR95
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem audit_gauge_retargeting_spec (hκ : 0 < κ) :
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
  first
  | exact QuantumNLS.TerraMultiHeadlineR95.audit_gauge_retargeting
  | (apply QuantumNLS.TerraMultiHeadlineR95.audit_gauge_retargeting <;> assumption)

end QuantumNLS.RD519Spec
#print axioms QuantumNLS.RD519Spec.audit_gauge_retargeting_spec
