import QuantumNLS.MainTheoremR03
/-! integrator trusted spec for R-AF8F7562 thm:main (MainTheoremR03): headline plus literal Iff.rfl pins of the top-level statement and the extended part (iii). -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.MainSpec
open QuantumNLS.MainTheoremR03
open QuantumNLS.UniformStaticR49b (SectorGauge)
variable {L κ : ℝ} [Fact (0 < L)]
theorem thm_main_spec (hκ : 0 < κ) : QuantumNLS.MainTheoremR03.MainStatementR03 (L := L) hκ :=
  QuantumNLS.MainTheoremR03.thm_main hκ
theorem pin_MainStatementR03 (hκ : 0 < κ) :
    QuantumNLS.MainTheoremR03.MainStatementR03 (L := L) hκ ↔
  ∃ (j : ℕ → ℕ) (q : SectorGauge),
    MainTheoremR02.PartI (L := L) hκ ∧ MainTheoremR02.PartII (L := L) hκ j q ∧ PartIII (L := L) hκ q ∧
      MainTheoremR01.PartIV (L := L) hκ ∧ MainTheoremR02.PartV (L := L) hκ q ∧ MainTheoremR01.PartVI (L := L) hκ ∧
      MainTheoremR02.Coherence (L := L) hκ q := Iff.rfl
theorem pin_PartIII (hκ : 0 < κ) (q : SectorGauge) :
    QuantumNLS.MainTheoremR03.PartIII (L := L) hκ q ↔
  MainTheoremR02.PartIII (L := L) hκ q ∧ MainTheoremR03Count.G1Clause (L := L) hκ q := Iff.rfl
end QuantumNLS.MainSpec
#print axioms QuantumNLS.MainSpec.thm_main_spec
