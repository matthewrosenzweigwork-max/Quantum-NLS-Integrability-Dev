import QuantumNLS.Prop021PairR133
import QuantumNLS.Prop024TransferR133

/-! PROP-021 with the printed existential PROP-022 premise and the
proved PROP-024 input. The reference-carrier assembly uses the exact
R131 binding from WIdent. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5500000
set_option synthInstance.maxHeartbeats 150000
open scoped InnerProductSpace ENNReal

namespace QuantumNLS.Prop021AssemblyR133
open PhysicalTensor Prop022GClassical Prop022GHilbert Prop022BExist
open Prop021StatementR132 Prop025OInputs Prop021GeneralR132
open Prop022FactorialMajorantR115 Prop021RatesR128 Prop021PairR133

variable {L : ℝ} [Fact (0 < L)]

/-- R131's exact remainder consumer is discharged by WIdent. -/
theorem torus_prop021 (hPair : PrintedPairFamily (L := L)) : Prop021Input (L := L) :=
  Prop021AssemblyR131.prop021 (printed_iff_fixed.mp hPair)
    Prop024WIdent.prop024RemainderInput_holds

private theorem enlarge_constants (A : ℝ) (hA : 0 < A) (c₁ c₂ T C₁ C₂ : ℝ)
    (hc : c₁ ≤ c₂) (hC : C₁ ≤ C₂)
    (h : TorusAtConstants (L := L) A hA c₁ T C₁) : TorusAtConstants (L := L) A hA c₂ T C₂ := by
  intro K M hM hK hs u₀ P hP hS N hN hNQ
  have hM₀ : 0 ≤ M := zero_le_one.trans hM
  have hQ : 0 ≤ Qpar A T M P := zero_le_one.trans (one_le_numberParameter (pairMajorant A) T M P)
  obtain ⟨⟨θ,ξ,h0,hn,he,hd⟩,hmarg,hprep⟩ :=
    h K M hM hK hs u₀ P hP hS N hN ((mul_le_mul_of_nonneg_right hc hQ).trans hNQ)
  refine ⟨⟨θ,ξ,h0,hn,?_,hd⟩,?_,?_⟩
  · intro t ht
    apply (he t ht).trans
    gcongr
  · intro k hk0 hk t ht
    apply (hmarg k hk0 hk t ht).trans
    apply ENNReal.ofReal_le_ofReal
    gcongr
  · intro k hk0 hk ψ hψ t ht
    apply (hprep k hk0 hk ψ hψ t ht).trans
    apply ENNReal.ofReal_le_ofReal
    gcongr

/-- The sole named input is the existential printed PROP-022 statement on
the reference carrier, which is the specialization used by the proof. -/
theorem prop021 (hPair : PrintedPairFamily (L := L)) : Prop021 (L := L) := by
  have hPairL := printed_iff_fixed.mp hPair
  have hTorus := (torus_statement (L := L)).mpr (torus_prop021 hPair)
  intro A hA
  obtain ⟨cA,hcA⟩ := hTorus A hA
  let C := Prop024FinalH1.printedConstant A
  have hC : 0 ≤ C := Prop024FinalH1.printedConstant_nonneg A
  have hRem : Prop021RemainderInputR131.RemainderEstimate (L := L) A C :=
    Prop024FinalH1.remainderEstimate_printed A hA
  let cutoff := 256 * Real.exp 1 * A
  refine ⟨max cA cutoff, fun T hT => ?_⟩
  obtain ⟨CAT,hCAT⟩ := hcA T hT
  let estimate := max CAT (T*C)
  have h : TorusAtConstants (L := L) A hA (max cA cutoff) T estimate :=
    enlarge_constants A hA cA (max cA cutoff) T CAT estimate
      (le_max_left cA cutoff) (le_max_left CAT (T*C)) hCAT
  refine ⟨estimate, fun H _ _ _ _ => ⟨?_,?_⟩⟩
  · intro hH
    exact ⟨exists_unitary_L2T L hH, fun U =>
      Prop021UnitaryR132.transfer_at_constants U A hA (max cA cutoff) T estimate h⟩
  · intro hH
    refine ⟨exists_isometry_fin hH L, fun J => ?_⟩
    exact Prop021IsometryR132.transfer_at_constants J A hA (max cA cutoff) T estimate C hT hC
      (le_max_right cA cutoff) (le_max_right CAT (T*C)) h hPairL hRem

end QuantumNLS.Prop021AssemblyR133
