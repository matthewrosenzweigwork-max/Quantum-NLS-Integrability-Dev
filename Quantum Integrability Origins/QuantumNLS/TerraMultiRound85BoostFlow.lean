import QuantumNLS.TerraMultiRound85BoostDuhamel
import QuantumNLS.TerraMultiRound85TranslationFlow

/-! The exact Galilean identity for the actual physical L² flow. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness QuantumNLS.LocalWellPosednessFull QuantumNLS.F04Global
open QuantumNLS.H1Bridge QuantumNLS.L2Flow QuantumNLS.DuhamelDuality
open QuantumNLS.TerraMultiRound85H1Bridge QuantumNLS.TerraMultiRound85H1Density
open QuantumNLS.TerraMultiRound85BoostH1 QuantumNLS.TerraMultiRound85BoostCubic
open QuantumNLS.TerraMultiRound85BoostFree QuantumNLS.TerraMultiRound85BoostDuhamel
open QuantumNLS.TerraMultiRound85TranslationFlow
namespace QuantumNLS.TerraMultiRound85BoostFlow
variable {L : ℝ} [Fact (0 < L)]

/-- Physical modulation preserves subtraction. -/
theorem boost_sub (k : ℤ) (u v : HL L) :
    QuantumNLS.RootMassBoostSymbol.boost k (u-v) =
      QuantumNLS.RootMassBoostSymbol.boost k u - QuantumNLS.RootMassBoostSymbol.boost k v := by
  apply MeasureTheory.Lp.ext
  have h1 := QuantumNLS.RootMassBoostSymbol.coe_boost k (u-v)
  have h2 := QuantumNLS.RootMassBoostSymbol.coe_boost k u
  have h3 := QuantumNLS.RootMassBoostSymbol.coe_boost k v
  have h4 := Lp.coeFn_sub u v
  have h5 := Lp.coeFn_sub (QuantumNLS.RootMassBoostSymbol.boost k u) (QuantumNLS.RootMassBoostSymbol.boost k v)
  filter_upwards [h1,h2,h3,h4,h5] with x h1x h2x h3x h4x h5x
  rw [h1x,h5x,h4x]
  simp only [Pi.sub_apply]
  rw [h2x,h3x]
  ring

/-- Physical modulation is an L² isometry. -/
theorem boost_isometry (k : ℤ) : Isometry (QuantumNLS.RootMassBoostSymbol.boost (L := L) k) := by
  apply isometry_iff_dist_eq.mpr
  intro u v
  rw [dist_eq_norm, dist_eq_norm, ← boost_sub, QuantumNLS.RootMassBoostSymbol.norm_boost]

/-- The H¹ Galilean transform embeds as the literal physical transform. -/
theorem emb_boostCLM (k : ℤ) (t : ℝ) (a : h04 L 1) :
    emb (boostCLM k t a) = boostPhase (L := L) k t •
      QuantumNLS.RootMassBoostSymbol.boost k (QuantumNLS.BornTranslation.trans (boostMove (L := L) k t) (emb a)) := by
  rw [boostCLM_apply, map_smul, emb_shift, emb_translate]

/-- The actual flow obeys the Galilean identity for all L² data and real times. -/
theorem boost_flow {κ : ℝ} (hκ : 0 ≤ κ) (k : ℤ) (u : HL L) (t : ℝ) :
    flowMap hκ (QuantumNLS.RootMassBoostSymbol.boost k u) t =
      boostPhase (L := L) k t • QuantumNLS.RootMassBoostSymbol.boost k
        (QuantumNLS.BornTranslation.trans (boostMove (L := L) k t) (flowMap hκ u t)) := by
  let B := QuantumNLS.RootMassBoostSymbol.boost (L := L) k
  let T := QuantumNLS.BornTranslation.trans (L := L) (boostMove (L := L) k t)
  have hB : Continuous B := (boost_isometry k).continuous
  have hscalar : Continuous (fun v : HL L => boostPhase (L := L) k t • v) := by fun_prop
  have h1 : Continuous (fun v : HL L => flowMap hκ (B v) t) := (continuous_flowMap hκ t).comp hB
  have h2 : Continuous (fun v : HL L => boostPhase (L := L) k t • B (T (flowMap hκ v t))) :=
    hscalar.comp (hB.comp (T.continuous.comp (continuous_flowMap hκ t)))
  have he := Continuous.ext_on (denseRange_emb (L := L)) h1 h2 (by
    rintro _ ⟨g, rfl⟩
    let v := umax (le_refl (1 : ℝ)) κ g
    have hv := umax_mild (hs := le_refl (1 : ℝ)) hκ g
    rw [Imax1_eq_univ hκ g] at hv
    have hh := flowMap_of_global_mild hκ (shift k g) (fun t => boostCLM k t (v t)) (boost_mild k g v hv) t
    change flowMap hκ (B (emb g)) t = boostPhase (L := L) k t • B (T (flowMap hκ (emb g) t))
    rw [flowMap_H1 hκ g t]
    simpa only [emb_shift, emb_boostCLM] using hh)
  exact congrFun he u

#print axioms boost_sub
#print axioms boost_isometry
#print axioms emb_boostCLM
#print axioms boost_flow
end QuantumNLS.TerraMultiRound85BoostFlow
