import QuantumNLS.TerraMultiRound85BoostFree
import QuantumNLS.TerraMultiRound85TranslationTime
import QuantumNLS.TerraMultiRound85TranslationCubic
import QuantumNLS.TerraMultiRound85PhaseFlow

/-! Galilean transformations in the global H¹ Duhamel equation. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness QuantumNLS.TerraMultiRound85BoostH1
open QuantumNLS.TerraMultiRound85BoostCubic QuantumNLS.TerraMultiRound85BoostFree
open QuantumNLS.TerraMultiRound85TranslationH1 QuantumNLS.TerraMultiRound85TranslationTime
open QuantumNLS.TerraMultiRound85TranslationCubic QuantumNLS.TerraMultiRound85PhaseFlow
namespace QuantumNLS.TerraMultiRound85BoostDuhamel
variable {L : ℝ} [Fact (0 < L)]

/-- The actual time-dependent Galilean transform on H¹ coefficients. -/
def boostCLM (k : ℤ) (t : ℝ) : h04 L 1 →L[ℂ] h04 L 1 :=
  boostPhase (L := L) k t • (shift k).comp
    (QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) 1 (boostMove (L := L) k t))

@[simp] theorem boostCLM_apply (k : ℤ) (t : ℝ) (a : h04 L 1) :
    boostCLM k t a = boostPhase (L := L) k t •
      shift k (QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) 1 (boostMove (L := L) k t) a) := rfl

/-- The transformed H¹ curve is strongly continuous. -/
theorem continuous_boost_curve (k : ℤ) {u : ℝ → h04 L 1} (hu : Continuous u) :
    Continuous fun t => boostCLM k t (u t) := by
  have hm : Continuous (boostMove (L := L) k) := by unfold boostMove; fun_prop
  have ht := continuous_translate_curve 1 hm hu
  have hs := (shift k).continuous.comp ht
  change Continuous (fun t : ℝ => boostPhase (L := L) k t •
    shift k (QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) 1 (boostMove (L := L) k t) (u t)))
  exact continuous_smul.comp ((continuous_boostPhase (L := L) k).prodMk hs)

/-- The cubic map commutes with the Galilean transform at each time. -/
theorem Fh_boostCLM (k : ℤ) (t : ℝ) (a : h04 L 1) :
    Fh (le_refl (1 : ℝ)) (boostCLM k t a) = boostCLM k t (Fh (le_refl (1 : ℝ)) a) := by
  simp only [boostCLM_apply, Fh_unit_phase _ _ (norm_boostPhase k t), Fh_shift, Fh_translate]

/-- The free group transports the transform at time `r` to time `t`. -/
theorem Sgrp_boostCLM (k : ℤ) (t r : ℝ) (a : h04 L 1) :
    Sgrp 1 (t-r) (boostCLM k r a) = boostCLM k t (Sgrp 1 (t-r) a) := by
  rw [boostCLM_apply, map_smul, Sgrp_shift]
  simp only [boostCLM_apply, smul_smul]
  have hphase : boostPhase (L := L) k r * boostPhase (L := L) k (t-r) = boostPhase (L := L) k t := by
    rw [mul_comm, ← boostPhase_add]
    congr 1
    ring
  rw [hphase]
  congr 1
  rw [← translate_Sgrp, ← QuantumNLS.TerraMultiRound85TranslationTime.translate_add]
  have hmove : boostMove (L := L) k (t-r) + boostMove (L := L) k r = boostMove (L := L) k t := by
    rw [← boostMove_add]
    congr 1
    ring
  rw [hmove]

/-- At time zero the Galilean transform is the actual Fourier index shift. -/
theorem boostCLM_zero (k : ℤ) (a : h04 L 1) : boostCLM k 0 a = shift k a := by
  rw [boostCLM_apply, boostPhase_zero, one_smul]
  congr 1
  apply WSeq.ext
  funext n
  change transPhase (L := L) (boostMove (L := L) k 0) n * a.val n = a.val n
  simp [boostMove, transPhase, fourier_eval_zero]

/-- The Galilean transform of a global H¹ mild curve is another such curve. -/
theorem boost_mild {κ : ℝ} (k : ℤ) (u0 : h04 L 1) (u : ℝ → h04 L 1)
    (hu : IsMild (le_refl (1 : ℝ)) κ Set.univ u0 u) :
    IsMild (le_refl (1 : ℝ)) κ Set.univ (shift k u0) (fun t => boostCLM k t (u t)) := by
  refine ⟨Set.mem_univ _, Set.ordConnected_univ, ?_, ?_⟩
  · exact (continuous_boost_curve k (continuousOn_univ.mp hu.cont)).continuousOn
  · intro t ht
    have hi := integrable_duhamel (le_refl (1 : ℝ)) hu.ordConnected hu.cont t 0 t
      (Set.mem_univ 0) (Set.mem_univ t)
    rw [hu.duhamel_eq t (Set.mem_univ t)]
    unfold duhamel
    rw [map_sub, map_smul, ← (boostCLM k t).intervalIntegral_comp_comm hi]
    rw [show boostCLM k t (Sgrp 1 t u0) = Sgrp 1 t (shift k u0) from (Sgrp_shift k t u0).symm]
    congr 2
    apply intervalIntegral.integral_congr
    intro r hr
    change boostCLM k t (Sgrp 1 (t-r) (Fh (le_refl (1 : ℝ)) (u r))) =
      Sgrp 1 (t-r) (Fh (le_refl (1 : ℝ)) (boostCLM k r (u r)))
    rw [Fh_boostCLM]
    exact (Sgrp_boostCLM k t r (Fh (le_refl (1 : ℝ)) (u r))).symm

#print axioms continuous_boost_curve
#print axioms Fh_boostCLM
#print axioms Sgrp_boostCLM
#print axioms boostCLM_zero
#print axioms boost_mild
end QuantumNLS.TerraMultiRound85BoostDuhamel
