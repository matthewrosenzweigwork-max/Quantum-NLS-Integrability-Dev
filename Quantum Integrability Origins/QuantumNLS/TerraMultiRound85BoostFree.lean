import QuantumNLS.TerraMultiRound85BoostCubic
import QuantumNLS.TerraMultiRound85TranslationH1

/-! Exact free Schrödinger Galilean intertwining on H¹. -/
set_option autoImplicit false
noncomputable section
open QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness QuantumNLS.TerraMultiRound85BoostH1
open QuantumNLS.TerraMultiRound85TranslationH1 AddCircle
namespace QuantumNLS.TerraMultiRound85BoostFree
variable {L : ℝ} [Fact (0 < L)]

/-- The scalar Galilean time phase. -/
def boostPhase (k : ℤ) (t : ℝ) : ℂ := phase L t k

theorem norm_boostPhase (k : ℤ) (t : ℝ) : ‖boostPhase (L := L) k t‖ = 1 := by
  exact norm_phase L t k

theorem boostPhase_add (k : ℤ) (s t : ℝ) :
    boostPhase (L := L) k (s+t) = boostPhase (L := L) k s * boostPhase (L := L) k t := by
  exact phase_add L s t k

theorem boostPhase_zero (k : ℤ) : boostPhase (L := L) k 0 = 1 := phase_zero L k

theorem continuous_boostPhase (k : ℤ) : Continuous (boostPhase (L := L) k) := continuous_phase L k

/-- Spatial motion associated with the Galilean phase. -/
def boostMove (k : ℤ) (t : ℝ) : ℝ := -2 * freq L k * t

theorem boostMove_add (k : ℤ) (s t : ℝ) :
    boostMove (L := L) k (s+t) = boostMove (L := L) k s + boostMove (L := L) k t := by
  unfold boostMove
  ring

theorem transPhase_exp (y : ℝ) (n : ℤ) :
    transPhase (L := L) y n = Complex.exp (Complex.I * ((freq L n * y : ℝ) : ℂ)) := by
  unfold transPhase
  rw [fourier_coe_apply]
  congr 1
  unfold freq
  push_cast
  ring

/-- Free evolution of a modulated field, with the exact moving argument and phase. -/
theorem Sgrp_shift (k : ℤ) (t : ℝ) (a : h04 L 1) :
    Sgrp 1 t (shift k a) = boostPhase (L := L) k t •
      shift k (QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) 1 (boostMove (L := L) k t) (Sgrp 1 t a)) := by
  apply WSeq.ext
  funext n
  change phase L t n * a.val (n-k) = boostPhase (L := L) k t *
    (transPhase (L := L) (boostMove (L := L) k t) (n-k) * (phase L t (n-k) * a.val (n-k)))
  have hfreq : freq L n = freq L (n-k) + freq L k := by
    rw [← freq_add]
    congr 1
    omega
  have hphase : phase L t n = boostPhase (L := L) k t *
      (transPhase (L := L) (boostMove (L := L) k t) (n-k) * phase L t (n-k)) := by
    unfold boostPhase phase boostMove
    rw [transPhase_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [hfreq]
    push_cast
    ring
  rw [hphase]
  ring

#print axioms norm_boostPhase
#print axioms boostPhase_add
#print axioms boostMove_add
#print axioms transPhase_exp
#print axioms Sgrp_shift
end QuantumNLS.TerraMultiRound85BoostFree
