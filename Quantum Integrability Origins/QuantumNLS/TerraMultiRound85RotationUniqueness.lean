import QuantumNLS.TerraMultiRound85DynamicsInput
import QuantumNLS.GlobalCompatFinalR47a
import QuantumNLS.ChartFrequencies

/-! Active frequencies are uniquely determined by the actual all-time rotations. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound85RotationUniqueness
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.GlobalCompatR47a QuantumNLS.L2Flow QuantumNLS.ActionTorus
variable {L : ℝ} [Fact (0 < L)] {κ d : ℝ} (hκ : 0 < κ)
variable {Φl : ℝ → L2T L → QuantumNLS.D01LocalPrimitive.K}
variable {Ψl : ℝ → QuantumNLS.D01LocalPrimitive.K → L2T L}
variable {Φ : ℝ → L2T L → QuantumNLS.D01LocalPrimitive.K}
variable {Ψ : ℝ → QuantumNLS.D01LocalPrimitive.K → L2T L}

def Rotates (ν : ℤ → PosL1 → ℝ) : Prop :=
  ∀ (u : L2T L) (t : ℝ) (n : ℤ), 0 < (QuantumNLS.RootIndexedMasses.masses hκ u).1 n →
    Φ κ (flowMap hκ.le u t) n =
      Complex.exp (-Complex.I * ((t * ν n (QuantumNLS.RootIndexedMasses.masses hκ u) : ℝ) : ℂ)) * Φ κ u n

/-- Rotation witnesses agree wherever the corresponding action is active. -/
theorem active_rotation_unique
    (h : Extension κ hκ d (Φl κ) (Ψl κ) (Φ κ) (Ψ κ))
    (ν μ : ℤ → PosL1 → ℝ) (hν : Rotates (Φ := Φ) hκ ν) (hμ : Rotates (Φ := Φ) hκ μ)
    (a : PosL1) (n : ℤ) (ha : 0 < a.1 n) : ν n a = μ n a := by
  let u : L2T L := Ψ κ (sqrtVec a)
  have hu : QuantumNLS.RootIndexedMasses.masses hκ u = a := by
    apply Subtype.ext
    apply lp.ext
    funext j
    rw [← h.moduli, h.right_inv]
    exact sqrtVec_mem a j
  have hactive : 0 < (QuantumNLS.RootIndexedMasses.masses hκ u).1 n := by rw [hu]; exact ha
  have hw : Φ κ u n ≠ 0 := by
    intro hz
    rw [← h.moduli, hz, norm_zero] at hactive
    norm_num at hactive
  have heq : ν n (QuantumNLS.RootIndexedMasses.masses hκ u) =
      μ n (QuantumNLS.RootIndexedMasses.masses hκ u) := by
    apply QuantumNLS.ChartFrequencies.freq_eq_of_char_eq hw
    intro t
    rw [← hν u t n hactive, hμ u t n hactive]
  simpa only [hu] using heq

#print axioms active_rotation_unique
end QuantumNLS.TerraMultiRound85RotationUniqueness
