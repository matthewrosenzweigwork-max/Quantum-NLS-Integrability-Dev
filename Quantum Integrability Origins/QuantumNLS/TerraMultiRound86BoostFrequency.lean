import QuantumNLS.TerraMultiRound86Chart
import QuantumNLS.TerraMultiRound85DynamicsInput
import QuantumNLS.TerraMultiRound85BoostFlow
import QuantumNLS.TerraMultiRound82Characters
import QuantumNLS.GlobalCompatFinalR47a

/-! Galilean frequency covariance, from the accepted physical-dynamics theorem. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound86BoostFrequency
open QuantumNLS.TerraMultiRound86Chart
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.GlobalCompatR47a QuantumNLS.L2Flow QuantumNLS.Fourier
open QuantumNLS.LocalWellPosedness
open QuantumNLS.TerraMultiRound85DynamicsInput QuantumNLS.TerraMultiRound85BoostFlow
open QuantumNLS.TerraMultiRound85BoostFree QuantumNLS.TerraMultiRound82Characters
variable {L : ℝ} [Fact (0 < L)] {κ d CL : ℝ} (hκ : 0 < κ)
variable {Φl : ℝ → L2T L → QuantumNLS.D01LocalPrimitive.K}
variable {Ψl : ℝ → QuantumNLS.D01LocalPrimitive.K → L2T L}
variable {Φ : ℝ → L2T L → QuantumNLS.D01LocalPrimitive.K}
variable {Ψ : ℝ → QuantumNLS.D01LocalPrimitive.K → L2T L}

/-- The exact momentum phase in the physical Galilean transformation. -/
theorem boost_character (k n : ℤ) (t : ℝ) :
    boostPhase (L := L) k t *
      Complex.exp (Complex.I * ((QuantumNLS.LocalSpectral.pm L (n-k) : ℝ) : ℂ) *
        ((boostMove (L := L) k t : ℝ) : ℂ)) =
    Complex.exp (-Complex.I * ((t * (QuantumNLS.LocalSpectral.pm L n ^ 2 -
      QuantumNLS.LocalSpectral.pm L (n-k) ^ 2) : ℝ) : ℂ)) := by
  unfold boostPhase phase boostMove
  rw [← Complex.exp_add]
  congr 1
  have hf : freq L k = QuantumNLS.LocalSpectral.pm L k := rfl
  rw [hf, ← boost_momentum L k n]
  push_cast
  ring

/-- The frequency at a boosted field has the printed momentum correction. -/
theorem boost_frequency_intermediate
    (h : Extension κ hκ d (Φl κ) (Ψl κ) (Φ κ) (Ψ κ))
    (hc : Compatibility d CL Φ Ψ) :
    ∃ ν : ℤ → QuantumNLS.ActionTorus.PosL1 → ℝ,
      (∀ (u : L2T L) (t : ℝ) (n : ℤ), 0 < (QuantumNLS.RootIndexedMasses.masses hκ u).1 n →
        Φ κ (flowMap hκ.le u t) n =
          Complex.exp (-Complex.I * ((t * ν n (QuantumNLS.RootIndexedMasses.masses hκ u) : ℝ) : ℂ)) * Φ κ u n) ∧
      ∀ (u : L2T L) (n k : ℤ), 0 < (QuantumNLS.RootIndexedMasses.masses hκ u).1 (n-k) →
        ν n (QuantumNLS.RootIndexedMasses.masses hκ (QuantumNLS.RootMassBoostSymbol.boost k u)) =
          ν (n-k) (QuantumNLS.RootIndexedMasses.masses hκ u) +
            (QuantumNLS.LocalSpectral.pm L n)^2 - (QuantumNLS.LocalSpectral.pm L (n-k))^2 := by
  obtain ⟨ν, hrot, -⟩ := (QuantumNLS.REF88Final.global_physical_dynamics hκ (chart_of_extension h hc)).1
  refine ⟨ν, hrot, ?_⟩
  intro u n k ha
  let B := QuantumNLS.RootMassBoostSymbol.boost (L := L) k
  have hchart (v : L2T L) : Φ κ (B v) n = Φ κ v (n-k) := ((hc.1 κ hκ).1 v n).2.2.1 k
  have hact : 0 < (QuantumNLS.RootIndexedMasses.masses hκ (B u)).1 n := by
    rw [← h.moduli, hchart, h.moduli]
    exact ha
  have hw : Φ κ (B u) n ≠ 0 := by
    intro hz
    rw [← h.moduli, hz, norm_zero] at hact
    norm_num at hact
  have hcanc : ν n (QuantumNLS.RootIndexedMasses.masses hκ (B u)) =
      ν (n-k) (QuantumNLS.RootIndexedMasses.masses hκ u) +
        ((QuantumNLS.LocalSpectral.pm L n)^2 - (QuantumNLS.LocalSpectral.pm L (n-k))^2) := by
    apply shifted_frequency hw
    intro t
    have hp : boostPhase (L := L) k t =
        Complex.exp (((-(t * freq L k ^ 2) : ℝ) : ℂ) * Complex.I) := by
      unfold boostPhase phase
      congr 1
      push_cast
      ring
    calc
      _ = Φ κ (flowMap hκ.le (B u) t) n := (hrot (B u) t n hact).symm
      _ = Φ κ (boostPhase (L := L) k t • B
            (QuantumNLS.BornTranslation.trans (boostMove (L := L) k t) (flowMap hκ.le u t))) n := by
              rw [boost_flow hκ.le k u t]
      _ = boostPhase (L := L) k t *
            (Complex.exp (Complex.I * ((QuantumNLS.LocalSpectral.pm L (n-k) : ℝ) : ℂ) *
              ((boostMove (L := L) k t : ℝ) : ℂ)) * Φ κ (flowMap hκ.le u t) (n-k)) := by
              rw [hp, ((hc.1 κ hκ).1 _ n).1, hchart, ((hc.1 κ hκ).1 _ (n-k)).2.1]
      _ = _ := by
        rw [hrot u t (n-k) ha, hchart]
        calc
          _ = (boostPhase (L := L) k t * Complex.exp (Complex.I *
              ((QuantumNLS.LocalSpectral.pm L (n-k) : ℝ) : ℂ) *
              ((boostMove (L := L) k t : ℝ) : ℂ))) *
              (Complex.exp (-Complex.I * ((t * ν (n-k) (QuantumNLS.RootIndexedMasses.masses hκ u) : ℝ) : ℂ)) * Φ κ u (n-k)) := by ring
          _ = _ := by rw [boost_character]; ring
  linarith

#print axioms boost_character
#print axioms boost_frequency_intermediate
end QuantumNLS.TerraMultiRound86BoostFrequency
