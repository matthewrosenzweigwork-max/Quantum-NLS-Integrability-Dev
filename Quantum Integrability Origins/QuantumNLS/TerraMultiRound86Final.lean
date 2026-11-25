import QuantumNLS.TerraMultiRound86Assembly
import QuantumNLS.RC05FreqCov

/-! R-877E839C: the printed frequency covariance, including the explicit
conjugation clause, for every physical rotation witness. The only inputs
below are the established global chart/compatibility context. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open scoped ComplexConjugate
namespace QuantumNLS.TerraMultiRound86Final
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.D01LocalPrimitive (K)
open QuantumNLS.ActionTorus (PosL1)
open QuantumNLS.GlobalCompatR47a
open QuantumNLS.RC05Statement
open QuantumNLS.TerraMultiRound85RotationUniqueness
open QuantumNLS.TerraMultiRound86ScalingActionsAll (scaleAction)
variable {L : ℝ} [Fact (0 < L)] {d CL : ℝ}
variable {Φl : ℝ → L2T L → K} {Ψl : ℝ → K → L2T L}
variable {Φ : ℝ → L2T L → K} {Ψ : ℝ → K → L2T L}

theorem covariance_of_rotation
    (family : Family d Φl Ψl Φ Ψ) (hc : Compatibility d CL Φ Ψ)
    (ν : ℝ → ℤ → PosL1 → ℝ)
    (hrot : ∀ (q : ℝ) (hq : 0 < q), PhysicalFrequency hq (Φ := Φ q) (ν q)) :
    FreqCovClauses L ν := by
  obtain ⟨μ, hμ, hz, hb, hr, hconj, hs, hinv⟩ :=
    QuantumNLS.TerraMultiRound86Assembly.global_frequency_covariance family hc
  have heq (q : ℝ) (hq : 0 < q) (a : PosL1) (n : ℤ) (ha : 0 < a.1 n) :
      ν q n a = μ q hq n a :=
    active_rotation_unique hq (family q hq) (ν q) (μ q hq) (hrot q hq) (hμ q hq) a n ha
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q hq k a b hab n hn
    have ha : 0 < a.1 (n-k) := by rw [← hab n]; exact hn
    rw [heq q hq b n hn, heq q hq a (n-k) ha]
    exact hb q hq a b n k hab ha
  · intro q hq a b hab n hn
    have ha : 0 < a.1 (-n) := by rw [← hab n]; exact hn
    rw [heq q hq b n hn, heq q hq a (-n) ha]
    exact hr q hq a b n hab ha
  · intro q hq s hpos a b hab n ha
    have hba : b = scaleAction s a := by
      apply Subtype.ext
      apply lp.ext
      funext j
      exact hab j
    subst b
    have hactive : 0 < (scaleAction s a).1 n := by
      change 0 < s^2 * a.1 n
      exact mul_pos (sq_pos_of_pos hpos) ha
    rw [heq q hq (scaleAction s a) n hactive,
      heq (q*s^2) (mul_pos hq (sq_pos_of_pos hpos)) a n ha]
    exact hs q hq s hpos a n ha
  · intro q hq u
    refine ⟨hconj q hq u, ?_⟩
    intro n hn
    have ha : 0 < (QuantumNLS.RootIndexedMasses.masses hq u).1 (-n) := by
      rw [← hconj q hq u n]; exact hn
    rw [heq q hq (QuantumNLS.RootIndexedMasses.masses hq (star u)) n hn,
      heq q hq (QuantumNLS.RootIndexedMasses.masses hq u) (-n) ha]
    exact hr q hq _ _ n (hconj q hq u) ha
  · intro q hq u γ y
    obtain ⟨hphase, htrans, -, -⟩ := hinv q hq u γ y 0
    exact ⟨hphase, htrans, fun n => congrArg (ν q n) hphase, fun n => congrArg (ν q n) htrans⟩

/-- The corollary in the exact printed-clauses interface used by the
full-transform theorem, with no physical-dynamics predecessor hypothesis. -/
theorem global_frequency_covariance : QuantumNLS.RC05FreqCov.FreqCovCorollary := by
  intro L inst
  letI : Fact (0 < L) := inst
  obtain ⟨d, CL, hd, hCL, Φl, Ψl, hl, hex, hcompat⟩ := global_compatibility L
  refine ⟨d, CL, hd, hCL, Φl, Ψl, hl, hex, ?_⟩
  intro Φ Ψ hf
  obtain ⟨μ, hμ, -⟩ := QuantumNLS.TerraMultiRound86Assembly.global_frequency_covariance hf (hcompat Φ Ψ hf)
  let ν : ℝ → ℤ → PosL1 → ℝ := fun q => if hq : 0 < q then μ q hq else 0
  have hrot : ∀ (q : ℝ) (hq : 0 < q), PhysicalFrequency hq (Φ := Φ q) (ν q) := by
    intro q hq
    change Rotates (Φ := Φ) hq (ν q)
    simpa [ν, hq] using hμ q hq
  exact ⟨ν, hrot, covariance_of_rotation hf (hcompat Φ Ψ hf) ν hrot⟩

#print axioms covariance_of_rotation
#print axioms global_frequency_covariance
end QuantumNLS.TerraMultiRound86Final
