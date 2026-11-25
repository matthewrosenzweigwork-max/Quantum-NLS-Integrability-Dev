import QuantumNLS.TerraMultiRound86Chart
import QuantumNLS.TerraMultiRound86BoostActionsAll
import QuantumNLS.TerraMultiRound86ReflectionActionsAll
import QuantumNLS.TerraMultiRound86ScalingActionsAll
import QuantumNLS.TerraMultiRound85InvariantFrequency
import QuantumNLS.TerraMultiRound85RotationUniqueness

/-! Frequency covariance, using the accepted physical-dynamics theorem at each coupling. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped ComplexConjugate
namespace QuantumNLS.TerraMultiRound86Assembly
open QuantumNLS.TerraMultiRound86Chart
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.GlobalCompatR47a QuantumNLS.L2Flow QuantumNLS.ActionTorus
open QuantumNLS.TerraMultiRound85DynamicsInput QuantumNLS.TerraMultiRound85RotationUniqueness
open QuantumNLS.TerraMultiRound86BoostActionsAll QuantumNLS.TerraMultiRound86ReflectionActionsAll
open QuantumNLS.TerraMultiRound86ScalingActionsAll QuantumNLS.TerraMultiRound85InvariantFrequency
variable {L : ℝ} [Fact (0 < L)] {d CL : ℝ}
variable {Φl : ℝ → L2T L → QuantumNLS.D01LocalPrimitive.K}
variable {Ψl : ℝ → QuantumNLS.D01LocalPrimitive.K → L2T L}
variable {Φ : ℝ → L2T L → QuantumNLS.D01LocalPrimitive.K}
variable {Ψ : ℝ → QuantumNLS.D01LocalPrimitive.K → L2T L}

theorem global_frequency_covariance
    (family : ∀ q (hq : 0 < q), Extension q hq d (Φl q) (Ψl q) (Φ q) (Ψ q))
    (hc : Compatibility d CL Φ Ψ) :
    ∃ ν : ∀ q : ℝ, 0 < q → ℤ → PosL1 → ℝ,
      (∀ (q : ℝ) (hq : 0 < q), Rotates (Φ := Φ) hq (ν q hq)) ∧
      (∀ (q : ℝ) (hq : 0 < q) (u : L2T L) t n, (QuantumNLS.RootIndexedMasses.masses hq u).1 n = 0 →
        Φ q (flowMap hq.le u t) n = 0) ∧
      (∀ (q : ℝ) (hq : 0 < q) (a b : PosL1) (n k : ℤ), (∀ j, b.1 j = a.1 (j-k)) → 0 < a.1 (n-k) →
        ν q hq n b = ν q hq (n-k) a + (QuantumNLS.LocalSpectral.pm L n)^2 -
          (QuantumNLS.LocalSpectral.pm L (n-k))^2) ∧
      (∀ (q : ℝ) (hq : 0 < q) (a b : PosL1) (n : ℤ), (∀ j, b.1 j = a.1 (-j)) → 0 < a.1 (-n) →
        ν q hq n b = ν q hq (-n) a) ∧
      (∀ (q : ℝ) (hq : 0 < q) (u : L2T L) n,
        (QuantumNLS.RootIndexedMasses.masses hq (star u)).1 n =
          (QuantumNLS.RootIndexedMasses.masses hq u).1 (-n)) ∧
      (∀ (q : ℝ) (hq : 0 < q) s (hs : 0 < s) (a : PosL1) n, 0 < a.1 n →
        ν q hq n (scaleAction s a) = ν (q*s^2) (mul_pos hq (sq_pos_of_pos hs)) n a) ∧
      (∀ (q : ℝ) (hq : 0 < q) (u : L2T L) (γ y : ℝ) (n : ℤ),
        QuantumNLS.RootIndexedMasses.masses hq (Complex.exp ((γ : ℂ) * Complex.I) • u) =
          QuantumNLS.RootIndexedMasses.masses hq u ∧
        QuantumNLS.RootIndexedMasses.masses hq (QuantumNLS.BornTranslation.trans y u) =
          QuantumNLS.RootIndexedMasses.masses hq u ∧
        ν q hq n (QuantumNLS.RootIndexedMasses.masses hq (Complex.exp ((γ : ℂ) * Complex.I) • u)) =
          ν q hq n (QuantumNLS.RootIndexedMasses.masses hq u) ∧
        ν q hq n (QuantumNLS.RootIndexedMasses.masses hq (QuantumNLS.BornTranslation.trans y u)) =
          ν q hq n (QuantumNLS.RootIndexedMasses.masses hq u)) := by
  let ν : ∀ q : ℝ, 0 < q → ℤ → PosL1 → ℝ := fun q hq =>
    Classical.choose (QuantumNLS.REF88Final.global_physical_dynamics hq (chart_of_extension (family q hq) hc)).1
  have hr : ∀ (q : ℝ) (hq : 0 < q), Rotates (Φ := Φ) hq (ν q hq) := by
    intro q hq
    exact (Classical.choose_spec (QuantumNLS.REF88Final.global_physical_dynamics hq (chart_of_extension (family q hq) hc)).1).1
  refine ⟨ν, hr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq u t n hz
    exact (Classical.choose_spec (QuantumNLS.REF88Final.global_physical_dynamics hq (chart_of_extension (family q hq) hc)).1).2.1 u t n hz
  · intro q hq a b n k hb ha
    obtain ⟨μ, hm, hf⟩ := boost_frequency_all_intermediate hq (family q hq) hc
    have hbactive : 0 < b.1 n := by rw [hb n]; exact ha
    have h1 := active_rotation_unique hq (family q hq) (ν q hq) μ (hr q hq) hm b n hbactive
    have h2 := active_rotation_unique hq (family q hq) (ν q hq) μ (hr q hq) hm a (n-k) ha
    rw [h1, h2]
    exact hf a b n k hb ha
  · intro q hq a b n hb ha
    obtain ⟨μ, hm, hf⟩ := reflection_frequency_all_intermediate hq (family q hq) hc
    have hbactive : 0 < b.1 n := by rw [hb n]; exact ha
    have h1 := active_rotation_unique hq (family q hq) (ν q hq) μ (hr q hq) hm b n hbactive
    have h2 := active_rotation_unique hq (family q hq) (ν q hq) μ (hr q hq) hm a (-n) ha
    rw [h1, h2]
    exact hf a b n hb ha
  · intro q hq u n
    rw [← (family q hq).moduli, ((hc.1 q hq).1 u n).2.2.2.2]
    simpa using ((family q hq).moduli u (-n))
  · intro q hq s hs a n ha
    let hq' : 0 < q*s^2 := mul_pos hq (sq_pos_of_pos hs)
    obtain ⟨μ, μ', hm, hm', hf⟩ := frequency_scaling_all_intermediate hq s hs (family q hq) (family (q*s^2) hq') hc
    have hscaled : 0 < (scaleAction s a).1 n := by
      change 0 < s^2 * a.1 n
      exact mul_pos (sq_pos_of_pos hs) ha
    have h1 := active_rotation_unique hq (family q hq) (ν q hq) μ (hr q hq) hm (scaleAction s a) n hscaled
    have h2 := active_rotation_unique hq' (family (q*s^2) hq') (ν (q*s^2) hq') μ' (hr (q*s^2) hq') hm' a n ha
    rw [h1, h2]
    exact hf a n ha
  · intro q hq u γ y n
    refine ⟨phase_mass_vector hq (family q hq) hc u γ, translation_mass_vector hq (family q hq) hc u y, ?_⟩
    exact phase_translation_frequency hq (family q hq) hc (ν q hq) u γ y n

#print axioms global_frequency_covariance
end QuantumNLS.TerraMultiRound86Assembly
