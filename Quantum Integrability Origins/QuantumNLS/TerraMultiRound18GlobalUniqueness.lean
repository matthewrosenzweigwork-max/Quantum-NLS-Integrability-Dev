import QuantumNLS.TerraMultiRound17NormPartial
import QuantumNLS.TerraMultiRound17CompactPartial

/-! Uniqueness and action identities for any global integral curves of the
actual D01 field. This module does not claim that such curves exist. -/
set_option autoImplicit false
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open Set
open QuantumNLS.D01LocalPrimitive
namespace QuantumNLS.TerraMultiRound18GlobalUniqueness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Any two global integral curves meeting at one time coincide. -/
theorem global_unique (S : Hyp H) {α β : ℝ → H}
    (hα : ∀ t, HasDerivAt α (S.Y (α t)) t)
    (hβ : ∀ t, HasDerivAt β (S.Y (β t)) t)
    {t₀ : ℝ} (heq : α t₀ = β t₀) : α = β := by
  ext t
  let a := min t t₀ - 1
  let b := max t t₀ + 1
  have ht : t ∈ Ioo a b := ⟨by dsimp [a]; linarith [min_le_left t t₀],
    by dsimp [b]; linarith [le_max_left t t₀]⟩
  have ht₀ : t₀ ∈ Ioo a b := ⟨by dsimp [a]; linarith [min_le_right t t₀],
    by dsimp [b]; linarith [le_max_right t t₀]⟩
  let K := α '' Icc a b ∪ β '' Icc a b
  have hcα : Continuous α := continuous_iff_continuousAt.mpr fun s => (hα s).continuousAt
  have hcβ : Continuous β := continuous_iff_continuousAt.mpr fun s => (hβ s).continuousAt
  have hK : IsCompact K := (isCompact_Icc.image hcα).union (isCompact_Icc.image hcβ)
  obtain ⟨L, hL⟩ := QuantumNLS.TerraMultiRound17CompactPartial.field_lipschitz_on_compact S hK
  have hαK : ∀ s ∈ Ioo a b, HasDerivAt α (S.Y (α s)) s ∧ α s ∈ K := by
    intro s hs
    exact ⟨hα s, Or.inl ⟨s, ⟨hs.1.le, hs.2.le⟩, rfl⟩⟩
  have hβK : ∀ s ∈ Ioo a b, HasDerivAt β (S.Y (β s)) s ∧ β s ∈ K := by
    intro s hs
    exact ⟨hβ s, Or.inr ⟨s, ⟨hs.1.le, hs.2.le⟩, rfl⟩⟩
  exact ODE_solution_unique_of_mem_Ioo (v := fun _ => S.Y) (s := fun _ => K)
    (fun _ _ => hL) ht₀ hαK hβK heq ht

/-- The action sequence and mass of any global integral curve evolve exponentially. -/
theorem global_action_and_mass (S : Hyp H) (u : ℝ → H)
    (hu : ∀ t, HasDerivAt u (S.Y (u t)) t) (t : ℝ) :
    S.act (u t) = Real.exp t • S.act (u 0) ∧
      ‖u t‖ ^ 2 = Real.exp t * ‖u 0‖ ^ 2 := by
  apply QuantumNLS.TerraMultiRound17NormPartial.action_and_mass_on_solution S
    (a := min 0 t - 1) (b := max 0 t + 1) ?_ u (fun s _ => hu s) t ?_
  · exact ⟨by linarith [min_le_left (0 : ℝ) t], by linarith [le_max_left (0 : ℝ) t]⟩
  · exact ⟨by linarith [min_le_right (0 : ℝ) t], by linarith [le_max_right (0 : ℝ) t]⟩

#print axioms global_unique
#print axioms global_action_and_mass
end QuantumNLS.TerraMultiRound18GlobalUniqueness
