import QuantumNLS.TerraMultiRound17CompactPartial

/-! Uniqueness of local D01 trajectories on an open interval. -/
set_option autoImplicit false
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open Set
open QuantumNLS.D01LocalPrimitive
namespace QuantumNLS.TerraMultiRound18LocalUniqueness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem local_unique (S : Hyp H) {a b t₀ : ℝ} {α β : ℝ → H}
    (hα : ∀ t ∈ Ioo a b, HasDerivAt α (S.Y (α t)) t)
    (hβ : ∀ t ∈ Ioo a b, HasDerivAt β (S.Y (β t)) t)
    (ht₀ : t₀ ∈ Ioo a b) (heq : α t₀ = β t₀) : EqOn α β (Ioo a b) := by
  intro t ht
  let c := (a + min t t₀) / 2
  let d := (b + max t t₀) / 2
  have hc : a < c := by dsimp [c]; linarith [lt_min ht.1 ht₀.1]
  have hd : d < b := by dsimp [d]; linarith [max_lt ht.2 ht₀.2]
  have htc : t ∈ Ioo c d := ⟨by dsimp [c]; linarith [ht.1, min_le_left t t₀],
    by dsimp [d]; linarith [ht.2, le_max_left t t₀]⟩
  have ht₀c : t₀ ∈ Ioo c d := ⟨by dsimp [c]; linarith [ht₀.1, min_le_right t t₀],
    by dsimp [d]; linarith [ht₀.2, le_max_right t t₀]⟩
  have hsub : Icc c d ⊆ Ioo a b := fun _ hs => ⟨lt_of_lt_of_le hc hs.1, lt_of_le_of_lt hs.2 hd⟩
  let K := α '' Icc c d ∪ β '' Icc c d
  have hcα : ContinuousOn α (Icc c d) := HasDerivAt.continuousOn fun s hs => hα s (hsub hs)
  have hcβ : ContinuousOn β (Icc c d) := HasDerivAt.continuousOn fun s hs => hβ s (hsub hs)
  have hK : IsCompact K := (isCompact_Icc.image_of_continuousOn hcα).union
    (isCompact_Icc.image_of_continuousOn hcβ)
  obtain ⟨L, hL⟩ := QuantumNLS.TerraMultiRound17CompactPartial.field_lipschitz_on_compact S hK
  have hαK : ∀ s ∈ Ioo c d, HasDerivAt α (S.Y (α s)) s ∧ α s ∈ K := by
    intro s hs
    exact ⟨hα s (hsub ⟨hs.1.le, hs.2.le⟩), Or.inl ⟨s, ⟨hs.1.le, hs.2.le⟩, rfl⟩⟩
  have hβK : ∀ s ∈ Ioo c d, HasDerivAt β (S.Y (β s)) s ∧ β s ∈ K := by
    intro s hs
    exact ⟨hβ s (hsub ⟨hs.1.le, hs.2.le⟩), Or.inr ⟨s, ⟨hs.1.le, hs.2.le⟩, rfl⟩⟩
  exact ODE_solution_unique_of_mem_Ioo (v := fun _ => S.Y) (s := fun _ => K)
    (fun _ _ => hL) ht₀c hαK hβK heq htc

#print axioms local_unique
end QuantumNLS.TerraMultiRound18LocalUniqueness
