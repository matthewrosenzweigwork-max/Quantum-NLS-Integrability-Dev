import QuantumNLS.TerraMultiRound18LocalUniqueness

/-! Local trajectories of the D01 field can be glued on overlapping open
intervals, without an invariant compact set. -/
set_option autoImplicit false
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open Set Filter Topology
open QuantumNLS.D01LocalPrimitive
namespace QuantumNLS.TerraMultiRound18LocalGluing

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem local_piecewise (S : Hyp H) {γ η : ℝ → H} {a b c d t₀ : ℝ}
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (S.Y (γ t)) t)
    (hη : ∀ t ∈ Ioo c d, HasDerivAt η (S.Y (η t)) t)
    (ht₀ : t₀ ∈ Ioo a b ∩ Ioo c d) (heq : γ t₀ = η t₀) :
    ∀ t ∈ Ioo a b ∪ Ioo c d,
      HasDerivAt ((Ioo a b).piecewise γ η) (S.Y (((Ioo a b).piecewise γ η) t)) t := by
  classical
  have hu : EqOn γ η (Ioo (max a c) (min b d)) :=
    QuantumNLS.TerraMultiRound18LocalUniqueness.local_unique S
      (fun t ht => hγ t ⟨(le_max_left _ _).trans_lt ht.1, ht.2.trans_le (min_le_left _ _)⟩)
      (fun t ht => hη t ⟨(le_max_right _ _).trans_lt ht.1, ht.2.trans_le (min_le_right _ _)⟩)
      ⟨max_lt ht₀.1.1 ht₀.2.1, lt_min ht₀.1.2 ht₀.2.2⟩ heq
  have hp : EqOn ((Ioo a b).piecewise γ η) η (Ioo c d) := by
    intro t ht
    by_cases hm : t ∈ Ioo a b
    · rw [piecewise_eq_of_mem _ _ _ hm]
      exact hu ⟨max_lt hm.1 ht.1, lt_min hm.2 ht.2⟩
    · exact piecewise_eq_of_notMem _ _ _ hm
  intro t ht
  by_cases hm : t ∈ Ioo a b
  · have hh : (Ioo a b).piecewise γ η =ᶠ[𝓝 t] γ := by
      filter_upwards [isOpen_Ioo.mem_nhds hm] with s hs
      exact piecewise_eq_of_mem _ _ _ hs
    have hval := hh.self_of_nhds
    rw [hval]
    exact (hγ t hm).congr_of_eventuallyEq hh
  · have ht' : t ∈ Ioo c d := ht.resolve_left hm
    have hh : (Ioo a b).piecewise γ η =ᶠ[𝓝 t] η := by
      filter_upwards [isOpen_Ioo.mem_nhds ht'] with s hs
      exact hp hs
    have hval := hh.self_of_nhds
    rw [hval]
    exact (hη t ht').congr_of_eventuallyEq hh

#print axioms local_piecewise
end QuantumNLS.TerraMultiRound18LocalGluing
