import QuantumNLS.Ext025A2ODE

/-! Global continuation from constructed uniform local trajectories in an
invariant set. Completeness or compactness of that set is not assumed.
The application must construct the local trajectories; it may not assume
its requested global flow as an input. -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped NNReal
namespace QuantumNLS.Ext025A8
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def SolOn (f : E → E) (K : Set E) (γ : ℝ → E) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivAt γ (f (γ t)) t ∧ γ t ∈ K

theorem solOn_unique {f : E → E} {K : Set E} {L : ℝ≥0}
    (hL : LipschitzOnWith L f K) {γ η : ℝ → E} {a b t₀ : ℝ}
    (hγ : SolOn f K γ (Ioo a b)) (hη : SolOn f K η (Ioo a b))
    (ht₀ : t₀ ∈ Ioo a b) (heq : γ t₀ = η t₀) : EqOn γ η (Ioo a b) :=
  ODE_solution_unique_of_mem_Ioo (fun _ _ => hL) ht₀ hγ hη heq

theorem solOn_piecewise {f : E → E} {K : Set E} {L : ℝ≥0}
    (hL : LipschitzOnWith L f K) {γ η : ℝ → E} {a b c d t₀ : ℝ}
    (hγ : SolOn f K γ (Ioo a b)) (hη : SolOn f K η (Ioo c d))
    (ht₀ : t₀ ∈ Ioo a b ∩ Ioo c d) (heq : γ t₀ = η t₀) :
    SolOn f K ((Ioo a b).piecewise γ η) (Ioo a b ∪ Ioo c d) := by
  classical
  have hu : EqOn γ η (Ioo (max a c) (min b d)) := solOn_unique hL
    (fun t ht => hγ t ⟨(le_max_left _ _).trans_lt ht.1,
      ht.2.trans_le (min_le_left _ _)⟩)
    (fun t ht => hη t ⟨(le_max_right _ _).trans_lt ht.1,
      ht.2.trans_le (min_le_right _ _)⟩)
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
    exact ⟨(hγ t hm).1.congr_of_eventuallyEq hh, (hγ t hm).2⟩
  · have ht' : t ∈ Ioo c d := ht.resolve_left hm
    have hh : (Ioo a b).piecewise γ η =ᶠ[𝓝 t] η := by
      filter_upwards [isOpen_Ioo.mem_nhds ht'] with s hs
      exact hp hs
    have hval := hh.self_of_nhds
    rw [hval]
    exact ⟨(hη t ht').1.congr_of_eventuallyEq hh, (hη t ht').2⟩

theorem uniform_invariant_global {f : E → E} {K : Set E} {L : ℝ≥0}
    (hL : LipschitzOnWith L f K) {ε : ℝ} (hε : 0 < ε)
    (hloc : ∀ x ∈ K, ∃ γ : ℝ → E, γ 0 = x ∧ SolOn f K γ (Ioo (-ε) ε))
    {x : E} (hx : x ∈ K) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t, HasDerivAt γ (f (γ t)) t ∧ γ t ∈ K := by
  classical
  let S := {a : ℝ | ∃ γ : ℝ → E, γ 0 = x ∧ SolOn f K γ (Ioo (-a) a)}
  have hS : ε ∈ S := hloc x hx
  have hunbdd : ¬ BddAbove S := by
    intro hbdd
    let A := sSup S
    have hA : ε ≤ A := le_csSup hbdd hS
    obtain ⟨a, ⟨γ, hγ0, hγ⟩, hlt⟩ :=
      Real.add_neg_lt_sSup (show S.Nonempty from ⟨ε, hS⟩)
        (ε := -(ε / 2)) (by linarith)
    change A + -(ε / 2) < a at hlt
    let t₀ := A - ε / 2
    have htpos : 0 < t₀ := by dsimp [t₀]; linarith
    have hta : t₀ < a := by dsimp [t₀]; linarith
    obtain ⟨ηleft, hηleft0, hηleft⟩ := hloc (γ (-t₀)) (hγ (-t₀) ⟨by linarith, by linarith⟩).2
    obtain ⟨ηright, hηright0, hηright⟩ := hloc (γ t₀) (hγ t₀ ⟨by linarith, hta⟩).2
    let γleft := fun t => ηleft (t + t₀)
    let γright := fun t => ηright (t - t₀)
    have hminus : SolOn f K γleft (Ioo (-t₀ - ε) (-t₀ + ε)) := by
      intro t ht
      have ht' : t + t₀ ∈ Ioo (-ε) ε := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      refine ⟨?_, (hηleft _ ht').2⟩
      simpa [γleft, Function.comp_def] using (hηleft _ ht').1.scomp t ((hasDerivAt_id t).add_const t₀)
    have hplus : SolOn f K γright (Ioo (t₀ - ε) (t₀ + ε)) := by
      intro t ht
      have ht' : t - t₀ ∈ Ioo (-ε) ε := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      refine ⟨?_, (hηright _ ht').2⟩
      simpa [γright, Function.comp_def] using (hηright _ ht').1.scomp t ((hasDerivAt_id t).sub_const t₀)
    let g₁ := (Ioo (-a) a).piecewise γ γleft
    have hg₁ : SolOn f K g₁ (Ioo (-(A + ε / 2)) a) := by
      have hh := solOn_piecewise hL hγ hminus
        (t₀ := -t₀) ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
        (by simpa [γleft] using hηleft0.symm)
      intro t ht
      apply hh t
      dsimp [t₀] at *
      exact Or.symm (Ioo_subset_Ioo_union_Ioo (by linarith) (by linarith) le_rfl ht)
    let g := (Ioo (-(A + ε / 2)) a).piecewise g₁ γright
    have hg : SolOn f K g (Ioo (-(A + ε / 2)) (A + ε / 2)) := by
      have hh := solOn_piecewise hL hg₁ hplus (t₀ := t₀)
        ⟨⟨by dsimp [t₀]; linarith, hta⟩, ⟨by linarith, by linarith⟩⟩ (by
          dsimp [g₁, γright]
          rw [piecewise_eq_of_mem _ _ _ (show t₀ ∈ Ioo (-a) a from ⟨by linarith, hta⟩)]
          simpa using hηright0.symm)
      intro t ht
      apply hh t
      dsimp [t₀] at *
      exact Ioo_subset_Ioo_union_Ioo le_rfl (by linarith) (by linarith) ht
    have hg0 : g 0 = x := by
      dsimp [g, g₁]
      rw [piecewise_eq_of_mem _ _ _ (show (0 : ℝ) ∈ Ioo (-(A + ε / 2)) a from
        ⟨by linarith, by linarith⟩),
        piecewise_eq_of_mem _ _ _ (show (0 : ℝ) ∈ Ioo (-a) a from ⟨by linarith, by linarith⟩)]
      exact hγ0
    have hmem : A + ε / 2 ∈ S := ⟨g, hg0, hg⟩
    have hle := le_csSup hbdd hmem
    change A + ε / 2 ≤ A at hle
    linarith
  have hex (a : ℝ) : ∃ γ : ℝ → E, γ 0 = x ∧ SolOn f K γ (Ioo (-a) a) := by
    obtain ⟨b, ⟨γ, hγ0, hγ⟩, hab⟩ := not_bddAbove_iff.mp hunbdd a
    exact ⟨γ, hγ0, fun t ht => hγ t ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  choose γ hγ0 hγ using hex
  let g := fun t => γ (|t| + 1) t
  have heq (a : ℝ) : EqOn g (γ a) (Ioo (-a) a) := by
    intro t ht
    let r := min a (|t| + 1)
    have hr : |t| < r := lt_min (abs_lt.mpr ht) (lt_add_one _)
    have h0 : (0 : ℝ) ∈ Ioo (-r) r := by constructor <;> linarith [abs_nonneg t]
    exact solOn_unique hL
      (fun s hs => hγ (|t| + 1) s
        ⟨(neg_le_neg (min_le_right a (|t| + 1))).trans_lt hs.1,
          hs.2.trans_le (min_le_right a (|t| + 1))⟩)
      (fun s hs => hγ a s
        ⟨(neg_le_neg (min_le_left a (|t| + 1))).trans_lt hs.1,
          hs.2.trans_le (min_le_left a (|t| + 1))⟩)
      h0 (by rw [hγ0, hγ0]) (abs_lt.mp hr)
  refine ⟨g, by simpa [g] using hγ0 (|0| + 1), fun t => ?_⟩
  have ht : t ∈ Ioo (-(|t| + 1)) (|t| + 1) := abs_lt.mp (lt_add_one _)
  have hh : g =ᶠ[𝓝 t] γ (|t| + 1) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact heq (|t| + 1) hs
  have hval := hh.self_of_nhds
  rw [hval]
  exact ⟨(hγ _ t ht).1.congr_of_eventuallyEq hh, (hγ _ t ht).2⟩
end QuantumNLS.Ext025A8

#print axioms QuantumNLS.Ext025A8.SolOn
#print axioms QuantumNLS.Ext025A8.solOn_unique
#print axioms QuantumNLS.Ext025A8.solOn_piecewise
#print axioms QuantumNLS.Ext025A8.uniform_invariant_global
