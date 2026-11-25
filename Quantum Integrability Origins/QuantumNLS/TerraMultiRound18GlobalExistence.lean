import QuantumNLS.TerraMultiRound18LocalGluing
import QuantumNLS.TerraMultiRound17D01Repair
import QuantumNLS.TerraMultiRound17NormPartial

/-! Construction of complete D01 trajectories by finite-horizon compact
confinement and overlap gluing. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open Set Metric Filter Topology
open QuantumNLS.D01LocalPrimitive
namespace QuantumNLS.TerraMultiRound18GlobalExistence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every finite symmetric time interval carries a trajectory through the
specified initial point. -/
theorem exists_on_interval (S : Hyp H) (u : H) (T : ℝ) (hT : 0 < T)
    (a : ℝ) (ha : a < T) :
    ∃ γ : ℝ → H, γ 0 = u ∧ ∀ t ∈ Ioo (-a) a, HasDerivAt γ (S.Y (γ t)) t := by
  classical
  let K := S.act ⁻¹' ((fun t : ℝ => Real.exp t • S.act u) '' Icc (-T) T)
  have hK : IsCompact K :=
    (QuantumNLS.TerraMultiRound15D01Partial.action_derivative_and_self_contraction S).2.2 u (-T) T
  have hu : u ∈ K := by
    refine ⟨0, ⟨by linarith, hT.le⟩, ?_⟩
    simp
  obtain ⟨r, hr, δ, hδ, hloc⟩ :=
    (QuantumNLS.TerraMultiRound17D01Repair.analytic_field_and_local_solutions S).2 K hK ⟨u, hu⟩ 0
  let U := {b : ℝ | b < T ∧ ∃ γ : ℝ → H, γ 0 = u ∧
    ∀ t ∈ Ioo (-b) b, HasDerivAt γ (S.Y (γ t)) t}
  let e := min δ T / 2
  have he : 0 < e := by dsimp [e]; positivity
  have heδ : e < δ := by dsimp [e]; linarith [min_le_left δ T]
  have heT : e < T := by dsimp [e]; linarith [min_le_right δ T]
  obtain ⟨γ₀, hγ₀0, hγ₀⟩ := hloc u hu u (mem_closedBall_self hr.le)
  have heU : e ∈ U := by
    refine ⟨heT, γ₀, hγ₀0, ?_⟩
    intro t ht
    exact hγ₀ t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hbound : BddAbove U := ⟨T, fun _ hb => hb.1.le⟩
  let A := sSup U
  have heA : e ≤ A := le_csSup hbound heU
  have hApos : 0 < A := lt_of_lt_of_le he heA
  have hAT : A ≤ T := csSup_le ⟨e, heU⟩ (fun _ hb => hb.1.le)
  have hATeq : A = T := by
    by_contra hne
    have hlt : A < T := lt_of_le_of_ne hAT hne
    let ε := min δ (min (T - A) A) / 2
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hεδ : ε < δ := by dsimp [ε]; linarith [min_le_left δ (min (T - A) A)]
    have hεgap : ε < T - A := by
      dsimp [ε]
      have h := (min_le_right δ (min (T - A) A)).trans (min_le_left (T - A) A)
      linarith
    have hεA : ε < A := by
      dsimp [ε]
      have h := (min_le_right δ (min (T - A) A)).trans (min_le_right (T - A) A)
      linarith
    obtain ⟨b, hbU, hbgt⟩ := Real.add_neg_lt_sSup (show U.Nonempty from ⟨e, heU⟩)
      (ε := -(ε / 2)) (by linarith)
    change A + -(ε / 2) < b at hbgt
    obtain ⟨hbT, γ, hγ0, hγ⟩ := hbU
    let t₀ := A - ε / 2
    have htpos : 0 < t₀ := by dsimp [t₀]; linarith
    have htb : t₀ < b := by dsimp [t₀]; linarith
    have hzero : (0 : ℝ) ∈ Ioo (-b) b := ⟨by linarith, by linarith⟩
    have hmem (t : ℝ) (ht : t ∈ Ioo (-b) b) (hseg : t ∈ Icc (-T) T) : γ t ∈ K := by
      refine ⟨t, hseg, ?_⟩
      have hh := (QuantumNLS.TerraMultiRound17NormPartial.action_and_mass_on_solution S hzero γ hγ t ht).1
      rw [hγ0] at hh
      exact hh.symm
    have hleft : γ (-t₀) ∈ K := hmem (-t₀) ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    have hright : γ t₀ ∈ K := hmem t₀ ⟨by linarith, htb⟩ ⟨by linarith, by linarith⟩
    obtain ⟨ηleft, hηleft0, hηleft⟩ := hloc (γ (-t₀)) hleft (γ (-t₀)) (mem_closedBall_self hr.le)
    obtain ⟨ηright, hηright0, hηright⟩ := hloc (γ t₀) hright (γ t₀) (mem_closedBall_self hr.le)
    let γleft := fun t => ηleft (t + t₀)
    let γright := fun t => ηright (t - t₀)
    have hminus : ∀ t ∈ Ioo (-t₀ - ε) (-t₀ + ε), HasDerivAt γleft (S.Y (γleft t)) t := by
      intro t ht
      have ht' : t + t₀ ∈ Ioo (0 - δ) (0 + δ) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      simpa [γleft, Function.comp_def] using (hηleft _ ht').scomp t ((hasDerivAt_id t).add_const t₀)
    have hplus : ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt γright (S.Y (γright t)) t := by
      intro t ht
      have ht' : t - t₀ ∈ Ioo (0 - δ) (0 + δ) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      simpa [γright, Function.comp_def] using (hηright _ ht').scomp t ((hasDerivAt_id t).sub_const t₀)
    let g₁ := (Ioo (-b) b).piecewise γ γleft
    have hg₁ : ∀ t ∈ Ioo (-(A + ε / 2)) b, HasDerivAt g₁ (S.Y (g₁ t)) t := by
      have hh := QuantumNLS.TerraMultiRound18LocalGluing.local_piecewise S hγ hminus
        (t₀ := -t₀) ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
        (by simpa [γleft] using hηleft0.symm)
      intro t ht
      apply hh t
      dsimp [t₀] at *
      exact Or.symm (Ioo_subset_Ioo_union_Ioo (by linarith) (by linarith) le_rfl ht)
    let g := (Ioo (-(A + ε / 2)) b).piecewise g₁ γright
    have hg : ∀ t ∈ Ioo (-(A + ε / 2)) (A + ε / 2), HasDerivAt g (S.Y (g t)) t := by
      have hh := QuantumNLS.TerraMultiRound18LocalGluing.local_piecewise S hg₁ hplus (t₀ := t₀)
        ⟨⟨by dsimp [t₀]; linarith, htb⟩, ⟨by linarith, by linarith⟩⟩ (by
          dsimp [g₁, γright]
          rw [piecewise_eq_of_mem _ _ _ (show t₀ ∈ Ioo (-b) b from ⟨by linarith, htb⟩)]
          simpa using hηright0.symm)
      intro t ht
      apply hh t
      dsimp [t₀] at *
      exact Ioo_subset_Ioo_union_Ioo le_rfl (by linarith) (by linarith) ht
    have hg0 : g 0 = u := by
      dsimp [g, g₁]
      rw [piecewise_eq_of_mem _ _ _ (show (0 : ℝ) ∈ Ioo (-(A + ε / 2)) b from
        ⟨by linarith, by linarith⟩), piecewise_eq_of_mem _ _ _ hzero]
      exact hγ0
    have hnew : A + ε / 2 ∈ U := ⟨by linarith, g, hg0, hg⟩
    have hle := le_csSup hbound hnew
    change A + ε / 2 ≤ A at hle
    linarith
  have haA : a < sSup U := by
    change a < A
    rw [hATeq]
    exact ha
  obtain ⟨b, hbU, hab⟩ := exists_lt_of_lt_csSup (show U.Nonempty from ⟨e, heU⟩) haA
  obtain ⟨_, γ, hγ0, hγ⟩ := hbU
  exact ⟨γ, hγ0, fun t ht => hγ t ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩

/-- Global existence, obtained by compatible finite-horizon solutions. -/
theorem exists_global (S : Hyp H) (u : H) :
    ∃ γ : ℝ → H, γ 0 = u ∧ ∀ t, HasDerivAt γ (S.Y (γ t)) t := by
  classical
  have hex (a : ℝ) : ∃ γ : ℝ → H, γ 0 = u ∧
      ∀ t ∈ Ioo (-a) a, HasDerivAt γ (S.Y (γ t)) t :=
    exists_on_interval S u (|a| + 1) (by positivity) a (by linarith [le_abs_self a])
  choose γ hγ0 hγ using hex
  let g := fun t => γ (|t| + 1) t
  have heq (a : ℝ) : EqOn g (γ a) (Ioo (-a) a) := by
    intro t ht
    let r := min a (|t| + 1)
    have hr : |t| < r := lt_min (abs_lt.mpr ht) (lt_add_one _)
    have h0 : (0 : ℝ) ∈ Ioo (-r) r := by constructor <;> linarith [abs_nonneg t]
    exact QuantumNLS.TerraMultiRound18LocalUniqueness.local_unique S
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
  exact (hγ _ t ht).congr_of_eventuallyEq hh

#print axioms exists_on_interval
#print axioms exists_global
end QuantumNLS.TerraMultiRound18GlobalExistence
