import NlsGge.GK38.Lib.WeaklyAnalytic
import NlsGge.GK38.Lib.HilbertValuedAnalytic

/-!
# Removable analytic singularities along subvarieties (library piece L3c of campaign E01)

Grébert–Kappeler book, Appendix A, Theorem A.6 (GKP Theorem 19.5).  Let `V₁, …, V_m` be analytic
subvarieties of an open subset `U` of a complex normed space `E` (locally the zero set of an
analytic map into some `ℂ^k`).  If `f : U → ℂ` is analytic on `U ∖ (V₁ ∪ … ∪ V_m)`, continuous on
`U`, and analytic on every complex disc contained in some `V_i`, then `f` is analytic on `U`.

Proof (as in the book): restricted to a line `ζ ↦ x + ζ h`, each defining map `φ_i` either
vanishes identically near `ζ = 0` (the disc lies in `V_i`, and the disc hypothesis applies) or has
an isolated zero at `0`; if none vanishes identically, the line meets `⋃ V_i` only at `ζ = 0`
near `0`, so the one-variable removable singularity theorem gives analyticity at `0`.  Hence `f`
is weakly analytic, and continuous hence locally bounded, so L3a
(`analyticOnNhd_of_weak_of_locBdd`) applies.

Uses of this piece (book Lemma 15.2, `β^n_m`): TWO subvarieties `Z_m = {γ_m² = 0}` and
`E_m = {Δ(µ_m) = 2(-1)^m}`, see `analyticOnNhd_of_continuous_of_analytic_off_two_zeros`; and one
subvariety `Z_n` for `z_n^±` and `I_n/γ_n²` (Thm 13.3, Prop 16.5), see
`analyticOnNhd_of_continuous_of_analytic_off_zero`.

No completeness of `E` is needed.  Local re-proof from Mathlib (E01-D8).
-/

set_option autoImplicit false

open Metric Set Filter Topology

namespace NlsGge.GK38.Lib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

section Defs

/-- `V` is an analytic subvariety of `U` (book Appendix A, before Thm A.6): around every point of
`U` there is a ball on which `V` is the zero set of an analytic map into some `ℂ^k`. -/
def IsAnalyticSubvariety (U V : Set E) : Prop :=
  ∀ x ∈ U, ∃ r > 0, ∃ (k : ℕ) (φ : E → Fin k → ℂ),
    AnalyticOnNhd ℂ φ (ball x r) ∧ ∀ y ∈ ball x r, (y ∈ V ↔ φ y = 0)

/-- The zero set of an analytic `ℂ^k`-valued map on an open set is an analytic subvariety. -/
theorem IsAnalyticSubvariety.of_vector {U : Set E} {k : ℕ} {φ : E → Fin k → ℂ}
    (hU : IsOpen U) (hφ : AnalyticOnNhd ℂ φ U) : IsAnalyticSubvariety U {x | φ x = 0} := by
  intro x hx
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx
  exact ⟨r, hr, k, φ, hφ.mono hrU, fun y _ => Iff.rfl⟩

/-- The zero set of an analytic scalar function on an open set is an analytic subvariety. -/
theorem IsAnalyticSubvariety.of_scalar {U : Set E} {g : E → ℂ}
    (hU : IsOpen U) (hg : AnalyticOnNhd ℂ g U) : IsAnalyticSubvariety U {x | g x = 0} := by
  intro x hx
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx
  refine ⟨r, hr, 1, fun y _ => g y, ?_, fun y _ => ?_⟩
  · intro y hy
    let L : ℂ →L[ℂ] (Fin 1 → ℂ) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℂ ℂ
    exact (L.analyticAt (g y)).comp (hg y (hrU hy))
  · simp [funext_iff]

end Defs

section Main

variable {U : Set E} {f : E → ℂ}

/-- The affine line `ζ ↦ x + ζ • h` is analytic. -/
private theorem analyticAt_line (x h : E) (ζ : ℂ) : AnalyticAt ℂ (fun ζ : ℂ => x + ζ • h) ζ := by
  fun_prop

/-- Key one-variable step: under the hypotheses of Thm A.6, `f` is analytic along every line. -/
private theorem analyticAt_line_of_off_subvarieties {ι : Type*} [Finite ι] {V : ι → Set E}
    (hU : IsOpen U) (hV : ∀ i, IsAnalyticSubvariety U (V i)) (hcont : ContinuousOn f U)
    (hoff : AnalyticOnNhd ℂ f (U \ ⋃ i, V i))
    (hdisc : ∀ i, ∀ x ∈ U, ∀ h : E, ∀ r > 0,
      (∀ ζ : ℂ, ‖ζ‖ < r → x + ζ • h ∈ V i ∩ U) →
        AnalyticAt ℂ (fun ζ : ℂ => f (x + ζ • h)) 0)
    {x : E} (hx : x ∈ U) (h : E) : AnalyticAt ℂ (fun ζ : ℂ => f (x + ζ • h)) 0 := by
  have hline : Continuous (fun ζ : ℂ => x + ζ • h) := by fun_prop
  have h0 : x + (0 : ℂ) • h = x := by simp
  choose r hr k φ hφ hiff using fun i => hV i x hx
  -- the line stays in the local balls and in `U`
  have hball : ∀ i, ∀ᶠ ζ in 𝓝 (0 : ℂ), x + ζ • h ∈ ball x (r i) := fun i =>
    hline.continuousAt.eventually_mem (by rw [h0]; exact isOpen_ball.mem_nhds (mem_ball_self (hr i)))
  have hUev : ∀ᶠ ζ in 𝓝 (0 : ℂ), x + ζ • h ∈ U :=
    hline.continuousAt.eventually_mem (by rw [h0]; exact hU.mem_nhds hx)
  have hball' : ∀ᶠ ζ in 𝓝 (0 : ℂ), ∀ i, x + ζ • h ∈ ball x (r i) := eventually_all.2 hball
  -- the defining maps along the line
  have hψ : ∀ i, AnalyticAt ℂ (fun ζ : ℂ => φ i (x + ζ • h)) 0 := fun i =>
    ((hφ i x (mem_ball_self (hr i))).comp_of_eq (analyticAt_line x h 0) h0)
  by_cases hz : ∃ i, ∀ᶠ ζ in 𝓝 (0 : ℂ), φ i (x + ζ • h) = 0
  · -- the disc lies in `V i`
    obtain ⟨i, hi⟩ := hz
    obtain ⟨ρ, hρ, hρev⟩ := Metric.eventually_nhds_iff.1 (hi.and (hball'.and hUev))
    refine hdisc i x hx h ρ hρ fun ζ hζ => ?_
    obtain ⟨h1, h2, h3⟩ := hρev (by simpa [dist_zero_right] using hζ)
    exact ⟨(hiff i _ (h2 i)).2 h1, h3⟩
  · -- isolated zeros: the line meets `⋃ V i` only at `0`, near `0`
    have hne : ∀ i, ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), φ i (x + ζ • h) ≠ 0 := fun i =>
      ((hψ i).eventually_eq_zero_or_eventually_ne_zero).resolve_left fun hi => hz ⟨i, hi⟩
    have hne' : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), ∀ i, φ i (x + ζ • h) ≠ 0 := eventually_all.2 hne
    have hdiff : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ (fun ζ : ℂ => f (x + ζ • h)) ζ := by
      filter_upwards [hne', nhdsWithin_le_nhds hball', nhdsWithin_le_nhds hUev] with ζ h1 h2 h3
      have hnot : x + ζ • h ∈ U \ ⋃ i, V i := by
        refine ⟨h3, ?_⟩
        simp only [mem_iUnion, not_exists]
        exact fun i hi => h1 i ((hiff i _ (h2 i)).1 hi)
      exact ((hoff _ hnot).comp_of_eq (g := f) (f := fun ζ : ℂ => x + ζ • h)
        (analyticAt_line x h ζ) rfl).differentiableAt
    have hcA : ContinuousAt (fun ζ : ℂ => f (x + ζ • h)) 0 :=
      (hcont.continuousAt (hU.mem_nhds hx)).comp_of_eq hline.continuousAt h0
    exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hdiff hcA

/-- **Grébert–Kappeler book Thm A.6; GKP Thm 19.5 (finitely many subvarieties).**
Let `V₁, …, V_m` be analytic subvarieties of the open set `U` of a complex normed space.  If
`f : E → ℂ` is analytic on `U ∖ ⋃ V_i`, continuous on `U`, and analytic on every complex disc in
`U` contained in some `V_i` (here: `ζ ↦ f (x + ζ h)` analytic at `0` whenever the whole disc
`{x + ζ h | ‖ζ‖ < r}` lies in `V_i ∩ U`), then `f` is analytic on `U`.  (The hypothesis on discs
is only needed at the centre `x`, so it is implied by the book's "analytic on the disc".) -/
theorem analyticOnNhd_of_continuous_of_analytic_off_subvarieties {ι : Type*} [Finite ι]
    {V : ι → Set E} (hU : IsOpen U) (hV : ∀ i, IsAnalyticSubvariety U (V i))
    (hcont : ContinuousOn f U) (hoff : AnalyticOnNhd ℂ f (U \ ⋃ i, V i))
    (hdisc : ∀ i, ∀ x ∈ U, ∀ h : E, ∀ r > 0,
      (∀ ζ : ℂ, ‖ζ‖ < r → x + ζ • h ∈ V i ∩ U) →
        AnalyticAt ℂ (fun ζ : ℂ => f (x + ζ • h)) 0) :
    AnalyticOnNhd ℂ f U := by
  refine analyticOnNhd_of_weak_of_locBdd hU ?_ (locBdd_of_continuousOn hU hcont)
  intro x hx h ℓ
  exact (ℓ.analyticAt _).comp (analyticAt_line_of_off_subvarieties hU hV hcont hoff hdisc hx h)

/-- **Plan statement (one subvariety `Z = {g = 0}`; GKP Thm 19.5 scalar case).**  `f` continuous on
`U`, analytic on `U ∩ {g ≠ 0}`, and analytic along every disc in `U` on which `g` vanishes
identically, is analytic on `U`.  (Strengthening of the plan's `hdisc`: the disc must lie in `U`,
and `r > 0` is quantified.) -/
theorem analyticOnNhd_of_continuous_of_analytic_off_zero {g : E → ℂ} (hU : IsOpen U)
    (hg : AnalyticOnNhd ℂ g U) (hf : ContinuousOn f U)
    (hoff : AnalyticOnNhd ℂ f (U ∩ {x | g x ≠ 0}))
    (hdisc : ∀ x ∈ U, ∀ h : E, ∀ r > 0,
      (∀ ζ : ℂ, ‖ζ‖ < r → x + ζ • h ∈ U ∧ g (x + ζ • h) = 0) →
        AnalyticAt ℂ (fun ζ : ℂ => f (x + ζ • h)) 0) :
    AnalyticOnNhd ℂ f U := by
  refine analyticOnNhd_of_continuous_of_analytic_off_subvarieties
    (V := fun _ : Unit => {x | g x = 0}) hU (fun _ => IsAnalyticSubvariety.of_scalar hU hg) hf ?_ ?_
  · convert hoff using 2
    ext x
    simp
  · intro _ x hx h r hr hd
    exact hdisc x hx h r hr fun ζ hζ => ⟨(hd ζ hζ).2, (hd ζ hζ).1⟩

/-- **Two subvarieties** (book Lemma 15.2: `Z_m = {γ_m² = 0}` and `E_m = {Δ(µ_m) = 2(-1)^m}`).
`f` continuous on `U`, analytic off `{g₁ = 0} ∪ {g₂ = 0}`, and analytic along every disc lying in
`{g₁ = 0}` or in `{g₂ = 0}`, is analytic on `U`. -/
theorem analyticOnNhd_of_continuous_of_analytic_off_two_zeros {g₁ g₂ : E → ℂ} (hU : IsOpen U)
    (hg₁ : AnalyticOnNhd ℂ g₁ U) (hg₂ : AnalyticOnNhd ℂ g₂ U) (hf : ContinuousOn f U)
    (hoff : AnalyticOnNhd ℂ f (U ∩ {x | g₁ x ≠ 0} ∩ {x | g₂ x ≠ 0}))
    (hdisc₁ : ∀ x ∈ U, ∀ h : E, ∀ r > 0,
      (∀ ζ : ℂ, ‖ζ‖ < r → x + ζ • h ∈ U ∧ g₁ (x + ζ • h) = 0) →
        AnalyticAt ℂ (fun ζ : ℂ => f (x + ζ • h)) 0)
    (hdisc₂ : ∀ x ∈ U, ∀ h : E, ∀ r > 0,
      (∀ ζ : ℂ, ‖ζ‖ < r → x + ζ • h ∈ U ∧ g₂ (x + ζ • h) = 0) →
        AnalyticAt ℂ (fun ζ : ℂ => f (x + ζ • h)) 0) :
    AnalyticOnNhd ℂ f U := by
  refine analyticOnNhd_of_continuous_of_analytic_off_subvarieties
    (V := ![{x | g₁ x = 0}, {x | g₂ x = 0}]) hU ?_ hf ?_ ?_
  · intro i
    fin_cases i
    · exact IsAnalyticSubvariety.of_scalar hU hg₁
    · exact IsAnalyticSubvariety.of_scalar hU hg₂
  · convert hoff using 2
    ext x
    simp [Fin.exists_fin_two]
    tauto
  · intro i x hx h r hr hd
    fin_cases i
    · exact hdisc₁ x hx h r hr fun ζ hζ => ⟨(hd ζ hζ).2, (hd ζ hζ).1⟩
    · exact hdisc₂ x hx h r hr fun ζ hζ => ⟨(hd ζ hζ).2, (hd ζ hζ).1⟩

/-- A complex disc in `U` on which a product `g₁ g₂` of analytic functions vanishes identically
lies in `{g₁ = 0}` or in `{g₂ = 0}` (identity theorem on the disc).  This is the check that the
book's Lemma 15.2 needs when `g = g₁ g₂` is fed to the one-subvariety theorem. -/
theorem disc_zero_of_mul_eq_zero {g₁ g₂ : E → ℂ}
    (hg₁ : AnalyticOnNhd ℂ g₁ U) (hg₂ : AnalyticOnNhd ℂ g₂ U) {x : E} {h : E} {r : ℝ} (hr : 0 < r)
    (hd : ∀ ζ : ℂ, ‖ζ‖ < r → x + ζ • h ∈ U ∧ g₁ (x + ζ • h) * g₂ (x + ζ • h) = 0) :
    (∀ ζ : ℂ, ‖ζ‖ < r → g₁ (x + ζ • h) = 0) ∨ (∀ ζ : ℂ, ‖ζ‖ < r → g₂ (x + ζ • h) = 0) := by
  have key : ∀ {g : E → ℂ}, AnalyticOnNhd ℂ g U →
      AnalyticOnNhd ℂ (fun ζ : ℂ => g (x + ζ • h)) (ball (0 : ℂ) r) := fun {g} hg ζ hζ =>
    (hg _ (hd ζ (by simpa using hζ)).1).comp_of_eq (analyticAt_line x h ζ) rfl
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) r := mem_ball_self hr
  have a1 := key hg₁
  have a2 := key hg₂
  have hz : ∀ {g : E → ℂ}, AnalyticOnNhd ℂ g U →
      (∀ᶠ ζ in 𝓝 (0 : ℂ), g (x + ζ • h) = 0) → ∀ ζ : ℂ, ‖ζ‖ < r → g (x + ζ • h) = 0 :=
    fun {g} hg hev ζ hζ => by
      have := (key hg).eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected
        h0 hev (by simpa using hζ)
      simpa using this
  rcases (a1 0 h0).eventually_eq_zero_or_eventually_ne_zero with e1 | e1
  · exact Or.inl (hz hg₁ e1)
  rcases (a2 0 h0).eventually_eq_zero_or_eventually_ne_zero with e2 | e2
  · exact Or.inr (hz hg₂ e2)
  exfalso
  have e3 : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), ‖ζ‖ < r :=
    nhdsWithin_le_nhds (by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with ζ hζ
      simpa using hζ)
  obtain ⟨ζ, h1, h2, h3⟩ := (e1.and (e2.and e3)).exists
  exact mul_ne_zero h1 h2 (hd ζ h3).2

/-- Product form: the one-subvariety theorem for `g = g₁ g₂`, with the disc hypothesis supplied
separately for discs in `{g₁ = 0}` and in `{g₂ = 0}`. -/
theorem analyticOnNhd_of_continuous_of_analytic_off_mul_zero {g₁ g₂ : E → ℂ} (hU : IsOpen U)
    (hg₁ : AnalyticOnNhd ℂ g₁ U) (hg₂ : AnalyticOnNhd ℂ g₂ U) (hf : ContinuousOn f U)
    (hoff : AnalyticOnNhd ℂ f (U ∩ {x | g₁ x * g₂ x ≠ 0}))
    (hdisc₁ : ∀ x ∈ U, ∀ h : E, ∀ r > 0,
      (∀ ζ : ℂ, ‖ζ‖ < r → x + ζ • h ∈ U ∧ g₁ (x + ζ • h) = 0) →
        AnalyticAt ℂ (fun ζ : ℂ => f (x + ζ • h)) 0)
    (hdisc₂ : ∀ x ∈ U, ∀ h : E, ∀ r > 0,
      (∀ ζ : ℂ, ‖ζ‖ < r → x + ζ • h ∈ U ∧ g₂ (x + ζ • h) = 0) →
        AnalyticAt ℂ (fun ζ : ℂ => f (x + ζ • h)) 0) :
    AnalyticOnNhd ℂ f U := by
  refine analyticOnNhd_of_continuous_of_analytic_off_zero (g := fun x => g₁ x * g₂ x) hU
    (fun y hy => (hg₁ y hy).mul (hg₂ y hy)) hf hoff ?_
  intro x hx h r hr hd
  rcases disc_zero_of_mul_eq_zero hg₁ hg₂ hr hd with h1 | h1
  · exact hdisc₁ x hx h r hr fun ζ hζ => ⟨(hd ζ hζ).1, h1 ζ hζ⟩
  · exact hdisc₂ x hx h r hr fun ζ hζ => ⟨(hd ζ hζ).1, h1 ζ hζ⟩

end Main

end NlsGge.GK38.Lib
