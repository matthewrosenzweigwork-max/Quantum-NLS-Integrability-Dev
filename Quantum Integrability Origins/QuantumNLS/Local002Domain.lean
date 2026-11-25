import Mathlib
import QuantumNLS.Local002Discharge

/-! LOCAL-002 exact-domain correspondence (Terra r178 request).

The printed operator is `𝓛_u = 2iJ∂_x + V_u` on `𝓓_σ = {f ∈ H¹(0,L;ℂ²) : f(L) = σ f(0)}`, `σ = (−1)^n`, `u ∈ L²(0,L)`.
`Local002Final` / `Local002Discharge` use its graph `LuGraph L κ u σ` and the graph notion `IsSelfAdjointGraph`
(`Local002SA`): dense domain and `G = adjGraph G`, `adjGraph G = {q | ∀ p ∈ G, ⟪q.1, p.2⟫ = ⟪q.2, p.1⟫}`, which is
literally the textbook adjoint graph.  Here it is PROVED, for every `u ∈ L²(0,L)` and every `κ`, that
* (`domOf_LuGraph`) the domain of the graph is EXACTLY `domain L σ = 𝓓_σ` (`V_u g ∈ L²` automatically for `g ∈ H¹`);
* (`LuGraph_functional`) the graph is that of a single-valued operator (the weak derivative is determined by the class);
* (`mem_LuGraph_iff`) `(f, φ) ∈ G ↔ f ∈ 𝓓_σ ∧ φ = Lu f`, with `Lu f = 2iJ f' + V_u f` for EVERY `H¹` representative
  (`Lu_ae`);
* (`isSelfAdjointGraph_iff`) graph self-adjointness is exactly: `𝓓_σ` dense, and `f ∈ 𝓓(A^*)`, `A^* f = φ` iff
  `f ∈ 𝓓_σ ∧ φ = Lu f`, where `(f, φ)` is in the adjoint iff `⟪f, A g⟫ = ⟪φ, g⟫` for all `g ∈ 𝓓_σ`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local002Domain
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002SA

variable {L κ : ℝ}

lemma continuous_Vpt (κ : ℝ) : Continuous (fun p : ℂ × E2 => Vpt κ p.1 p.2) := by
  have h := QuantumNLS.ResetFreeResolventLOCAL001.CompletionB.continuous_potentialPt κ
  have : (fun p : ℂ × E2 => Vpt κ p.1 p.2) =
      fun p => QuantumNLS.ResetFreeResolventLOCAL001.potentialPt κ p.1 p.2 :=
    funext fun p => QuantumNLS.Local002Discharge.Vpt_eq_potentialPt κ p.1 p.2
  rw [this]; exact h

lemma norm_Vpt_le (κ : ℝ) (w : ℂ) (g : E2) : ‖Vpt κ w g‖ ≤ 2 * Real.sqrt κ * ‖w‖ * ‖g‖ := by
  by_cases hκ : 0 ≤ κ
  · rw [QuantumNLS.Local002Discharge.Vpt_eq_potentialPt,
      QuantumNLS.ResetFreeResolventLOCAL001.potentialPt_norm hκ]
  · have := QuantumNLS.Local002Discharge.Vpt_nonpos (not_le.mp hκ).le w g
    rw [this, norm_zero]; positivity

/-- An `H¹` representative is bounded on `[0, L]`. -/
lemma rep_bound {f : H2 L} {g h : ℝ → E2} (hL : 0 ≤ L) (hrep : IsH1Rep L f g h) :
    ∃ M : ℝ, ∀ x ∈ Icc 0 L, ‖g x‖ ≤ M := by
  have hint : IntegrableOn h (Ioc 0 L) volume := by
    have := hrep.2.1.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    exact this
  refine ⟨‖g 0‖ + ∫ s in Ioc 0 L, ‖h s‖, fun x hx => ?_⟩
  rw [hrep.2.2 x hx]
  refine (norm_add_le _ _).trans ?_
  gcongr
  rw [intervalIntegral.integral_of_le hx.1]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine setIntegral_mono_set hint.norm ?_ ?_
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · exact (Ioc_subset_Ioc_right hx.2).eventuallyLE

lemma aesm_Vg (u : Lp ℂ 2 (μI L)) {f : H2 L} {g h : ℝ → E2} (hrep : IsH1Rep L f g h) :
    AEStronglyMeasurable (fun x => Vpt κ ((u : ℝ → ℂ) x) (g x)) (μI L) := by
  have hg : AEStronglyMeasurable g (μI L) := (Lp.aestronglyMeasurable f).congr hrep.1
  have hu : AEStronglyMeasurable (u : ℝ → ℂ) (μI L) := Lp.aestronglyMeasurable u
  have h2 : AEStronglyMeasurable (fun x => ((u : ℝ → ℂ) x, g x)) (μI L) := hu.prodMk hg
  have h3 := (continuous_Vpt κ).comp_aestronglyMeasurable h2
  exact h3

lemma ae_bound_Vg {f : H2 L} {g h : ℝ → E2} (u : Lp ℂ 2 (μI L)) (hrep : IsH1Rep L f g h) {M : ℝ}
    (hM : ∀ x ∈ Icc 0 L, ‖g x‖ ≤ M) :
    ∀ᵐ x ∂(μI L), ‖Vpt κ ((u : ℝ → ℂ) x) (g x)‖ ≤ (2 * Real.sqrt κ * M) * ‖(u : ℝ → ℂ) x‖ := by
  have hae : ∀ᵐ x ∂(μI L), x ∈ Ioc 0 L :=
    show ∀ᵐ x ∂(volume.restrict (Ioc 0 L)), x ∈ Ioc 0 L from ae_restrict_mem measurableSet_Ioc
  filter_upwards [hae] with x hx
  have h1 := norm_Vpt_le κ ((u : ℝ → ℂ) x) (g x)
  have h2 := hM x ⟨hx.1.le, hx.2⟩
  have hs : 0 ≤ 2 * Real.sqrt κ * ‖(u : ℝ → ℂ) x‖ := by positivity
  have h3 : 2 * Real.sqrt κ * ‖(u : ℝ → ℂ) x‖ * ‖g x‖ ≤ 2 * Real.sqrt κ * ‖(u : ℝ → ℂ) x‖ * M :=
    mul_le_mul_of_nonneg_left h2 hs
  have h4 : 2 * Real.sqrt κ * ‖(u : ℝ → ℂ) x‖ * M = (2 * Real.sqrt κ * M) * ‖(u : ℝ → ℂ) x‖ := by ring
  exact h1.trans (h3.trans h4.le)

lemma memLp_dom (u : Lp ℂ 2 (μI L)) (c : ℝ) :
    MemLp (fun x => c * ‖(u : ℝ → ℂ) x‖) 2 (μI L) :=
  (Lp.memLp u).norm.const_mul c

/-- `V_u g ∈ L²` for every `H¹` representative `g` and `u ∈ L²(0,L)`. -/
lemma Vg_memLp (hL : 0 ≤ L) (u : Lp ℂ 2 (μI L)) {f : H2 L} {g h : ℝ → E2} (hrep : IsH1Rep L f g h) :
    MemLp (fun x => Vpt κ ((u : ℝ → ℂ) x) (g x)) 2 (μI L) := by
  obtain ⟨M, hM⟩ := rep_bound hL hrep
  refine (memLp_dom u (2 * Real.sqrt κ * M)).mono (aesm_Vg u hrep) ?_
  filter_upwards [ae_bound_Vg (κ := κ) u hrep hM] with x hx
  exact hx.trans (Real.le_norm_self _)

lemma Jh_memLp {h : ℝ → E2} (hh : MemLp h 2 (μI L)) :
    MemLp (fun x => (2 * Complex.I) • Jm (h x)) 2 (μI L) := by
  have := (Jcl.comp_memLp' hh).const_smul (2 * Complex.I)
  convert this using 1
  funext x
  simp [Jcl_apply]

/-- **Exact domain**: the graph's domain is `𝓓_σ`. -/
theorem domOf_LuGraph (hL : 0 ≤ L) (u : Lp ℂ 2 (μI L)) (σ : ℤˣ) :
    domOf (LuGraph L κ (u : ℝ → ℂ) σ) = domain L σ := by
  ext f
  constructor
  · rintro ⟨φ, g, h, hrep, hb, -⟩
    exact ⟨g, h, hrep, hb⟩
  · rintro ⟨g, h, hrep, hb⟩
    have hm : MemLp (fun x => lopPt κ ((u : ℝ → ℂ) x) (h x) (g x)) 2 (μI L) := by
      have := (Jh_memLp hrep.2.1).add (Vg_memLp (κ := κ) hL u hrep)
      convert this using 1
      funext x
      rw [lopPt_split]
      rfl
    exact ⟨hm.toLp _, g, h, hrep, hb, hm.coeFn_toLp⟩

/-- The weak derivative is determined by the class. -/
lemma rep_unique {f : H2 L} {g h g' h' : ℝ → E2} (hL : 0 < L) (hrep : IsH1Rep L f g h)
    (hrep' : IsH1Rep L f g' h') : h =ᵐ[μI L] h' := by
  have hint : IntervalIntegrable (fun s => h s - h' s) volume 0 L := by
    have h1 := hrep.2.1.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h2 := hrep'.2.1.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le).2 (h1.sub h2)
  have h1i : IntervalIntegrable h volume 0 L :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le).2
      (hrep.2.1.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  have h2i : IntervalIntegrable h' volume 0 L :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le).2
      (hrep'.2.1.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  set Φ : ℝ → E2 := fun x => (g 0 - g' 0) + ∫ s in (0 : ℝ)..x, (h s - h' s) with hΦ
  have h0 : (0 : ℝ) ∈ uIcc 0 L := by rw [uIcc_of_le hL.le]; exact ⟨le_rfl, hL.le⟩
  have hΦc : ContinuousOn Φ (Icc 0 L) := by
    have hc := intervalIntegral.continuousOn_primitive_interval' hint h0
    rw [uIcc_of_le hL.le] at hc
    exact continuousOn_const.add hc
  have hΦg : ∀ x ∈ Icc 0 L, Φ x = g x - g' x := by
    intro x hx
    have hsub : uIcc 0 x ⊆ uIcc 0 L := by
      rw [uIcc_of_le hx.1, uIcc_of_le hL.le]; exact Icc_subset_Icc_right hx.2
    rw [hΦ]
    simp only
    rw [intervalIntegral.integral_sub (h1i.mono_set hsub) (h2i.mono_set hsub),
      hrep.2.2 x hx, hrep'.2.2 x hx]
    abel
  have hae0 : Φ =ᵐ[(volume : Measure ℝ).restrict (Ioc 0 L)] fun _ => (0 : E2) := by
    have h1 : ∀ᵐ x ∂(μI L), (f : ℝ → E2) x = g x := hrep.1
    have h2 : ∀ᵐ x ∂(μI L), (f : ℝ → E2) x = g' x := hrep'.1
    have h3 : ∀ᵐ x ∂(μI L), x ∈ Ioc 0 L := by unfold μI; exact ae_restrict_mem measurableSet_Ioc
    filter_upwards [h1, h2, h3] with x a b c
    rw [hΦg x ⟨c.1.le, c.2⟩, ← a, ← b]; simp
  have hzero : EqOn Φ (fun _ => (0 : E2)) (Ioc 0 L) :=
    Measure.eqOn_Ioc_of_ae_eq (μ := volume) hae0 (hΦc.mono Ioc_subset_Icc_self) continuousOn_const
  have hder := hint.ae_hasDerivAt_integral
  have hn : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ L := by simp [ae_iff, measure_singleton]
  have hk : (fun s => h s - h' s) =ᵐ[(volume : Measure ℝ).restrict (Ioc 0 L)] fun _ => 0 := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hder, hn] with x hx hxL hxm
    have hxI : x ∈ uIcc 0 L := by rw [uIcc_of_le hL.le]; exact ⟨hxm.1.le, hxm.2⟩
    have h0 : (0 : ℝ) ∈ uIcc 0 L := by rw [uIcc_of_le hL.le]; exact ⟨le_rfl, hL.le⟩
    have hd := (hx hxI 0 h0).const_add (g 0 - g' 0)
    have hlt : x < L := lt_of_le_of_ne hxm.2 hxL
    have hev : Φ =ᶠ[nhds x] fun _ => (0 : E2) := by
      filter_upwards [Ioo_mem_nhds hxm.1 hlt] with y hy
      exact hzero ⟨hy.1, hy.2.le⟩
    have hd0 : HasDerivAt Φ (h x - h' x) x := hd
    have hd1 : HasDerivAt Φ (0 : E2) x := (hasDerivAt_const x (0 : E2)).congr_of_eventuallyEq hev
    exact hd0.unique hd1
  filter_upwards [hk] with x hx
  exact sub_eq_zero.1 hx

/-- The graph is that of a single-valued operator. -/
theorem LuGraph_functional (hL : 0 < L) {u : ℝ → ℂ} {σ : ℤˣ} {f φ φ' : H2 L}
    (h1 : (f, φ) ∈ LuGraph L κ u σ) (h2 : (f, φ') ∈ LuGraph L κ u σ) : φ = φ' := by
  obtain ⟨g, h, hrep, -, ha⟩ := h1
  obtain ⟨g', h', hrep', -, ha'⟩ := h2
  have hh := rep_unique hL hrep hrep'
  have hgg : g =ᵐ[μI L] g' := hrep.1.symm.trans hrep'.1
  apply Lp.ext
  filter_upwards [ha, ha', hh, hgg] with x a b c d
  simp only [a, b, c, d]

/-- The printed action `Lu f = 2iJ f' + V_u f` (the unique `φ` with `(f, φ) ∈ G`; `0` off the domain). -/
def Lu (L κ : ℝ) (u : ℝ → ℂ) (σ : ℤˣ) (f : H2 L) : H2 L :=
  open Classical in if h : ∃ φ, (f, φ) ∈ LuGraph L κ u σ then h.choose else 0

theorem mem_LuGraph_iff (hL : 0 < L) (u : Lp ℂ 2 (μI L)) (σ : ℤˣ) (f φ : H2 L) :
    (f, φ) ∈ LuGraph L κ (u : ℝ → ℂ) σ ↔ f ∈ domain L σ ∧ φ = Lu L κ (u : ℝ → ℂ) σ f := by
  constructor
  · intro hp
    have hd : f ∈ domain L σ := by
      rw [← domOf_LuGraph hL.le u σ (κ := κ)]; exact ⟨φ, hp⟩
    refine ⟨hd, ?_⟩
    have hex : ∃ φ, (f, φ) ∈ LuGraph L κ (u : ℝ → ℂ) σ := ⟨φ, hp⟩
    unfold Lu
    rw [dif_pos hex]
    exact LuGraph_functional hL hp hex.choose_spec
  · rintro ⟨hd, rfl⟩
    have hex : ∃ φ, (f, φ) ∈ LuGraph L κ (u : ℝ → ℂ) σ := by
      rw [← domOf_LuGraph hL.le u σ (κ := κ)] at hd; exact hd
    unfold Lu
    rw [dif_pos hex]
    exact hex.choose_spec

/-- `Lu f = 2iJ g' + V_u g` almost everywhere, for every `H¹` representative `(g, h)` of `f`. -/
theorem Lu_ae (hL : 0 < L) (u : Lp ℂ 2 (μI L)) (σ : ℤˣ) {f : H2 L} {g h : ℝ → E2}
    (hrep : IsH1Rep L f g h) (hb : g L = (((σ : ℤ) : ℂ)) • g 0) :
    ((Lu L κ (u : ℝ → ℂ) σ f : H2 L) : ℝ → E2) =ᵐ[μI L]
      fun x => (2 * Complex.I) • Jm (h x) + Vpt κ ((u : ℝ → ℂ) x) (g x) := by
  have hd : f ∈ domain L σ := ⟨g, h, hrep, hb⟩
  have hex : ∃ φ, (f, φ) ∈ LuGraph L κ (u : ℝ → ℂ) σ := by
    rw [← domOf_LuGraph hL.le u σ (κ := κ)] at hd; exact hd
  have hmem := (mem_LuGraph_iff (κ := κ) hL u σ f _).2 ⟨hd, rfl⟩
  obtain ⟨g', h', hrep', -, ha⟩ := hmem
  have hh := rep_unique hL hrep' hrep
  have hgg : g' =ᵐ[μI L] g := hrep'.1.symm.trans hrep.1
  filter_upwards [ha, hh, hgg] with x a b c
  simp only [a, b, c, lopPt_split]

/-- **Graph self-adjointness is the printed self-adjointness**: `𝓓_σ` is dense, and the adjoint `A^*` of
`A = 𝓛_u` (`f ∈ 𝓓(A^*)` with `A^* f = φ` iff `⟪f, A g⟫ = ⟪φ, g⟫` for all `g ∈ 𝓓(A)`) equals `A`: the pair `(f, φ)`
satisfies the adjoint relation iff `f ∈ 𝓓_σ` and `φ = Lu f`. -/
theorem isSelfAdjointGraph_iff (hL : 0 < L) (u : Lp ℂ 2 (μI L)) (σ : ℤˣ) :
    IsSelfAdjointGraph (LuGraph L κ (u : ℝ → ℂ) σ) ↔
      Dense (domain L σ) ∧ ∀ f φ : H2 L,
        (∀ g ∈ domain L σ, ⟪f, Lu L κ (u : ℝ → ℂ) σ g⟫_ℂ = ⟪φ, g⟫_ℂ) ↔
          (f ∈ domain L σ ∧ φ = Lu L κ (u : ℝ → ℂ) σ f) := by
  have hadj : ∀ f φ : H2 L, (f, φ) ∈ adjGraph (LuGraph L κ (u : ℝ → ℂ) σ) ↔
      ∀ g ∈ domain L σ, ⟪f, Lu L κ (u : ℝ → ℂ) σ g⟫_ℂ = ⟪φ, g⟫_ℂ := by
    intro f φ
    constructor
    · intro h g hg
      have := h (g, Lu L κ (u : ℝ → ℂ) σ g) ((mem_LuGraph_iff hL u σ _ _).2 ⟨hg, rfl⟩)
      exact this
    · intro h p hp
      obtain ⟨hd, hpp⟩ := (mem_LuGraph_iff hL u σ p.1 p.2).1 hp
      have := h p.1 hd
      rw [hpp]; exact this
  constructor
  · rintro ⟨hdense, heq⟩
    refine ⟨by rwa [domOf_LuGraph hL.le u σ] at hdense, fun f φ => ?_⟩
    rw [← hadj, ← mem_LuGraph_iff hL u σ, ← heq]
  · rintro ⟨hdense, h⟩
    refine ⟨by rwa [domOf_LuGraph hL.le u σ], ?_⟩
    ext ⟨f, φ⟩
    rw [mem_LuGraph_iff hL u σ]
    exact ((hadj f φ).trans (h f φ)).symm

end QuantumNLS.Local002Domain
#print axioms QuantumNLS.Local002Domain.domOf_LuGraph
#print axioms QuantumNLS.Local002Domain.LuGraph_functional
#print axioms QuantumNLS.Local002Domain.mem_LuGraph_iff
#print axioms QuantumNLS.Local002Domain.Lu_ae
#print axioms QuantumNLS.Local002Domain.isSelfAdjointGraph_iff
