import QuantumNLS.H1Bridge

/-!
# EXT-003, Route Y stage (v), part C: restriction, gluing and existence on every short interval

Toward R-AEE17FD6 (`thm:root-L2-flow`): "The local lifespan depends only on a bound for this
conserved norm. Restarting at its endpoints therefore constructs the solution ... Local
uniqueness makes the constructions agree on overlaps. ... The `L⁴` bound on the finite union
follows by summing fourth powers of the bounds on its subintervals."

Route Y deviates from Bourgain's `X^{0,b}` proof (Bourgain 1993, §4); everything rests on the
elementary linear estimates LS1/LS2, DD1, DDL1, SG1, DL4a/DL4b, LC1, UQ1, HB1 (read-only).

Here, for `J = (α, β]`, `β ≤ α + T_L`:
* `restr`, `extL`: restriction of `L⁴` classes to a subinterval and extension by zero;
* `V_restr`: the Duhamel integral does not depend on the ambient interval;
* `Sol u w`: `u ∈ L⁴(J × 𝕋_L)` solves the cubic Duhamel equation with continuous `L²` curve `w`
  (from some, equivalently every, data time `a ∈ [α, β]`, `Sol.base`);
* `sol_restr`, `sol_glue`, `Sol.unique`;
* **`exists_sol`** (`κ ≥ 0`): for every `J` of length `≤ T_L`, every data time `a ∈ [α, β]`
  and every `g ∈ L²` there is a solution with `w(a) = g` and `‖w(t)‖₂ = ‖g‖₂` on `[α, β]`
  (restarting with the local lifespan of the conserved norm).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate BigOperators Topology ENNReal InnerProductSpace
open MeasureTheory Filter QuantumNLS.Fourier QuantumNLS.L4Strichartz
  QuantumNLS.L4StrichartzL2 QuantumNLS.DuhamelDuality QuantumNLS.DuhamelL4 QuantumNLS.DuhamelL4Limit
  QuantumNLS.LocalL4Contraction QuantumNLS.L4Uniqueness QuantumNLS.H1Bridge

namespace QuantumNLS.L4Gluing

attribute [local irreducible] QuantumNLS.L4StrichartzL2.evol

variable {L : ℝ} [Fact (0 < L)]

/-! ## 1. Restriction and extension -/

section RestrExt

variable {α β α' β' : ℝ} (hα : α ≤ α') (hβ : β' ≤ β)

include hα hβ in
lemma ae_restr {P : ℝ × AddCircle L → Prop} (h : ∀ᵐ p ∂(μJ (L := L) α β), P p) :
    ∀ᵐ p ∂(μJ (L := L) α' β'), P p := by
  rw [← μJ_restrict hα hβ]; exact ae_restrict_of_ae h

include hα hβ in
lemma memLp_restr {p : ℝ≥0∞} {f : ℝ × AddCircle L → ℂ} (hf : MemLp f p (μJ (L := L) α β)) :
    MemLp f p (μJ (L := L) α' β') := by
  rw [← μJ_restrict hα hβ]; exact hf.restrict _

/-- Restriction of an `L⁴` class to `(α', β'] ⊆ (α, β]`. -/
def restr (u : Lp ℂ 4 (μJ (L := L) α β)) : Lp ℂ 4 (μJ (L := L) α' β') :=
  (memLp_restr hα hβ (Lp.memLp u)).toLp _

lemma coeFn_restr (u : Lp ℂ 4 (μJ (L := L) α β)) :
    (restr hα hβ u : ℝ × AddCircle L → ℂ) =ᵐ[μJ (L := L) α' β'] u :=
  MemLp.coeFn_toLp _

include hα hβ in
lemma memLp_ext (u : Lp ℂ 4 (μJ (L := L) α' β')) :
    MemLp ((slab α' β').indicator (u : ℝ × AddCircle L → ℂ)) 4 (μJ (L := L) α β) := by
  rw [memLp_indicator_iff_restrict (measurableSet_slab α' β'), μJ_restrict hα hβ]
  exact Lp.memLp u

/-- Extension by zero of an `L⁴` class on `(α', β']` to `(α, β]`. -/
def extL (u : Lp ℂ 4 (μJ (L := L) α' β')) : Lp ℂ 4 (μJ (L := L) α β) :=
  (memLp_ext hα hβ u).toLp _

lemma coeFn_extL (u : Lp ℂ 4 (μJ (L := L) α' β')) :
    (extL hα hβ u : ℝ × AddCircle L → ℂ) =ᵐ[μJ (L := L) α β]
      (slab α' β').indicator (u : ℝ × AddCircle L → ℂ) :=
  MemLp.coeFn_toLp _

end RestrExt

/-! ## 2. The Duhamel integral does not depend on the ambient interval -/

section Consistency

variable {α β α' β' : ℝ} (hα : α ≤ α') (hβ : β' ≤ β) (hαβ : α ≤ β) (hlen : β ≤ α + TL L)
  (hα'β' : α' ≤ β') (hlen' : β' ≤ α' + TL L)

include hα hβ hαβ hlen hα'β' hlen' in
lemma freeL4_restr (h : HL L) :
    (freeL4 α β h : ℝ × AddCircle L → ℂ) =ᵐ[μJ (L := L) α' β'] freeL4 α' β' h := by
  have e : restr hα hβ (freeL4 α β h) = freeL4 α' β' h := by
    refine Lp_eq_of_slices _ _ ?_
    have h1 := ae_restrict_of_ae_restrict_of_subset (Set.Ioc_subset_Ioc hα hβ)
      (freeL4_slice hαβ hlen h)
    filter_upwards [h1, freeL4_slice hα'β' hlen' h,
      Measure.ae_ae_of_ae_prod (coeFn_restr hα hβ (freeL4 α β h))] with s e1 e2 e3
    filter_upwards [e1, e2, e3] with x x1 x2 x3
    rw [x3, x1, x2]
  rw [← e]
  exact (coeFn_restr hα hβ _).symm

include hα hβ in
/-- `∫_a^t U(t−s)F(s) ds` computed on `(α', β']` equals the one computed on `(α, β]`. -/
theorem V_restr (F : Lp ℂ (4 / 3) (μJ (L := L) α β)) (F' : Lp ℂ (4 / 3) (μJ (L := L) α' β'))
    (hFF : (F' : ℝ × AddCircle L → ℂ) =ᵐ[μJ (L := L) α' β'] F) {a t : ℝ}
    (ha : a ∈ Set.Icc α' β') (ht : t ∈ Set.Icc α' β') :
    V hα'β' hlen' F' a t = V hαβ hlen F a t := by
  have hS : Sop hα'β' hlen' F' a t = Sop hαβ hlen F a t := by
    refine ext_inner_left ℂ fun h => ?_
    rw [inner_Sop hα'β' hlen' F' ha.1 ht.1, inner_Sop hαβ hlen F (hα.trans ha.1) (hα.trans ht.1)]
    have hsupp : (fun p => conj (freeL4 α β h p) *
        ((Set.Ioc a t ×ˢ Set.univ).indicator (F : ℝ × AddCircle L → ℂ) p -
          (Set.Ioc t a ×ˢ Set.univ).indicator (F : ℝ × AddCircle L → ℂ) p)) =
        (slab α' β').indicator (fun p => conj (freeL4 α β h p) *
          ((Set.Ioc a t ×ˢ Set.univ).indicator (F : ℝ × AddCircle L → ℂ) p -
            (Set.Ioc t a ×ˢ Set.univ).indicator (F : ℝ × AddCircle L → ℂ) p)) := by
      funext p
      by_cases hp : p ∈ slab (L := L) α' β'
      · rw [Set.indicator_of_mem hp]
      · rw [Set.indicator_of_notMem hp]
        have h1 : p ∉ Set.Ioc a t ×ˢ (Set.univ : Set (AddCircle L)) := fun h1 =>
          hp ⟨⟨by linarith [h1.1.1, ha.1], by linarith [h1.1.2, ht.2]⟩, trivial⟩
        have h2 : p ∉ Set.Ioc t a ×ˢ (Set.univ : Set (AddCircle L)) := fun h2 =>
          hp ⟨⟨by linarith [h2.1.1, ht.1], by linarith [h2.1.2, ha.2]⟩, trivial⟩
        rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, sub_zero, mul_zero]
    rw [hsupp, integral_indicator (measurableSet_slab α' β')]
    rw [congrArg (fun μ => ∫ p, conj (freeL4 α β h p) *
        ((Set.Ioc a t ×ˢ Set.univ).indicator (F : ℝ × AddCircle L → ℂ) p -
          (Set.Ioc t a ×ˢ Set.univ).indicator (F : ℝ × AddCircle L → ℂ) p) ∂μ)
      (μJ_restrict (L := L) hα hβ)]
    refine integral_congr_ae ?_
    filter_upwards [freeL4_restr hα hβ hαβ hlen hα'β' hlen' h, hFF] with p e1 e2
    simp only [Set.indicator_apply, e1, e2]
  rw [V, V, hS]

end Consistency

#print axioms V_restr

/-! ## 3. Solutions with a continuous `L²` curve -/

section Sol

variable {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L)

/-- `u ∈ L⁴(J × 𝕋_L)` solves the cubic Duhamel equation (coefficient `c`) on `J = (α, β]` with
continuous `L²` curve `w`: for some data time `a ∈ [α, β]`, `u` solves it with data `w(a)` and
`w(t) = U(t−a)w(a) + c ∫_a^t U(t−s)(|u|²u)(s) ds` for every `t ∈ [α, β]`. -/
def Sol (c : ℂ) (u : Lp ℂ 4 (μJ (L := L) α β)) (w : ℝ → HL L) : Prop :=
  ∃ a ∈ Set.Icc α β, IsDuhamel hαβ hlen c a (w a) u ∧
    ∀ t ∈ Set.Icc α β, Dcurve hαβ hlen c a (w a) u t = w t

variable {hαβ hlen}

/-- Every point of `[α, β]` can serve as the data time. -/
lemma Sol.base {c : ℂ} {u : Lp ℂ 4 (μJ (L := L) α β)} {w : ℝ → HL L} (h : Sol hαβ hlen c u w)
    {b : ℝ} (hb : b ∈ Set.Icc α β) :
    IsDuhamel hαβ hlen c b (w b) u ∧ ∀ t ∈ Set.Icc α β, Dcurve hαβ hlen c b (w b) u t = w t := by
  obtain ⟨a, ha, hD, hw⟩ := h
  have e : Dcurve hαβ hlen c a (w a) u b = w b := hw b hb
  refine ⟨?_, fun t ht => ?_⟩
  · have := isDuhamel_rebase hαβ hlen c a b (w a) hD
    rwa [e] at this
  · rw [← e, ← Dcurve_rebase]
    exact hw t ht

lemma Sol.congr {c : ℂ} {u : Lp ℂ 4 (μJ (L := L) α β)} {w w' : ℝ → HL L}
    (h : Sol hαβ hlen c u w) (hw : ∀ t ∈ Set.Icc α β, w t = w' t) : Sol hαβ hlen c u w' := by
  obtain ⟨a, ha, hD, hwD⟩ := h
  refine ⟨a, ha, ?_, fun t ht => ?_⟩
  · rw [← hw a ha]; exact hD
  · rw [← hw a ha, ← hw t ht]; exact hwD t ht

lemma sol_of_isDuhamel {c : ℂ} {u : Lp ℂ 4 (μJ (L := L) α β)} {a : ℝ} (ha : a ∈ Set.Icc α β)
    {g : HL L} (hu : IsDuhamel hαβ hlen c a g u) :
    Sol hαβ hlen c u (Dcurve hαβ hlen c a g u) := by
  refine ⟨a, ha, ?_, fun t _ => ?_⟩
  · rw [Dcurve_self]; exact hu
  · rw [Dcurve_self]

lemma Sol.slices {c : ℂ} {u : Lp ℂ 4 (μJ (L := L) α β)} {w : ℝ → HL L}
    (h : Sol hαβ hlen c u w) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc α β)),
      (fun x => u (t, x)) =ᵐ[volume] (w t : AddCircle L → ℂ) := by
  obtain ⟨hD, hw⟩ := h.base (b := α) ⟨le_rfl, hαβ⟩
  filter_upwards [hD, ae_restrict_mem measurableSet_Ioc] with t h1 h2
  have e := hw t (Set.Ioc_subset_Icc_self h2)
  rw [Dcurve] at e
  rw [← e]
  exact h1

/-- **Local uniqueness of solutions with curves**: equal at one time, equal throughout. -/
lemma Sol.unique (h1 : β - α ≤ 1) (hlt : α < β) {c : ℂ} {u v : Lp ℂ 4 (μJ (L := L) α β)}
    {w w' : ℝ → HL L} (hu : Sol hαβ hlen c u w) (hv : Sol hαβ hlen c v w') {b : ℝ}
    (hb : b ∈ Set.Icc α β) (hbw : w b = w' b) : u = v ∧ ∀ t ∈ Set.Icc α β, w t = w' t := by
  obtain ⟨hu1, hu2⟩ := hu.base hb
  obtain ⟨hv1, hv2⟩ := hv.base hb
  rw [← hbw] at hv1 hv2
  have huv := duhamel_unique hαβ hlen h1 hlt c b hb (w b) hu1 hv1
  refine ⟨huv, fun t ht => ?_⟩
  rw [← hu2 t ht, ← hv2 t ht, huv]

end Sol

section RestrGlue

/-- **Restriction of solutions.** -/
theorem sol_restr {α β α' β' : ℝ} {hαβ : α ≤ β} {hlen : β ≤ α + TL L} {c : ℂ}
    {u : Lp ℂ 4 (μJ (L := L) α β)} {w : ℝ → HL L} (hu : Sol hαβ hlen c u w)
    (hα : α ≤ α') (hβ : β' ≤ β) (hα'β' : α' ≤ β') (hlen' : β' ≤ α' + TL L) :
    Sol hα'β' hlen' c (restr hα hβ u) w := by
  obtain ⟨hD, hw⟩ := hu.base (b := α') ⟨hα, hα'β'.trans hβ⟩
  have hcub : (cub (restr hα hβ u) : ℝ × AddCircle L → ℂ) =ᵐ[μJ (L := L) α' β'] cub u := by
    filter_upwards [coeFn_cub (restr hα hβ u), ae_restr hα hβ (coeFn_cub u),
      coeFn_restr hα hβ u] with p e1 e2 e3
    rw [e1, e2]
    simp only [cubF]
    rw [e3]
  have hVr : ∀ t ∈ Set.Icc α' β',
      V hα'β' hlen' (cub (restr hα hβ u)) α' t = V hαβ hlen (cub u) α' t := fun t ht =>
    V_restr hα hβ hαβ hlen hα'β' hlen' (cub u) (cub (restr hα hβ u)) hcub ⟨le_rfl, hα'β'⟩ ht
  refine ⟨α', ⟨le_rfl, hα'β'⟩, ?_, fun t ht => ?_⟩
  · have hD' := ae_restrict_of_ae_restrict_of_subset (Set.Ioc_subset_Ioc hα hβ) hD
    filter_upwards [hD', ae_restrict_mem measurableSet_Ioc,
      Measure.ae_ae_of_ae_prod (coeFn_restr hα hβ u)] with t h1 h2 h3
    rw [hVr t (Set.Ioc_subset_Icc_self h2)]
    exact Filter.EventuallyEq.trans h3 h1
  · have e := hw t ⟨hα.trans ht.1, ht.2.trans hβ⟩
    rw [Dcurve] at e ⊢
    rw [hVr t ht]
    exact e

lemma ae_of_restrict_sub {s s' : Set ℝ} (hs : MeasurableSet s) (_hss : s ⊆ s') {P : ℝ → Prop}
    (h : ∀ᵐ t ∂(volume.restrict s), P t) :
    ∀ᵐ t ∂(volume.restrict s'), t ∈ s → P t := by
  have h' := (ae_restrict_iff' hs).1 h
  exact ae_restrict_of_ae h'

/-- **Gluing** two solutions with the same curve at a common endpoint. -/
theorem sol_glue {α γ β : ℝ} (hαγ : α ≤ γ) (hγβ : γ ≤ β) (hαβ : α ≤ β) (hlen : β ≤ α + TL L)
    (hlen1 : γ ≤ α + TL L) (hlen2 : β ≤ γ + TL L) {c : ℂ}
    {u₁ : Lp ℂ 4 (μJ (L := L) α γ)} {u₂ : Lp ℂ 4 (μJ (L := L) γ β)} {w : ℝ → HL L}
    (hu₁ : Sol hαγ hlen1 c u₁ w) (hu₂ : Sol hγβ hlen2 c u₂ w) :
    Sol hαβ hlen c (extL le_rfl hγβ u₁ + extL hαγ le_rfl u₂) w := by
  set U := extL le_rfl hγβ u₁ + extL hαγ le_rfl u₂ with hUdef
  have hU : (U : ℝ × AddCircle L → ℂ) =ᵐ[μJ (L := L) α β]
      fun p => (slab α γ).indicator (u₁ : ℝ × AddCircle L → ℂ) p +
        (slab γ β).indicator (u₂ : ℝ × AddCircle L → ℂ) p := by
    filter_upwards [Lp.coeFn_add (extL le_rfl hγβ u₁) (extL hαγ le_rfl u₂),
      coeFn_extL le_rfl hγβ u₁, coeFn_extL hαγ le_rfl u₂] with p e1 e2 e3
    rw [e1, Pi.add_apply, e2, e3]
  have hU1 : (U : ℝ × AddCircle L → ℂ) =ᵐ[μJ (L := L) α γ] u₁ := by
    filter_upwards [ae_restr le_rfl hγβ hU, ae_mem_J (L := L) (α := α) (β := γ)] with p e hp
    rw [e]
    have h2 : p ∉ slab (L := L) γ β := fun h => by linarith [h.1.1, hp.2]
    rw [Set.indicator_of_mem (show p ∈ slab (L := L) α γ from ⟨hp, trivial⟩),
      Set.indicator_of_notMem h2, add_zero]
  have hU2 : (U : ℝ × AddCircle L → ℂ) =ᵐ[μJ (L := L) γ β] u₂ := by
    filter_upwards [ae_restr hαγ le_rfl hU, ae_mem_J (L := L) (α := γ) (β := β)] with p e hp
    rw [e]
    have h1 : p ∉ slab (L := L) α γ := fun h => by linarith [h.1.2, hp.1]
    rw [Set.indicator_of_notMem h1,
      Set.indicator_of_mem (show p ∈ slab (L := L) γ β from ⟨hp, trivial⟩), zero_add]
  have hc1 : (cub u₁ : ℝ × AddCircle L → ℂ) =ᵐ[μJ (L := L) α γ] cub U := by
    filter_upwards [coeFn_cub u₁, ae_restr le_rfl hγβ (coeFn_cub U), hU1] with p e1 e2 e3
    rw [e1, e2]
    simp only [cubF]
    rw [e3]
  have hc2 : (cub u₂ : ℝ × AddCircle L → ℂ) =ᵐ[μJ (L := L) γ β] cub U := by
    filter_upwards [coeFn_cub u₂, ae_restr hαγ le_rfl (coeFn_cub U), hU2] with p e1 e2 e3
    rw [e1, e2]
    simp only [cubF]
    rw [e3]
  obtain ⟨hD1, hw1⟩ := hu₁.base (b := γ) ⟨hαγ, le_rfl⟩
  obtain ⟨hD2, hw2⟩ := hu₂.base (b := γ) ⟨le_rfl, hγβ⟩
  have hV1 : ∀ t ∈ Set.Icc α γ, V hαγ hlen1 (cub u₁) γ t = V hαβ hlen (cub U) γ t := fun t ht =>
    V_restr le_rfl hγβ hαβ hlen hαγ hlen1 (cub U) (cub u₁) hc1 ⟨hαγ, le_rfl⟩ ht
  have hV2 : ∀ t ∈ Set.Icc γ β, V hγβ hlen2 (cub u₂) γ t = V hαβ hlen (cub U) γ t := fun t ht =>
    V_restr hαγ le_rfl hαβ hlen hγβ hlen2 (cub U) (cub u₂) hc2 ⟨le_rfl, hγβ⟩ ht
  refine ⟨γ, ⟨hαγ, hγβ⟩, ?_, fun t ht => ?_⟩
  · filter_upwards [ae_of_restrict_sub measurableSet_Ioc (Set.Ioc_subset_Ioc le_rfl hγβ) hD1,
      ae_of_restrict_sub measurableSet_Ioc (Set.Ioc_subset_Ioc hαγ le_rfl) hD2,
      ae_of_restrict_sub measurableSet_Ioc (Set.Ioc_subset_Ioc le_rfl hγβ)
        (Measure.ae_ae_of_ae_prod hU1),
      ae_of_restrict_sub measurableSet_Ioc (Set.Ioc_subset_Ioc hαγ le_rfl)
        (Measure.ae_ae_of_ae_prod hU2),
      ae_restrict_mem measurableSet_Ioc] with t d1 d2 s1 s2 ht
    by_cases htγ : t ≤ γ
    · have ht1 : t ∈ Set.Ioc α γ := ⟨ht.1, htγ⟩
      rw [← hV1 t ⟨ht.1.le, htγ⟩]
      exact Filter.EventuallyEq.trans (s1 ht1) (d1 ht1)
    · push Not at htγ
      have ht2 : t ∈ Set.Ioc γ β := ⟨htγ, ht.2⟩
      rw [← hV2 t ⟨htγ.le, ht.2⟩]
      exact Filter.EventuallyEq.trans (s2 ht2) (d2 ht2)
  · by_cases htγ : t ≤ γ
    · have e := hw1 t ⟨ht.1, htγ⟩
      rw [Dcurve] at e ⊢
      rw [← hV1 t ⟨ht.1, htγ⟩]
      exact e
    · push Not at htγ
      have e := hw2 t ⟨htγ.le, ht.2⟩
      rw [Dcurve] at e ⊢
      rw [← hV2 t ⟨htγ.le, ht.2⟩]
      exact e

end RestrGlue

#print axioms sol_restr
#print axioms sol_glue

/-! ## 4. Existence with conserved norm on every interval of length `≤ T_L` -/

section Exist

lemma isDuhamel_degenerate {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L) (hab : ¬ α < β)
    (c : ℂ) (a : ℝ) (g : HL L) (u : Lp ℂ 4 (μJ (L := L) α β)) : IsDuhamel hαβ hlen c a g u := by
  have h0 : volume.restrict (Set.Ioc α β) = 0 := by
    rw [Set.Ioc_eq_empty hab, Measure.restrict_empty]
  show ∀ᵐ t ∂(volume.restrict (Set.Ioc α β)), _
  rw [h0, MeasureTheory.ae_zero]
  exact eventually_bot

/-- **Existence with conserved norm** (`κ ≥ 0`): on every `J = (α, β]` with `β ≤ α + T_L`, for every
data time `a ∈ [α, β]` and every `g ∈ L²(𝕋_L)`, there is a solution `u ∈ L⁴(J × 𝕋_L)` with
continuous curve `w`, `w(a) = g` and `‖w(t)‖₂ = ‖g‖₂` on `[α, β]`. -/
theorem exists_sol {κ : ℝ} (hκ : 0 ≤ κ) {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L) {a : ℝ}
    (ha : a ∈ Set.Icc α β) (g : HL L) :
    ∃ (u : Lp ℂ 4 (μJ (L := L) α β)) (w : ℝ → HL L), Sol hαβ hlen (cNLS κ) u w ∧ w a = g ∧
      ∀ t ∈ Set.Icc α β, ‖w t‖ = ‖g‖ := by
  obtain ⟨τ, hτ, hτ1, hτL, H⟩ := local_flow (L := L) hκ ‖g‖ (norm_nonneg g)
  -- one short step
  have hloc : ∀ (α' β' : ℝ) (h : α' ≤ β') (hl : β' ≤ α' + TL L), β' - α' ≤ τ →
      ∀ b ∈ Set.Icc α' β', ∀ g' : HL L, ‖g'‖ = ‖g‖ →
        ∃ (u : Lp ℂ 4 (μJ (L := L) α' β')) (w : ℝ → HL L), Sol h hl (cNLS κ) u w ∧ w b = g' ∧
          ∀ t ∈ Set.Icc α' β', ‖w t‖ = ‖g‖ := by
    intro α' β' h hl hτ' b hb g' hg'
    by_cases hlt : α' < β'
    · obtain ⟨⟨U, hU⟩, hm⟩ := H α' β' h hl hlt (by linarith) b hb g' hg'.le
      exact ⟨U, _, sol_of_isDuhamel hb hU, Dcurve_self h hl _ b g' U,
        fun t ht => (hm U hU t ht).trans hg'⟩
    · have hbt : ∀ t ∈ Set.Icc α' β', t = b := fun t ht => by
        push Not at hlt; linarith [ht.1, ht.2, hb.1, hb.2]
      refine ⟨0, Dcurve h hl (cNLS κ) b g' 0, ⟨b, hb, isDuhamel_degenerate h hl hlt _ _ _ _,
        fun t ht => ?_⟩, Dcurve_self h hl _ b g' 0, fun t ht => ?_⟩
      · rw [hbt t ht, Dcurve_self, Dcurve_self]
      · rw [hbt t ht, Dcurve_self, hg']
  have hTa : β ≤ a + TL L := hlen.trans (by linarith [ha.1])
  have hTa' : a ≤ α + TL L := ha.2.trans hlen
  -- forward from `a`
  have hfwd : ∀ n : ℕ, ∀ β' (h1 : a ≤ β') (h2 : β' ≤ β), β' - a ≤ n * τ →
      ∃ (u : Lp ℂ 4 (μJ (L := L) a β')) (w : ℝ → HL L),
        Sol h1 (h2.trans hTa) (cNLS κ) u w ∧ w a = g ∧ ∀ t ∈ Set.Icc a β', ‖w t‖ = ‖g‖ := by
    intro n
    induction n with
    | zero =>
      intro β' h1 h2 hn
      simp only [CharP.cast_eq_zero, zero_mul] at hn
      exact hloc a β' h1 (h2.trans hTa) (by linarith) a ⟨le_rfl, h1⟩ g rfl
    | succ n ih =>
      intro β' h1 h2 hn
      set γ := max a (β' - τ) with hγ
      have hγ1 : a ≤ γ := le_max_left _ _
      have hγ2 : γ ≤ β' := max_le h1 (by linarith)
      have hγn : γ - a ≤ n * τ := by
        rcases le_total a (β' - τ) with h | h
        · rw [hγ, max_eq_right h]; push_cast at hn; linarith
        · rw [hγ, max_eq_left h, sub_self]; positivity
      obtain ⟨u₁, w₁, hs₁, hw₁a, hm₁⟩ := ih γ hγ1 (hγ2.trans h2) hγn
      obtain ⟨u₂, w₂, hs₂, hw₂γ, hm₂⟩ := hloc γ β' hγ2 ((h2.trans hTa).trans (by linarith))
        (by rw [hγ]; linarith [le_max_right a (β' - τ)]) γ ⟨le_rfl, hγ2⟩ (w₁ γ)
        (hm₁ γ ⟨hγ1, le_rfl⟩)
      set w : ℝ → HL L := fun t => if t ≤ γ then w₁ t else w₂ t with hwdef
      have hs₁' := hs₁.congr (w' := w) fun t ht => by simp only [hwdef, ht.2, ↓reduceIte]
      have hs₂' := hs₂.congr (w' := w) fun t ht => by
        by_cases htγ : t ≤ γ
        · have : t = γ := le_antisymm htγ ht.1
          simp only [hwdef, htγ, ↓reduceIte]; rw [this, hw₂γ]
        · simp only [hwdef, htγ, ↓reduceIte]
      refine ⟨_, w, sol_glue hγ1 hγ2 h1 (h2.trans hTa) (hγ2.trans (h2.trans hTa))
        ((h2.trans hTa).trans (by linarith)) hs₁' hs₂', ?_, fun t ht => ?_⟩
      · simp only [hwdef, hγ1, ↓reduceIte]; exact hw₁a
      · by_cases htγ : t ≤ γ
        · simp only [hwdef, htγ, ↓reduceIte]; exact hm₁ t ⟨ht.1, htγ⟩
        · simp only [hwdef, htγ, ↓reduceIte]; push Not at htγ; exact hm₂ t ⟨htγ.le, ht.2⟩
  -- backward from `a`
  have hbwd : ∀ n : ℕ, ∀ α' (h1 : α' ≤ a) (h2 : α ≤ α'), a - α' ≤ n * τ →
      ∃ (u : Lp ℂ 4 (μJ (L := L) α' a)) (w : ℝ → HL L),
        Sol h1 (hTa'.trans (by linarith)) (cNLS κ) u w ∧ w a = g ∧
          ∀ t ∈ Set.Icc α' a, ‖w t‖ = ‖g‖ := by
    intro n
    induction n with
    | zero =>
      intro α' h1 h2 hn
      simp only [CharP.cast_eq_zero, zero_mul] at hn
      exact hloc α' a h1 (hTa'.trans (by linarith)) (by linarith) a ⟨h1, le_rfl⟩ g rfl
    | succ n ih =>
      intro α' h1 h2 hn
      set γ := min a (α' + τ) with hγ
      have hγ1 : γ ≤ a := min_le_left _ _
      have hγ2 : α' ≤ γ := le_min h1 (by linarith)
      have hγn : a - γ ≤ n * τ := by
        rcases le_total a (α' + τ) with h | h
        · rw [hγ, min_eq_left h, sub_self]; positivity
        · rw [hγ, min_eq_right h]; push_cast at hn; linarith
      obtain ⟨u₂, w₂, hs₂, hw₂a, hm₂⟩ := ih γ hγ1 (h2.trans hγ2) hγn
      obtain ⟨u₁, w₁, hs₁, hw₁γ, hm₁⟩ := hloc α' γ hγ2 ((hγ1.trans hTa').trans (by linarith))
        (by rw [hγ]; linarith [min_le_right a (α' + τ)]) γ ⟨hγ2, le_rfl⟩ (w₂ γ)
        (hm₂ γ ⟨le_rfl, hγ1⟩)
      set w : ℝ → HL L := fun t => if t < γ then w₁ t else w₂ t with hwdef
      have hs₁' := hs₁.congr (w' := w) fun t ht => by
        by_cases htγ : t < γ
        · simp only [hwdef, htγ, ↓reduceIte]
        · have : t = γ := le_antisymm ht.2 (not_lt.1 htγ)
          simp only [hwdef, htγ, ↓reduceIte]; rw [this, hw₁γ]
      have hs₂' := hs₂.congr (w' := w) fun t ht => by
        simp only [hwdef, not_lt.2 ht.1, ↓reduceIte]
      refine ⟨_, w, sol_glue hγ2 hγ1 h1 (hTa'.trans (by linarith))
        ((hγ1.trans hTa').trans (by linarith)) (hTa'.trans (by linarith)) hs₁' hs₂', ?_,
        fun t ht => ?_⟩
      · simp only [hwdef, not_lt.2 hγ1, ↓reduceIte]; exact hw₂a
      · by_cases htγ : t < γ
        · simp only [hwdef, htγ, ↓reduceIte]; exact hm₁ t ⟨ht.1, htγ.le⟩
        · simp only [hwdef, htγ, ↓reduceIte]; exact hm₂ t ⟨not_lt.1 htγ, ht.2⟩
  obtain ⟨n, hn⟩ := exists_nat_gt ((β - α) / τ)
  have hnτ : β - α ≤ n * τ := by
    have := (div_lt_iff₀ hτ).1 hn; linarith
  obtain ⟨uf, wf, hsf, hwfa, hmf⟩ := hfwd n β ha.2 le_rfl (by linarith [ha.1])
  obtain ⟨ub, wb, hsb, hwba, hmb⟩ := hbwd n α ha.1 le_rfl (by linarith [ha.2])
  set w : ℝ → HL L := fun t => if t < a then wb t else wf t with hwdef
  have hsb' := hsb.congr (w' := w) fun t ht => by
    by_cases hta : t < a
    · simp only [hwdef, hta, ↓reduceIte]
    · have : t = a := le_antisymm ht.2 (not_lt.1 hta)
      simp only [hwdef, hta, ↓reduceIte]; rw [this, hwba, hwfa]
  have hsf' := hsf.congr (w' := w) fun t ht => by
    simp only [hwdef, not_lt.2 ht.1, ↓reduceIte]
  refine ⟨_, w, sol_glue ha.1 ha.2 hαβ hlen hTa' hTa hsb' hsf', ?_, fun t ht => ?_⟩
  · simp only [hwdef, lt_irrefl, ↓reduceIte]; exact hwfa
  · by_cases hta : t < a
    · simp only [hwdef, hta, ↓reduceIte]; exact hmb t ⟨ht.1, hta.le⟩
    · simp only [hwdef, hta, ↓reduceIte]; exact hmf t ⟨not_lt.1 hta, ht.2⟩

end Exist

#print axioms exists_sol

/-! ## 5. Bookkeeping for norms on subintervals -/

section Norms

lemma restr_sub {α β α' β' : ℝ} (hα : α ≤ α') (hβ : β' ≤ β) (u v : Lp ℂ 4 (μJ (L := L) α β)) :
    restr hα hβ (u - v) = restr hα hβ u - restr hα hβ v := by
  refine Lp.ext ?_
  filter_upwards [coeFn_restr hα hβ (u - v), Lp.coeFn_sub (restr hα hβ u) (restr hα hβ v),
    coeFn_restr hα hβ u, coeFn_restr hα hβ v, ae_restr hα hβ (Lp.coeFn_sub u v)]
    with p e1 e2 e3 e4 e5
  rw [e1, e2, Pi.sub_apply, e3, e4, e5, Pi.sub_apply]

/-- `‖u|_{(α', β']}‖_{L⁴((α',β'] × 𝕋_L)} = ‖1_{(α',β']} u‖_{L⁴((α,β] × 𝕋_L)}`. -/
lemma norm_restr {α β α' β' : ℝ} (hα : α ≤ α') (hβ : β' ≤ β) (u : Lp ℂ 4 (μJ (L := L) α β)) :
    ‖restr hα hβ u‖ = ‖ind α' β' u‖ := by
  rw [norm_ind_eq, Lp.norm_def, eLpNorm_congr_ae (coeFn_restr hα hβ u),
    eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_slab α' β'), μJ_restrict hα hβ]

lemma ind_self {α β : ℝ} (u : Lp ℂ 4 (μJ (L := L) α β)) : ind α β u = u := by
  refine Lp.ext ?_
  filter_upwards [coeFn_ind α β u, ae_mem_J (L := L) (α := α) (β := β)] with p e hp
  rw [e, Set.indicator_of_mem (show p ∈ slab (L := L) α β from ⟨hp, trivial⟩)]

/-- Transport of a solution along equalities of the endpoints. -/
lemma sol_cast {α β α' β' : ℝ} (e1 : α = α') (e2 : β = β') {hαβ : α ≤ β}
    {hlen : β ≤ α + TL L} (hαβ' : α' ≤ β') (hlen' : β' ≤ α' + TL L) {c : ℂ}
    {u : Lp ℂ 4 (μJ (L := L) α β)} {w : ℝ → HL L} (h : Sol hαβ hlen c u w) :
    ∃ u' : Lp ℂ 4 (μJ (L := L) α' β'), Sol hαβ' hlen' c u' w := by
  subst e1; subst e2
  exact ⟨u, h⟩

end Norms

end QuantumNLS.L4Gluing
