import QuantumNLS.Ext025LGP07Full
import QuantumNLS.Ext025LGP07Polar

/-!
# EXT-025 layer A (GP-07 unconditional route), module 2: the square root `(T+c)^{1/2}`
# of the associated operator WITHOUT a projection-valued measure

COMPLETES the frozen `Ext025LGP07` (f3738ed4...) / `Ext025LGP07Full` (4d1cc605...) (neither edited)
by an UNCONDITIONAL square-root clause: the clause of `contract_GP07_full` quantifies over a
projection-valued measure `P` of `T` and is vacuous for a `T` without one.  Here the root is built
from Mathlib's BOUNDED continuous functional calculus only.

Exact source text (FINAL_EXTERNAL_THEOREM_INSTANCES.json, sha256
82876b0400535292c74c814f70269d4dea6778fb05d4d3066b73e8a3d0d13782, instance
`FIN-EXT025-GP-07`, "Representation of a densely defined closed semibounded quadratic form"):
* Hypotheses: "The quadratic form is densely defined, Hermitian, closed in its shifted form
  norm and bounded below on a complex Hilbert space."
* Conclusion: "It has a unique associated selfadjoint operator with the same form domain;
  membership in the operator domain is characterized by representing the form against every
  form-domain test vector by an ambient Hilbert vector."
* Normalization: "Dense domain is explicit. Selfadjointness of a merely formal differential
  expression is not inferred."

Construction.  `V := FormSpace F` is the shifted form Hilbert space (inner product
`q(u,v) + c <u,v>`, `c = 1 - F.bound`), `i := inclusion F : V →L E` is injective with dense
range.  With `R := (i i†)^{1/2} = CFC.sqrt (i i†)` (module `Ext025LGP07Polar`) the root is
`S := R⁻¹`, the `LinearPMap` with `domain = ran R` and `S (R a) = a`.  By the polar
decomposition `i = R ∘ Z` (`Z : V ≃ₗᵢ E` unitary) one gets `ran R = ran i = F.domain`
(Douglas' lemma `ran i = ran (i i†)^{1/2}` is thereby a consequence, not an input) and
`S ∘ i = Z`.  Proved UNCONDITIONALLY, for every `F : FormData E` and every `T` with
`GP07_prop F T` (the printed associated operator):

(a) `D(S) = F.domain`;
(b) `S` is selfadjoint (`S† = S` as `LinearPMap`s) and nonnegative;
(c) `q(v,u) + c <v,u> = <S v, S u>` for `v,u ∈ F.domain`;
(d) `S ∘ S = T + c` with exact domains.
These four are exactly `GP07_root_prop F T S` of the frozen `Ext025LGP07Full`
(same Prop, same shift `c = 1 - F.bound`).  `contract_GP07_unconditional` is the full
GP-07 contract with this clause and NO projection-valued-measure hypothesis.

Shift.  `c = 1 - F.bound` is the shift of the repository's frozen encoding (the form space
`FormSpace F` and the closedness clause of `FormData` are normalized by exactly this shift); the
printed instance text contains no square-root clause at all.  See the review record for the note on
other shifts.
-/
set_option autoImplicit false
set_option maxHeartbeats 3200000
noncomputable section
open Filter Topology
open scoped InnerProductSpace LinearPMap

namespace QuantumNLS.Ext025L

open QuantumNLS.Ext025B7ClosedForm
open QuantumNLS.Ext025L.Polar

universe u

section root
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (F : FormData E)

/-- The bounded factor `R = (i i†)^{1/2}` for the form inclusion `i`. -/
def formR : E →L[ℂ] E := polarR (inclusion F)

theorem formR_injective : Function.Injective (formR F) :=
  polarR_injective (inclusion F) (inclusion_dense F)

/-- The unitary of the polar decomposition `i = R ∘ Z`. -/
def formZ : FormSpace F ≃ₗᵢ[ℂ] E :=
  polarZ (inclusion F) (inclusion_injective F) (inclusion_dense F)

theorem formR_Z (v : FormSpace F) : inclusion F v = formR F (formZ F v) :=
  polar_decomp (inclusion F) (inclusion_injective F) (inclusion_dense F) v

theorem formR_Z' (a : E) : formR F a = inclusion F ((formZ F).symm a) := by
  have h := formR_Z F ((formZ F).symm a)
  rw [(formZ F).apply_symm_apply] at h
  exact h.symm

/-- The square root `S = (T + c)^{1/2} = R⁻¹` as an unbounded operator: domain `ran R`,
`S (R a) = a`. -/
def formRoot : E →ₗ.[ℂ] E where
  domain := LinearMap.range (formR F : E →ₗ[ℂ] E)
  toFun := (LinearEquiv.ofInjective (formR F : E →ₗ[ℂ] E) (formR_injective F)).symm.toLinearMap

theorem formRoot_apply (x : (formRoot F).domain) (a : E) (h : formR F a = (x : E)) :
    formRoot F x = a := by
  have hx : x = ⟨formR F a, LinearMap.mem_range_self (formR F : E →ₗ[ℂ] E) a⟩ :=
    Subtype.ext h.symm
  rw [hx]
  change (LinearEquiv.ofInjective (formR F : E →ₗ[ℂ] E) (formR_injective F)).symm
      (LinearEquiv.ofInjective (formR F : E →ₗ[ℂ] E) (formR_injective F) a) = a
  exact LinearEquiv.symm_apply_apply _ a

theorem mem_formRoot_domain (x : E) : x ∈ (formRoot F).domain ↔ ∃ a, formR F a = x :=
  LinearMap.mem_range

/-- (a) `D(S) = F.domain`. -/
theorem formRoot_domain (x : E) : x ∈ (formRoot F).domain ↔ x ∈ F.domain := by
  rw [mem_formRoot_domain, ← inclusion_range F]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(formZ F).symm a, (formR_Z' F a).symm⟩
  · rintro ⟨v, rfl⟩
    exact ⟨formZ F v, (formR_Z F v).symm⟩

/-- `S` applied to a form-domain vector is the unitary `Z` of the form class. -/
theorem formRoot_form (v : FormSpace F) (hv : (inclusion F v) ∈ (formRoot F).domain) :
    formRoot F ⟨inclusion F v, hv⟩ = formZ F v :=
  formRoot_apply F _ _ (formR_Z F v).symm

/-- (c) `q(v,u) + c <v,u> = <S v, S u>`. -/
theorem formRoot_form_eq (v u : F.domain) (hv : (v : E) ∈ (formRoot F).domain)
    (hu : (u : E) ∈ (formRoot F).domain) :
    F.q v u + ((1 - F.bound : ℝ) : ℂ) * ⟪(v : E), (u : E)⟫_ℂ =
      ⟪formRoot F ⟨v, hv⟩, formRoot F ⟨u, hu⟩⟫_ℂ := by
  have hv' : (inclusion F (toV (F := F) v)) ∈ (formRoot F).domain := hv
  have hu' : (inclusion F (toV (F := F) u)) ∈ (formRoot F).domain := hu
  have e1 : formRoot F ⟨(v : E), hv⟩ = formZ F (toV (F := F) v) := formRoot_form F _ hv'
  have e2 : formRoot F ⟨(u : E), hu⟩ = formZ F (toV (F := F) u) := formRoot_form F _ hu'
  rw [e1, e2, LinearIsometryEquiv.inner_map_map]
  exact (inner_eq F (toV (F := F) v) (toV (F := F) u)).symm

theorem formRoot_symmetric (x y : (formRoot F).domain) :
    ⟪formRoot F x, (y : E)⟫_ℂ = ⟪(x : E), formRoot F y⟫_ℂ := by
  obtain ⟨a, ha⟩ := (mem_formRoot_domain F x).mp x.property
  obtain ⟨b, hb⟩ := (mem_formRoot_domain F y).mp y.property
  rw [formRoot_apply F x a ha, formRoot_apply F y b hb, ← ha, ← hb]
  exact (polarR_inner (inclusion F) a b).symm

theorem formRoot_dense : Dense ((formRoot F).domain : Set E) := by
  have h := polarR_denseRange (inclusion F) (inclusion_dense F)
  have hr : ((formRoot F).domain : Set E) = Set.range (formR F) := by
    ext w
    change w ∈ LinearMap.range (formR F : E →ₗ[ℂ] E) ↔ _
    simp
  rw [hr]
  exact h

/-- (b) `S` is selfadjoint. -/
theorem formRoot_selfAdjoint : IsSelfAdjoint (formRoot F) := by
  have hd := formRoot_dense F
  have hle : formRoot F ≤ (formRoot F)† :=
    LinearPMap.IsFormalAdjoint.le_adjoint hd (fun x y => formRoot_symmetric F x y)
  have hdom : (formRoot F)†.domain ≤ (formRoot F).domain := by
    intro y hy
    set w : E := (formRoot F)† ⟨y, hy⟩ with hw
    have hform := LinearPMap.adjoint_isFormalAdjoint hd
    have h1 : ∀ x : (formRoot F).domain,
        ⟪w, (x : E)⟫_ℂ = ⟪y, formRoot F x⟫_ℂ := fun x => hform ⟨y, hy⟩ x
    have h2 : formR F w = y := by
      refine ext_inner_right ℂ (fun a => ?_)
      have hxa : (formR F a) ∈ (formRoot F).domain := LinearMap.mem_range_self (formR F : E →ₗ[ℂ] E) a
      have := h1 ⟨formR F a, hxa⟩
      rw [formRoot_apply F ⟨formR F a, hxa⟩ a rfl] at this
      have e : ⟪formR F w, a⟫_ℂ = ⟪w, formR F a⟫_ℂ := polarR_inner (inclusion F) w a
      rw [e]
      exact this
    exact ⟨w, h2⟩
  have heq : formRoot F = (formRoot F)† :=
    LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 hdom)
  exact heq.symm

/-- (b) `S` is nonnegative. -/
theorem formRoot_nonneg (x : (formRoot F).domain) : 0 ≤ (⟪(x : E), formRoot F x⟫_ℂ).re := by
  obtain ⟨a, ha⟩ := (mem_formRoot_domain F x).mp x.property
  rw [formRoot_apply F x a ha, ← ha]
  have hpos : (formR F).IsPositive := polarR_isPositive (inclusion F)
  have h := hpos.re_inner_nonneg_left a
  exact h

end root

/-- (d) for any `T` with the printed domain characterization: `S ∘ S = T + c` with exact
domains. -/
theorem formRoot_sq {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (F : FormData E) (T : E →ₗ.[ℂ] E) (hT : GP07_prop F T) (x f : E) :
    (∃ hx : x ∈ T.domain, T ⟨x, hx⟩ = f) ↔
      ∃ (hx : x ∈ (formRoot F).domain) (hy : formRoot F ⟨x, hx⟩ ∈ (formRoot F).domain),
        formRoot F ⟨formRoot F ⟨x, hx⟩, hy⟩ = f + ((1 - F.bound : ℝ) : ℂ) • x := by
  obtain ⟨hsa, hrep⟩ := hT
  have hSsa := formRoot_selfAdjoint F
  have hAin : ∀ x : E, x ∈ (formRoot F).domain → x ∈ F.domain := fun x hx =>
    (formRoot_domain F x).mp hx
  have hBS : ∀ v : F.domain, (v : E) ∈ (formRoot F).domain := fun v =>
    (formRoot_domain F v).mpr v.property
  have hform := formRoot_form_eq F
  constructor
  · rintro ⟨hx, hTx⟩
    have hxF : x ∈ F.domain := ((hrep x (T ⟨x, hx⟩)).mp ⟨hx, rfl⟩).1
    have hxS : x ∈ (formRoot F).domain := hBS ⟨x, hxF⟩
    have hdense : Dense ((formRoot F).domain : Set E) := hSsa.dense_domain
    have hadj : ∀ w : (formRoot F).domain,
        ⟪f + ((1 - F.bound : ℝ) : ℂ) • x, (w : E)⟫_ℂ =
          ⟪formRoot F ⟨x, hxS⟩, formRoot F w⟫_ℂ := by
      intro w
      have hwF : (w : E) ∈ F.domain := hAin w w.property
      have hf := hform ⟨w, hwF⟩ ⟨x, hxF⟩ w.property hxS
      have hqw : F.q ⟨w, hwF⟩ ⟨x, hxF⟩ = ⟪(w : E), f⟫_ℂ := by
        have := (hrep x f).mp ⟨hx, hTx⟩
        obtain ⟨hxF', hq'⟩ := this
        exact hq' ⟨w, hwF⟩
      rw [hqw] at hf
      have hf' : ⟪(w : E), f⟫_ℂ + ((1 - F.bound : ℝ) : ℂ) * ⟪(w : E), x⟫_ℂ =
          ⟪formRoot F w, formRoot F ⟨x, hxS⟩⟫_ℂ := hf
      calc ⟪f + ((1 - F.bound : ℝ) : ℂ) • x, (w : E)⟫_ℂ
          = (starRingEnd ℂ) ⟪(w : E), f + ((1 - F.bound : ℝ) : ℂ) • x⟫_ℂ :=
            (inner_conj_symm _ _).symm
        _ = (starRingEnd ℂ) (⟪(w : E), f⟫_ℂ + ((1 - F.bound : ℝ) : ℂ) * ⟪(w : E), x⟫_ℂ) := by
            rw [inner_add_right, inner_smul_right]
        _ = (starRingEnd ℂ) ⟪formRoot F w, formRoot F ⟨x, hxS⟩⟫_ℂ := by
            rw [hf']
        _ = _ := inner_conj_symm _ _
    have hy : formRoot F ⟨x, hxS⟩ ∈ (formRoot F)†.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _
        ⟨f + ((1 - F.bound : ℝ) : ℂ) • x, hadj⟩
    have hval := LinearPMap.adjoint_apply_eq hdense
      (⟨formRoot F ⟨x, hxS⟩, hy⟩ : (formRoot F)†.domain) hadj
    have hEq : (formRoot F)† = formRoot F := hSsa
    have hdomEq : ((formRoot F)†).domain = (formRoot F).domain := by
      rw [hEq]
    have hy' : formRoot F ⟨x, hxS⟩ ∈ (formRoot F).domain := by
      have hy2 := hy
      rw [hdomEq] at hy2
      exact hy2
    refine ⟨hxS, hy', ?_⟩
    have hc := pmap_congr hEq ⟨_, hy⟩ ⟨_, hy'⟩ rfl
    rw [← hc]
    exact hval
  · rintro ⟨hx, hy, hSSx⟩
    have hxF : x ∈ F.domain := hAin x hx
    refine (hrep x f).mpr ⟨hxF, fun v => ?_⟩
    have hvS : (v : E) ∈ (formRoot F).domain := hBS v
    have hf := hform v ⟨x, hxF⟩ hvS hx
    have hsym : ⟪formRoot F ⟨v, hvS⟩, formRoot F ⟨x, hx⟩⟫_ℂ =
        ⟪(v : E), formRoot F ⟨formRoot F ⟨x, hx⟩, hy⟩⟫_ℂ :=
      formRoot_symmetric F ⟨v, hvS⟩ ⟨formRoot F ⟨x, hx⟩, hy⟩
    rw [hSSx, inner_add_right, inner_smul_right] at hsym
    have hf' : F.q v ⟨x, hxF⟩ + ((1 - F.bound : ℝ) : ℂ) * ⟪(v : E), x⟫_ℂ =
        ⟪formRoot F ⟨v, hvS⟩, formRoot F ⟨x, hx⟩⟫_ℂ := hf
    change F.q v ⟨x, hxF⟩ = ⟪(v : E), f⟫_ℂ
    linear_combination hf'.trans hsym

/-- The unconditional square-root clause: for the printed associated operator `T` of `F`,
the root `S = formRoot F` satisfies (a)-(d), no projection-valued measure involved. -/
theorem formRoot_prop {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (F : FormData E) (T : E →ₗ.[ℂ] E) (hT : GP07_prop F T) :
    GP07_root_prop F T (formRoot F) :=
  ⟨formRoot_domain F, formRoot_selfAdjoint F, formRoot_nonneg F, formRoot_form_eq F,
    formRoot_sq F T hT⟩

universe u'

/-- FIN-EXT025-GP-07 as a Lean theorem, FULL and UNCONDITIONAL.  Conjuncts 1-3 are the frozen
`Ext025LGP07.contract_GP07` (existence of the selfadjoint `T` with the printed domain
characterization, uniqueness, form-domain clauses); conjunct 4 is the square-root identification
`D((T+c)^{1/2}) = F.domain` with `S = (CFC.sqrt (i i†))⁻¹` (`formRoot F`), `c = 1 - F.bound`:
`S` selfadjoint nonnegative, `q(v,u) + c<v,u> = <S v, S u>`, `S ∘ S = T + c` with exact domains.
No projection-valued measure hypothesis. -/
theorem contract_GP07_unconditional {E : Type u'} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (F : QuantumNLS.Ext025B7ClosedForm.FormData E) :
    ∃ T : E →ₗ.[ℂ] E,
      (IsSelfAdjoint T ∧
        ∀ x f : E, (∃ hx : x ∈ T.domain, T ⟨x, hx⟩ = f) ↔
          ∃ hx : x ∈ F.domain, ∀ v : F.domain, F.q v ⟨x, hx⟩ = ⟪(v : E), f⟫_ℂ) ∧
      (∀ T' : E →ₗ.[ℂ] E, GP07_prop F T' → T' = T) ∧ GP07_formdomain F T ∧
      GP07_root_prop F T (formRoot F) := by
  obtain ⟨T, hp, hu, hf⟩ := gp07_main F
  exact ⟨T, hp, hu, hf, formRoot_prop F T hp⟩

end QuantumNLS.Ext025L

#print axioms QuantumNLS.Ext025L.formRoot_prop
#print axioms QuantumNLS.Ext025L.contract_GP07_unconditional
