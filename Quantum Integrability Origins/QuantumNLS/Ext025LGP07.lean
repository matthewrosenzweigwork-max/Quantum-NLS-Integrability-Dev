import QuantumNLS.Ext025B7ClosedForm

/-!
# EXT-025 layer A: contract theorem for FIN-EXT025-GP-07

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

Lean reading.  The hypotheses are the structure `Ext025B7ClosedForm.FormData` (a submodule
`F.domain` dense in the Hilbert space `E`, a form `F.q` sesquilinear in the first slot and
Hermitian, a lower bound `F.bound`, and closedness stated by sequences in the shifted form
norm `sqrt(Re q(u,u) + (1-bound)‖u‖²)`), exactly the printed list.  Conclusion
(`contract_GP07`): there is a unique selfadjoint `T` with
  `x ∈ D(T) ∧ T x = f  ↔  x ∈ F.domain ∧ ∀ v ∈ F.domain, q(v,x) = ⟪v, f⟫`
(the printed domain characterization, for every ambient `f`), and `T` has the same form
domain as `F`, in the following precise sense (no spectral calculus is used; the form of a
semibounded operator is the closure of `x ↦ ⟪x,Tx⟫` on `D(T)`): `D(T) ⊆ F.domain`,
`q(v,x) = ⟪v,Tx⟫` for `x ∈ D(T)`, `D(T)` is a core (every `x ∈ F.domain` is a form-norm limit
of elements of `D(T)`), and the set of ambient limits of form-Cauchy sequences from `D(T)`
(the form domain of `T`) is exactly `F.domain`.
NOT proved here: the identification of this form domain with `D(√(T+c))` for a spectral square
root (an equivalent characterization); this is recorded as an open sub-clause in the review record.
-/
set_option autoImplicit false
set_option maxHeartbeats 3200000
noncomputable section
open Filter Topology
open scoped InnerProductSpace LinearPMap

namespace QuantumNLS.Ext025L

open QuantumNLS.Ext025B7ClosedForm

universe u

/-- The form-space copy of an element of the form domain (its own norm instance). -/
def toV {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {F : FormData E}
    (z : F.domain) : FormSpace F := z

/-- Domain characterization and form-domain statement for the associated operator. -/
def GP07_prop {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (F : FormData E) (T : E →ₗ.[ℂ] E) : Prop :=
  IsSelfAdjoint T ∧
    ∀ x f : E, (∃ hx : x ∈ T.domain, T ⟨x, hx⟩ = f) ↔
      ∃ hx : x ∈ F.domain, ∀ v : F.domain, F.q v ⟨x, hx⟩ = ⟪(v : E), f⟫_ℂ

/-- Form-domain clauses (`D(T) ⊆ form domain`, representation of `q`, core, equality of the
form domain of `T` with `F.domain`). -/
def GP07_formdomain {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (F : FormData E) (T : E →ₗ.[ℂ] E) : Prop :=
  (∀ x : T.domain, (x : E) ∈ F.domain) ∧
  (∀ (x : T.domain) (hx : (x : E) ∈ F.domain) (v : F.domain),
      F.q v ⟨x, hx⟩ = ⟪(v : E), T x⟫_ℂ) ∧
  (∀ x : F.domain, ∃ (u : ℕ → T.domain) (hu : ∀ n, (u n : E) ∈ F.domain),
      Tendsto (fun n => Real.sqrt ((F.q (x - ⟨u n, hu n⟩) (x - ⟨u n, hu n⟩)).re +
        (1 - F.bound) * ‖((x - ⟨u n, hu n⟩ : F.domain) : E)‖ ^ 2)) atTop (𝓝 0) ∧
      Tendsto (fun n => (u n : E)) atTop (𝓝 (x : E))) ∧
  {x : E | ∃ u : ℕ → T.domain, Tendsto (fun n => (u n : E)) atTop (𝓝 x) ∧
      ∀ ε > 0, ∃ M : ℕ, ∀ n ≥ M, ∀ m ≥ M,
        Real.sqrt ((⟪((u n : E) - (u m : E)), T (u n - u m)⟫_ℂ).re +
          (1 - F.bound) * ‖(u n : E) - (u m : E)‖ ^ 2) < ε} = (F.domain : Set E)

theorem gp07_main {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (F : FormData E) :
    ∃ T : E →ₗ.[ℂ] E, GP07_prop F T ∧ (∀ T' : E →ₗ.[ℂ] E, GP07_prop F T' → T' = T) ∧
      GP07_formdomain F T := by
  obtain ⟨T, ⟨hsa, hass, hcl, hlb⟩, huniq⟩ := associated_operator F
  -- translation of `Associated` into the printed domain characterization
  have hrep : ∀ x f : E, (∃ hx : x ∈ T.domain, T ⟨x, hx⟩ = f) ↔
      ∃ hx : x ∈ F.domain, ∀ v : F.domain, F.q v ⟨x, hx⟩ = ⟪(v : E), f⟫_ℂ := by
    intro x f
    rw [hass x f]
    constructor
    · rintro ⟨u, hu, hq⟩
      have hx : x ∈ F.domain := by rw [← hu]; exact (toDomain F u).property
      refine ⟨hx, fun v => ?_⟩
      have h := hq v
      have hux : (⟨x, hx⟩ : F.domain) = toDomain F u := Subtype.ext hu.symm
      rw [hux]
      exact h
    · rintro ⟨hx, hq⟩
      exact ⟨(⟨x, hx⟩ : F.domain), rfl, fun v => hq v⟩
  have hprop : GP07_prop F T := ⟨hsa, hrep⟩
  have hunique : ∀ T' : E →ₗ.[ℂ] E, GP07_prop F T' → T' = T := by
    rintro T' ⟨hsa', hrep'⟩
    have hass' : Ext025SForms.Associated (inclusion F) (formQ F) T' := by
      intro x f
      rw [hrep' x f]
      constructor
      · rintro ⟨hx, hq⟩
        exact ⟨(⟨x, hx⟩ : F.domain), rfl, fun v => hq v⟩
      · rintro ⟨u, hu, hq⟩
        have hx : x ∈ F.domain := by rw [← hu]; exact (toDomain F u).property
        refine ⟨hx, fun v => ?_⟩
        have hux : (⟨x, hx⟩ : F.domain) = toDomain F u := Subtype.ext hu.symm
        rw [hux]
        exact hq v
    have hlb' : ∀ x : T'.domain, -((1 - F.bound) * ‖(x : E)‖ ^ 2) ≤ (⟪(x : E), T' x⟫_ℂ).re := by
      intro x
      have h := associated_lower_bound F T' hass' x
      nlinarith [sq_nonneg ‖(x : E)‖]
    exact huniq T' ⟨hsa', hass', hsa'.isClosed, hlb'⟩
  -- consequences of the representation
  have hdomF : ∀ x : T.domain, (x : E) ∈ F.domain := fun x =>
    ((hrep x (T x)).mp ⟨x.property, rfl⟩).1
  have hq : ∀ (x : T.domain) (hx : (x : E) ∈ F.domain) (v : F.domain),
      F.q v ⟨x, hx⟩ = ⟪(v : E), T x⟫_ℂ := by
    intro x hx v
    exact ((hrep x (T x)).mp ⟨x.property, rfl⟩).2 v
  -- form norm of an element of the form domain, as the norm of the constructed form space
  have hfn : ∀ z : F.domain, Real.sqrt ((F.q z z).re + (1 - F.bound) * ‖(z : E)‖ ^ 2) =
      ‖toV (F := F) z‖ := fun z => (norm_eq F (toV (F := F) z)).symm
  -- approximation by elements of D(T)
  have happrox : ∀ (x : F.domain) (ε : ℝ), 0 < ε → ∃ (w : E) (hwT : w ∈ T.domain)
      (hw : w ∈ F.domain),
      Real.sqrt ((F.q (x - ⟨w, hw⟩) (x - ⟨w, hw⟩)).re +
        (1 - F.bound) * ‖((x - ⟨w, hw⟩ : F.domain) : E)‖ ^ 2) < ε := by
    intro x ε hε
    obtain ⟨y, hy⟩ := (Ext025SForms.form_core_dense (inclusion F)
      (inclusion_injective F)).exists_dist_lt (toV (F := F) x) hε
    set ua : FormSpace F := (inclusion F).adjoint y with hua
    have hw : ambient F ua ∈ F.domain := (toDomain F ua).property
    have hrepw : ∀ v : F.domain, F.q v ⟨ambient F ua, hw⟩ =
        ⟪(v : E), y - ((1 - F.bound : ℝ) : ℂ) • ambient F ua⟫_ℂ := by
      intro v
      have h1 := inner_eq F (toV (F := F) v) ua
      have h2 : @inner ℂ (FormSpace F) _ (toV (F := F) v) ua =
          ⟪inclusion F (toV (F := F) v), y⟫_ℂ := by
        rw [hua]
        exact (inclusion F).adjoint_inner_right (toV (F := F) v) y
      rw [h2] at h1
      have h3 : formQ F (toV (F := F) v) ua = F.q v ⟨ambient F ua, hw⟩ := rfl
      rw [h3] at h1
      rw [inner_sub_right, inner_smul_right]
      have h4 : ⟪inclusion F (toV (F := F) v), y⟫_ℂ = ⟪(v : E), y⟫_ℂ := rfl
      have h5 : ⟪ambient F (toV (F := F) v), ambient F ua⟫_ℂ = ⟪(v : E), ambient F ua⟫_ℂ := rfl
      rw [h4, h5] at h1
      linear_combination -h1
    have hwT : ambient F ua ∈ T.domain :=
      ((hrep _ _).mpr ⟨hw, hrepw⟩).1
    refine ⟨ambient F ua, hwT, hw, ?_⟩
    rw [hfn]
    have : toV (F := F) (x - ⟨ambient F ua, hw⟩ : F.domain) = toV (F := F) x - ua := rfl
    rw [this]
    simpa only [dist_eq_norm] using hy
  have hcore : ∀ x : F.domain, ∃ (u : ℕ → T.domain) (hu : ∀ n, (u n : E) ∈ F.domain),
      Tendsto (fun n => Real.sqrt ((F.q (x - ⟨u n, hu n⟩) (x - ⟨u n, hu n⟩)).re +
        (1 - F.bound) * ‖((x - ⟨u n, hu n⟩ : F.domain) : E)‖ ^ 2)) atTop (𝓝 0) ∧
      Tendsto (fun n => (u n : E)) atTop (𝓝 (x : E)) := by
    intro x
    choose w hwT hw hlt using fun n : ℕ => happrox x (1 / ((n : ℝ) + 1)) (by positivity)
    refine ⟨fun n => ⟨w n, hwT n⟩, hw, ?_, ?_⟩
    · refine squeeze_zero (fun n => Real.sqrt_nonneg _) (fun n => (hlt n).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    · rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have h1 := hlt n
      rw [hfn] at h1
      have h2 := ambient_norm_le F (toV (F := F) (x - ⟨w n, hw n⟩ : F.domain))
      have h3 : ambient F (toV (F := F) (x - ⟨w n, hw n⟩ : F.domain)) = (x : E) - w n := rfl
      rw [h3] at h2
      change ‖w n - (x : E)‖ ≤ 1 / ((n : ℝ) + 1)
      rw [norm_sub_rev]
      exact h2.trans h1.le
  refine ⟨T, hprop, hunique, hdomF, hq, hcore, ?_⟩
  -- the form domain of T
  have hqq : ∀ (a : ℕ → F.domain) (u : ℕ → T.domain), (∀ n, (u n : E) = (a n : E)) → ∀ n m,
      F.q (a n - a m) (a n - a m) = ⟪((u n : E) - (u m : E)), T (u n - u m)⟫_ℂ := by
    intro a u hau n m
    have hx : ((u n - u m : T.domain) : E) ∈ F.domain := hdomF _
    have h := hq (u n - u m) hx (a n - a m)
    have e : (⟨((u n - u m : T.domain) : E), hx⟩ : F.domain) = a n - a m := by
      apply Subtype.ext
      change (u n : E) - (u m : E) = (a n : E) - (a m : E)
      rw [hau n, hau m]
    rw [e] at h
    rw [h]
    change ⟪(a n : E) - (a m : E), _⟫_ℂ = _
    rw [← hau n, ← hau m]
  ext x
  simp only [Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · rintro ⟨u, hlim, hcau⟩
    let a : ℕ → F.domain := fun n => ⟨u n, hdomF (u n)⟩
    have hqa := hqq a u (fun n => rfl)
    have hraw : ∀ ε > 0, ∃ M : ℕ, ∀ n ≥ M, ∀ m ≥ M,
        Real.sqrt ((F.q (a n - a m) (a n - a m)).re +
          (1 - F.bound) * ‖((a n - a m : F.domain) : E)‖ ^ 2) < ε := by
      intro ε hε
      obtain ⟨M, hM⟩ := hcau ε hε
      refine ⟨M, fun n hn m hm => ?_⟩
      have h := hM n hn m hm
      rw [← hqa n m] at h
      exact h
    obtain ⟨v, hv, -⟩ := F.closed a x hraw hlim
    rw [← hv]
    exact v.property
  · intro hx
    obtain ⟨u, hu, h1, h2⟩ := hcore ⟨x, hx⟩
    refine ⟨u, h2, fun ε hε => ?_⟩
    obtain ⟨M, hM⟩ := eventually_atTop.mp (h1.eventually (gt_mem_nhds (half_pos hε)))
    refine ⟨M, fun n hn m hm => ?_⟩
    let a : ℕ → F.domain := fun n => ⟨u n, hu n⟩
    have hqa := hqq a u (fun n => rfl)
    rw [← hqa n m]
    have e : ((a n - a m : F.domain) : E) = (u n : E) - (u m : E) := rfl
    rw [e] at *
    have hn' := hM n hn
    have hm' := hM m hm
    show Real.sqrt ((F.q (a n - a m) (a n - a m)).re +
      (1 - F.bound) * ‖((a n - a m : F.domain) : E)‖ ^ 2) < ε
    rw [hfn]
    have hsplit : toV (F := F) (a n - a m) =
        toV (F := F) (⟨x, hx⟩ - a m : F.domain) - toV (F := F) (⟨x, hx⟩ - a n : F.domain) := by
      change a n - a m = (⟨x, hx⟩ - a m) - (⟨x, hx⟩ - a n)
      abel
    rw [hsplit]
    rw [hfn] at hn' hm'
    calc _ ≤ ‖toV (F := F) (⟨x, hx⟩ - a m : F.domain)‖ +
          ‖toV (F := F) (⟨x, hx⟩ - a n : F.domain)‖ := norm_sub_le _ _
      _ < ε := by linarith

/-- FIN-EXT025-GP-07 as a Lean theorem. -/
theorem contract_GP07 {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (F : FormData E) :
    ∃ T : E →ₗ.[ℂ] E,
      (IsSelfAdjoint T ∧
        ∀ x f : E, (∃ hx : x ∈ T.domain, T ⟨x, hx⟩ = f) ↔
          ∃ hx : x ∈ F.domain, ∀ v : F.domain, F.q v ⟨x, hx⟩ = ⟪(v : E), f⟫_ℂ) ∧
      (∀ T' : E →ₗ.[ℂ] E, GP07_prop F T' → T' = T) ∧ GP07_formdomain F T :=
  gp07_main F

end QuantumNLS.Ext025L

#print axioms QuantumNLS.Ext025L.contract_GP07
