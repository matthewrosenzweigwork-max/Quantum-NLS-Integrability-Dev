import QuantumNLS.SpectralLeftStep
import QuantumNLS.BetheConditionalBasis

/-!
# Proof of the abstract continuity-of-completeness principle (EXT-001, R-9BF8373D)

Authorized step: NEW VERIFIED OWNER AUTHORIZATION — EXT-001 full step
(`implementation/ops/STATUS.md`, recorded 2026-11-15 13:58:00 UTC). This module PROVES, with no
hypotheses, exactly BCB1's `BetheConditionalBasis.AbstractContinuity` (BCB1 `b1d403e1…`, read-only;
the statement is used verbatim, not restated).

Route.
1. Translation (`hyp_of_inputs`): from the unbounded `A t` (self-adjoint, `‖x‖² ≤ Re⟨x, A t x⟩`) and
   its two-sided inverse `R t` one gets the helper interface `SpectralFamilySteps.Hyp` for
   `R`, `v` and `μ t i = (ev t i)⁻¹`: `R t` symmetric (self-adjointness of `A t` via
   `LinearPMap.adjoint_isFormalAdjoint` on its dense domain), `‖R t f‖² ≤ Re⟨R t f, f⟩`,
   antitone, strongly right continuous, `R 0` compact; `ev t i ≥ 1` and
   `R t (v t i) = (ev t i)⁻¹ • v t i`; `R t` injective.
2. Base case (`fullAt_of_dense`): density of `span (v t)` gives the level-`y` spanning property
   `FullAt` at every level `y > 0` (`exists_orth_eigvec`).
3. Real induction (`fullAt_all`): on `t ∈ ℝ≥0`, per level `y > 0`, with `Hyp.left_step` (at the
   infimum of failures) and `Hyp.right_step` (beyond it).
4. Density (`dense_all`): if `FullAt` holds at every level `y > 0`, every `z ⊥ span (v t)` satisfies
   `Re⟨R t z, z⟩ ≤ y‖z‖²` for all `y > 0` (`re_inner_le_of_mem_orth`), hence `R t z = 0`, hence
   `z = 0` by injectivity (this excludes the kernel); so `(span (v t))ᗮ = ⊥`.
5. `abstractContinuity : AbstractContinuity`.

No orthogonality or simplicity of the eigenvalues is used (the family need not be orthogonal).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped InnerProductSpace ComplexConjugate NNReal Topology
open Filter

namespace QuantumNLS.AbstractContinuityProof

open QuantumNLS.CompactSpectralHelpers QuantumNLS.SpectralFamilySteps QuantumNLS.SpectralLeftStep

section Steps

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] {ι : Type*}
  {R : ℝ≥0 → E →L[ℂ] E} {v : ℝ≥0 → ι → E} {μ : ℝ≥0 → ι → ℝ}

/-- A vector orthogonal to every member of a family is orthogonal to its span. -/
lemma mem_orth_span {u : ι → E} {w : E} (h : ∀ i, ⟪u i, w⟫_ℂ = 0) :
    w ∈ (Submodule.span ℂ (Set.range u))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]

/-- **Base case**: density of the span at `t` gives the level-`y` spanning property at `t`. -/
theorem fullAt_of_dense (H : Hyp R v μ) (t : ℝ≥0)
    (hd : (Submodule.span ℂ (Set.range (v t))).topologicalClosure = ⊤) {y : ℝ} (hy : 0 < y) :
    FullAt (v t) (μ t) (R t) y := by
  intro x lam hlam hx
  by_contra hxn
  obtain ⟨w, hw0, -, horth⟩ :=
    exists_orth_eigvec (v t) (μ t) (H.compact t) (H.symm t) (H.eig t) (hy.trans hlam).ne' hx hxn
  have hwO := mem_orth_span (u := v t) horth
  rw [Submodule.topologicalClosure_eq_top_iff.1 hd] at hwO
  exact hw0 ((Submodule.mem_bot ℂ).1 hwO)

/-- **Real induction at level `y`**: the level-`y` spanning property propagates from `t = 0`
(given by initial density) to every `t ≥ 0`. -/
theorem fullAt_all (H : Hyp R v μ)
    (h0 : (Submodule.span ℂ (Set.range (v 0))).topologicalClosure = ⊤) {y : ℝ} (hy : 0 < y)
    (t : ℝ≥0) : FullAt (v t) (μ t) (R t) y := by
  by_contra hfail
  set S := {s : ℝ≥0 | ¬ FullAt (v s) (μ s) (R s) y}
  have hSne : S.Nonempty := ⟨t, hfail⟩
  have hbdd : BddBelow S := OrderBot.bddBelow S
  set τ := sInf S
  have hbelow : ∀ s, s < τ → FullAt (v s) (μ s) (R s) y := fun s hs => by
    by_contra hc
    exact absurd hs (not_lt.2 (csInf_le hbdd hc))
  have hτ : FullAt (v τ) (μ τ) (R τ) y := by
    rcases eq_or_ne τ 0 with h | h
    · rw [h]; exact fullAt_of_dense H 0 h0 hy
    · exact SpectralLeftStep.Hyp.left_step H hy (pos_iff_ne_zero.2 h) hbelow
  have hR : ∀ᶠ s in 𝓝[≥] τ, FullAt (v s) (μ s) (R s) y :=
    (H.right_step hy hτ).mono fun s hs => hs.1
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 hR
  obtain ⟨s, hsS, hsu⟩ := exists_lt_of_csInf_lt hSne hu
  exact hsS (hsub ⟨csInf_le hbdd hsS, hsu⟩)

/-- **Density at every parameter** from initial density, for an injective family. -/
theorem dense_all (H : Hyp R v μ) (hinj : ∀ t x, R t x = 0 → x = 0)
    (h0 : (Submodule.span ℂ (Set.range (v 0))).topologicalClosure = ⊤) (t : ℝ≥0) :
    (Submodule.span ℂ (Set.range (v t))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro z hz
  have hle : ∀ y : ℝ, 0 < y → RCLike.re ⟪R t z, z⟫_ℂ ≤ y * ‖z‖ ^ 2 := by
    intro y hy
    have := finiteDimensional_eigUp (H.compact t) (H.symm t) hy
    have hsub : eigUp (R t) y ≤ Submodule.span ℂ (Set.range (v t)) := by
      refine iSup₂_le fun lam hlam x hx => ?_
      exact Submodule.span_mono (Set.image_subset_range _ _)
        (fullAt_all H h0 hy t x lam hlam (eig_apply hx))
    exact re_inner_le_of_mem_orth (H.compact t) (H.symm t) (H.pos t) hy
      (Submodule.orthogonal_le hsub hz)
  have hq0 : RCLike.re ⟪R t z, z⟫_ℂ ≤ 0 := by
    by_contra hc
    push Not at hc
    set q := RCLike.re ⟪R t z, z⟫_ℂ
    have hn := sq_nonneg ‖z‖
    have hy : 0 < q / (‖z‖ ^ 2 + 1) := by positivity
    have h1 := hle _ hy
    have h2 : q / (‖z‖ ^ 2 + 1) * (‖z‖ ^ 2 + 1) = q := by field_simp
    nlinarith
  have h1 : ‖R t z‖ ^ 2 ≤ 0 := (H.dom t z).trans hq0
  have h2 : ‖R t z‖ = 0 := by nlinarith [norm_nonneg (R t z)]
  exact hinj t z (norm_eq_zero.1 h2)

end Steps

section Translation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] {ι : Type*}

/-- Self-adjoint (unbounded) operators are symmetric on their domain. -/
lemma selfAdjoint_inner {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) (x y : A.domain) :
    ⟪A x, (y : E)⟫_ℂ = ⟪(x : E), A y⟫_ℂ := by
  have h := LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.1 hA] at h
  exact h x y

/-- **Translation of the BCB1 `AbstractContinuity` hypotheses into the helper interface `Hyp`**,
with `μ t i = (ev t i)⁻¹`, together with `ev t i ≥ 1` and injectivity of every `R t`. -/
theorem hyp_of_inputs (A : ℝ≥0 → E →ₗ.[ℂ] E) (R : ℝ≥0 → E →L[ℂ] E)
    (hsa : ∀ t, IsSelfAdjoint (A t))
    (hpos : ∀ t, ∀ x : (A t).domain, ‖(x : E)‖ ^ 2 ≤ (⟪(x : E), A t x⟫_ℂ).re)
    (hinvR : ∀ t f, ∃ h : R t f ∈ (A t).domain, A t ⟨R t f, h⟩ = f)
    (hinvL : ∀ t (x : (A t).domain), R t (A t x) = (x : E))
    (hanti : ∀ s t, s ≤ t → ∀ f, (⟪R t f, f⟫_ℂ).re ≤ (⟪R s f, f⟫_ℂ).re)
    (hrc : ∀ t f, Tendsto (fun s => R s f) (𝓝[≥] t) (𝓝 (R t f)))
    (hc0 : IsCompactOperator (R 0))
    (v : ℝ≥0 → ι → E) (ev : ℝ≥0 → ι → ℝ)
    (hvc : ∀ i, Continuous (fun t => v t i))
    (hvne : ∀ t i, v t i ≠ 0)
    (hli : ∀ t, LinearIndependent ℂ (v t))
    (heig : ∀ t i, ∃ h : v t i ∈ (A t).domain, A t ⟨v t i, h⟩ = (ev t i : ℂ) • v t i) :
    Hyp R v (fun t i => (ev t i)⁻¹) ∧ (∀ t i, 1 ≤ ev t i) ∧ (∀ t x, R t x = 0 → x = 0) := by
  have hsymm : ∀ t, (R t : E →ₗ[ℂ] E).IsSymmetric := by
    intro t f g
    obtain ⟨hf, hf'⟩ := hinvR t f
    obtain ⟨hg, hg'⟩ := hinvR t g
    have h := selfAdjoint_inner (hsa t) ⟨R t f, hf⟩ ⟨R t g, hg⟩
    rw [hf', hg'] at h
    exact h.symm
  have hdom : ∀ t f, ‖R t f‖ ^ 2 ≤ RCLike.re ⟪R t f, f⟫_ℂ := by
    intro t f
    obtain ⟨hf, hf'⟩ := hinvR t f
    have h := hpos t ⟨R t f, hf⟩
    rw [hf'] at h
    rw [RCLike.re_to_complex]
    exact h
  have hev : ∀ t i, 1 ≤ ev t i := by
    intro t i
    obtain ⟨h, he⟩ := heig t i
    have h1 := hpos t ⟨v t i, h⟩
    rw [he] at h1
    have h2 : (⟪v t i, (ev t i : ℂ) • v t i⟫_ℂ).re = ev t i * ‖v t i‖ ^ 2 := by
      rw [← RCLike.re_to_complex, inner_re_symm, re_inner_real_smul]
    have h1' : ‖v t i‖ ^ 2 ≤ ev t i * ‖v t i‖ ^ 2 := by rw [← h2]; exact h1
    have hp : 0 < ‖v t i‖ ^ 2 := by have := norm_pos_iff.2 (hvne t i); positivity
    nlinarith
  have heigR : ∀ t i, R t (v t i) = (((ev t i)⁻¹ : ℝ) : ℂ) • v t i := by
    intro t i
    obtain ⟨h, he⟩ := heig t i
    have h1 := hinvL t ⟨v t i, h⟩
    rw [he, map_smul] at h1
    have h1' : (ev t i : ℂ) • R t (v t i) = v t i := h1
    have hne : (ev t i : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le (hev t i)).ne'
    calc R t (v t i) = ((ev t i : ℂ)⁻¹ * (ev t i : ℂ)) • R t (v t i) := by
          rw [inv_mul_cancel₀ hne, one_smul]
      _ = (ev t i : ℂ)⁻¹ • ((ev t i : ℂ) • R t (v t i)) := by rw [smul_smul]
      _ = (((ev t i)⁻¹ : ℝ) : ℂ) • v t i := by rw [h1', Complex.ofReal_inv]
  have hinj : ∀ t x, R t x = 0 → x = 0 := by
    intro t x hx
    obtain ⟨h, h'⟩ := hinvR t x
    have e : (⟨R t x, h⟩ : (A t).domain) = 0 := Subtype.ext hx
    rw [e, LinearPMap.map_zero] at h'
    exact h'.symm
  have hanti' : ∀ s t, s ≤ t → ∀ f, RCLike.re ⟪R t f, f⟫_ℂ ≤ RCLike.re ⟪R s f, f⟫_ℂ := by
    intro s t hst f
    rw [RCLike.re_to_complex, RCLike.re_to_complex]
    exact hanti s t hst f
  have H : Hyp R v (fun t i => (ev t i)⁻¹) :=
    { symm := hsymm
      dom := hdom
      anti := hanti'
      compact0 := hc0
      rcont := hrc
      vcont := hvc
      vne := hvne
      indep := hli
      eig := heigR }
  exact ⟨H, hev, hinj⟩

end Translation

/-- **EXT-001 / R-9BF8373D: the abstract continuity-of-completeness principle, proved.**
Exactly BCB1's `AbstractContinuity` (`b1d403e1…`), with no hypotheses. -/
theorem abstractContinuity : BetheConditionalBasis.AbstractContinuity := by
  intro E _ _ _ ι A R hsa hpos hinvR hinvL hanti hrc hc0 v ev hvc hvne hli heig h0 t
  obtain ⟨H, -, hinj⟩ := hyp_of_inputs A R hsa hpos hinvR hinvL hanti hrc hc0 v ev hvc hvne hli heig
  exact dense_all H hinj h0 t

end QuantumNLS.AbstractContinuityProof

#print axioms QuantumNLS.AbstractContinuityProof.fullAt_of_dense
#print axioms QuantumNLS.AbstractContinuityProof.fullAt_all
#print axioms QuantumNLS.AbstractContinuityProof.dense_all
#print axioms QuantumNLS.AbstractContinuityProof.hyp_of_inputs
#print axioms QuantumNLS.AbstractContinuityProof.abstractContinuity
