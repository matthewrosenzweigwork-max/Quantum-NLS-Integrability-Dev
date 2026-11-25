import QuantumNLS.ContactFormTheorem
import QuantumNLS.ContactFormFamily

/-! Literal source contract FIN-EXT025-GP-07 (coverage qualifications follow below).
Hypotheses:
The quadratic form is densely defined, Hermitian, closed in its shifted form norm and bounded below on a complex Hilbert space.
Conclusion:
It has a unique associated selfadjoint operator with the same form domain; membership in the operator domain is characterized by representing the form against every form-domain test vector by an ambient Hilbert vector.
Application wrappers:
The trace estimate and positivity of the repulsive coupling make the contact-form norm equivalent to the bosonic H1 norm. Smooth symmetric periodic functions are dense. The report also gives a variational-resolvent construction; the standard representation theorem is an equivalent foundation, not a source for the collision-domain regularity argument.
The coefficient is 2c per unordered collision pair with the report’s coordinate-trace convention; after mean-field scaling c=kappa/N. The theorem does not determine this normalization or the piecewise H2 characterization; those are proved in the report.
-/

/-! FIN-EXT025-GP-07. A closed semibounded Hermitian form is encoded on its
complete shifted-form Hilbert space V, with its continuous injective dense
inclusion i into H. The identity hform is the definition of that shifted inner
product, not an assumed representation theorem. No compactness is imposed.
CONTRACT ISSUE: the form domain is D((T+a)^(1/2)), generally larger than D(T).
The theorem below gives the exact test-vector domain and form-core density;
the square-root identification is tracked separately in the gaps receipt. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ComplexConjugate LinearPMap
open InnerProductSpace
namespace QuantumNLS.Ext025SForms
variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Real shifts preserve the exact maximal adjoint domain. -/
def shift (T : H →ₗ.[ℂ] H) (a : ℝ) : H →ₗ.[ℂ] H where
  domain := T.domain
  toFun := T.toFun - (a : ℂ) • T.domain.subtype

theorem shift_selfAdjoint {T : H →ₗ.[ℂ] H} (hT : IsSelfAdjoint T) (a : ℝ) :
    IsSelfAdjoint (shift T a) := by
  have hd := hT.dense_domain
  have he : T† = T := hT
  have hsym : T.IsFormalAdjoint T := by
    have h := LinearPMap.adjoint_isFormalAdjoint hd
    rwa [he] at h
  have hdom : ∀ y : H, y ∈ (shift T a)†.domain ↔ y ∈ T.domain := by
    intro y
    rw [LinearPMap.mem_adjoint_domain_iff]
    have ht : y ∈ T.domain ↔ y ∈ T†.domain := by rw [he]
    rw [ht, LinearPMap.mem_adjoint_domain_iff]
    change Continuous (fun x : T.domain => ⟪y, T x - (a : ℂ) • (x : H)⟫_ℂ) ↔
      Continuous (fun x : T.domain => ⟪y,T x⟫_ℂ)
    simp_rw [inner_sub_right, inner_smul_right]
    have hg : Continuous fun x : T.domain => (a : ℂ) * ⟪y, (x : H)⟫_ℂ :=
      continuous_const.mul ((innerSL ℂ y).continuous.comp continuous_subtype_val)
    constructor
    · intro h
      convert h.add hg using 1
      funext x
      change ⟪y,T x⟫_ℂ = (⟪y,T x⟫_ℂ - (a : ℂ) * ⟪y,(x : H)⟫_ℂ) +
        (a : ℂ) * ⟪y,(x : H)⟫_ℂ
      ring
    · intro h
      exact h.sub hg
  apply LinearPMap.isSelfAdjoint_def.mpr
  refine LinearPMap.ext (Submodule.ext hdom) ?_
  intro x hx hy
  change (shift T a)† ⟨x, hx⟩ = T ⟨x, hy⟩ - (a : ℂ) • x
  apply LinearPMap.adjoint_apply_eq (T := shift T a) hd
  intro w
  change ⟪T ⟨x, hy⟩ - (a : ℂ) • x, (w : H)⟫_ℂ =
    ⟪x, T ⟨w, w.2⟩ - (a : ℂ) • (w : H)⟫_ℂ
  rw [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, hsym ⟨x, hy⟩ ⟨w, w.2⟩]

/-- The variational resolvent of the shifted form. -/
def resolvent (i : V →L[ℂ] H) : H →L[ℂ] H := i.comp i.adjoint

theorem resolvent_symmetric (i : V →L[ℂ] H) (f g : H) :
    ⟪resolvent i f, g⟫_ℂ = ⟪f, resolvent i g⟫_ℂ := by
  change ⟪i (i.adjoint f), g⟫_ℂ = ⟪f, i (i.adjoint g)⟫_ℂ
  rw [← i.adjoint_inner_right, ← i.adjoint_inner_left]

theorem adjoint_injective (i : V →L[ℂ] H) (hd : DenseRange i) :
    Function.Injective i.adjoint := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have hz : ∀ v : V, ⟪f, i v⟫_ℂ = 0 := by
    intro v
    rw [← i.adjoint_inner_left, hf, inner_zero_left]
  have hc : IsClosed {x : H | ⟪f, x⟫_ℂ = 0} :=
    isClosed_eq (innerSL ℂ f).continuous continuous_const
  have hh := closure_minimal (s := Set.range i) (t := {x : H | ⟪f, x⟫_ℂ = 0})
    (by rintro _ ⟨v,rfl⟩; exact hz v) hc (hd f)
  exact inner_self_eq_zero.mp hh

theorem resolvent_injective (i : V →L[ℂ] H) (hi : Function.Injective i)
    (hd : DenseRange i) : Function.Injective (resolvent i) :=
  hi.comp (adjoint_injective i hd)

/-- Inverse on the full range, with no operator-domain conclusions assumed. -/
def inverse (i : V →L[ℂ] H) (hi : Function.Injective i) (hd : DenseRange i) :
    H →ₗ.[ℂ] H where
  domain := LinearMap.range (resolvent i).toLinearMap
  toFun := (LinearEquiv.ofInjective (resolvent i).toLinearMap
    (resolvent_injective i hi hd)).symm.toLinearMap

theorem inverse_resolvent (i : V →L[ℂ] H) (hi : Function.Injective i)
    (hd : DenseRange i) (f : H) :
    inverse i hi hd ⟨resolvent i f, ⟨f,rfl⟩⟩ = f :=
  (LinearEquiv.ofInjective (resolvent i).toLinearMap
    (resolvent_injective i hi hd)).symm_apply_apply f

theorem inverse_selfAdjoint (i : V →L[ℂ] H) (hi : Function.Injective i)
    (hd : DenseRange i) : IsSelfAdjoint (inverse i hi hd) := by
  refine PhysicalEnergy.isSelfAdjoint_of_inverse (inverse i hi hd) (resolvent i)
    (resolvent_symmetric i) (fun f => ⟨f,rfl⟩) (inverse_resolvent i hi hd) ?_
  intro x y
  obtain ⟨f,hf⟩ := x.2
  obtain ⟨g,hg⟩ := y.2
  have hx : x = ⟨resolvent i f, ⟨f,rfl⟩⟩ := Subtype.ext hf.symm
  have hy : y = ⟨resolvent i g, ⟨g,rfl⟩⟩ := Subtype.ext hg.symm
  rw [hx, hy, inverse_resolvent, inverse_resolvent]
  exact (resolvent_symmetric i f g).symm

/-- Exact form/ambient test-vector graph, without conflating the domains. -/
def Associated (i : V →L[ℂ] H) (q : V → V → ℂ) (T : H →ₗ.[ℂ] H) : Prop :=
  ∀ x f : H, (∃ hx : x ∈ T.domain, T ⟨x,hx⟩ = f) ↔
    ∃ u : V, i u = x ∧ ∀ v : V, q v u = ⟪i v, f⟫_ℂ

theorem shifted_inverse_associated (i : V →L[ℂ] H) (hi : Function.Injective i)
    (hd : DenseRange i) (q : V → V → ℂ) (a : ℝ)
    (hform : ∀ v u, q v u + (a : ℂ) * ⟪i v, i u⟫_ℂ = ⟪v,u⟫_ℂ) :
    Associated i q (shift (inverse i hi hd) a) := by
  intro x f
  constructor
  · rintro ⟨hx,hf⟩
    obtain ⟨g,hg⟩ := hx
    have hx : x ∈ (inverse i hi hd).domain := ⟨g,hg⟩
    have he : (⟨x,hx⟩ : (inverse i hi hd).domain) = ⟨resolvent i g,⟨g,rfl⟩⟩ :=
      Subtype.ext hg.symm
    have hf' : g - (a : ℂ) • x = f := by
      change inverse i hi hd ⟨x,hx⟩ - (a : ℂ) • x = f at hf
      rwa [he, inverse_resolvent] at hf
    refine ⟨i.adjoint g, hg, fun v => ?_⟩
    have h := hform v (i.adjoint g)
    rw [i.adjoint_inner_right] at h
    rw [← hf', inner_sub_right, inner_smul_right, ← hg]
    exact eq_sub_of_add_eq h
  · rintro ⟨u,hu,hq⟩
    let g : H := f + (a : ℂ) • x
    have hu' : u = i.adjoint g := by
      apply ext_inner_left ℂ
      intro v
      rw [i.adjoint_inner_right]
      change ⟪v,u⟫_ℂ = ⟪i v,f + (a : ℂ) • x⟫_ℂ
      rw [← hform, hq, hu, inner_add_right, inner_smul_right]
    have hr : resolvent i g = x := by change i (i.adjoint g) = x; rw [← hu', hu]
    refine ⟨⟨g,hr⟩, ?_⟩
    change inverse i hi hd ⟨x,⟨g,hr⟩⟩ - (a : ℂ) • x = f
    have he : (⟨x,⟨g,hr⟩⟩ : (inverse i hi hd).domain) =
        ⟨resolvent i g,⟨g,rfl⟩⟩ := Subtype.ext hr.symm
    rw [he, inverse_resolvent]
    change f + (a : ℂ) • x - (a : ℂ) • x = f
    abel

/-- General closed semibounded form representation, encoded in the complete
shifted form norm. Existence, uniqueness, exact maximal test-vector graph,
closedness and the inherited lower bound are conclusions. -/
theorem «FIN-EXT025-GP-07» (i : V →L[ℂ] H) (hi : Function.Injective i)
    (hd : DenseRange i) (q : V → V → ℂ) (a : ℝ)
    (hform : ∀ v u, q v u + (a : ℂ) * ⟪i v, i u⟫_ℂ = ⟪v,u⟫_ℂ) :
    ∃! T : H →ₗ.[ℂ] H, IsSelfAdjoint T ∧ Associated i q T ∧ T.IsClosed ∧
      ∀ x : T.domain, -(a * ‖(x : H)‖ ^ 2) ≤ (⟪(x : H), T x⟫_ℂ).re := by
  let T := shift (inverse i hi hd) a
  have ha : Associated i q T := shifted_inverse_associated i hi hd q a hform
  have hs : IsSelfAdjoint T := shift_selfAdjoint (inverse_selfAdjoint i hi hd) a
  refine ⟨T, ⟨hs,ha,hs.isClosed, ?_⟩, ?_⟩
  · intro x
    obtain ⟨u,hu,hq⟩ := (ha x (T x)).mp ⟨x.2,rfl⟩
    have h := congrArg Complex.re (hform u u)
    simp only [hq, hu, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at h
    have hxnorm : (⟪(x : H),(x : H)⟫_ℂ).re = ‖(x : H)‖^2 :=
      (norm_sq_eq_re_inner (𝕜 := ℂ) (x : H)).symm
    have hunorm : (⟪u,u⟫_ℂ).re = ‖u‖^2 :=
      (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
    rw [hxnorm,hunorm] at h
    nlinarith [sq_nonneg ‖u‖]
  · rintro S ⟨_,hS,_,_⟩
    have hle : S ≤ T := by
      constructor
      · intro x hx
        obtain ⟨ht,_⟩ := (ha x (S ⟨x,hx⟩)).mpr ((hS x _).mp ⟨hx,rfl⟩)
        exact ht
      · intro x y hxy
        obtain ⟨ht,he⟩ := (ha x (S x)).mpr ((hS x _).mp ⟨x.2,rfl⟩)
        have hy : y = ⟨(x : H),ht⟩ := Subtype.ext hxy.symm
        rw [hy,he]
    have hge : T.domain ≤ S.domain := by
      intro x hx
      exact ((hS x (T ⟨x,hx⟩)).mpr ((ha x _).mp ⟨hx,rfl⟩)).1
    exact LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 hge)

/-- D(T) is a core for the form: its preimage is range(i*), dense in V.
This is density in the shifted form norm, rather than the ambient norm. -/
theorem form_core_dense (i : V →L[ℂ] H) (hi : Function.Injective i) :
    DenseRange i.adjoint := by
  change Dense (i.adjoint.range : Set V)
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, i.adjoint.orthogonal_range,
    ContinuousLinearMap.adjoint_adjoint]
  exact LinearMap.ker_eq_bot.mpr hi

/-- Exact preimage of the operator domain inside the form space. -/
theorem form_core_preimage (i : V →L[ℂ] H) (hi : Function.Injective i)
    (hd : DenseRange i) (a : ℝ) (u : V) :
    i u ∈ (shift (inverse i hi hd) a).domain ↔ u ∈ i.adjoint.range := by
  constructor
  · rintro ⟨f,hf⟩
    exact ⟨f,hi hf⟩
  · rintro ⟨f,hf⟩
    exact ⟨f,congrArg i hf⟩

section Contact
open ContactOperator ContactFormTheorem
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}
/-- R-98129FE7 and R-8E4D05E7: actual contact form, literal 2c normalization,
unique selfadjoint nonnegative operator and both directions of its form graph. -/
theorem gp07_contact {c : ℝ} (hc : 0 ≤ c) :
    (∃! T : SymL2 L N →ₗ.[ℂ] SymL2 L N, IsSelfAdjoint T ∧ IsAssociated c T) ∧
    (∀ x f : SymL2 L N,
      (∃ hx : x ∈ (Hop c hc).domain, Hop c hc ⟨x,hx⟩ = f) ↔
        ∃ u : VSym L N, valSym u = x ∧
          ∀ v : VSym L N, ContactForm.q c v.1 u.1 = ⟪valSym v,f⟫_ℂ) := by
  refine ⟨⟨Hop c hc, ⟨Hop_isSelfAdjoint hc, Hop_isAssociated hc⟩,
    fun T h => eq_Hop_of_isAssociated hc T h.1 h.2⟩, Hop_isAssociated hc⟩
/-- Trace estimate and repulsive coupling give the exact two-sided
comparison with the physical bosonic H1 norm (and hence its complete form norm). -/
theorem gp07_contact_norm {c : ℝ} (hc : 0 ≤ c) (u : PhysicalEnergy.PhysH1 L N) :
    ‖u‖^2 ≤ ContactForm.formNormSq c u ∧
    ContactForm.formNormSq c u ≤
      (1 + 2*c*(Fintype.card (ContactForm.Pair N)*(1+L⁻¹))) * ‖u‖^2 :=
  ⟨ContactForm.H1_le_formNormSq hc u, ContactForm.formNormSq_le hc u⟩

/-- R-81E86877: all repulsive couplings use the same H1 form domain, and
the actual variational resolvents are norm-Lipschitz through zero coupling. -/
theorem gp07_zero_coupling {c : ℝ} (hc : 0 ≤ c) :
    ‖(Rop c hc : SymL2 L N →L[ℂ] SymL2 L N) - Rop 0 le_rfl‖ ≤
      ContactFormFamily.lipConst L N * |c| := by
  simpa only [sub_zero] using ContactFormFamily.Rop_lipschitz hc (le_refl (0 : ℝ))

/-- Literal coordinate-trace coupling normalization; this is a repository
contact-form fact, not a consequence of the abstract representation theorem. -/
theorem gp07_meanfield_normalization (κ : ℝ) (u v : PhysicalEnergy.PhysH1 L N) :
    ContactForm.q (κ / N) u v = ContactForm.kinSum u v +
      ((2 * (κ / N) : ℝ) : ℂ) * ContactForm.contactSum u v := rfl
end Contact
end QuantumNLS.Ext025SForms

#print axioms QuantumNLS.Ext025SForms.shift
#print axioms QuantumNLS.Ext025SForms.shift_selfAdjoint
#print axioms QuantumNLS.Ext025SForms.resolvent
#print axioms QuantumNLS.Ext025SForms.resolvent_symmetric
#print axioms QuantumNLS.Ext025SForms.adjoint_injective
#print axioms QuantumNLS.Ext025SForms.resolvent_injective
#print axioms QuantumNLS.Ext025SForms.inverse
#print axioms QuantumNLS.Ext025SForms.inverse_resolvent
#print axioms QuantumNLS.Ext025SForms.inverse_selfAdjoint
#print axioms QuantumNLS.Ext025SForms.Associated
#print axioms QuantumNLS.Ext025SForms.shifted_inverse_associated
#print axioms QuantumNLS.Ext025SForms.«FIN-EXT025-GP-07»
#print axioms QuantumNLS.Ext025SForms.form_core_dense
#print axioms QuantumNLS.Ext025SForms.form_core_preimage
#print axioms QuantumNLS.Ext025SForms.gp07_contact
#print axioms QuantumNLS.Ext025SForms.gp07_contact_norm
#print axioms QuantumNLS.Ext025SForms.gp07_zero_coupling
#print axioms QuantumNLS.Ext025SForms.gp07_meanfield_normalization

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025SForms." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Ext025SForms audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
