import QuantumNLS.Ext025SForms
import Mathlib.Topology.MetricSpace.Cauchy

/-! GP-07: construct the shifted-form Hilbert space from an unbundled
Hermitian form, a lower bound, and the sequence definition of closedness.
The square-root domain representation remains a separate open clause. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Filter Topology
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.Ext025B7ClosedForm
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Raw form data. Closedness is stated in the original ambient space and
in the explicit scalar form distance; no Hilbert encoding is a premise. -/
structure FormData (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  domain : Submodule ℂ E
  q : domain → domain → ℂ
  bound : ℝ
  hermitian : ∀ u v, conj (q v u) = q u v
  add_left : ∀ u v w, q (u+v) w = q u w+q v w
  smul_left : ∀ u v c, q (c • u) v = conj c*q u v
  lower : ∀ u : domain, bound*‖(u : E)‖^2 ≤ (q u u).re
  dense : DenseRange (fun u : domain => (u : E))
  closed : ∀ (u : ℕ → domain) (x : E),
    (∀ ε > 0, ∃ M : ℕ, ∀ n ≥ M, ∀ m ≥ M,
      Real.sqrt ((q (u n-u m) (u n-u m)).re+(1-bound)*‖((u n-u m : domain) : E)‖^2) < ε) →
    Tendsto (fun n => (u n : E)) atTop (𝓝 x) →
    ∃ v : domain, (v : E) = x ∧
      Tendsto (fun n => Real.sqrt ((q (u n-v) (u n-v)).re+
        (1-bound)*‖((u n-v : domain) : E)‖^2)) atTop (𝓝 0)

/-- A fresh carrier, so the ambient subspace norm is never overwritten. -/
def FormSpace (F : FormData E) : Type _ := F.domain

def toDomain (F : FormData E) (u : FormSpace F) : F.domain := u

def ambient (F : FormData E) (u : FormSpace F) : E := (toDomain F u).val

instance form_add (F : FormData E) : AddCommGroup (FormSpace F) :=
  inferInstanceAs (AddCommGroup F.domain)
instance form_module (F : FormData E) : Module ℂ (FormSpace F) :=
  inferInstanceAs (Module ℂ F.domain)

theorem toDomain_add (F : FormData E) (u v : FormSpace F) :
    toDomain F (u+v) = toDomain F u+toDomain F v := rfl
theorem toDomain_sub (F : FormData E) (u v : FormSpace F) :
    toDomain F (u-v) = toDomain F u-toDomain F v := rfl
theorem toDomain_smul (F : FormData E) (c : ℂ) (u : FormSpace F) :
    toDomain F (c • u) = c • toDomain F u := rfl

def formQ (F : FormData E) (u v : FormSpace F) : ℂ := F.q (toDomain F u) (toDomain F v)

theorem formQ_hermitian (F : FormData E) (u v : FormSpace F) :
    conj (formQ F v u) = formQ F u v := F.hermitian _ _
theorem formQ_add (F : FormData E) (u v w : FormSpace F) :
    formQ F (u+v) w = formQ F u w+formQ F v w := by
  simp only [formQ,toDomain_add,F.add_left]
theorem formQ_smul (F : FormData E) (u v : FormSpace F) (c : ℂ) :
    formQ F (c • u) v = conj c*formQ F u v := by
  simp only [formQ,toDomain_smul,F.smul_left]

def formInner (F : FormData E) (u v : FormSpace F) : ℂ :=
  formQ F u v+((1-F.bound : ℝ) : ℂ)*⟪ambient F u,ambient F v⟫_ℂ

theorem formInner_re (F : FormData E) (u : FormSpace F) :
    (formInner F u u).re = (formQ F u u).re+(1-F.bound)*‖ambient F u‖^2 := by
  have hn : (⟪ambient F u,ambient F u⟫_ℂ).re = ‖ambient F u‖^2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (ambient F u)).symm
  simp only [formInner,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,hn]

theorem formInner_coercive (F : FormData E) (u : FormSpace F) :
    ‖ambient F u‖^2 ≤ (formInner F u u).re := by
  rw [formInner_re]
  have h : F.bound*‖ambient F u‖^2 ≤ (formQ F u u).re := F.lower (toDomain F u)
  nlinarith [h]

@[instance_reducible]
def core (F : FormData E) : InnerProductSpace.Core ℂ (FormSpace F) where
  inner := formInner F
  conj_inner_symm u v := by
    simp only [formInner,map_add,map_mul,formQ_hermitian,Complex.conj_ofReal,inner_conj_symm]
  re_inner_nonneg u := (sq_nonneg _).trans (formInner_coercive F u)
  add_left u v w := by
    have he : ambient F (u+v) = ambient F u+ambient F v := rfl
    simp only [formInner,formQ_add,he,inner_add_left]
    ring
  smul_left u v c := by
    have he : ambient F (c • u) = c • ambient F u := rfl
    simp only [formInner,formQ_smul,he,inner_smul_left]
    ring
  definite u hu := by
    have h := formInner_coercive F u
    rw [hu,Complex.zero_re] at h
    have hz : ambient F u = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (ambient F u)])
    exact Subtype.ext hz

instance form_normed (F : FormData E) : NormedAddCommGroup (FormSpace F) :=
  letI : InnerProductSpace.Core ℂ (FormSpace F) := core F
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance form_innerProduct (F : FormData E) : InnerProductSpace ℂ (FormSpace F) :=
  InnerProductSpace.ofCore (core F).toCore

theorem inner_eq (F : FormData E) (u v : FormSpace F) :
    ⟪u,v⟫_ℂ = formQ F u v+((1-F.bound : ℝ) : ℂ)*⟪ambient F u,ambient F v⟫_ℂ := rfl

theorem norm_eq (F : FormData E) (u : FormSpace F) :
    ‖u‖ = Real.sqrt ((formQ F u u).re+(1-F.bound)*‖ambient F u‖^2) := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) u]
  exact congrArg Real.sqrt (formInner_re F u)

theorem ambient_norm_le (F : FormData E) (u : FormSpace F) : ‖ambient F u‖ ≤ ‖u‖ := by
  have h := formInner_coercive F u
  have hn : (⟪u,u⟫_ℂ).re = ‖u‖^2 := (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
  change ‖ambient F u‖^2 ≤ (⟪u,u⟫_ℂ).re at h
  rw [hn] at h
  nlinarith [norm_nonneg (ambient F u),norm_nonneg u]

/-- The inclusion is constructed with its coercive bound. -/
def inclusion (F : FormData E) : FormSpace F →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := fun u => ambient F u
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun u => by
      change ‖ambient F u‖ ≤ 1*‖u‖
      simpa only [one_mul] using ambient_norm_le F u)

theorem inclusion_apply (F : FormData E) (u : FormSpace F) : inclusion F u = ambient F u := rfl

theorem inclusion_injective (F : FormData E) : Function.Injective (inclusion F) :=
  Subtype.val_injective

theorem inclusion_dense (F : FormData E) : DenseRange (inclusion F) := F.dense

variable [CompleteSpace E]

/-- Ambient completeness plus raw closedness yields form-space completeness. -/
instance form_complete (F : FormData E) : CompleteSpace (FormSpace F) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hambient : CauchySeq (fun n => inclusion F (u n)) :=
    (inclusion F).uniformContinuous.comp_cauchySeq hu
  obtain ⟨x,hx⟩ := cauchySeq_tendsto_of_complete hambient
  have hraw : ∀ ε > 0, ∃ M : ℕ, ∀ n ≥ M, ∀ m ≥ M,
      Real.sqrt ((F.q (toDomain F (u n)-toDomain F (u m))
        (toDomain F (u n)-toDomain F (u m))).re+
        (1-F.bound)*‖((toDomain F (u n)-toDomain F (u m) : F.domain) : E)‖^2) < ε := by
    intro ε hε
    obtain ⟨M,hM⟩ := Metric.cauchySeq_iff.mp hu ε hε
    refine ⟨M,fun n hn m hm => ?_⟩
    change Real.sqrt ((formQ F (u n-u m) (u n-u m)).re+
      (1-F.bound)*‖ambient F (u n-u m)‖^2) < ε
    rw [← norm_eq F (u n-u m)]
    simpa only [dist_eq_norm] using hM n hn m hm
  obtain ⟨v,hv,hlim⟩ := F.closed (fun n => toDomain F (u n)) x hraw hx
  let vf : FormSpace F := v
  refine ⟨vf,?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [norm_eq F]
  exact hlim

omit [CompleteSpace E] in
/-- The formerly supplied shifted Hilbert encoding is now a conclusion. -/
theorem shifted_encoding (F : FormData E) :
    Function.Injective (inclusion F) ∧ DenseRange (inclusion F) ∧
    ∀ u v : FormSpace F,
      formQ F u v+((1-F.bound : ℝ) : ℂ)*⟪inclusion F u,inclusion F v⟫_ℂ = ⟪u,v⟫_ℂ :=
  ⟨inclusion_injective F,inclusion_dense F,fun _ _ => rfl⟩

/-- The frozen variational theorem now applies to raw closed-form data.
The exact operator domain is the all-test-vector graph, distinct from the
form domain. This does not assert the separate square-root representation. -/
theorem associated_operator (F : FormData E) :
    ∃! T : E →ₗ.[ℂ] E, IsSelfAdjoint T ∧
      Ext025SForms.Associated (inclusion F) (formQ F) T ∧ T.IsClosed ∧
      ∀ x : T.domain, -((1-F.bound)*‖(x : E)‖^2) ≤ (⟪(x : E),T x⟫_ℂ).re :=
  Ext025SForms.«FIN-EXT025-GP-07» (inclusion F) (inclusion_injective F)
    (inclusion_dense F) (formQ F) (1-F.bound) (fun _ _ => rfl)

omit [CompleteSpace E] in
/-- The form domain is exactly the original submodule, with its newly
constructed form topology; no operator domain is substituted for it. -/
theorem inclusion_range (F : FormData E) : (inclusion F).range = F.domain := by
  apply Submodule.ext
  intro x
  constructor
  · rintro ⟨u,rfl⟩
    exact (toDomain F u).property
  · intro hx
    exact ⟨⟨x,hx⟩,rfl⟩

omit [CompleteSpace E] in
/-- The associated operator retains the original numerical lower bound b,
not merely the weaker coercive-shift lower bound. -/
theorem associated_lower_bound (F : FormData E) (T : E →ₗ.[ℂ] E)
    (ha : Ext025SForms.Associated (inclusion F) (formQ F) T) (x : T.domain) :
    F.bound*‖(x : E)‖^2 ≤ (⟪(x : E),T x⟫_ℂ).re := by
  obtain ⟨u,hu,hq⟩ := (ha x (T x)).mp ⟨x.property,rfl⟩
  have h := F.lower (toDomain F u)
  change F.bound*‖inclusion F u‖^2 ≤ (formQ F u u).re at h
  have he := hq u
  rw [hu] at he
  rw [he] at h
  rw [hu] at h
  exact h

end QuantumNLS.Ext025B7ClosedForm

#print axioms QuantumNLS.Ext025B7ClosedForm.FormData
#print axioms QuantumNLS.Ext025B7ClosedForm.FormSpace
#print axioms QuantumNLS.Ext025B7ClosedForm.toDomain
#print axioms QuantumNLS.Ext025B7ClosedForm.ambient
#print axioms QuantumNLS.Ext025B7ClosedForm.form_add
#print axioms QuantumNLS.Ext025B7ClosedForm.form_module
#print axioms QuantumNLS.Ext025B7ClosedForm.toDomain_add
#print axioms QuantumNLS.Ext025B7ClosedForm.toDomain_sub
#print axioms QuantumNLS.Ext025B7ClosedForm.toDomain_smul
#print axioms QuantumNLS.Ext025B7ClosedForm.formQ
#print axioms QuantumNLS.Ext025B7ClosedForm.formQ_hermitian
#print axioms QuantumNLS.Ext025B7ClosedForm.formQ_add
#print axioms QuantumNLS.Ext025B7ClosedForm.formQ_smul
#print axioms QuantumNLS.Ext025B7ClosedForm.formInner
#print axioms QuantumNLS.Ext025B7ClosedForm.formInner_re
#print axioms QuantumNLS.Ext025B7ClosedForm.formInner_coercive
#print axioms QuantumNLS.Ext025B7ClosedForm.core
#print axioms QuantumNLS.Ext025B7ClosedForm.form_normed
#print axioms QuantumNLS.Ext025B7ClosedForm.form_innerProduct
#print axioms QuantumNLS.Ext025B7ClosedForm.inner_eq
#print axioms QuantumNLS.Ext025B7ClosedForm.norm_eq
#print axioms QuantumNLS.Ext025B7ClosedForm.ambient_norm_le
#print axioms QuantumNLS.Ext025B7ClosedForm.inclusion
#print axioms QuantumNLS.Ext025B7ClosedForm.inclusion_apply
#print axioms QuantumNLS.Ext025B7ClosedForm.inclusion_injective
#print axioms QuantumNLS.Ext025B7ClosedForm.inclusion_dense
#print axioms QuantumNLS.Ext025B7ClosedForm.form_complete
#print axioms QuantumNLS.Ext025B7ClosedForm.shifted_encoding
#print axioms QuantumNLS.Ext025B7ClosedForm.associated_operator
#print axioms QuantumNLS.Ext025B7ClosedForm.inclusion_range
#print axioms QuantumNLS.Ext025B7ClosedForm.associated_lower_bound

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025B7ClosedForm." then
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
  Lean.logInfo m!"Ext025B7ClosedForm audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
