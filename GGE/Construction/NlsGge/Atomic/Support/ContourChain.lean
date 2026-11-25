/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams

Finite-family append/reversal and image proofs are adapted from
https://github.com/bjbraams/lean-CA, commit333a684877588d3667c7a0d37e5074aaa2e5b7b7,
ComplexAnalysis/Cycle.lean. The new endpoint-indexed C1-leaf tree represents the
actual accepted LIB042 finite concatenations; it makes no global C1 assertion.
-/

import NlsGge.Atomic.Support.ContourPiecewise

/-! Actual finite C1 chains and cycles, with literal path and leaf-integral bridges.

Leaves may have distinct endpoints. Only outer endpoints of a closed chain agree.
The empty cycle has empty trace and zero integral. This module carries no index,
Cauchy, source geometry, winding normalization, or idempotence assumptions.
-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval

namespace NlsGge.Atomic.ContourChain

/-- Actual finite C1 leaves with literally matching internal endpoints. -/
inductive Chain : ℂ → ℂ → Type
  | leaf {a b : ℂ} (γ : Path a b)
      (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1)) : Chain a b
  | join {a b c : ℂ} (p : Chain a b) (q : Chain b c) : Chain a c

namespace Chain

/-- The literal normalized concatenation; it need not be globally C1. -/
def path : {a b : ℂ} → Chain a b → Path a b
  | _, _, .leaf γ _ => γ
  | _, _, .join p q => (path p).trans (path q)

def trace {a b : ℂ} (c : Chain a b) : Set ℂ := Set.range c.path

/-- Integrability is proved at every actual C1 leaf. -/
def Integrable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] :
    {a b : ℂ} → (c : Chain a b) → (ω : ℂ → ℂ →L[ℂ] F) → Prop
  | _, _, .leaf γ _, ω => CurveIntegrable ω γ
  | _, _, .join p q, ω => Integrable p ω ∧ Integrable q ω

/-- Literal finite sum of the actual leaf curve integrals. -/
def integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] :
    {a b : ℂ} → (c : Chain a b) → (ω : ℂ → ℂ →L[ℂ] F) → F
  | _, _, .leaf γ _, ω => curveIntegral ω γ
  | _, _, .join p q, ω => integral p ω + integral q ω

@[simp] lemma path_leaf {a b : ℂ} (γ : Path a b) (hc) : (leaf γ hc).path = γ := rfl
@[simp] lemma path_join {a b c : ℂ} (p : Chain a b) (q : Chain b c) :
    (join p q).path = p.path.trans q.path := rfl

lemma path_piecewiseC1 {a b : ℂ} (c : Chain a b) : LIB042.PiecewiseC1 c.path := by
  induction c with
  | leaf γ hc => exact .ofC1 γ hc
  | join p q hp hq => exact .trans hp hq

@[simp] lemma trace_leaf {a b : ℂ} (γ : Path a b) (hc) :
    (leaf γ hc).trace = Set.range γ := rfl

lemma trace_join {a b c : ℂ} (p : Chain a b) (q : Chain b c) :
    (join p q).trace = p.trace ∪ q.trace := Path.trans_range _ _

lemma path_source {a b : ℂ} (c : Chain a b) : c.path 0 = a := c.path.source
lemma path_target {a b : ℂ} (c : Chain a b) : c.path 1 = b := c.path.target

lemma source_mem_trace {a b : ℂ} (c : Chain a b) : a ∈ c.trace :=
  ⟨0, c.path.source⟩
lemma target_mem_trace {a b : ℂ} (c : Chain a b) : b ∈ c.trace :=
  ⟨1, c.path.target⟩
lemma path_mem_trace {a b : ℂ} (c : Chain a b) (t : I) : c.path t ∈ c.trace :=
  mem_range_self t
lemma extend_mem_trace {a b : ℂ} (c : Chain a b) (t : ℝ) : c.path.extend t ∈ c.trace :=
  by
    change c.path.extend t ∈ Set.range c.path
    rw [← c.path.extend_range]
    exact mem_range_self t
lemma trace_subset_iff {a b : ℂ} (c : Chain a b) {U : Set ℂ} :
    c.trace ⊆ U ↔ ∀ t, c.path t ∈ U := Set.range_subset_iff
lemma isCompact_trace {a b : ℂ} (c : Chain a b) : IsCompact c.trace :=
  _root_.isCompact_range c.path.continuous

section Integrals
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {a b : ℂ} {c : Chain a b} {ω : ℂ → ℂ →L[ℂ] F}

lemma Integrable.curveIntegrable_path (hi : c.Integrable ω) : CurveIntegrable ω c.path := by
  induction c with
  | leaf γ hc => exact hi
  | join p q hp hq => exact (hp hi.1).trans (hq hi.2)

lemma integral_eq_curveIntegral (hi : c.Integrable ω) : c.integral ω = curveIntegral ω c.path := by
  induction c with
  | leaf γ hc => rfl
  | join p q hp hq =>
      change p.integral ω + q.integral ω = curveIntegral ω (p.path.trans q.path)
      rw [curveIntegral_trans hi.1.curveIntegrable_path hi.2.curveIntegrable_path,
        hp hi.1, hq hi.2]

lemma integrable_of_continuousOn {U : Set ℂ} (hω : ContinuousOn ω U)
    (himage : ∀ t, c.path t ∈ U) : c.Integrable ω := by
  induction c with
  | leaf γ hc => exact hω.curveIntegrable_of_contDiffOn hc himage
  | join p q hp hq =>
      have him : p.trace ∪ q.trace ⊆ U := by
        rw [← trace_join]
        exact (trace_subset_iff _).2 himage
      exact ⟨hp (fun t => him (Or.inl (p.path_mem_trace t))),
        hq (fun t => him (Or.inr (q.path_mem_trace t)))⟩

lemma integral_eq_of_path_eq {d : Chain a b} (he : c.path = d.path)
    (hc : c.Integrable ω) (hd : d.Integrable ω) : c.integral ω = d.integral ω := by
  rw [integral_eq_curveIntegral hc, integral_eq_curveIntegral hd, he]

lemma integral_eq_of_path_eq_of_continuousOn {d : Chain a b} {U : Set ℂ}
    (he : c.path = d.path) (hω : ContinuousOn ω U) (hcU : c.trace ⊆ U) :
    c.integral ω = d.integral ω := by
  have hdU : d.trace ⊆ U := by simpa only [trace, ← he] using hcU
  exact integral_eq_of_path_eq he
    (integrable_of_continuousOn hω ((trace_subset_iff _).1 hcU))
    (integrable_of_continuousOn hω ((trace_subset_iff _).1 hdU))

end Integrals

/-- The sum of actual leaf endpoint displacements. -/
def boundary : {a b : ℂ} → Chain a b → ℂ
  | a, b, .leaf _ _ => b - a
  | _, _, .join p q => boundary p + boundary q

lemma boundary_eq {a b : ℂ} (c : Chain a b) : c.boundary = b - a := by
  induction c with
  | leaf γ hc => rfl
  | join p q hp hq => change p.boundary + q.boundary = _; rw [hp, hq]; abel

lemma contDiffOn_symm {a b : ℂ} {γ : Path a b}
    (hc : ContDiffOn ℝ 1 γ.extend (Icc 0 1)) :
    ContDiffOn ℝ 1 γ.symm.extend (Icc 0 1) := by
  rw [Path.extend_symm]
  exact hc.comp (contDiff_const.sub contDiff_id).contDiffOn
    (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)

/-- Actual reversal, with reversed join order and proved C1 leaf regularity. -/
def reverse : {a b : ℂ} → Chain a b → Chain b a
  | _, _, .leaf γ hc => .leaf γ.symm (contDiffOn_symm hc)
  | _, _, .join p q => .join (reverse q) (reverse p)

lemma path_reverse {a b : ℂ} (c : Chain a b) : c.reverse.path = c.path.symm := by
  induction c with
  | leaf γ hc => rfl
  | join p q hp hq => simp only [reverse, path, hp, hq, Path.trans_symm]

lemma trace_reverse {a b : ℂ} (c : Chain a b) : c.reverse.trace = c.trace := by
  unfold trace
  rw [path_reverse, Path.symm_range]

lemma Integrable.reverse {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {a b : ℂ} {c : Chain a b} {ω : ℂ → ℂ →L[ℂ] F} (hi : c.Integrable ω) :
    c.reverse.Integrable ω := by
  induction c with
  | leaf γ hc => exact hi.symm
  | join p q hp hq => exact ⟨hq hi.2, hp hi.1⟩

lemma integral_reverse {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {a b : ℂ} {c : Chain a b} {ω : ℂ → ℂ →L[ℂ] F} (hi : c.Integrable ω) :
    c.reverse.integral ω = -c.integral ω := by
  rw [integral_eq_curveIntegral hi.reverse, path_reverse, curveIntegral_symm,
    integral_eq_curveIntegral hi]


/-- A genuine primitive on the trace computes the leaf sum by actual FTC.
Completeness excludes the incomplete-space integral convention. -/
theorem integral_eq_sub_of_hasDerivAt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {a b : ℂ} (c : Chain a b) {U : Set ℂ} {f P : ℂ → F}
    (hf : ContinuousOn f U) (hP : ∀ z ∈ U, HasDerivAt P (f z) z)
    (hcU : c.trace ⊆ U) :
    c.Integrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) ∧
      c.integral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) = P b - P a := by
  have hPc : ContinuousOn P U := fun z hz => (hP z hz).continuousAt.continuousWithinAt
  have hQ : Continuous (fun t : I => P (c.path t)) :=
    hPc.comp_continuous c.path.continuous (fun t => hcU (c.path_mem_trace t))
  have hlocal : ∀ t : I, ∃ Q : ℂ → F, HasDerivAt Q (f (c.path t)) (c.path t) ∧
      ∀ᶠ u in 𝓝 t, P (c.path u) = P (c.path t) + (Q (c.path u) - Q (c.path t)) := by
    intro t
    refine ⟨P, hP _ (hcU (c.path_mem_trace t)), Filter.Eventually.of_forall ?_⟩
    intro u
    abel
  have he := (ContourPiecewise.curveIntegral_eq_sub_of_locally_primitive_of_piecewiseC1
    c.path.continuous hQ hlocal hf (r := id) continuous_id (fun _ => rfl)
    c.path_piecewiseC1 (fun t => hcU (c.path_mem_trace t))).2
  have hi := integrable_of_continuousOn
    ((ContinuousLinearMap.toSpanSingletonLIE ℂ F).continuous.comp_continuousOn hf)
    (fun t => hcU (c.path_mem_trace t))
  refine ⟨hi, ?_⟩
  calc
    c.integral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) =
        curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) c.path :=
      integral_eq_curveIntegral hi
    _ = P (c.path 1) - P (c.path 0) := he
    _ = P b - P a := by rw [path_target, path_source]

end Chain

/-- Reconstruction stays in Prop: no elimination of PiecewiseC1 proofs into Type. -/
theorem exists_chain_of_piecewiseC1 {a b : ℂ} {γ : Path a b}
    (hγ : LIB042.PiecewiseC1 γ) : ∃ c : Chain a b, c.path = γ := by
  induction hγ with
  | ofC1 γ hc => exact ⟨.leaf γ hc, rfl⟩
  | trans hγ hδ hp hq =>
      obtain ⟨p, hp⟩ := hp
      obtain ⟨q, hq⟩ := hq
      exact ⟨.join p q, by simp only [Chain.path_join, hp, hq]⟩

/-- Only the outer endpoints are required to agree. -/
abbrev ClosedChain := Σ a : ℂ, Chain a a

/-- A genuine finite family of closed chains, including the empty family. -/
structure Cycle where
  n : ℕ
  chain : Fin n → ClosedChain

namespace Cycle

def range (Γ : Cycle) : Set ℂ := ⋃ i, (Γ.chain i).2.trace

def Integrable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (Γ : Cycle) (ω : ℂ → ℂ →L[ℂ] F) : Prop := ∀ i, (Γ.chain i).2.Integrable ω

def integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (Γ : Cycle) (ω : ℂ → ℂ →L[ℂ] F) : F := ∑ i, (Γ.chain i).2.integral ω

def empty : Cycle := ⟨0, Fin.elim0⟩
def single (c : ClosedChain) : Cycle := ⟨1, fun _ => c⟩
def append (Γ Δ : Cycle) : Cycle := ⟨Γ.n + Δ.n, Fin.append Γ.chain Δ.chain⟩
def reverse (Γ : Cycle) : Cycle := ⟨Γ.n, fun i => ⟨(Γ.chain i).1, (Γ.chain i).2.reverse⟩⟩

@[simp] lemma range_empty : empty.range = ∅ := by simp [range, empty]
@[simp] lemma integrable_empty {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (ω : ℂ → ℂ →L[ℂ] F) : empty.Integrable ω := fun i => Fin.elim0 i
@[simp] lemma integral_empty {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (ω : ℂ → ℂ →L[ℂ] F) : empty.integral ω = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact Fin.elim0 i

lemma chain_mem_range (Γ : Cycle) (i : Fin Γ.n) (t : I) :
    (Γ.chain i).2.path t ∈ Γ.range := mem_iUnion.mpr ⟨i, mem_range_self t⟩
lemma chain_extend_mem_range (Γ : Cycle) (i : Fin Γ.n) (t : ℝ) :
    (Γ.chain i).2.path.extend t ∈ Γ.range :=
  mem_iUnion.mpr ⟨i, (Γ.chain i).2.extend_mem_trace t⟩
lemma range_subset_iff (Γ : Cycle) {U : Set ℂ} :
    Γ.range ⊆ U ↔ ∀ i t, (Γ.chain i).2.path t ∈ U := by
  simp only [range, iUnion_subset_iff, Chain.trace_subset_iff]
lemma isCompact_range (Γ : Cycle) : IsCompact Γ.range :=
  isCompact_iUnion fun i => (Γ.chain i).2.isCompact_trace
lemma isClosed_range (Γ : Cycle) : IsClosed Γ.range := Γ.isCompact_range.isClosed
lemma isBounded_range (Γ : Cycle) : Bornology.IsBounded Γ.range := Γ.isCompact_range.isBounded
lemma isOpen_compl_range (Γ : Cycle) : IsOpen Γ.rangeᶜ := Γ.isClosed_range.isOpen_compl

section Integrals
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {Γ : Cycle} {ω : ℂ → ℂ →L[ℂ] F}

lemma integrable_of_continuousOn {U : Set ℂ} (hω : ContinuousOn ω U) (hΓ : Γ.range ⊆ U) :
    Γ.Integrable ω := fun i => Chain.integrable_of_continuousOn hω
      (fun t => hΓ (Γ.chain_mem_range i t))

lemma integral_eq_sum_curveIntegral (hi : Γ.Integrable ω) :
    Γ.integral ω = ∑ i, curveIntegral ω (Γ.chain i).2.path := by
  unfold integral
  exact Finset.sum_congr rfl (fun i _ => Chain.integral_eq_curveIntegral (hi i))

lemma Integrable.reverse (hi : Γ.Integrable ω) : Γ.reverse.Integrable ω :=
  fun i => (hi i).reverse

lemma integral_reverse (hi : Γ.Integrable ω) : Γ.reverse.integral ω = -Γ.integral ω := by
  change (∑ i, (Γ.chain i).2.reverse.integral ω) = -(∑ i, (Γ.chain i).2.integral ω)
  simp only [Chain.integral_reverse (hi _), Finset.sum_neg_distrib]

end Integrals

lemma range_reverse (Γ : Cycle) : Γ.reverse.range = Γ.range := by
  simp only [range, reverse, Chain.trace_reverse]


@[simp] lemma range_single (c : ClosedChain) : (single c).range = c.2.trace := by
  change (⋃ _ : Fin 1, c.2.trace) = c.2.trace
  simp only [iUnion_const]

lemma append_chain_castAdd (Γ Δ : Cycle) (i : Fin Γ.n) :
    (Γ.append Δ).chain (Fin.castAdd Δ.n i) = Γ.chain i := Fin.append_left _ _ _
lemma append_chain_natAdd (Γ Δ : Cycle) (i : Fin Δ.n) :
    (Γ.append Δ).chain (Fin.natAdd Γ.n i) = Δ.chain i := Fin.append_right _ _ _

lemma range_append (Γ Δ : Cycle) : (Γ.append Δ).range = Γ.range ∪ Δ.range := by
  ext z
  simp only [range, mem_iUnion, mem_union]
  constructor
  · rintro ⟨i, hi⟩
    induction i using Fin.addCases with
    | left i => exact Or.inl ⟨i, (Γ.append_chain_castAdd Δ i) ▸ hi⟩
    | right i => exact Or.inr ⟨i, (Γ.append_chain_natAdd Δ i) ▸ hi⟩
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact ⟨Fin.castAdd _ i, (Γ.append_chain_castAdd Δ i).symm ▸ hi⟩
    · exact ⟨Fin.natAdd _ i, (Γ.append_chain_natAdd Δ i).symm ▸ hi⟩

section AppendIntegrals
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {Γ Δ : Cycle} {ω : ℂ → ℂ →L[ℂ] F}

lemma Integrable.append (hΓ : Γ.Integrable ω) (hΔ : Δ.Integrable ω) :
    (Γ.append Δ).Integrable ω := by
  intro i
  induction i using Fin.addCases with
  | left i => exact (Γ.append_chain_castAdd Δ i).symm ▸ hΓ i
  | right i => exact (Γ.append_chain_natAdd Δ i).symm ▸ hΔ i

lemma integral_append (Γ Δ : Cycle) (ω : ℂ → ℂ →L[ℂ] F) :
    (Γ.append Δ).integral ω = Γ.integral ω + Δ.integral ω := by
  change (∑ i : Fin (Γ.n + Δ.n), ((Γ.append Δ).chain i).2.integral ω) = _
  rw [Fin.sum_univ_add]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => by rw [append_chain_castAdd])
  · exact Finset.sum_congr rfl (fun i _ => by rw [append_chain_natAdd])

@[simp] lemma integral_single (c : ClosedChain) (ω : ℂ → ℂ →L[ℂ] F) :
    (single c).integral ω = c.2.integral ω := by
  change (∑ _ : Fin 1, c.2.integral ω) = c.2.integral ω
  simp only [Fin.sum_univ_one]

end AppendIntegrals

/-- Primitive integrals over finite families of actual closed chains vanish,
including the empty family. No Cauchy or index hypothesis is used. -/
theorem integral_eq_zero_of_hasDerivAt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (Γ : Cycle) {U : Set ℂ} {f P : ℂ → F}
    (hf : ContinuousOn f U) (hP : ∀ z ∈ U, HasDerivAt P (f z) z)
    (hΓU : Γ.range ⊆ U) :
    Γ.Integrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) ∧
      Γ.integral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) = 0 := by
  have hc (i : Fin Γ.n) := (Γ.chain i).2.integral_eq_sub_of_hasDerivAt hf hP
    (fun z hz => hΓU (mem_iUnion.mpr ⟨i, hz⟩))
  refine ⟨fun i => (hc i).1, ?_⟩
  unfold integral
  apply Finset.sum_eq_zero
  intro i _
  simpa only [sub_self] using (hc i).2

end Cycle
end NlsGge.Atomic.ContourChain
