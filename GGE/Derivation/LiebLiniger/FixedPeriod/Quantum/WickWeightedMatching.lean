import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Embedding
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-! MATERIAL Group2 Q2-024 proof unit: exact WEIGHTED ordered matchings.
Only the original physical matching DATA and unused-coordinate scalar product
are required. No actual operator/Module.End/word quantization is imported,
no matching/derivative identity is assumed, and repeated fields are retained.
The output theorem earns the literal j! weighted matching coefficient for the
SAME source DATA. This unit is NOT an atomic Q2-024 completion. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

structure SourceWickMatchingTerm where
  inputDegree : ℕ
  outputDegree : ℕ
  inputFields : Fin inputDegree → Lp ℂ 2 μ
  outputFields : Fin outputDegree → Lp ℂ 2 μ
  contractions : ℕ
  coefficient : ℂ

/-- An uncontracted head annihilation is retained in its original input order. -/
def sourceMatchingKeep (g : Lp ℂ 2 μ) (t : SourceWickMatchingTerm μ) :
    SourceWickMatchingTerm μ :=
  { t with
    inputDegree := t.inputDegree + 1
    inputFields := Fin.cons g t.inputFields }

/-- One genuine contraction: record its actual inner product and increase j.
No epsilon appears in this combinatorial coefficient. -/
def sourceMatchingContract (c : ℂ) (t : SourceWickMatchingTerm μ) :
    SourceWickMatchingTerm μ :=
  { t with contractions := t.contractions + 1, coefficient := c * t.coefficient }

/-- All ordered partial matchings of actual input/output physical field slots.
The uncontracted branch keeps the head; each contracted branch removes exactly
one current creator slot. Equal resulting terms are deliberately NOT deduplicated. -/
def sourceWickMatchingTerms : (p : ℕ) → (Fin p → Lp ℂ 2 μ) →
    (q : ℕ) → (Fin q → Lp ℂ 2 μ) → List (SourceWickMatchingTerm μ)
  | 0, gs, q, hs =>
    [{ inputDegree := 0, outputDegree := q, inputFields := gs, outputFields := hs,
       contractions := 0, coefficient := 1 }]
  | p + 1, gs, 0, hs =>
    (sourceWickMatchingTerms p (Fin.tail gs) 0 hs).map (sourceMatchingKeep μ (gs 0))
  | p + 1, gs, q + 1, hs =>
    (sourceWickMatchingTerms p (Fin.tail gs) (q + 1) hs).map (sourceMatchingKeep μ (gs 0)) ++
      (List.ofFn (fun i : Fin (q + 1) =>
        (sourceWickMatchingTerms p (Fin.tail gs) q (i.removeNth hs)).map
          (sourceMatchingContract μ (inner ℂ (gs 0) (hs i))))).flatten

def physicalUnusedProduct {p j : ℕ} (gs : Fin p → Lp ℂ 2 μ)
    (e : Fin j ↪ Fin p) (u : Lp ℂ 2 μ) : ℂ := by
  classical
  exact ∏ k : Fin p, if k ∈ Set.range e then 1 else inner ℂ (gs k) u


end LiebLiniger.FixedPeriod.Quantum
end


/-! Source-exact WEIGHTED matching bijection/recurrence for Q2-024.
All finite source positions and every original complex physical factor are retained.
SOURCE ONLY / UNCOMPILED; independent source review and kernel gates pending. -/
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-! Explicit selected-head / omitted-head finite embedding bijections needed
for the physical WEIGHTED matching recurrence. No field values are compared.
SOURCE ONLY / UNCOMPILED. -/

/-- Omit exactly one original codomain slot. Inverse uses the genuine
succAbove equivalence, so the last slot and zero remaining slots are included. -/
def sourceMatchingAvoidEmbeddingEquiv (j n : ℕ) (t : Fin (n + 1)) :
    (Fin j ↪ Fin n) ≃ {a : Fin j ↪ Fin (n + 1) // t ∉ Set.range a} where
  toFun a := ⟨a.trans t.succAboveEmb, by
    rintro ⟨i, hi⟩
    exact (t.succAbove_ne (a i)) hi⟩
  invFun a :=
    { toFun := fun i => (finSuccAboveEquiv t).symm
        ⟨a.1 i, fun h => a.2 ⟨i, h⟩⟩
      inj' := by
        intro i k h
        apply a.1.injective
        have hs := congrArg (fun z : Fin n => ((finSuccAboveEquiv t) z).val) h
        simpa only [Equiv.apply_symm_apply] using hs }
  left_inv a := by
    apply Function.Embedding.ext
    intro i
    exact (finSuccAboveEquiv t).symm_apply_apply (a i)
  right_inv a := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    have hs := (finSuccAboveEquiv t).apply_symm_apply
      (⟨a.1 i, fun h => a.2 ⟨i, h⟩⟩ : {x : Fin (n + 1) // x ≠ t})
    exact congrArg Subtype.val hs

/-- Put one selected matched pair first, and retain the literal order of every
other original creator/annihilator slot via succAbove. -/
def sourceMatchingInsertHeadEmbedding {j n : ℕ} (t : Fin (n + 1))
    (a : Fin j ↪ Fin n) : Fin (j + 1) ↪ Fin (n + 1) :=
  (Equiv.embeddingFinSucc j (Fin (n + 1))).symm
    ⟨(sourceMatchingAvoidEmbeddingEquiv j n t a).1,
      ⟨t, (sourceMatchingAvoidEmbeddingEquiv j n t a).2⟩⟩

@[simp] theorem sourceMatchingInsertHeadEmbedding_zero {j n : ℕ}
    (t : Fin (n + 1)) (a : Fin j ↪ Fin n) :
    sourceMatchingInsertHeadEmbedding t a 0 = t := by
  unfold sourceMatchingInsertHeadEmbedding
  simpa only [Fin.cons_zero] using congrFun
    (Equiv.coe_embeddingFinSucc_symm
      (⟨(sourceMatchingAvoidEmbeddingEquiv j n t a).1,
        ⟨t, (sourceMatchingAvoidEmbeddingEquiv j n t a).2⟩⟩ :
        Σ f : Fin j ↪ Fin (n + 1), {i // i ∉ Set.range f})) 0

@[simp] theorem sourceMatchingInsertHeadEmbedding_succ {j n : ℕ}
    (t : Fin (n + 1)) (a : Fin j ↪ Fin n) (i : Fin j) :
    sourceMatchingInsertHeadEmbedding t a i.succ = t.succAbove (a i) := by
  unfold sourceMatchingInsertHeadEmbedding
  have h := congrFun (Equiv.coe_embeddingFinSucc_symm
    (⟨(sourceMatchingAvoidEmbeddingEquiv j n t a).1,
      ⟨t, (sourceMatchingAvoidEmbeddingEquiv j n t a).2⟩⟩ :
      Σ f : Fin j ↪ Fin (n + 1), {i // i ∉ Set.range f})) i.succ
  simp only [Fin.cons_succ] at h
  exact h.trans (show (sourceMatchingAvoidEmbeddingEquiv j n t a).1 i =
    t.succAbove (a i) from rfl)

/-- This is an actual bijection, not a counting premise: an embedding with
first value t is exactly a remaining embedding avoiding the deleted slot. -/
def sourceMatchingHeadEmbeddingEquiv (j n : ℕ) (t : Fin (n + 1)) :
    (Fin j ↪ Fin n) ≃ {a : Fin (j + 1) ↪ Fin (n + 1) // a 0 = t} where
  toFun a := ⟨sourceMatchingInsertHeadEmbedding t a,
    sourceMatchingInsertHeadEmbedding_zero t a⟩
  invFun a := (sourceMatchingAvoidEmbeddingEquiv j n t).symm
    ⟨(Equiv.embeddingFinSucc j (Fin (n + 1)) a.1).1, by
      rintro ⟨i, hi⟩
      have hhead := (Equiv.embeddingFinSucc j (Fin (n + 1)) a.1).2.property
      apply hhead
      exact ⟨i, hi.trans a.2.symm⟩⟩
  left_inv a := by
    apply (sourceMatchingAvoidEmbeddingEquiv j n t).injective
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    have htail : (sourceMatchingAvoidEmbeddingEquiv j n t a).1 i =
        t.succAbove (a i) := rfl
    simpa only [Equiv.apply_symm_apply, Equiv.embeddingFinSucc_fst,
      Function.comp_apply] using
        (sourceMatchingInsertHeadEmbedding_succ t a i).trans htail.symm
  right_inv a := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · exact (sourceMatchingInsertHeadEmbedding_zero t _).trans a.2.symm
    · rw [sourceMatchingInsertHeadEmbedding_succ]
      have h := (sourceMatchingAvoidEmbeddingEquiv j n t).apply_symm_apply
        (⟨(Equiv.embeddingFinSucc j (Fin (n + 1)) a.1).1, by
          rintro ⟨l, hl⟩
          have hhead := (Equiv.embeddingFinSucc j (Fin (n + 1)) a.1).2.property
          exact hhead ⟨l, hl.trans a.2.symm⟩⟩ :
          {b : Fin j ↪ Fin (n + 1) // t ∉ Set.range b})
      exact congrFun (congrArg (fun b => (b.1 : Fin j → Fin (n + 1))) h) k


/-! Weighted simultaneous-reindexing and unique selected-head multiplicity.
These are finite scalar identities retaining every original physical field.
SOURCE ONLY / UNCOMPILED; not yet the whole matching-list identity. -/

private theorem embedding_range_precomp {j p : ℕ}
    (a : Fin j ↪ Fin p) (σ : Equiv.Perm (Fin j)) :
    Set.range (σ.toEmbedding.trans a) = Set.range a := by
  ext k
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨σ i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨σ.symm i, by simp⟩


/-- Pure polarized weight of one ORDERED embedding pair. -/
def sourceWickOrderedPairWeight {p q j : ℕ}
    (gs : Fin p → Lp ℂ 2 μ) (hs : Fin q → Lp ℂ 2 μ)
    (v u : Lp ℂ 2 μ) (a : Fin j ↪ Fin p) (b : Fin j ↪ Fin q) : ℂ :=
  physicalUnusedProduct μ gs a u * conj (physicalUnusedProduct μ hs b v) *
    ∏ i : Fin j, inner ℂ (gs (a i)) (hs (b i))

/-- Relabeling matched positions simultaneously changes NONE of the physical
weight, including spectator factors. No distinct-field assumption is used. -/
theorem sourceWickOrderedPairWeight_precomp {p q j : ℕ}
    (gs : Fin p → Lp ℂ 2 μ) (hs : Fin q → Lp ℂ 2 μ)
    (v u : Lp ℂ 2 μ) (a : Fin j ↪ Fin p) (b : Fin j ↪ Fin q)
    (σ : Equiv.Perm (Fin j)) :
    sourceWickOrderedPairWeight μ gs hs v u
      (σ.toEmbedding.trans a) (σ.toEmbedding.trans b) =
      sourceWickOrderedPairWeight μ gs hs v u a b := by
  classical
  have ha : physicalUnusedProduct μ gs (σ.toEmbedding.trans a) u =
      physicalUnusedProduct μ gs a u := by
    unfold physicalUnusedProduct
    apply Finset.prod_congr rfl
    intro k hk
    simp only [embedding_range_precomp]
  have hb : physicalUnusedProduct μ hs (σ.toEmbedding.trans b) v =
      physicalUnusedProduct μ hs b v := by
    unfold physicalUnusedProduct
    apply Finset.prod_congr rfl
    intro k hk
    simp only [embedding_range_precomp]
  unfold sourceWickOrderedPairWeight
  rw [ha, hb]
  congr 1
  exact Equiv.prod_comp σ (fun i => inner ℂ (gs (a i)) (hs (b i)))

private def precompEmbeddingEquiv {j p : ℕ} (σ : Equiv.Perm (Fin j)) :
    (Fin j ↪ Fin p) ≃ (Fin j ↪ Fin p) where
  toFun a := σ.toEmbedding.trans a
  invFun a := σ.symm.toEmbedding.trans a
  left_inv a := by ext i; simp
  right_inv a := by ext i; simp

/-- Selecting annihilator0 somewhere among ordered matches produces EXACTLY
j+1 copies of the weight with annihilator0 in the first matched position.
The factor is earned by UNIQUE source slots and actual weighted invariance,
not by counting equal-valued physical fields or forgetting their factors. -/
theorem sourceWickOrderedPairWeight_selected_head (p q j : ℕ)
    (gs : Fin (p + 1) → Lp ℂ 2 μ) (hs : Fin q → Lp ℂ 2 μ)
    (v u : Lp ℂ 2 μ) :
    (∑ a : Fin (j + 1) ↪ Fin (p + 1), ∑ b : Fin (j + 1) ↪ Fin q,
      if (0 : Fin (p + 1)) ∈ Set.range a then
        sourceWickOrderedPairWeight μ gs hs v u a b else 0) =
      ((j + 1 : ℕ) : ℂ) *
        (∑ a : Fin (j + 1) ↪ Fin (p + 1), ∑ b : Fin (j + 1) ↪ Fin q,
          if a 0 = 0 then sourceWickOrderedPairWeight μ gs hs v u a b else 0) := by
  classical
  let W := sourceWickOrderedPairWeight (j := j + 1) μ gs hs v u
  have hpoint (a : Fin (j + 1) ↪ Fin (p + 1)) (b : Fin (j + 1) ↪ Fin q) :
      (if (0 : Fin (p + 1)) ∈ Set.range a then W a b else 0) =
        ∑ k : Fin (j + 1), if a k = 0 then W a b else 0 := by
    by_cases h : (0 : Fin (p + 1)) ∈ Set.range a
    · obtain ⟨i, hi⟩ := h
      have heq (k : Fin (j + 1)) : a k = 0 ↔ k = i := by
        rw [← hi]
        exact a.injective.eq_iff
      have hmem : (0 : Fin (p + 1)) ∈ Set.range a := ⟨i, hi⟩
      rw [if_pos hmem]
      simp only [heq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    · have hh (k : Fin (j + 1)) : a k ≠ 0 := fun hk => h ⟨k, hk⟩
      rw [if_neg h]
      symm
      apply Finset.sum_eq_zero
      intro k hk
      exact if_neg (hh k)
  have hslot (k : Fin (j + 1)) :
      (∑ a : Fin (j + 1) ↪ Fin (p + 1), ∑ b : Fin (j + 1) ↪ Fin q,
        if a k = 0 then W a b else 0) =
      ∑ a : Fin (j + 1) ↪ Fin (p + 1), ∑ b : Fin (j + 1) ↪ Fin q,
        if a 0 = 0 then W a b else 0 := by
    let σ : Equiv.Perm (Fin (j + 1)) := Equiv.swap 0 k
    let ea := precompEmbeddingEquiv (p := p + 1) σ
    let eb := precompEmbeddingEquiv (p := q) σ
    calc
      _ = ∑ a : Fin (j + 1) ↪ Fin (p + 1), ∑ b : Fin (j + 1) ↪ Fin q,
          if (ea a) k = 0 then W (ea a) (eb b) else 0 := by
        rw [← ea.sum_comp (fun a => ∑ b : Fin (j + 1) ↪ Fin q,
          if a k = 0 then W a b else 0)]
        apply Finset.sum_congr rfl
        intro a ha
        exact (eb.sum_comp (fun b => if (ea a) k = 0 then W (ea a) b else 0)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        have hw := sourceWickOrderedPairWeight_precomp μ gs hs v u a b σ
        have hk : (ea a) k = a 0 := by
          change a (Equiv.swap 0 k k) = a 0
          rw [Equiv.swap_apply_right]
        change (if (ea a) k = 0 then W (ea a) (eb b) else 0) = _
        rw [hk]
        change (if a 0 = 0 then
          sourceWickOrderedPairWeight μ gs hs v u
            (σ.toEmbedding.trans a) (σ.toEmbedding.trans b) else 0) = _
        rw [hw]
  calc
    _ = ∑ a : Fin (j + 1) ↪ Fin (p + 1), ∑ b : Fin (j + 1) ↪ Fin q,
        ∑ k : Fin (j + 1), if a k = 0 then W a b else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact hpoint a b
    _ = ∑ k : Fin (j + 1), ∑ a : Fin (j + 1) ↪ Fin (p + 1),
        ∑ b : Fin (j + 1) ↪ Fin q, if a k = 0 then W a b else 0 := by
      calc
        _ = ∑ a : Fin (j + 1) ↪ Fin (p + 1), ∑ k : Fin (j + 1),
            ∑ b : Fin (j + 1) ↪ Fin q, if a k = 0 then W a b else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      simp only [hslot, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rfl


/-! Exact scalar weights of the existing physical matching list. No new
matching enumeration or formal polynomial realization replaces that list.
SOURCE ONLY / UNCOMPILED. -/

/-- Literal pure matrix pairing of one actual matching rank-one kernel. -/
def sourceWickMatchingPureWeight (t : SourceWickMatchingTerm μ)
    (v u : Lp ℂ 2 μ) : ℂ :=
  t.coefficient * ((∏ i : Fin t.outputDegree, inner ℂ v (t.outputFields i)) *
    ∏ k : Fin t.inputDegree, inner ℂ (t.inputFields k) u)

/-- Count-j part of the SAME recursive matching list, retaining repetitions. -/
def sourceWickMatchingPureSum (p q j : ℕ) (gs : Fin p → Lp ℂ 2 μ)
    (hs : Fin q → Lp ℂ 2 μ) (v u : Lp ℂ 2 μ) : ℂ :=
  (((sourceWickMatchingTerms μ p gs q hs).filter
    (fun t => decide (t.contractions = j))).map
      (fun t => sourceWickMatchingPureWeight μ t v u)).sum

private def matchingPureList (j : ℕ) (ts : List (SourceWickMatchingTerm μ))
    (v u : Lp ℂ 2 μ) : ℂ :=
  ((ts.filter (fun t => decide (t.contractions = j))).map
    (fun t => sourceWickMatchingPureWeight μ t v u)).sum

private theorem matchingPureWeight_keep (g : Lp ℂ 2 μ)
    (t : SourceWickMatchingTerm μ) (v u : Lp ℂ 2 μ) :
    sourceWickMatchingPureWeight μ (sourceMatchingKeep μ g t) v u =
      inner ℂ g u * sourceWickMatchingPureWeight μ t v u := by
  unfold sourceWickMatchingPureWeight sourceMatchingKeep
  dsimp only
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

private theorem matchingPureWeight_contract (c : ℂ)
    (t : SourceWickMatchingTerm μ) (v u : Lp ℂ 2 μ) :
    sourceWickMatchingPureWeight μ (sourceMatchingContract μ c t) v u =
      c * sourceWickMatchingPureWeight μ t v u := by
  unfold sourceWickMatchingPureWeight sourceMatchingContract
  dsimp only
  ring

private theorem matchingPureList_nil (j : ℕ) (v u : Lp ℂ 2 μ) :
    matchingPureList μ j [] v u = 0 := rfl

private theorem matchingPureList_cons (j : ℕ) (t : SourceWickMatchingTerm μ)
    (ts : List (SourceWickMatchingTerm μ)) (v u : Lp ℂ 2 μ) :
    matchingPureList μ j (t :: ts) v u =
      (if t.contractions = j then sourceWickMatchingPureWeight μ t v u else 0) +
        matchingPureList μ j ts v u := by
  classical
  by_cases h : t.contractions = j <;>
    simp [matchingPureList, h]

private theorem matchingPureList_append (j : ℕ)
    (as bs : List (SourceWickMatchingTerm μ)) (v u : Lp ℂ 2 μ) :
    matchingPureList μ j (as ++ bs) v u =
      matchingPureList μ j as v u + matchingPureList μ j bs v u := by
  induction as with
  | nil => simp only [List.nil_append, matchingPureList_nil, zero_add]
  | cons t ts ih =>
    simp only [List.cons_append, matchingPureList_cons, ih, add_assoc]

private theorem matchingPureList_keep (j : ℕ) (g : Lp ℂ 2 μ)
    (ts : List (SourceWickMatchingTerm μ)) (v u : Lp ℂ 2 μ) :
    matchingPureList μ j (ts.map (sourceMatchingKeep μ g)) v u =
      inner ℂ g u * matchingPureList μ j ts v u := by
  induction ts with
  | nil => simp only [List.map_nil, matchingPureList_nil, mul_zero]
  | cons t ts ih =>
    rw [List.map_cons, matchingPureList_cons, matchingPureList_cons, ih, mul_add]
    have hc : (sourceMatchingKeep μ g t).contractions = t.contractions := rfl
    rw [hc]
    by_cases h : t.contractions = j
    · simp only [if_pos h, matchingPureWeight_keep]
    · simp only [if_neg h, mul_zero]

private theorem matchingPureList_contract_zero (c : ℂ)
    (ts : List (SourceWickMatchingTerm μ)) (v u : Lp ℂ 2 μ) :
    matchingPureList μ 0 (ts.map (sourceMatchingContract μ c)) v u = 0 := by
  induction ts with
  | nil => exact matchingPureList_nil μ 0 v u
  | cons t ts ih =>
    rw [List.map_cons, matchingPureList_cons, ih, add_zero]
    have hc : (sourceMatchingContract μ c t).contractions ≠ 0 := by
      change t.contractions + 1 ≠ 0
      omega
    exact if_neg hc

private theorem matchingPureList_contract_succ (j : ℕ) (c : ℂ)
    (ts : List (SourceWickMatchingTerm μ)) (v u : Lp ℂ 2 μ) :
    matchingPureList μ (j + 1) (ts.map (sourceMatchingContract μ c)) v u =
      c * matchingPureList μ j ts v u := by
  induction ts with
  | nil => simp only [List.map_nil, matchingPureList_nil, mul_zero]
  | cons t ts ih =>
    rw [List.map_cons, matchingPureList_cons, matchingPureList_cons, ih, mul_add]
    have hc : (sourceMatchingContract μ c t).contractions = j + 1 ↔
        t.contractions = j := Nat.add_right_cancel_iff
    by_cases h : t.contractions = j
    · rw [if_pos (hc.mpr h), if_pos h, matchingPureWeight_contract]
    · rw [if_neg (fun hh => h (hc.mp hh)), if_neg h, mul_zero]

private theorem matchingPureList_flatten (j : ℕ)
    (tss : List (List (SourceWickMatchingTerm μ))) (v u : Lp ℂ 2 μ) :
    matchingPureList μ j tss.flatten v u =
      (tss.map (fun ts => matchingPureList μ j ts v u)).sum := by
  induction tss with
  | nil => rfl
  | cons ts tss ih =>
    simp only [List.flatten_cons, matchingPureList_append, List.map_cons, List.sum_cons, ih]

/-- The exact weighted scalar recurrence of61a1: a retained annihilator
contributes its pure pairing; a contraction contributes its ORIGINAL complex
inner product and removes the selected creator, with no multiplicity loss. -/
theorem sourceWickMatchingPureSum_succ_succ (p q j : ℕ)
    (gs : Fin (p + 1) → Lp ℂ 2 μ) (hs : Fin (q + 1) → Lp ℂ 2 μ)
    (v u : Lp ℂ 2 μ) :
    sourceWickMatchingPureSum μ (p + 1) (q + 1) (j + 1) gs hs v u =
      inner ℂ (gs 0) u *
        sourceWickMatchingPureSum μ p (q + 1) (j + 1) (Fin.tail gs) hs v u +
      ∑ i : Fin (q + 1), inner ℂ (gs 0) (hs i) *
        sourceWickMatchingPureSum μ p q j (Fin.tail gs) (i.removeNth hs) v u := by
  change matchingPureList μ (j + 1)
    (sourceWickMatchingTerms μ (p + 1) gs (q + 1) hs) v u = _
  rw [sourceWickMatchingTerms, matchingPureList_append, matchingPureList_keep,
    matchingPureList_flatten, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply, matchingPureList_contract_succ]
  rfl

/-- In the zero-contraction branch every creator and annihilator is retained;
contracted branches contribute zero, even when physical fields coincide. -/
theorem sourceWickMatchingPureSum_succ_zero_count (p q : ℕ)
    (gs : Fin (p + 1) → Lp ℂ 2 μ) (hs : Fin (q + 1) → Lp ℂ 2 μ)
    (v u : Lp ℂ 2 μ) :
    sourceWickMatchingPureSum μ (p + 1) (q + 1) 0 gs hs v u =
      inner ℂ (gs 0) u * sourceWickMatchingPureSum μ p (q + 1) 0 (Fin.tail gs) hs v u := by
  change matchingPureList μ 0
    (sourceWickMatchingTerms μ (p + 1) gs (q + 1) hs) v u = _
  rw [sourceWickMatchingTerms, matchingPureList_append, matchingPureList_keep,
    matchingPureList_flatten, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply, matchingPureList_contract_zero,
    Finset.sum_const_zero, add_zero]
  rfl



private theorem matchingInsert_mem_range {j n : ℕ} (t : Fin (n + 1))
    (a : Fin j ↪ Fin n) (k : Fin n) :
    t.succAbove k ∈ Set.range (sourceMatchingInsertHeadEmbedding t a) ↔
      k ∈ Set.range a := by
  constructor
  · rintro ⟨i, hi⟩
    refine Fin.cases
      (motive := fun z => sourceMatchingInsertHeadEmbedding t a z = t.succAbove k →
        k ∈ Set.range a) ?_ (fun l => ?_) i hi
    · intro hzero
      rw [sourceMatchingInsertHeadEmbedding_zero] at hzero
      exact False.elim ((t.ne_succAbove k) hzero)
    · intro hsucc
      rw [sourceMatchingInsertHeadEmbedding_succ] at hsucc
      exact ⟨l, Fin.succAbove_right_injective hsucc⟩
  · rintro ⟨i, hi⟩
    exact ⟨i.succ, by rw [sourceMatchingInsertHeadEmbedding_succ, hi]⟩

private theorem physicalUnusedProduct_insertHead {j n : ℕ}
    (gs : Fin (n + 1) → Lp ℂ 2 μ) (t : Fin (n + 1))
    (a : Fin j ↪ Fin n) (u : Lp ℂ 2 μ) :
    physicalUnusedProduct μ gs (sourceMatchingInsertHeadEmbedding t a) u =
      physicalUnusedProduct μ (t.removeNth gs) a u := by
  classical
  have ht : t ∈ Set.range (sourceMatchingInsertHeadEmbedding t a) :=
    ⟨0, sourceMatchingInsertHeadEmbedding_zero t a⟩
  unfold physicalUnusedProduct
  rw [Fin.prod_univ_succAbove _ t]
  rw [if_pos ht, one_mul]
  apply Finset.prod_congr rfl
  intro k hk
  simpa only [matchingInsert_mem_range, Fin.removeNth]

private theorem matchingAvoid_zero_mem {p j : ℕ}
    (a : Fin j ↪ Fin p) (k : Fin p) :
    k.succ ∈ Set.range (sourceMatchingAvoidEmbeddingEquiv j p 0 a).1 ↔
      k ∈ Set.range a := by
  change k.succ ∈ Set.range (a.trans (Fin.succAboveEmb 0)) ↔ _
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (Fin.succ_injective p) (by simpa only [Function.Embedding.trans_apply,
      Fin.coe_succAboveEmb, Fin.zero_succAbove] using hi)⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by simpa only [Function.Embedding.trans_apply,
      Fin.coe_succAboveEmb, Fin.zero_succAbove] using congrArg Fin.succ hi⟩

private theorem physicalUnusedProduct_avoidZero {p j : ℕ}
    (gs : Fin (p + 1) → Lp ℂ 2 μ) (a : Fin j ↪ Fin p)
    (u : Lp ℂ 2 μ) :
    physicalUnusedProduct μ gs (sourceMatchingAvoidEmbeddingEquiv j p 0 a).1 u =
      inner ℂ (gs 0) u * physicalUnusedProduct μ (Fin.tail gs) a u := by
  classical
  have h0 := (sourceMatchingAvoidEmbeddingEquiv j p 0 a).2
  unfold physicalUnusedProduct
  rw [Fin.prod_univ_succ, if_neg h0]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  simpa only [matchingAvoid_zero_mem, Fin.tail]

/-- Both the matched inner products and every unused physical slot factor
through the genuine selected-head bijection. Conjugation stays on the output
spectators, giving precisely the original inner(gs0,hs_t) factor. -/
theorem sourceWickOrderedPairWeight_insertHead (p q j : ℕ)
    (gs : Fin (p + 1) → Lp ℂ 2 μ) (hs : Fin (q + 1) → Lp ℂ 2 μ)
    (v u : Lp ℂ 2 μ) (t : Fin (q + 1))
    (a : Fin j ↪ Fin p) (b : Fin j ↪ Fin q) :
    sourceWickOrderedPairWeight μ gs hs v u
      (sourceMatchingInsertHeadEmbedding 0 a) (sourceMatchingInsertHeadEmbedding t b) =
      inner ℂ (gs 0) (hs t) *
        sourceWickOrderedPairWeight μ (Fin.tail gs) (t.removeNth hs) v u a b := by
  classical
  unfold sourceWickOrderedPairWeight
  rw [physicalUnusedProduct_insertHead, physicalUnusedProduct_insertHead,
    Fin.prod_univ_succ]
  simp only [sourceMatchingInsertHeadEmbedding_zero, sourceMatchingInsertHeadEmbedding_succ,
    Fin.removeNth_zero, Fin.removeNth, Fin.zero_succAbove, Fin.tail]
  ring

/-- The unselected source head retains its full physical spectator factor;
repeated field values cause no cancellation or deduplication of source slots. -/
theorem sourceWickOrderedPairWeight_avoidZero (p q j : ℕ)
    (gs : Fin (p + 1) → Lp ℂ 2 μ) (hs : Fin q → Lp ℂ 2 μ)
    (v u : Lp ℂ 2 μ) (a : Fin j ↪ Fin p) (b : Fin j ↪ Fin q) :
    sourceWickOrderedPairWeight μ gs hs v u
      (sourceMatchingAvoidEmbeddingEquiv j p 0 a).1 b =
      inner ℂ (gs 0) u * sourceWickOrderedPairWeight μ (Fin.tail gs) hs v u a b := by
  classical
  unfold sourceWickOrderedPairWeight
  rw [physicalUnusedProduct_avoidZero]
  change (inner ℂ (gs 0) u * physicalUnusedProduct μ (Fin.tail gs) a u) *
      conj (physicalUnusedProduct μ hs b v) *
        (∏ i, inner ℂ (gs ((0 : Fin (p + 1)).succAbove (a i))) (hs (b i))) = _
  simp only [Fin.zero_succAbove, Fin.tail]
  ring

/-- Full finite ordered-embedding sum, with all actual scalar factors. -/
def sourceWickOrderedPairSum (p q j : ℕ) (gs : Fin p → Lp ℂ 2 μ)
    (hs : Fin q → Lp ℂ 2 μ) (v u : Lp ℂ 2 μ) : ℂ :=
  ∑ a : Fin j ↪ Fin p, ∑ b : Fin j ↪ Fin q,
    sourceWickOrderedPairWeight μ gs hs v u a b

private theorem sum_if_eq_subtype {α : Type} [Fintype α]
    (P : α → Prop) [DecidablePred P] (F : α → ℂ) :
    (∑ a : α, if P a then F a else 0) = ∑ a : {a // P a}, F a := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun a => by simp only [Finset.mem_filter,
    Finset.mem_univ, true_and]) F

private theorem orderedUnselected_sum (p q j : ℕ)
    (gs : Fin (p + 1) → Lp ℂ 2 μ) (hs : Fin q → Lp ℂ 2 μ)
    (v u : Lp ℂ 2 μ) :
    (∑ a : Fin j ↪ Fin (p + 1), ∑ b : Fin j ↪ Fin q,
      if (0 : Fin (p + 1)) ∉ Set.range a then
        sourceWickOrderedPairWeight μ gs hs v u a b else 0) =
      inner ℂ (gs 0) u * sourceWickOrderedPairSum μ p q j (Fin.tail gs) hs v u := by
  classical
  let W := sourceWickOrderedPairWeight (j := j) μ gs hs v u
  calc
    _ = ∑ a : Fin j ↪ Fin (p + 1),
        if (0 : Fin (p + 1)) ∉ Set.range a then ∑ b : Fin j ↪ Fin q, W a b else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : (0 : Fin (p + 1)) ∉ Set.range a <;>
        simp only [h, not_true_eq_false, not_false_eq_true, if_true, if_false,
          Finset.sum_const_zero, W]
    _ = ∑ a : {a : Fin j ↪ Fin (p + 1) // (0 : Fin (p + 1)) ∉ Set.range a},
        ∑ b : Fin j ↪ Fin q, W a b := sum_if_eq_subtype _ _
    _ = ∑ a : Fin j ↪ Fin p, ∑ b : Fin j ↪ Fin q,
        W (sourceMatchingAvoidEmbeddingEquiv j p 0 a).1 b :=
      ((sourceMatchingAvoidEmbeddingEquiv j p 0).sum_comp
        (fun a => ∑ b : Fin j ↪ Fin q, W a.1 b)).symm
    _ = _ := by
      simp only [W, sourceWickOrderedPairWeight_avoidZero, sourceWickOrderedPairSum,
        Finset.mul_sum]

private theorem orderedFirstSelected_sum (p q j : ℕ)
    (gs : Fin (p + 1) → Lp ℂ 2 μ) (hs : Fin (q + 1) → Lp ℂ 2 μ)
    (v u : Lp ℂ 2 μ) :
    (∑ a : Fin (j + 1) ↪ Fin (p + 1), ∑ b : Fin (j + 1) ↪ Fin (q + 1),
      if a 0 = 0 then sourceWickOrderedPairWeight μ gs hs v u a b else 0) =
      ∑ t : Fin (q + 1), inner ℂ (gs 0) (hs t) *
        sourceWickOrderedPairSum μ p q j (Fin.tail gs) (t.removeNth hs) v u := by
  classical
  let W := sourceWickOrderedPairWeight (j := j + 1) μ gs hs v u
  have hb (a : Fin j ↪ Fin p) :
      (∑ b : Fin (j + 1) ↪ Fin (q + 1), W (sourceMatchingInsertHeadEmbedding 0 a) b) =
      ∑ t : Fin (q + 1), ∑ b : Fin j ↪ Fin q,
        W (sourceMatchingInsertHeadEmbedding 0 a) (sourceMatchingInsertHeadEmbedding t b) := by
    calc
      _ = ∑ t : Fin (q + 1), ∑ b : Fin (j + 1) ↪ Fin (q + 1),
          if b 0 = t then W (sourceMatchingInsertHeadEmbedding 0 a) b else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b hb
        simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [sum_if_eq_subtype]
        exact ((sourceMatchingHeadEmbeddingEquiv j q t).sum_comp
          (fun b => W (sourceMatchingInsertHeadEmbedding 0 a) b.1)).symm
  calc
    _ = ∑ a : Fin (j + 1) ↪ Fin (p + 1),
        if a 0 = 0 then ∑ b : Fin (j + 1) ↪ Fin (q + 1), W a b else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : a 0 = 0 <;>
        simp only [h, if_true, if_false, Finset.sum_const_zero, W]
    _ = ∑ a : {a : Fin (j + 1) ↪ Fin (p + 1) // a 0 = 0},
        ∑ b : Fin (j + 1) ↪ Fin (q + 1), W a b := sum_if_eq_subtype _ _
    _ = ∑ a : Fin j ↪ Fin p, ∑ b : Fin (j + 1) ↪ Fin (q + 1),
        W (sourceMatchingInsertHeadEmbedding 0 a) b :=
      ((sourceMatchingHeadEmbeddingEquiv j p 0).sum_comp
        (fun a => ∑ b : Fin (j + 1) ↪ Fin (q + 1), W a.1 b)).symm
    _ = ∑ a : Fin j ↪ Fin p, ∑ t : Fin (q + 1), ∑ b : Fin j ↪ Fin q,
        W (sourceMatchingInsertHeadEmbedding 0 a) (sourceMatchingInsertHeadEmbedding t b) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hb a
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      simp only [W, sourceWickOrderedPairWeight_insertHead, sourceWickOrderedPairSum,
        Finset.mul_sum]

/-- Actual WEIGHTED ordered-pair recurrence. Its factor j+1 is obtained by
unique source slots and simultaneous reindexing; no coefficient or spectator
is removed, and arbitrary coincident physical fields are retained. -/
theorem sourceWickOrderedPairSum_succ_succ (p q j : ℕ)
    (gs : Fin (p + 1) → Lp ℂ 2 μ) (hs : Fin (q + 1) → Lp ℂ 2 μ)
    (v u : Lp ℂ 2 μ) :
    sourceWickOrderedPairSum μ (p + 1) (q + 1) (j + 1) gs hs v u =
      inner ℂ (gs 0) u *
        sourceWickOrderedPairSum μ p (q + 1) (j + 1) (Fin.tail gs) hs v u +
      ((j + 1 : ℕ) : ℂ) *
        ∑ t : Fin (q + 1), inner ℂ (gs 0) (hs t) *
          sourceWickOrderedPairSum μ p q j (Fin.tail gs) (t.removeNth hs) v u := by
  classical
  let W := sourceWickOrderedPairWeight (j := j + 1) μ gs hs v u
  have hsplit : sourceWickOrderedPairSum μ (p + 1) (q + 1) (j + 1) gs hs v u =
      (∑ a : Fin (j + 1) ↪ Fin (p + 1), ∑ b : Fin (j + 1) ↪ Fin (q + 1),
        if (0 : Fin (p + 1)) ∉ Set.range a then W a b else 0) +
      (∑ a : Fin (j + 1) ↪ Fin (p + 1), ∑ b : Fin (j + 1) ↪ Fin (q + 1),
        if (0 : Fin (p + 1)) ∈ Set.range a then W a b else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases h : (0 : Fin (p + 1)) ∈ Set.range a <;>
      simp only [h, not_true_eq_false, not_false_eq_true, if_true, if_false,
        zero_add, add_zero, W]
  rw [hsplit, orderedUnselected_sum, sourceWickOrderedPairWeight_selected_head,
    orderedFirstSelected_sum]

/-- Zero matched slots retain every original physical factor. -/
theorem sourceWickOrderedPairSum_zero_count (p q : ℕ)
    (gs : Fin p → Lp ℂ 2 μ) (hs : Fin q → Lp ℂ 2 μ) (v u : Lp ℂ 2 μ) :
    sourceWickOrderedPairSum μ p q 0 gs hs v u =
      (∏ k : Fin p, inner ℂ (gs k) u) * (∏ i : Fin q, inner ℂ v (hs i)) := by
  classical
  unfold sourceWickOrderedPairSum sourceWickOrderedPairWeight physicalUnusedProduct
  have hempty {n : ℕ} (a : Fin 0 ↪ Fin n) : Set.range a = ∅ := by
    ext k
    simp only [Set.mem_range, Set.mem_empty_iff_false]
    exact ⟨fun ⟨i, _⟩ => Fin.elim0 i, False.elim⟩
  simp only [hempty, Set.mem_empty_iff_false, if_false, Fintype.prod_empty,
    mul_one, map_prod, inner_conj_symm]
  simp

private theorem sourceWickMatchingPureSum_zero_input (q j : ℕ)
    (gs : Fin 0 → Lp ℂ 2 μ) (hs : Fin q → Lp ℂ 2 μ) (v u : Lp ℂ 2 μ) :
    sourceWickMatchingPureSum μ 0 q j gs hs v u =
      if j = 0 then ∏ i : Fin q, inner ℂ v (hs i) else 0 := by
  classical
  unfold sourceWickMatchingPureSum
  rw [sourceWickMatchingTerms]
  by_cases h : j = 0
  · subst j
    simp [sourceWickMatchingPureWeight]
  · have hh : (0 : ℕ) ≠ j := Ne.symm h
    simp [sourceWickMatchingPureWeight, h, hh]

private theorem sourceWickMatchingPureSum_zero_output (p j : ℕ)
    (gs : Fin (p + 1) → Lp ℂ 2 μ) (hs : Fin 0 → Lp ℂ 2 μ) (v u : Lp ℂ 2 μ) :
    sourceWickMatchingPureSum μ (p + 1) 0 j gs hs v u =
      inner ℂ (gs 0) u * sourceWickMatchingPureSum μ p 0 j (Fin.tail gs) hs v u := by
  change matchingPureList μ j (sourceWickMatchingTerms μ (p + 1) gs 0 hs) v u = _
  rw [sourceWickMatchingTerms, matchingPureList_keep]
  rfl

private theorem ordered_zero_input_pos (q j : ℕ)
    (gs : Fin 0 → Lp ℂ 2 μ) (hs : Fin q → Lp ℂ 2 μ) (v u : Lp ℂ 2 μ) :
    sourceWickOrderedPairSum μ 0 q (j + 1) gs hs v u = 0 := by
  letI : IsEmpty (Fin (j + 1) ↪ Fin 0) := ⟨fun a => Fin.elim0 (a 0)⟩
  exact Fintype.sum_empty _

private theorem ordered_zero_output_pos (p j : ℕ)
    (gs : Fin p → Lp ℂ 2 μ) (hs : Fin 0 → Lp ℂ 2 μ) (v u : Lp ℂ 2 μ) :
    sourceWickOrderedPairSum μ p 0 (j + 1) gs hs v u = 0 := by
  letI : IsEmpty (Fin (j + 1) ↪ Fin 0) := ⟨fun b => Fin.elim0 (b 0)⟩
  unfold sourceWickOrderedPairSum
  simp only [Fintype.sum_empty, Finset.sum_const_zero]

/-- WHOLE weighted matching identity for the SAME actual recursive61a1 list.
Each unordered partial matching has j! simultaneous orderings, with ALL its
complex contractions and unselected physical pure pairings unchanged. -/
theorem sourceWickOrderedPairing_eq_factorial_matchingPureSum (p q j : ℕ)
    (gs : Fin p → Lp ℂ 2 μ) (hs : Fin q → Lp ℂ 2 μ) (v u : Lp ℂ 2 μ) :
    (∑ a : Fin j ↪ Fin p, ∑ b : Fin j ↪ Fin q,
      physicalUnusedProduct μ gs a u * conj (physicalUnusedProduct μ hs b v) *
        ∏ i : Fin j, inner ℂ (gs (a i)) (hs (b i))) =
      (j.factorial : ℂ) * sourceWickMatchingPureSum μ p q j gs hs v u := by
  change sourceWickOrderedPairSum μ p q j gs hs v u = _
  induction p generalizing q j hs with
  | zero =>
    cases j with
    | zero =>
      rw [sourceWickOrderedPairSum_zero_count, sourceWickMatchingPureSum_zero_input]
      simp
    | succ j =>
      rw [ordered_zero_input_pos, sourceWickMatchingPureSum_zero_input]
      simp
  | succ p ih =>
    cases q with
    | zero =>
      rw [sourceWickMatchingPureSum_zero_output]
      cases j with
      | zero =>
        have hh := ih 0 0 (Fin.tail gs) hs
        rw [sourceWickOrderedPairSum_zero_count] at hh ⊢
        simp only [Nat.factorial_zero, Nat.cast_one, one_mul,
          Fintype.prod_empty, mul_one] at hh ⊢
        rw [← hh, Fin.prod_univ_succ]
        rfl
      | succ j =>
        rw [ordered_zero_output_pos]
        have hh := ih 0 (j + 1) (Fin.tail gs) hs
        rw [ordered_zero_output_pos] at hh
        calc
          0 = inner ℂ (gs 0) u * 0 := (mul_zero _).symm
          _ = inner ℂ (gs 0) u * ((Nat.factorial (j + 1) : ℂ) *
              sourceWickMatchingPureSum μ p 0 (j + 1) (Fin.tail gs) hs v u) :=
            congrArg (fun z : ℂ => inner ℂ (gs 0) u * z) hh
          _ = _ := by ring
    | succ q =>
      cases j with
      | zero =>
        rw [sourceWickOrderedPairSum_zero_count,
          sourceWickMatchingPureSum_succ_zero_count]
        have hh := ih (q + 1) 0 (Fin.tail gs) hs
        rw [sourceWickOrderedPairSum_zero_count] at hh
        simp only [Nat.factorial_zero, Nat.cast_one, one_mul] at hh ⊢
        rw [← hh, Fin.prod_univ_succ]
        simp only [Fin.tail]
        ring
      | succ j =>
        rw [sourceWickOrderedPairSum_succ_succ,
          sourceWickMatchingPureSum_succ_succ]
        rw [ih (q + 1) (j + 1) (Fin.tail gs) hs]
        simp_rw [ih q j (Fin.tail gs)]
        have hsum : (∑ t : Fin (q + 1), inner ℂ (gs 0) (hs t) *
            ((j.factorial : ℂ) * sourceWickMatchingPureSum μ p q j
              (Fin.tail gs) (t.removeNth hs) v u)) =
            (j.factorial : ℂ) * ∑ t : Fin (q + 1), inner ℂ (gs 0) (hs t) *
              sourceWickMatchingPureSum μ p q j (Fin.tail gs) (t.removeNth hs) v u := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          ring
        rw [hsum]
        have hfac : ((j + 1).factorial : ℂ) =
            ((j + 1 : ℕ) : ℂ) * (j.factorial : ℂ) := by
          rw [Nat.factorial_succ, Nat.cast_mul]
        rw [hfac]
        ring


end LiebLiniger.FixedPeriod.Quantum
end
