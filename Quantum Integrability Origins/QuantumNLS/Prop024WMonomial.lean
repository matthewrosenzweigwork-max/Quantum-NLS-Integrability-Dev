import QuantumNLS.Prop024WWeylPhysical

/-! PROP-024 affine Weyl action, module 6: the polynomial extension to products of creation and
annihilation operators (normal-ordered monomials).

On the physical smooth domain `physSmooth L = ⋂ⱼ momentDomain j` every letter `a*(f)`, `a(f)`
is an endomorphism, so every word (product of letters) is an endomorphism, and the conjugation
`T ↦ W(v)⁻¹ T W(v)` of module 5 is an algebra automorphism.  Hence:

* `weylConj_word`: `W(v)⁻¹ a^#(f₁) ⋯ a^#(f_k) W(v) = ∏ₖ (a^#(f_k) + c_k)`, with
  `c = ⟨v,f⟩` for a creator and `c = ⟨f,v⟩` for an annihilator;
* `weylConj_normalMonomial`: the same for `a*(f₁)⋯a*(f_k) a(g₁)⋯a(g_l)`;
* `weylConj_word_cells`: the expansion into cells, one for each way of keeping a letter or
  replacing it by its c-number shift:
  `W(v)⁻¹ word(w) W(v) = ∑_{(c,u) ∈ cells v w} c • word u`  (`2^|w|` cells);
* linear combinations of words (`weylConj_poly`).

No compatibility premise; all objects are the frozen ones through module 5. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace
namespace QuantumNLS.Prop024WMonomial
open PhysicalTensor Prop024WWeylPhysical

variable {L : ℝ} [Fact (0 < L)]

/-- Endomorphisms of the physical smooth domain. -/
abbrev PEnd (L : ℝ) [Fact (0 < L)] : Type := Module.End ℂ (physSmooth L)

/-- A letter of a creation/annihilation word. -/
inductive Letter (L : ℝ) [Fact (0 < L)] where
  | cre (f : L2T L) : Letter L
  | ann (f : L2T L) : Letter L

/-- The operator of a letter. -/
def Letter.op : Letter L → PEnd L
  | .cre f => creP f
  | .ann f => annP f

/-- The c-number produced by the Weyl displacement `W(v)` for a letter. -/
def Letter.shift (v : L2T L) : Letter L → ℂ
  | .cre f => inner ℂ v f
  | .ann f => inner ℂ f v

/-- The displaced letter `a^#(f) + c`. -/
def Letter.shifted (v : L2T L) (l : Letter L) : PEnd L := l.op + l.shift v • (1 : PEnd L)

/-- Letterwise form of the affine Weyl action. -/
theorem weylConj_letter (v : L2T L) (l : Letter L) :
    weylConj v l.op = l.shifted v := by
  cases l with
  | cre f => exact (weyl_affine_action v f).2.2.2
  | ann f => exact (weyl_affine_action v f).2.2.1

/-- The product of the operators of a word (the empty word is the identity). -/
def word (w : List (Letter L)) : PEnd L := (w.map Letter.op).prod

lemma word_nil : word ([] : List (Letter L)) = 1 := rfl

lemma word_cons (l : Letter L) (w : List (Letter L)) : word (l :: w) = l.op * word w := by
  simp [word]

/-- **Monomial extension.** Conjugation by the printed Weyl operator replaces every letter of
a word by its displaced letter. -/
theorem weylConj_word (v : L2T L) (w : List (Letter L)) :
    weylConj v (word w) = (w.map (Letter.shifted v)).prod := by
  unfold word
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  exact weylConj_letter v l

/-- A normal-ordered monomial `a*(f₁)⋯a*(f_k) a(g₁)⋯a(g_l)`. -/
def normalMonomial (cs as : List (L2T L)) : PEnd L :=
  (cs.map creP).prod * (as.map annP).prod

lemma normalMonomial_eq_word (cs as : List (L2T L)) :
    normalMonomial cs as = word (cs.map Letter.cre ++ as.map Letter.ann) := by
  unfold normalMonomial word
  rw [List.map_append, List.prod_append, List.map_map, List.map_map]
  rfl

/-- **Normal-ordered monomials.** -/
theorem weylConj_normalMonomial (v : L2T L) (cs as : List (L2T L)) :
    weylConj v (normalMonomial cs as) =
      (cs.map (fun f => creP f + (inner ℂ v f) • (1 : PEnd L))).prod *
        (as.map (fun f => annP f + (inner ℂ f v) • (1 : PEnd L))).prod := by
  rw [normalMonomial_eq_word, weylConj_word, List.map_append, List.prod_append, List.map_map,
    List.map_map]
  rfl

/-- Linear combinations of words (polynomials in the letters). -/
theorem weylConj_poly (v : L2T L) {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (w : ι → List (Letter L)) :
    weylConj v (∑ i ∈ s, c i • word (w i)) =
      ∑ i ∈ s, c i • (((w i).map (Letter.shifted v)).prod) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, weylConj_word]

/-! ### Expansion into cells -/

/-- The cells of a word: for each letter, either keep it or replace it by its c-number shift. -/
def cells (v : L2T L) : List (Letter L) → List (ℂ × List (Letter L))
  | [] => [(1, [])]
  | l :: w =>
      (cells v w).map (fun p => (p.1, l :: p.2)) ++
        (cells v w).map (fun p => (l.shift v * p.1, p.2))

lemma length_cells (v : L2T L) (w : List (Letter L)) : (cells v w).length = 2 ^ w.length := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    simp only [cells, List.length_append, List.length_map, ih, List.length_cons, pow_succ]
    ring

lemma op_mul_cells_sum (l : Letter L) (t : List (ℂ × List (Letter L))) :
    l.op * (t.map (fun p => p.1 • (word p.2 : PEnd L))).sum =
      (t.map (fun p => p.1 • (word (l :: p.2) : PEnd L))).sum := by
  induction t with
  | nil => simp
  | cons p t ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, ih, mul_smul_comm, word_cons]

lemma smul_cells_sum (c : ℂ) (t : List (ℂ × List (Letter L))) :
    c • (t.map (fun p => p.1 • (word p.2 : PEnd L))).sum =
      (t.map (fun p => (c * p.1) • (word p.2 : PEnd L))).sum := by
  induction t with
  | nil => simp
  | cons p t ih =>
    simp only [List.map_cons, List.sum_cons, smul_add, ih, smul_smul]

/-- **Expansion of the conjugated monomial into cells.** -/
theorem weylConj_word_cells (v : L2T L) (w : List (Letter L)) :
    weylConj v (word w) = ((cells v w).map (fun p => p.1 • word p.2)).sum := by
  induction w with
  | nil =>
    rw [word_nil, map_one]
    simp [cells, word_nil]
  | cons l w ih =>
    rw [word_cons, map_mul, weylConj_letter, ih]
    unfold Letter.shifted
    rw [add_mul, smul_mul_assoc, one_mul, op_mul_cells_sum, smul_cells_sum]
    simp only [cells, List.map_append, List.map_map, List.sum_append]
    rfl

end QuantumNLS.Prop024WMonomial

#print axioms QuantumNLS.Prop024WMonomial.weylConj_letter
#print axioms QuantumNLS.Prop024WMonomial.weylConj_word
#print axioms QuantumNLS.Prop024WMonomial.weylConj_normalMonomial
#print axioms QuantumNLS.Prop024WMonomial.weylConj_poly
#print axioms QuantumNLS.Prop024WMonomial.weylConj_word_cells
#print axioms QuantumNLS.Prop024WMonomial.length_cells

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024WMonomial." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024WMonomial." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
        throwError "Held identifier in dependency closure: {n}"
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
  Lean.logInfo m!"Prop024WMonomial aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
