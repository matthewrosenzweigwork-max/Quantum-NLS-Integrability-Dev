import LiebLiniger.FixedPeriod.Quantum.WickContraction
import LiebLiniger.FixedPeriod.Quantum.WickSectorMap
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Concrete finite-mode differential normal ordering

The finite-mode algebraic particle space is `MvPolynomial (Fin d) ℂ`.
Creation in mode `i` multiplies by `X i`, and annihilation is `pderiv i`.
The product theorem below expands *every* annihilation word, retaining repeated
contraction choices as repeated list entries. Thus no commutation relation or
normal-ordering conclusion is an assumption.

This is the algebraic expansion step of LLFP-Q2-024. Identification with the
actual `SymmetricSector` Wick maps, grouping ordered choices into the manuscript's
`epsilon^j / j!` derivative contractions, and the compact-kernel limiting passage
are still required. LLFP-Q2-024--028 are not claimed complete by this file.
-/

open scoped BigOperators

noncomputable section

namespace LiebLiniger.FixedPeriod.Quantum

/-- Algebraic finite-particle vectors in `d` actual coordinate modes. -/
abbrev AlgebraicFiniteModes (d : ℕ) := MvPolynomial (Fin d) ℂ

/-- Creation in one of the finite coordinate modes. -/
def finiteModeCreation {d : ℕ} (i : Fin d) (f : AlgebraicFiniteModes d) :
    AlgebraicFiniteModes d := MvPolynomial.X i * f

/-- Annihilation in one of the finite coordinate modes. -/
def finiteModeAnnihilation {d : ℕ} (i : Fin d) (f : AlgebraicFiniteModes d) :
    AlgebraicFiniteModes d := MvPolynomial.pderiv i f

/-- The concrete creation-annihilation relation, including distinct modes. -/
theorem finiteMode_ccr {d : ℕ} (i j : Fin d) (f : AlgebraicFiniteModes d) :
    finiteModeAnnihilation i (finiteModeCreation j f) =
      finiteModeCreation j (finiteModeAnnihilation i f) +
        if i = j then f else 0 := by
  classical
  by_cases h : i = j
  · subst j
    simp only [finiteModeAnnihilation, finiteModeCreation, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_X_self, one_mul, ite_true, add_comm]
  · simp only [finiteModeAnnihilation, finiteModeCreation, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_X_of_ne (Ne.symm h), zero_mul, zero_add, if_neg h,
      add_zero]

/-- An ordered word of actual coordinate partial derivatives; the first letter
acts last, as in ordinary operator composition. -/
def finiteModeDerivativeWord {d : ℕ} : List (Fin d) →
    AlgebraicFiniteModes d → AlgebraicFiniteModes d
  | [], f => f
  | i :: w, f => MvPolynomial.pderiv i (finiteModeDerivativeWord w f)

/-- Every choice of which derivatives hit the left factor. Multiplicities are
retained: equal letters in the input word still represent distinct choices. -/
def contractionWordSplits {α : Type*} : List α → List (List α × List α)
  | [] => [([], [])]
  | i :: w =>
      (contractionWordSplits w).map (fun ab => (i :: ab.1, ab.2)) ++
      (contractionWordSplits w).map (fun ab => (ab.1, i :: ab.2))

/-- Each split accounts for every annihilation letter exactly once. -/
theorem contractionWordSplits_length {α : Type*} (w : List α)
    (a b : List α) (h : (a, b) ∈ contractionWordSplits w) :
    a.length + b.length = w.length := by
  induction w generalizing a b with
  | nil =>
    simp only [contractionWordSplits, List.mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | cons i w ih =>
    simp only [contractionWordSplits, List.mem_append, List.mem_map] at h
    rcases h with ⟨⟨a', b'⟩, hab, heq⟩ | ⟨⟨a', b'⟩, hab, heq⟩
    · cases heq
      simpa only [List.length_cons, Nat.succ_add] using congrArg Nat.succ (ih a' b' hab)
    · cases heq
      simpa only [List.length_cons, Nat.add_succ] using congrArg Nat.succ (ih a' b' hab)

private theorem pderiv_list_sum {d : ℕ} (i : Fin d)
    (l : List (AlgebraicFiniteModes d)) :
    MvPolynomial.pderiv i l.sum = (l.map (MvPolynomial.pderiv i)).sum := by
  induction l with
  | nil => simp only [List.sum_nil, map_zero, List.map_nil]
  | cons f l ih => simp only [List.sum_cons, map_add, ih, List.map_cons]

/-- Appending derivative words is actual composition on all finite vectors. -/
theorem finiteModeDerivativeWord_append {d : ℕ} (a b : List (Fin d))
    (f : AlgebraicFiniteModes d) :
    finiteModeDerivativeWord (a ++ b) f =
      finiteModeDerivativeWord a (finiteModeDerivativeWord b f) := by
  induction a with
  | nil => rfl
  | cons i a ih => simp only [List.cons_append, finiteModeDerivativeWord, ih]

/-- Full finite-mode Leibniz expansion, including repeated coordinate modes.
The list of splits retains exactly the ordered choices counted by contractions. -/
theorem finiteModeDerivativeWord_mul {d : ℕ} (w : List (Fin d))
    (f g : AlgebraicFiniteModes d) :
    finiteModeDerivativeWord w (f * g) =
      ((contractionWordSplits w).map fun ab =>
        finiteModeDerivativeWord ab.1 f * finiteModeDerivativeWord ab.2 g).sum := by
  induction w with
  | nil => simp only [finiteModeDerivativeWord, contractionWordSplits,
      List.map_singleton, List.sum_singleton]
  | cons i w ih =>
    rw [finiteModeDerivativeWord, ih, pderiv_list_sum]
    simp only [contractionWordSplits, List.map_append, List.sum_append, List.map_map,
      Function.comp_def, finiteModeDerivativeWord, MvPolynomial.pderiv_mul,
      List.sum_map_add]

/-- An arbitrary normal-ordered finite-mode differential monomial: multiply
by the creation polynomial after applying the annihilation word. -/
def finiteModeNormalOrdered {d : ℕ} (c : AlgebraicFiniteModes d)
    (w : List (Fin d)) (f : AlgebraicFiniteModes d) : AlgebraicFiniteModes d :=
  c * finiteModeDerivativeWord w f

/-- Exact finite-mode product expansion before grouping by contraction order.
No bound on particle number or positive occupation assumption is imposed. -/
theorem finiteModeNormalOrdered_product {d : ℕ}
    (c e : AlgebraicFiniteModes d) (w v : List (Fin d))
    (f : AlgebraicFiniteModes d) :
    finiteModeNormalOrdered c w (finiteModeNormalOrdered e v f) =
      ((contractionWordSplits w).map fun ab =>
        finiteModeNormalOrdered (c * finiteModeDerivativeWord ab.1 e)
          (ab.2 ++ v) f).sum := by
  simp only [finiteModeNormalOrdered]
  rw [finiteModeDerivativeWord_mul, ← List.sum_map_mul_left]
  simp only [List.map_map, Function.comp_def, finiteModeDerivativeWord_append,
    mul_assoc]

/-- Derivative words commute with multiplication by a scalar constant. -/
theorem finiteModeDerivativeWord_C_mul {d : ℕ} (w : List (Fin d))
    (z : ℂ) (f : AlgebraicFiniteModes d) :
    finiteModeDerivativeWord w (MvPolynomial.C z * f) =
      MvPolynomial.C z * finiteModeDerivativeWord w f := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [finiteModeDerivativeWord, ih, MvPolynomial.pderiv_C_mul]

private theorem finiteModeNormalOrdered_C_mul {d : ℕ}
    (c : AlgebraicFiniteModes d) (w : List (Fin d))
    (z : ℂ) (f : AlgebraicFiniteModes d) :
    finiteModeNormalOrdered c w (MvPolynomial.C z * f) =
      MvPolynomial.C z * finiteModeNormalOrdered c w f := by
  simp only [finiteModeNormalOrdered, finiteModeDerivativeWord_C_mul]
  ring

/-- Normal ordering in the epsilon-adapted unnormalized occupation basis:
creation is `X i`, annihilation is `epsilon * pderiv i`. This has the same
algebraic epsilon normalization as symmetric square-root scaling after rescaling
the occupation basis; the isometric Hilbert-space identification is not supplied.
-/
def finiteModeScaledNormalOrdered {d : ℕ} (epsilon : ℂ)
    (c : AlgebraicFiniteModes d) (w : List (Fin d))
    (f : AlgebraicFiniteModes d) : AlgebraicFiniteModes d :=
  MvPolynomial.C (epsilon ^ w.length) * finiteModeNormalOrdered c w f

/-- Exact epsilon bookkeeping for *every* finite-mode ordered contraction.
Each derivative which hits the right creation polynomial contributes one epsilon;
the remaining annihilators are composed with the right annihilation word.
This theorem includes zero epsilon, empty words and all finite polynomial vectors.
-/
theorem finiteModeScaledNormalOrdered_product {d : ℕ} (epsilon : ℂ)
    (c e : AlgebraicFiniteModes d) (w v : List (Fin d))
    (f : AlgebraicFiniteModes d) :
    finiteModeScaledNormalOrdered epsilon c w
        (finiteModeScaledNormalOrdered epsilon e v f) =
      ((contractionWordSplits w).map fun ab =>
        MvPolynomial.C (epsilon ^ ab.1.length) *
          finiteModeScaledNormalOrdered epsilon
            (c * finiteModeDerivativeWord ab.1 e) (ab.2 ++ v) f).sum := by
  simp only [finiteModeScaledNormalOrdered]
  rw [finiteModeNormalOrdered_C_mul, finiteModeNormalOrdered_product,
    ← List.sum_map_mul_left, ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab hab
  rcases ab with ⟨a, b⟩
  have hlen := contractionWordSplits_length w a b hab
  have hpow : epsilon ^ w.length * epsilon ^ v.length =
      epsilon ^ a.length * epsilon ^ (b.length + v.length) := by
    calc
      epsilon ^ w.length * epsilon ^ v.length =
          epsilon ^ (w.length + v.length) := (pow_add _ _ _).symm
      _ = epsilon ^ (a.length + (b.length + v.length)) := by
        rw [← hlen, Nat.add_assoc]
      _ = epsilon ^ a.length * epsilon ^ (b.length + v.length) := pow_add _ _ _
  simp only [List.length_append]
  rw [← mul_assoc, ← map_mul, hpow, map_mul, mul_assoc]

/-- Coordinate partial derivatives genuinely commute on the finite-mode
polynomial carrier; this is checked on every polynomial coefficient. -/
theorem finiteMode_pderiv_comm {d : ℕ} (i j : Fin d)
    (f : AlgebraicFiniteModes d) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j f) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i f) := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  · ext m
    simp only [MvPolynomial.coeff_pderiv]
    have hi : (Finsupp.single j 1 : Fin d →₀ ℕ) i = 0 := by
      simp only [Finsupp.single_apply, if_neg (Ne.symm hij)]
    have hj : (Finsupp.single i 1 : Fin d →₀ ℕ) j = 0 := by
      simp only [Finsupp.single_apply, if_neg hij]
    have hindex : m + Finsupp.single i 1 + Finsupp.single j 1 =
        m + Finsupp.single j 1 + Finsupp.single i 1 := by ac_rfl
    simp only [Finsupp.add_apply, hi, hj, add_zero, hindex,
      mul_comm, mul_left_comm, mul_assoc]

/-- Changing the order of actual mixed partial derivatives preserves their action. -/
theorem finiteModeDerivativeWord_perm {d : ℕ} {a b : List (Fin d)}
    (h : a.Perm b) (f : AlgebraicFiniteModes d) :
    finiteModeDerivativeWord a f = finiteModeDerivativeWord b f := by
  induction h generalizing f with
  | nil => rfl
  | cons i h ih =>
    change MvPolynomial.pderiv i (finiteModeDerivativeWord _ f) =
      MvPolynomial.pderiv i (finiteModeDerivativeWord _ f)
    exact congrArg (fun z : AlgebraicFiniteModes d => MvPolynomial.pderiv i z) (ih f)
  | swap i j w =>
    change MvPolynomial.pderiv j (MvPolynomial.pderiv i (finiteModeDerivativeWord w f)) =
      MvPolynomial.pderiv i (MvPolynomial.pderiv j (finiteModeDerivativeWord w f))
    exact finiteMode_pderiv_comm j i (finiteModeDerivativeWord w f)
  | trans h₁ h₂ ih₁ ih₂ => exact (ih₁ f).trans (ih₂ f)

/-- All j! orderings of a selected list of j coordinate derivatives act alike.
Repeated coordinate labels remain distinct selected positions. -/
theorem finiteMode_mixedDerivative_permutation_sum {d : ℕ}
    (a : List (Fin d)) (f : AlgebraicFiniteModes d) :
    (∑ σ : Equiv.Perm (Fin a.length),
      finiteModeDerivativeWord (List.ofFn (a.get ∘ σ)) f) =
        a.length.factorial • finiteModeDerivativeWord a f := by
  classical
  have hterm (σ : Equiv.Perm (Fin a.length)) :
      finiteModeDerivativeWord (List.ofFn (a.get ∘ σ)) f =
        finiteModeDerivativeWord a f := by
    apply finiteModeDerivativeWord_perm
    simpa only [List.ofFn_get] using σ.ofFn_comp_perm a.get
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin]

/-- The exact inverse factorial removes precisely the ordering multiplicity,
including j=0. The displayed sum consists of actual polynomial mixed derivatives. -/
theorem finiteMode_mixedDerivative_div_factorial {d : ℕ}
    (epsilon : ℂ) (a : List (Fin d)) (f : AlgebraicFiniteModes d) :
    (epsilon ^ a.length / (a.length.factorial : ℂ)) •
      (∑ σ : Equiv.Perm (Fin a.length),
        finiteModeDerivativeWord (List.ofFn (a.get ∘ σ)) f) =
      epsilon ^ a.length • finiteModeDerivativeWord a f := by
  rw [finiteMode_mixedDerivative_permutation_sum, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]

/-- Partition a finite sum by an integer-valued order, retaining multiplicities. -/
private theorem list_sum_group_order {α A : Type*} [AddCommMonoid A]
    (l : List α) (order : α → ℕ) (N : ℕ) (F : α → A)
    (hN : ∀ a ∈ l, order a ≤ N) :
    (l.map F).sum = ∑ j ∈ Finset.range (N + 1),
      ((l.filter (fun a => decide (order a = j))).map F).sum := by
  classical
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, List.filter_nil, Finset.sum_const_zero]
  | cons a l ih =>
    have ha : order a ∈ Finset.range (N + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (hN a List.mem_cons_self))
    have hsingle : (∑ j ∈ Finset.range (N + 1),
        if order a = j then F a else 0) = F a := by
      rw [Finset.sum_eq_single (order a)]
      · simp only [ite_true]
      · intro j hj hja
        exact if_neg (Ne.symm hja)
      · intro hnot
        exact (hnot ha).elim
    have hcons (j : ℕ) :
        (((a :: l).filter (fun x => decide (order x = j))).map F).sum =
          (if order a = j then F a else 0) +
            ((l.filter (fun x => decide (order x = j))).map F).sum := by
      by_cases h : order a = j <;> simp [h]
    simp_rw [hcons]
    rw [Finset.sum_add_distrib, hsingle, List.map_cons, List.sum_cons,
      ih (fun x hx => hN x (List.mem_cons_of_mem a hx))]

/-- Group the complete finite-mode expansion by the number of contractions.
This tranche preserves the genuine operator terms rather than defining a
mixed-derivative target to be the requested answer. -/
theorem finiteModeScaledNormalOrdered_product_grouped {d : ℕ} (epsilon : ℂ)
    (c e : AlgebraicFiniteModes d) (w v : List (Fin d))
    (f : AlgebraicFiniteModes d) :
    finiteModeScaledNormalOrdered epsilon c w
        (finiteModeScaledNormalOrdered epsilon e v f) =
      ∑ j ∈ Finset.range (w.length + 1),
        MvPolynomial.C (epsilon ^ j) *
          ((((contractionWordSplits w).filter
            (fun ab => decide (ab.1.length = j))).map fun ab =>
              finiteModeScaledNormalOrdered epsilon
                (c * finiteModeDerivativeWord ab.1 e) (ab.2 ++ v) f).sum) := by
  rw [finiteModeScaledNormalOrdered_product]
  have hbound (ab : List (Fin d) × List (Fin d))
      (hab : ab ∈ contractionWordSplits w) : ab.1.length ≤ w.length := by
    have hlen := contractionWordSplits_length w ab.1 ab.2 hab
    exact hlen ▸ Nat.le_add_right ab.1.length ab.2.length
  rw [list_sum_group_order (contractionWordSplits w) (fun ab => ab.1.length)
    w.length _ hbound]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab hab
  have hlen : ab.1.length = j := by
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp hab).2
  rw [hlen]

/-- A literal ordered mixed-derivative sum: first choose the contracted
annihilation positions, then sum over all orders of those selected positions.
This is an explicit expression in actual coordinate partial derivatives. The
identification with Frechet derivative tensors and Hilbert-sector kernels remains
a separate obligation. -/
def finiteModeOrderedMixedSum {d : ℕ} (epsilon : ℂ)
    (c e : AlgebraicFiniteModes d) (w v : List (Fin d)) (j : ℕ)
    (f : AlgebraicFiniteModes d) : AlgebraicFiniteModes d :=
  ((((contractionWordSplits w).filter (fun ab => decide (ab.1.length = j))).map
    fun ab => ∑ σ : Equiv.Perm (Fin ab.1.length),
      finiteModeScaledNormalOrdered epsilon
        (c * finiteModeDerivativeWord (List.ofFn (ab.1.get ∘ σ)) e)
        (ab.2 ++ v) f).sum)

private theorem finiteModeOrderedMixedSum_eq_factorial {d : ℕ} (epsilon : ℂ)
    (c e : AlgebraicFiniteModes d) (w v : List (Fin d)) (j : ℕ)
    (f : AlgebraicFiniteModes d) :
    finiteModeOrderedMixedSum epsilon c e w v j f =
      j.factorial •
        ((((contractionWordSplits w).filter (fun ab => decide (ab.1.length = j))).map
          fun ab => finiteModeScaledNormalOrdered epsilon
            (c * finiteModeDerivativeWord ab.1 e) (ab.2 ++ v) f).sum) := by
  classical
  unfold finiteModeOrderedMixedSum
  have hterm (ab : List (Fin d) × List (Fin d))
      (hab : ab ∈ (contractionWordSplits w).filter
        (fun ab => decide (ab.1.length = j))) :
      (∑ σ : Equiv.Perm (Fin ab.1.length),
        finiteModeScaledNormalOrdered epsilon
          (c * finiteModeDerivativeWord (List.ofFn (ab.1.get ∘ σ)) e)
          (ab.2 ++ v) f) =
        j.factorial • finiteModeScaledNormalOrdered epsilon
          (c * finiteModeDerivativeWord ab.1 e) (ab.2 ++ v) f := by
    have hlen : ab.1.length = j := by
      simpa only [decide_eq_true_eq] using (List.mem_filter.mp hab).2
    subst j
    have hperm (σ : Equiv.Perm (Fin ab.1.length)) :
        finiteModeDerivativeWord (List.ofFn (ab.1.get ∘ σ)) e =
          finiteModeDerivativeWord ab.1 e := by
      apply finiteModeDerivativeWord_perm
      simpa only [List.ofFn_get] using σ.ofFn_comp_perm ab.1.get
    simp only [hperm, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin]
  calc
    _ = ((((contractionWordSplits w).filter (fun ab => decide (ab.1.length = j))).map
          fun ab => j.factorial • finiteModeScaledNormalOrdered epsilon
            (c * finiteModeDerivativeWord ab.1 e) (ab.2 ++ v) f).sum) := by
      apply congrArg List.sum
      exact List.map_congr_left hterm
    _ = _ := by
      simp only [nsmul_eq_mul]
      exact List.sum_map_mul_left _ _ _

/-- Complete finite-mode normal ordering with the exact epsilon^j / j!
coefficient, for the independently enumerated ordered mixed-derivative sums.
This closes the contraction-choice counting step. It does not assert the still
unproved physical tensor-kernel identification. -/
theorem finiteModeScaledNormalOrdered_product_div_factorial {d : ℕ} (epsilon : ℂ)
    (c e : AlgebraicFiniteModes d) (w v : List (Fin d))
    (f : AlgebraicFiniteModes d) :
    finiteModeScaledNormalOrdered epsilon c w
        (finiteModeScaledNormalOrdered epsilon e v f) =
      ∑ j ∈ Finset.range (w.length + 1),
        MvPolynomial.C (epsilon ^ j / (j.factorial : ℂ)) *
          finiteModeOrderedMixedSum epsilon c e w v j f := by
  rw [finiteModeScaledNormalOrdered_product_grouped]
  apply Finset.sum_congr rfl
  intro j hj
  rw [finiteModeOrderedMixedSum_eq_factorial, ← Nat.cast_smul_eq_nsmul ℂ,
    MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul,
    div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j))]

private theorem finiteModeDerivativeWord_coeff_eq_zero {d : ℕ}
    (w : List (Fin d)) (f : AlgebraicFiniteModes d) (m : Fin d →₀ ℕ)
    (h : f.totalDegree < (∑ i, m i) + w.length) :
    (finiteModeDerivativeWord w f).coeff m = 0 := by
  classical
  induction w generalizing m with
  | nil =>
    change f.coeff m = 0
    apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
    change f.totalDegree < m.sum (fun _ n => n)
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    simpa only [List.length_nil, Nat.add_zero] using h
  | cons i w ih =>
    change (MvPolynomial.pderiv i (finiteModeDerivativeWord w f)).coeff m = 0
    rw [MvPolynomial.coeff_pderiv]
    have hsum : (∑ k : Fin d, (m + (Finsupp.single i 1 : Fin d →₀ ℕ)) k) =
        (∑ k : Fin d, m k) + 1 := by
      simp [Finsupp.add_apply, Finset.sum_add_distrib, Finsupp.single_apply]
    have h' : f.totalDegree < (∑ k : Fin d, (m + (Finsupp.single i 1 : Fin d →₀ ℕ)) k) + w.length := by
      rw [hsum]
      simpa only [List.length_cons, Nat.succ_eq_add_one, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using h
    rw [ih _ h', zero_mul]

/-- Excess mixed derivatives vanish on the actual finite-mode polynomial.
No artificial truncation or particle-sector restriction is inserted. -/
theorem finiteModeDerivativeWord_eq_zero_of_totalDegree_lt {d : ℕ}
    (w : List (Fin d)) (f : AlgebraicFiniteModes d) (h : f.totalDegree < w.length) :
    finiteModeDerivativeWord w f = 0 := by
  ext m
  simp only [MvPolynomial.coeff_zero]
  exact finiteModeDerivativeWord_coeff_eq_zero w f m
    (h.trans_le (Nat.le_add_left w.length (∑ i, m i)))

private theorem finiteModeOrderedMixedSum_eq_zero {d : ℕ} (epsilon : ℂ)
    (c e : AlgebraicFiniteModes d) (w v : List (Fin d)) (j : ℕ)
    (f : AlgebraicFiniteModes d) (hj : e.totalDegree < j) :
    finiteModeOrderedMixedSum epsilon c e w v j f = 0 := by
  classical
  unfold finiteModeOrderedMixedSum
  apply List.sum_eq_zero
  intro z hz
  rcases List.mem_map.mp hz with ⟨ab, hab, rfl⟩
  have hlen : ab.1.length = j := by
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp hab).2
  apply Finset.sum_eq_zero
  intro σ hσ
  have hzero : finiteModeDerivativeWord (List.ofFn (ab.1.get ∘ σ)) e = 0 :=
    finiteModeDerivativeWord_eq_zero_of_totalDegree_lt _ e
      (by simpa only [List.length_ofFn, hlen] using hj)
  simp only [hzero, mul_zero, finiteModeScaledNormalOrdered,
    finiteModeNormalOrdered, zero_mul]

/-- The complete ordered mixed-derivative product formula has the manuscript's
minimum contraction limit, because excessive creation derivatives actually vanish.
The top degree here is the actual degree of the right creation polynomial. -/
theorem finiteModeScaledNormalOrdered_product_min {d : ℕ} (epsilon : ℂ)
    (c e : AlgebraicFiniteModes d) (w v : List (Fin d))
    (f : AlgebraicFiniteModes d) :
    finiteModeScaledNormalOrdered epsilon c w
        (finiteModeScaledNormalOrdered epsilon e v f) =
      ∑ j ∈ Finset.range (min w.length e.totalDegree + 1),
        MvPolynomial.C (epsilon ^ j / (j.factorial : ℂ)) *
          finiteModeOrderedMixedSum epsilon c e w v j f := by
  rw [finiteModeScaledNormalOrdered_product_div_factorial]
  apply (Finset.sum_subset
    (Finset.range_mono (Nat.add_le_add_right (Nat.min_le_left _ _) 1)) ?_).symm
  intro j hj hjnot
  have hlarge : e.totalDegree < j := by
    simp only [Finset.mem_range] at hj hjnot
    omega
  rw [finiteModeOrderedMixedSum_eq_zero epsilon c e w v j f hlarge, mul_zero]

section TensorContractions

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
variable [IsFiniteMeasure μ]

/-- Reindex equal full tensor sectors by the actual equality of coordinate counts. -/
def contractionFullSectorCast {m n : ℕ} (h : m = n) :
    ProductL2 μ (Fin m) ≃ₗᵢ[ℂ] ProductL2 μ (Fin n) := by
  subst n
  exact LinearIsometryEquiv.refl ℂ _

/-- Swap two *whole coordinate blocks*. This is the actual product-measure
pullback under `(x,y) ↦ (y,x)`, not an unnamed slot-identification hypothesis. -/
def contractionSwapBlocks (p k : ℕ) :
    ProductL2 μ (Fin (p + k)) →ₗᵢ[ℂ] ProductL2 μ (Fin (k + p)) :=
  (unregroupL2 μ k p).comp
    ((Lp.compMeasurePreservingₗᵢ ℂ Prod.swap
      (Measure.measurePreserving_swap (μ := sectorMeasure μ k) (ν := sectorMeasure μ p))).comp
      (regroupL2 μ p k))

/-- Literal tensor composition of the source contraction, before the two
falling-factorial coefficients. Here `p_b = r+j` and `q_c = j+s`, making the
consumed slots visible in the types. After A2 acts, swapping its outputs past
the `r` untouched inputs puts its first `j` outputs in A1's last `j` inputs.
The final `s` outputs remain spectators for A1. -/
def unscaledTensorContraction {r j s qb pc : ℕ}
    (A1 : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ qb)
    (A2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ (j + s)) :
    SymmetricSector μ (r + pc) →L[ℂ] SymmetricSector μ (qb + s) :=
  symmetricSectorProjection μ (qb + s) ∘L
    fullTensorLift μ (fullSectorExtension μ A1) s ∘L
    (contractionFullSectorCast μ (show r + (j + s) = (r + j) + s by omega)).toLinearIsometry.toContinuousLinearMap ∘L
    (contractionSwapBlocks μ (j + s) r).toContinuousLinearMap ∘L
    fullTensorLift μ (fullSectorExtension μ A2) r ∘L
    (contractionSwapBlocks μ r pc).toContinuousLinearMap ∘L
    (symmetricSectorInclusion μ (r + pc)).toContinuousLinearMap

/-- Genuine Hilbert tensor contraction estimate. No bound for a desired
contraction is an input: both A tensor identity norm estimates are proved upstream. -/
theorem norm_unscaledTensorContraction_le {r j s qb pc : ℕ}
    (A1 : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ qb)
    (A2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ (j + s)) :
    ‖unscaledTensorContraction μ A1 A2‖ ≤ ‖A1‖ * ‖A2‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (unscaledTensorContraction μ A1 A2)
    (mul_nonneg (ContinuousLinearMap.opNorm_nonneg A1) (ContinuousLinearMap.opNorm_nonneg A2))
  intro f
  simp only [unscaledTensorContraction, ContinuousLinearMap.comp_apply]
  calc
    _ ≤ ‖fullTensorLift μ (fullSectorExtension μ A1) s
        (contractionFullSectorCast μ (show r + (j + s) = (r + j) + s by omega)
          (contractionSwapBlocks μ (j + s) r
            (fullTensorLift μ (fullSectorExtension μ A2) r
              (contractionSwapBlocks μ r pc (symmetricSectorInclusion μ (r + pc) f)))))‖ :=
      norm_symmetricSectorProjection_apply_le μ (qb + s) _
    _ ≤ ‖A1‖ * ‖contractionFullSectorCast μ
        (show r + (j + s) = (r + j) + s by omega)
          (contractionSwapBlocks μ (j + s) r
            (fullTensorLift μ (fullSectorExtension μ A2) r
              (contractionSwapBlocks μ r pc (symmetricSectorInclusion μ (r + pc) f))))‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right
          ((norm_fullTensorLift_le μ _ s).trans (norm_fullSectorExtension_le μ A1))
          (norm_nonneg _))
    _ = ‖A1‖ * ‖fullTensorLift μ (fullSectorExtension μ A2) r
        (contractionSwapBlocks μ r pc (symmetricSectorInclusion μ (r + pc) f))‖ := by
      rw [LinearIsometryEquiv.norm_map, LinearIsometry.norm_map]
    _ ≤ ‖A1‖ * (‖A2‖ *
        ‖contractionSwapBlocks μ r pc (symmetricSectorInclusion μ (r + pc) f)‖) :=
      mul_le_mul_of_nonneg_left
        ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right
            ((norm_fullTensorLift_le μ _ r).trans (norm_fullSectorExtension_le μ A2))
            (norm_nonneg _))) (ContinuousLinearMap.opNorm_nonneg A1)
    _ = (‖A1‖ * ‖A2‖) * ‖f‖ := by
      rw [LinearIsometry.norm_map, LinearIsometry.norm_map, mul_assoc]

/-- Source contraction tensor with exactly its two falling-factorial coefficients.
Its equality to differentiating the polynomial kernels is an additional theorem,
not part of this definition or a hidden assumption of the norm estimate. -/
def tensorDerivativeContraction {r j s qb pc : ℕ}
    (A1 : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ qb)
    (A2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ (j + s)) :
    SymmetricSector μ (r + pc) →L[ℂ] SymmetricSector μ (qb + s) :=
  ((((r + j).descFactorial j : ℝ) * ((j + s).descFactorial j : ℝ) : ℝ) : ℂ) •
    unscaledTensorContraction μ A1 A2

/-- The exact falling-factorial norm estimate for the genuine source tensor
composition, including zero-mode and zero-contraction cases. -/
theorem norm_tensorDerivativeContraction_le {r j s qb pc : ℕ}
    (A1 : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ qb)
    (A2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ (j + s)) :
    ‖tensorDerivativeContraction μ A1 A2‖ ≤
      ((r + j).descFactorial j : ℝ) * ((j + s).descFactorial j : ℝ) * ‖A1‖ * ‖A2‖ := by
  let coefficient : ℝ := ((r + j).descFactorial j : ℝ) * ((j + s).descFactorial j : ℝ)
  have hc : 0 ≤ coefficient := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  change ‖(coefficient : ℂ) • unscaledTensorContraction μ A1 A2‖ ≤
    coefficient * ‖A1‖ * ‖A2‖
  calc
    _ ≤ ‖(coefficient : ℂ)‖ * ‖unscaledTensorContraction μ A1 A2‖ :=
      ContinuousLinearMap.opNorm_smul_le (coefficient : ℂ) (unscaledTensorContraction μ A1 A2)
    _ = coefficient * ‖unscaledTensorContraction μ A1 A2‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
    _ ≤ coefficient * (‖A1‖ * ‖A2‖) :=
      mul_le_mul_of_nonneg_left (norm_unscaledTensorContraction_le μ A1 A2) hc
    _ = _ := by ring

/-- Explicit degree-dependent constant for the source polynomial bound. -/
def contractionDegreeConstant (D : ℕ) : ℝ := ((D + 1 : ℕ) : ℝ) ^ D

/-- The arithmetic step of LLFP-Q2-028, valid also for unavailable orders,
where natural falling factorials automatically vanish. -/
theorem contractionCoefficient_polynomial_le (n k j D : ℕ)
    (hj : j ≤ D) (hk : k ≤ D) :
    (n.descFactorial j : ℝ) * (k.descFactorial j : ℝ) ≤
      contractionDegreeConstant D * (1 + (n : ℝ)) ^ D := by
  have hn : n.descFactorial j ≤ (n + 1) ^ D :=
    (Nat.descFactorial_le_pow n j).trans
      ((Nat.pow_le_pow_left (Nat.le_succ n) j).trans
        (Nat.pow_le_pow_right (Nat.succ_pos n) hj))
  have hk' : k.descFactorial j ≤ (D + 1) ^ D :=
    (Nat.descFactorial_le_pow k j).trans
      ((Nat.pow_le_pow_left (hk.trans (Nat.le_succ D)) j).trans
        (Nat.pow_le_pow_right (Nat.succ_pos D) hj))
  have hcast : ((n.descFactorial j * k.descFactorial j : ℕ) : ℝ) ≤
      (((n + 1) ^ D * (D + 1) ^ D : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.mul_le_mul hn hk')
  simpa only [contractionDegreeConstant, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_add, Nat.cast_one, add_comm, mul_comm] using hcast

/-- Polynomial growth when the second kernel has a fixed output degree at
most D; the first kernel's input degree is the varying degree. -/
theorem norm_tensorDerivativeContraction_polynomial_right {r j s qb pc D : ℕ}
    (A1 : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ qb)
    (A2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ (j + s))
    (hj : j ≤ D) (hs : j + s ≤ D) :
    ‖tensorDerivativeContraction μ A1 A2‖ ≤
      contractionDegreeConstant D * (1 + ((r + j : ℕ) : ℝ)) ^ D * ‖A1‖ * ‖A2‖ := by
  exact (norm_tensorDerivativeContraction_le μ A1 A2).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (contractionCoefficient_polynomial_le (r + j) (j + s) j D hj hs)
        (ContinuousLinearMap.opNorm_nonneg A1)) (ContinuousLinearMap.opNorm_nonneg A2))

/-- Polynomial growth in the reverse product, with the first kernel's input
degree fixed and the second kernel's output degree varying. -/
theorem norm_tensorDerivativeContraction_polynomial_left {r j s qb pc D : ℕ}
    (A1 : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ qb)
    (A2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ (j + s))
    (hj : j ≤ D) (hr : r + j ≤ D) :
    ‖tensorDerivativeContraction μ A1 A2‖ ≤
      contractionDegreeConstant D * (1 + ((j + s : ℕ) : ℝ)) ^ D * ‖A1‖ * ‖A2‖ := by
  have hcoeff : ((r + j).descFactorial j : ℝ) * ((j + s).descFactorial j : ℝ) ≤
      contractionDegreeConstant D * (1 + ((j + s : ℕ) : ℝ)) ^ D := by
    simpa only [mul_comm] using
      contractionCoefficient_polynomial_le (j + s) (r + j) j D hj hr
  exact (norm_tensorDerivativeContraction_le μ A1 A2).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff (ContinuousLinearMap.opNorm_nonneg A1))
      (ContinuousLinearMap.opNorm_nonneg A2))

end TensorContractions

end LiebLiniger.FixedPeriod.Quantum
