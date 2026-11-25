import Mathlib

/-!
# PROP-008 `lem:B4-high-moments`, stage B (word algebra)
(source/chapters/propagation/spectral_calculus.tex:24-60: "a product of `2p` centered factors")

Ordered products of operators (`wprod`), their expansion over finite index sets, the isolated-factor
vanishing lemma (`wprod_inner_eq_zero`: an `O j` commuting with all other factors, with `Π O_j u = 0`, where
`Π` is a self-adjoint operator fixing `u` and commuting with all other factors, kills the expectation) and the
operator-norm bound.  Pure algebra on `V →L[ℂ] V`, no tensor products.
-/

set_option autoImplicit false
open scoped InnerProductSpace
open Finset

namespace QuantumNLS.HighMomentsWord

section Algebra

variable {M : Type*} [Monoid M]

/-- Ordered product `O 0 * O 1 * ⋯ * O (m-1)`. -/
def wprod : (m : ℕ) → (Fin m → M) → M
  | 0, _ => 1
  | m + 1, O => O 0 * wprod m (fun i => O i.succ)

@[simp] theorem wprod_zero (O : Fin 0 → M) : wprod 0 O = 1 := rfl

theorem wprod_succ (m : ℕ) (O : Fin (m + 1) → M) :
    wprod (m + 1) O = O 0 * wprod m (fun i => O i.succ) := rfl

theorem wprod_commute_left {m : ℕ} (x : M) (O : Fin m → M) (h : ∀ i, Commute x (O i)) :
    Commute x (wprod m O) := by
  induction m with
  | zero => exact Commute.one_right x
  | succ m ih => exact (h 0).mul_right (ih _ (fun i => h i.succ))

/-- A factor commuting with all others can be moved to the right end. -/
theorem wprod_move_right : ∀ {m : ℕ} (O : Fin (m + 1) → M) (j : Fin (m + 1)),
    (∀ i, i ≠ j → Commute (O i) (O j)) →
    wprod (m + 1) O = wprod m (fun i => O (j.succAbove i)) * O j := by
  intro m
  induction m with
  | zero =>
    intro O j _
    have hj : j = 0 := Fin.ext (by have h2 := j.2; simp at h2 ⊢)
    subst hj
    simp [wprod]
  | succ m ih =>
    intro O j hcomm
    refine Fin.cases ?_ (fun j' => ?_) j hcomm
    · intro hcomm
      have hc : Commute (O 0) (wprod (m + 1) (fun i => O (Fin.succ i))) :=
        wprod_commute_left _ _ (fun i => (hcomm i.succ (Fin.succ_ne_zero i)).symm)
      rw [wprod_succ, hc.eq]
      congr 1
    · intro hcomm
      have ih' := ih (fun i => O i.succ) j' (fun i hi => hcomm i.succ (by simpa using hi))
      rw [wprod_succ, ih', wprod_succ]
      simp only [Fin.succ_succAbove_zero, Fin.succ_succAbove_succ, mul_assoc]

theorem wprod_const (x : M) : ∀ m : ℕ, wprod m (fun _ => x) = x ^ m := by
  intro m
  induction m with
  | zero => simp [wprod]
  | succ m ih => rw [wprod_succ, ih, pow_succ']

theorem wprod_eq_prod_ofFn : ∀ (m : ℕ) (O : Fin m → M), wprod m O = (List.ofFn O).prod := by
  intro m
  induction m with
  | zero => intro O; simp [wprod]
  | succ m ih => intro O; rw [wprod_succ, List.ofFn_succ, List.prod_cons, ih]

theorem wprod_append (m n : ℕ) (a : Fin m → M) (b : Fin n → M) :
    wprod (m + n) (Fin.append a b) = wprod m a * wprod n b := by
  rw [wprod_eq_prod_ofFn, wprod_eq_prod_ofFn, wprod_eq_prod_ofFn, List.ofFn_fin_append,
    List.prod_append]

end Algebra

section Expand

variable {M : Type*} [Semiring M]

theorem wprod_smul {R : Type*} [CommSemiring R] [Algebra R M] : ∀ (m : ℕ) (c : Fin m → R) (O : Fin m → M),
    wprod m (fun j => c j • O j) = (∏ j, c j) • wprod m O := by
  intro m
  induction m with
  | zero => intro c O; simp [wprod]
  | succ m ih =>
    intro c O
    rw [wprod_succ, wprod_succ, ih, Fin.prod_univ_succ, smul_mul_smul_comm]

theorem sum_piFinset_succ {β G : Type*} [AddCommMonoid G] {m : ℕ} (I : Fin (m + 1) → Finset β)
    (g : (Fin (m + 1) → β) → G) :
    ∑ s ∈ Fintype.piFinset I, g s =
      ∑ a ∈ I 0, ∑ t ∈ Fintype.piFinset (fun i : Fin m => I i.succ), g (Fin.cons a t) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun s => (s 0, Fin.tail s)) (fun x => Fin.cons x.1 x.2) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rw [Fintype.mem_piFinset] at hs
    rw [Finset.mem_product, Fintype.mem_piFinset]
    exact ⟨hs 0, fun i => hs i.succ⟩
  · intro x hx
    rw [Finset.mem_product, Fintype.mem_piFinset] at hx
    rw [Fintype.mem_piFinset]
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hx.1
    · simpa using hx.2 i
  · intro s _
    simp
  · intro x _
    simp
  · intro s _
    simp

theorem wprod_sum {β : Type*} : ∀ (m : ℕ) (I : Fin m → Finset β) (F : Fin m → β → M),
    wprod m (fun j => ∑ s ∈ I j, F j s) =
      ∑ s ∈ Fintype.piFinset I, wprod m (fun j => F j (s j)) := by
  intro m
  induction m with
  | zero => intro I F; simp [wprod]
  | succ m ih =>
    intro I F
    rw [wprod_succ, ih (fun i => I i.succ) (fun i => F i.succ), sum_piFinset_succ, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun t _ => ?_))
    rw [wprod_succ]
    simp

end Expand

section Vanish

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem wprod_norm_le : ∀ (m : ℕ) (O : Fin m → (V →L[ℂ] V)), ‖wprod m O‖ ≤ ∏ j, ‖O j‖ := by
  intro m
  induction m with
  | zero =>
    intro O
    rw [wprod_zero, Finset.univ_eq_empty, Finset.prod_empty]
    exact (ContinuousLinearMap.norm_id_le : ‖ContinuousLinearMap.id ℂ V‖ ≤ 1)
  | succ m ih =>
    intro O
    rw [wprod_succ, Fin.prod_univ_succ]
    refine (norm_mul_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_left (ih _) (norm_nonneg _)

/-- An isolated factor kills the expectation. -/
theorem wprod_inner_eq_zero {m : ℕ} (O : Fin (m + 1) → (V →L[ℂ] V)) (j : Fin (m + 1))
    (Pi : V →L[ℂ] V) (u : V)
    (hsa : ∀ x y, ⟪Pi x, y⟫_ℂ = ⟪x, Pi y⟫_ℂ) (hPu : Pi u = u)
    (hcomm : ∀ i, i ≠ j → Commute (O i) (O j)) (hPcomm : ∀ i, i ≠ j → Commute Pi (O i))
    (hvan : Pi (O j u) = 0) : ⟪u, wprod (m + 1) O u⟫_ℂ = 0 := by
  rw [wprod_move_right O j hcomm]
  set W := wprod m (fun i => O (j.succAbove i)) with hW
  have hc : Commute Pi W :=
    wprod_commute_left _ _ (fun i => hPcomm _ (Fin.succAbove_ne j i))
  have h1 : Pi (W (O j u)) = W (Pi (O j u)) := by
    have := congrArg (fun T : V →L[ℂ] V => T (O j u)) hc.eq
    simpa using this
  calc ⟪u, (W * O j) u⟫_ℂ = ⟪Pi u, W (O j u)⟫_ℂ := by rw [hPu]; rfl
    _ = ⟪u, Pi (W (O j u))⟫_ℂ := hsa _ _
    _ = 0 := by rw [h1, hvan]; simp

end Vanish

end QuantumNLS.HighMomentsWord
