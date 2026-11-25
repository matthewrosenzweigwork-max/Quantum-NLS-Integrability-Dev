import Mathlib

/-!
# R-CB4CC6EE (`values:lem:tail`), B2: scale-free partial fractions of the barycentric filter

Support module (algebra only, no analysis). For real `s` put `Xs s = (s - i)⁻¹`, `Ys s = (s + i)⁻¹`.
Then `Xs s - Ys s = (2i) Xs s Ys s` and `1 - Xs s Ys s = s^2/(s^2+1)`.

Main results:
* `pf_labeled`: for a commutative setting `X Y : ℝ → ℂ` with `X t - Y t = c (X t Y t)` (`c ≠ 0`), for every `p`
  there are constants `α β : ℕ → ℂ` (depending only on `p`) with
  `(1 - X t Y t)^p - 1 = ∑_{a<p} (α a X t^(a+1) + β a Y t^(a+1))` for all `t`.
  Proof: the span of the generators `{X^a, Y^a : 1 ≤ a ≤ n}` is closed under multiplication by `X Y`
  (using `X Y = c⁻¹(X - Y)`, `X Y^(m+1) = c⁻¹(X Y^m - Y^(m+1))`, and an induction giving
  `X^(m+1) Y ∈ span{X^b, Y^b : b ≤ m+1}`), and the labelled sums form a submodule containing the generators.
* `pf_transport`: with `α β` from `pf_labeled` at `c = 2i` and the standard `Xs, Ys`, for every `R > 0` and `t : ℝ`,
  `((t^2/(t^2+R^2) : ℝ) : ℂ)^p - 1 = ∑_{a<p} (α a x_R(t)^(a+1) + β a y_R(t)^(a+1))`
  with `x_R(t) = R (t - R i)⁻¹`, `y_R(t) = R (t + R i)⁻¹`. The constants do not depend on `R`
  (they come from the single choice at scale `R = 1`, transported by `t ↦ t/R`).
-/

namespace QuantumNLS.ValuesTailPartialFraction

open Submodule Finset

noncomputable section

/-- Generators `X^a`, `Y^a` with `1 ≤ a ≤ n`, as functions `ℝ → ℂ`. -/
def gen (X Y : ℝ → ℂ) (n : ℕ) : Set (ℝ → ℂ) :=
  {g | (∃ a, 1 ≤ a ∧ a ≤ n ∧ g = fun t => X t ^ a) ∨ (∃ a, 1 ≤ a ∧ a ≤ n ∧ g = fun t => Y t ^ a)}

lemma gen_mono (X Y : ℝ → ℂ) {n m : ℕ} (h : n ≤ m) : gen X Y n ⊆ gen X Y m := by
  rintro g (⟨a, h1, h2, rfl⟩ | ⟨a, h1, h2, rfl⟩)
  · exact Or.inl ⟨a, h1, h2.trans h, rfl⟩
  · exact Or.inr ⟨a, h1, h2.trans h, rfl⟩

lemma span_gen_mono (X Y : ℝ → ℂ) {n m : ℕ} (h : n ≤ m) :
    span ℂ (gen X Y n) ≤ span ℂ (gen X Y m) :=
  span_mono (gen_mono X Y h)

lemma mem_gen_X (X Y : ℝ → ℂ) {n a : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ n) :
    (fun t => X t ^ a) ∈ span ℂ (gen X Y n) :=
  subset_span (Or.inl ⟨a, h1, h2, rfl⟩)

lemma mem_gen_Y (X Y : ℝ → ℂ) {n a : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ n) :
    (fun t => Y t ^ a) ∈ span ℂ (gen X Y n) :=
  subset_span (Or.inr ⟨a, h1, h2, rfl⟩)

section Relation

variable {X Y : ℝ → ℂ} {c : ℂ}

lemma XY_eq (hc : c ≠ 0) (hrel : ∀ t, X t - Y t = c * (X t * Y t)) (t : ℝ) :
    X t * Y t = c⁻¹ * (X t - Y t) := by
  rw [hrel t]
  field_simp

lemma XY_mem (hc : c ≠ 0) (hrel : ∀ t, X t - Y t = c * (X t * Y t)) (n : ℕ) :
    (fun t => X t * Y t) ∈ span ℂ (gen X Y (n + 1)) := by
  have e : (fun t => X t * Y t) = c⁻¹ • (fun t => X t ^ 1) - c⁻¹ • (fun t => Y t ^ 1) := by
    funext t
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, pow_one]
    rw [XY_eq hc hrel t]
    ring
  rw [e]
  exact sub_mem (smul_mem _ _ (mem_gen_X X Y (le_refl 1) (by omega)))
    (smul_mem _ _ (mem_gen_Y X Y (le_refl 1) (by omega)))

/-- `X Y^(n+1) ∈ span{gen (n+1)}`, by induction using `X Y = c⁻¹ (X - Y)`. -/
lemma B_mem (hc : c ≠ 0) (hrel : ∀ t, X t - Y t = c * (X t * Y t)) (n : ℕ) :
    (fun t => X t * Y t ^ (n + 1)) ∈ span ℂ (gen X Y (n + 1)) := by
  induction n with
  | zero =>
    have e : (fun t => X t * Y t ^ (0 + 1)) = c⁻¹ • (fun t => X t ^ 1) - c⁻¹ • (fun t => Y t ^ 1) := by
      funext t
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, pow_one, zero_add]
      rw [XY_eq hc hrel t]
      ring
    rw [e]
    exact sub_mem (smul_mem _ _ (mem_gen_X X Y (le_refl 1) (by omega)))
      (smul_mem _ _ (mem_gen_Y X Y (le_refl 1) (by omega)))
  | succ n ih =>
    have e : (fun t => X t * Y t ^ (n + 1 + 1)) =
        c⁻¹ • (fun t => X t * Y t ^ (n + 1)) - c⁻¹ • (fun t => Y t ^ (n + 1 + 1)) := by
      funext t
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have h := XY_eq hc hrel t
      calc X t * Y t ^ (n + 1 + 1) = (X t * Y t) * Y t ^ (n + 1) := by ring
        _ = c⁻¹ * (X t - Y t) * Y t ^ (n + 1) := by rw [h]
        _ = c⁻¹ * (X t * Y t ^ (n + 1)) - c⁻¹ * Y t ^ (n + 1 + 1) := by ring
    rw [e]
    exact sub_mem (smul_mem _ _ (span_gen_mono X Y (by omega) ih))
      (smul_mem _ _ (mem_gen_Y X Y (by omega) (by omega)))

/-- Multiplication by `X` maps `span (gen n)` into `span (gen (n+1))`. -/
lemma mulX_mem (hc : c ≠ 0) (hrel : ∀ t, X t - Y t = c * (X t * Y t)) (n : ℕ) {g : ℝ → ℂ}
    (hg : g ∈ span ℂ (gen X Y n)) : (fun t => X t * g t) ∈ span ℂ (gen X Y (n + 1)) := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    rcases hg with ⟨a, h1, h2, rfl⟩ | ⟨a, h1, h2, rfl⟩
    · have e : (fun t => X t * (fun t => X t ^ a) t) = fun t => X t ^ (a + 1) := by
        funext t
        simp only [pow_succ]
        ring
      rw [e]
      exact mem_gen_X X Y (by omega) (by omega)
    · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      exact span_gen_mono X Y (by omega) (B_mem hc hrel b)
  | zero =>
    have e : (fun t => X t * (0 : ℝ → ℂ) t) = 0 := by
      funext t
      simp
    rw [e]
    exact zero_mem _
  | add x y _ _ hx hy =>
    have e : (fun t => X t * (x + y) t) = (fun t => X t * x t) + (fun t => X t * y t) := by
      funext t
      simp only [Pi.add_apply, Pi.add_apply, mul_add]
    rw [e]
    exact add_mem hx hy
  | smul a x _ hx =>
    have e : (fun t => X t * (a • x) t) = a • (fun t => X t * x t) := by
      funext t
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact smul_mem _ _ hx

/-- `X^(m+1) Y ∈ span (gen (m+1))`. -/
lemma A_mem (hc : c ≠ 0) (hrel : ∀ t, X t - Y t = c * (X t * Y t)) (m : ℕ) :
    (fun t => X t ^ (m + 1) * Y t) ∈ span ℂ (gen X Y (m + 1)) := by
  induction m with
  | zero =>
    have e : (fun t => X t ^ (0 + 1) * Y t) = fun t => X t * Y t := by
      funext t
      simp
    rw [e]
    exact XY_mem hc hrel 0
  | succ m ih =>
    have e : (fun t => X t ^ (m + 1 + 1) * Y t) = fun t => X t * (fun t => X t ^ (m + 1) * Y t) t := by
      funext t
      simp only [pow_succ]
      ring
    rw [e]
    exact mulX_mem hc hrel (m + 1) ih

/-- Multiplication by `X Y` maps `span (gen n)` into `span (gen (n+1))`. -/
lemma mulXY_mem (hc : c ≠ 0) (hrel : ∀ t, X t - Y t = c * (X t * Y t)) (n : ℕ) {g : ℝ → ℂ}
    (hg : g ∈ span ℂ (gen X Y n)) : (fun t => g t * (X t * Y t)) ∈ span ℂ (gen X Y (n + 1)) := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    rcases hg with ⟨a, h1, h2, rfl⟩ | ⟨a, h1, h2, rfl⟩
    · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      have e : (fun t => (fun t => X t ^ (b + 1)) t * (X t * Y t)) =
          fun t => X t ^ (b + 1 + 1) * Y t := by
        funext t
        simp only [pow_succ]
        ring
      rw [e]
      exact span_gen_mono X Y (by omega) (A_mem hc hrel (b + 1))
    · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      have e : (fun t => (fun t => Y t ^ (b + 1)) t * (X t * Y t)) =
          fun t => X t * Y t ^ (b + 1 + 1) := by
        funext t
        simp only [pow_succ]
        ring
      rw [e]
      exact span_gen_mono X Y (by omega) (B_mem hc hrel (b + 1))
  | zero =>
    have e : (fun t => (0 : ℝ → ℂ) t * (X t * Y t)) = 0 := by
      funext t
      simp
    rw [e]
    exact zero_mem _
  | add x y _ _ hx hy =>
    have e : (fun t => (x + y) t * (X t * Y t)) =
        (fun t => x t * (X t * Y t)) + (fun t => y t * (X t * Y t)) := by
      funext t
      simp only [Pi.add_apply, add_mul]
    rw [e]
    exact add_mem hx hy
  | smul a x _ hx =>
    have e : (fun t => (a • x) t * (X t * Y t)) = a • (fun t => x t * (X t * Y t)) := by
      funext t
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact smul_mem _ _ hx

/-- `(1 - XY)^n - 1 ∈ span (gen n)`. -/
lemma poly_mem (hc : c ≠ 0) (hrel : ∀ t, X t - Y t = c * (X t * Y t)) (n : ℕ) :
    (fun t => (1 - X t * Y t) ^ n - 1) ∈ span ℂ (gen X Y n) := by
  induction n with
  | zero =>
    have e : (fun t => (1 - X t * Y t) ^ 0 - 1) = 0 := by
      funext t
      simp
    rw [e]
    exact zero_mem _
  | succ n ih =>
    have e : (fun t => (1 - X t * Y t) ^ (n + 1) - 1) =
        (fun t => ((1 - X t * Y t) ^ n - 1) - ((1 - X t * Y t) ^ n - 1) * (X t * Y t) - X t * Y t) := by
      funext t
      ring
    rw [e]
    have ih' := span_gen_mono X Y (Nat.le_succ n) ih
    exact sub_mem (sub_mem ih' (mulXY_mem hc hrel n ih)) (XY_mem hc hrel n)

end Relation

/-- The labelled sums `∑_{a<n} (α a X^(a+1) + β a Y^(a+1))`, as a submodule of `ℝ → ℂ`. -/
def Lin (X Y : ℝ → ℂ) (n : ℕ) : Submodule ℂ (ℝ → ℂ) where
  carrier := {g | ∃ α β : ℕ → ℂ, ∀ t, g t = ∑ a ∈ range n, (α a * X t ^ (a + 1) + β a * Y t ^ (a + 1))}
  add_mem' := by
    rintro g h ⟨α, β, hg⟩ ⟨α', β', hh⟩
    refine ⟨fun a => α a + α' a, fun a => β a + β' a, fun t => ?_⟩
    simp only [Pi.add_apply, hg t, hh t]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  zero_mem' := ⟨fun _ => 0, fun _ => 0, fun t => by simp⟩
  smul_mem' := by
    rintro r g ⟨α, β, hg⟩
    refine ⟨fun a => r * α a, fun a => r * β a, fun t => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, hg t, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => by ring)

lemma gen_le_Lin (X Y : ℝ → ℂ) (n : ℕ) : gen X Y n ⊆ (Lin X Y n : Set (ℝ → ℂ)) := by
  rintro g (⟨a, h1, h2, rfl⟩ | ⟨a, h1, h2, rfl⟩)
  · refine ⟨fun j => if j = a - 1 then 1 else 0, fun _ => 0, fun t => ?_⟩
    rw [Finset.sum_eq_single (a - 1)]
    · simp only [ite_true, zero_mul, add_zero, one_mul]
      congr 1
      omega
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  · refine ⟨fun _ => 0, fun j => if j = a - 1 then 1 else 0, fun t => ?_⟩
    rw [Finset.sum_eq_single (a - 1)]
    · simp only [ite_true, zero_mul, zero_add, one_mul]
      congr 1
      omega
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h

/-- **Labelled partial fractions.** For `X - Y = c X Y` (`c ≠ 0`), the identity
`(1 - XY)^p - 1 = ∑_{a<p} (α a X^(a+1) + β a Y^(a+1))` holds with `p`-dependent constants. -/
theorem pf_labeled {X Y : ℝ → ℂ} {c : ℂ} (hc : c ≠ 0) (hrel : ∀ t, X t - Y t = c * (X t * Y t))
    (p : ℕ) : ∃ α β : ℕ → ℂ, ∀ t : ℝ,
      (1 - X t * Y t) ^ p - 1 = ∑ a ∈ range p, (α a * X t ^ (a + 1) + β a * Y t ^ (a + 1)) := by
  have hmem : (fun t => (1 - X t * Y t) ^ p - 1) ∈ Lin X Y p :=
    (span_le.mpr (gen_le_Lin X Y p)) (poly_mem hc hrel p)
  obtain ⟨α, β, h⟩ := hmem
  exact ⟨α, β, h⟩

/-- The standard pair `Xs s = (s - i)⁻¹`, `Ys s = (s + i)⁻¹` on the real line. -/
def Xs (s : ℝ) : ℂ := (((s : ℝ) : ℂ) - Complex.I)⁻¹

/-- See `Xs`. -/
def Ys (s : ℝ) : ℂ := (((s : ℝ) : ℂ) + Complex.I)⁻¹

lemma sub_I_ne (s : ℝ) : ((s : ℂ) - Complex.I) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

lemma add_I_ne (s : ℝ) : ((s : ℂ) + Complex.I) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

lemma Xs_rel (s : ℝ) : Xs s - Ys s = (2 * Complex.I) * (Xs s * Ys s) := by
  unfold Xs Ys
  have h1 := sub_I_ne s
  have h2 := add_I_ne s
  field_simp
  ring

/-- Scale-free partial fractions at the standard pair. -/
theorem pf_standard (p : ℕ) : ∃ α β : ℕ → ℂ, ∀ s : ℝ,
    (1 - Xs s * Ys s) ^ p - 1 = ∑ a ∈ range p, (α a * Xs s ^ (a + 1) + β a * Ys s ^ (a + 1)) :=
  pf_labeled (c := 2 * Complex.I) (by simp [Complex.I_ne_zero]) Xs_rel p

/-- `1 - Xs s Ys s = s^2/(s^2+1)`. -/
lemma one_sub_XsYs (s : ℝ) : 1 - Xs s * Ys s = (((s ^ 2 / (s ^ 2 + 1)) : ℝ) : ℂ) := by
  unfold Xs Ys
  have h1 := sub_I_ne s
  have h2 := add_I_ne s
  have hd : ((s : ℂ) ^ 2 + 1) ≠ 0 := by
    have : ((s : ℂ) - Complex.I) * ((s : ℂ) + Complex.I) = (s : ℂ) ^ 2 + 1 := by
      ring_nf
      simp [Complex.I_sq]
      ring
    rw [← this]
    exact mul_ne_zero h1 h2
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring

/-- **Transport to radius `R`.** The constants do not depend on `R`. -/
theorem pf_transport (p : ℕ) : ∃ α β : ℕ → ℂ, ∀ R : ℝ, 0 < R → ∀ t : ℝ,
    ((t ^ 2 / (t ^ 2 + R ^ 2) : ℝ) : ℂ) ^ p - 1 =
      ∑ a ∈ range p, (α a * ((R : ℂ) * ((t : ℂ) - (R : ℂ) * Complex.I)⁻¹) ^ (a + 1) +
        β a * ((R : ℂ) * ((t : ℂ) + (R : ℂ) * Complex.I)⁻¹) ^ (a + 1)) := by
  obtain ⟨α, β, h⟩ := pf_standard p
  refine ⟨α, β, fun R hR t => ?_⟩
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have e1 : Xs (t / R) = (R : ℂ) * ((t : ℂ) - (R : ℂ) * Complex.I)⁻¹ := by
    unfold Xs
    have h1 : ((t : ℂ) - (R : ℂ) * Complex.I) ≠ 0 := by
      intro h0
      have := congrArg Complex.im h0
      simp at this
      linarith
    push_cast
    field_simp
  have e2 : Ys (t / R) = (R : ℂ) * ((t : ℂ) + (R : ℂ) * Complex.I)⁻¹ := by
    unfold Ys
    have h1 : ((t : ℂ) + (R : ℂ) * Complex.I) ≠ 0 := by
      intro h0
      have := congrArg Complex.im h0
      simp at this
      linarith
    push_cast
    field_simp
  have e0 : (1 - Xs (t / R) * Ys (t / R)) = (((t / R) ^ 2 / ((t / R) ^ 2 + 1) : ℝ) : ℂ) :=
    one_sub_XsYs (t / R)
  have e3 : (((t / R) ^ 2 / ((t / R) ^ 2 + 1) : ℝ) : ℂ) = ((t ^ 2 / (t ^ 2 + R ^ 2) : ℝ) : ℂ) := by
    congr 1
    have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR.ne'
    have ht : t ^ 2 + R ^ 2 ≠ 0 := by positivity
    field_simp
  have := h (t / R)
  rw [e0, e3, e1, e2] at this
  exact this

end

#print axioms QuantumNLS.ValuesTailPartialFraction.pf_labeled
#print axioms QuantumNLS.ValuesTailPartialFraction.pf_standard
#print axioms QuantumNLS.ValuesTailPartialFraction.pf_transport

end QuantumNLS.ValuesTailPartialFraction
