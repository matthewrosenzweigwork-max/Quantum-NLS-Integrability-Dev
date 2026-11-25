import Mathlib
import NlsGge.Analysis.ODEFlowDeriv38

/-!
# Global linear ODE in a Banach space: existence and uniqueness on `ℝ` (38, B2 part a)

Generic infrastructure for `LinearODEParamDeriv38`: for a continuous family `C : ℝ → G →L[ℝ] G`
the linear ODE `D' = C x (D x)` has, for every initial value at `0`, exactly one solution on all
of `ℝ`.  Existence chains `NlsGge.ODEFlowDeriv38.exists_lin38` on `[0, n]`, glued by uniqueness,
and handles `x < 0` by the reflection `C ↦ -C(-·)`.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped NNReal

namespace NlsGge.NLS38

section Generic

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A continuous operator-valued function is bounded on a compact interval, by a nonnegative
constant. -/
lemma clm_bound_Icc38 (C : ℝ → G →L[ℝ] G) (hC : Continuous C) (a b : ℝ) :
    ∃ K : ℝ≥0, ∀ t ∈ Icc a b, ‖C t‖ ≤ K := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hC.continuousOn
  exact ⟨M.toNNReal, fun t ht => (hM t ht).trans (Real.le_coe_toNNReal M)⟩

lemma lipschitzOnWith_clm38 (T : G →L[ℝ] G) (K : ℝ≥0) (hT : ‖T‖ ≤ K) {s : Set G} :
    LipschitzOnWith K (fun y => T y) s := by
  refine LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact (T.le_opNorm _).trans (by gcongr)

/-- **Uniqueness** of solutions of the linear ODE `D' = C x (D x)` on `ℝ`. -/
theorem lin_unique38 (C : ℝ → G →L[ℝ] G) (hC : Continuous C) {D₁ D₂ : ℝ → G}
    (h1 : ∀ x, HasDerivAt D₁ (C x (D₁ x)) x) (h2 : ∀ x, HasDerivAt D₂ (C x (D₂ x)) x)
    (h0 : D₁ 0 = D₂ 0) : D₁ = D₂ := by
  funext x
  obtain ⟨K, hK⟩ := clm_bound_Icc38 C hC (-(|x| + 1)) (|x| + 1)
  have hx : x ∈ Ioo (-(|x| + 1)) (|x| + 1) := by
    constructor <;> cases abs_cases x <;> linarith
  have h0m : (0 : ℝ) ∈ Ioo (-(|x| + 1)) (|x| + 1) := by
    constructor <;> linarith [abs_nonneg x]
  have := ODE_solution_unique_of_mem_Ioo (v := fun t y => C t y) (s := fun _ => (univ : Set G))
    (K := K) (f := D₁) (g := D₂) (a := -(|x| + 1)) (b := |x| + 1) (t₀ := 0)
    (fun t ht => lipschitzOnWith_clm38 (C t) K (hK t (Ioo_subset_Icc_self ht)))
    h0m (fun t _ => ⟨h1 t, trivial⟩) (fun t _ => ⟨h2 t, trivial⟩) h0
  exact this hx

/-- Uniqueness on `[0, T]` (right derivatives). -/
lemma lin_unique_Icc38 (C : ℝ → G →L[ℝ] G) (hC : Continuous C) {T : ℝ} {D₁ D₂ : ℝ → G}
    (h1 : ∀ t ∈ Icc 0 T, HasDerivWithinAt D₁ (C t (D₁ t)) (Icc 0 T) t)
    (h2 : ∀ t ∈ Icc 0 T, HasDerivWithinAt D₂ (C t (D₂ t)) (Icc 0 T) t)
    (h0 : D₁ 0 = D₂ 0) : EqOn D₁ D₂ (Icc 0 T) := by
  by_cases hT : 0 ≤ T
  swap
  · intro t ht; exact absurd (ht.1.trans ht.2) hT
  obtain ⟨K, hK⟩ := clm_bound_Icc38 C hC 0 T
  have hmono : ∀ t ∈ Ico 0 T, ∀ {D : ℝ → G}, HasDerivWithinAt D (C t (D t)) (Icc 0 T) t →
      HasDerivWithinAt D (C t (D t)) (Ici t) t := fun t ht D h =>
    h.mono_of_mem_nhdsWithin (by
      have : Icc t T ∈ 𝓝[Ici t] t := Icc_mem_nhdsGE ht.2
      filter_upwards [this] with y hy
      exact ⟨ht.1.trans hy.1, hy.2⟩)
  exact ODE_solution_unique_of_mem_Icc_right (v := fun t y => C t y)
    (s := fun _ => (univ : Set G)) (K := K) (f := D₁) (g := D₂) (a := 0) (b := T)
    (fun t ht => lipschitzOnWith_clm38 (C t) K (hK t ⟨ht.1, ht.2.le⟩))
    (fun t ht => (h1 t ht).continuousWithinAt) (fun t ht => hmono t ht (h1 t ⟨ht.1, ht.2.le⟩))
    (fun _ _ => trivial)
    (fun t ht => (h2 t ht).continuousWithinAt) (fun t ht => hmono t ht (h2 t ⟨ht.1, ht.2.le⟩))
    (fun _ _ => trivial) h0

variable [CompleteSpace G]

/-- Forward existence on `[0, ∞)`: a two-sided derivative at every `x > 0` and a right derivative
at `0`. -/
theorem exists_fwd_lin38 (C : ℝ → G →L[ℝ] G) (hC : Continuous C) (M₀ : G) :
    ∃ D : ℝ → G, D 0 = M₀ ∧ (∀ x, 0 < x → HasDerivAt D (C x (D x)) x) ∧
      HasDerivWithinAt D (C 0 (D 0)) (Ici 0) 0 := by
  have hn : ∀ n : ℕ, ∃ D : ℝ → G, D 0 = M₀ ∧
      ∀ t ∈ Icc 0 (n : ℝ), HasDerivWithinAt D (C t (D t)) (Icc 0 (n : ℝ)) t := fun n => by
    obtain ⟨K, hK⟩ := clm_bound_Icc38 C hC 0 n
    exact (NlsGge.ODEFlowDeriv38.exists_lin38 C K hK hC.continuousOn M₀)
  choose D hD0 hD using hn
  have hag : ∀ n m : ℕ, n ≤ m → EqOn (D n) (D m) (Icc 0 (n : ℝ)) := fun n m hnm =>
    lin_unique_Icc38 C hC (hD n)
      (fun t ht => (hD m t ⟨ht.1, ht.2.trans (by exact_mod_cast hnm)⟩).mono
        (Icc_subset_Icc_right (by exact_mod_cast hnm))) (by rw [hD0, hD0])
  set F : ℝ → G := fun x => D ⌈x⌉₊ x with hF
  have hFN : ∀ N : ℕ, EqOn F (D N) (Icc 0 (N : ℝ)) := fun N y hy => by
    have hc : ⌈y⌉₊ ≤ N := Nat.ceil_le.2 hy.2
    exact hag _ _ hc ⟨hy.1, Nat.le_ceil y⟩
  have hF0 : F 0 = M₀ := by simp [hF, hD0]
  refine ⟨F, hF0, fun x hx => ?_, ?_⟩
  · set N : ℕ := ⌈x⌉₊ + 1 with hN
    have hxN : x < N := by
      have := Nat.le_ceil x
      simp only [hN, Nat.cast_add, Nat.cast_one]
      linarith
    have hI : Icc 0 (N : ℝ) ∈ 𝓝 x := Icc_mem_nhds hx hxN
    have h1 := (hD N x ⟨hx.le, hxN.le⟩).hasDerivAt hI
    have hev : F =ᶠ[𝓝 x] D N := by
      filter_upwards [hI] with y hy using hFN N hy
    rw [hFN N ⟨hx.le, hxN.le⟩]
    exact h1.congr_of_eventuallyEq hev
  · set N : ℕ := 1 with hN
    have hI : Icc 0 (N : ℝ) ∈ 𝓝[Ici 0] (0 : ℝ) := Icc_mem_nhdsGE (by simp [hN])
    have h1 := (hD N 0 ⟨le_rfl, by simp [hN]⟩).mono_of_mem_nhdsWithin hI
    have hev : F =ᶠ[𝓝[Ici 0] (0 : ℝ)] D N := by
      filter_upwards [hI] with y hy using hFN N hy
    have hF0N : F 0 = D N 0 := hFN N ⟨le_rfl, by simp [hN]⟩
    rw [hF0N]
    exact h1.congr_of_eventuallyEq hev hF0N

/-- **Global existence** for the linear ODE `D' = C x (D x)` with `D 0 = M₀` on all of `ℝ`. -/
theorem exists_global_lin38 (C : ℝ → G →L[ℝ] G) (hC : Continuous C) (M₀ : G) :
    ∃ D : ℝ → G, D 0 = M₀ ∧ ∀ x, HasDerivAt D (C x (D x)) x := by
  obtain ⟨Dp, hp0, hpd, hpr⟩ := exists_fwd_lin38 C hC M₀
  obtain ⟨Dm, hm0, hmd, hmr⟩ := exists_fwd_lin38 (fun y => -(C (-y))) (by fun_prop) M₀
  set D : ℝ → G := fun x => if 0 ≤ x then Dp x else Dm (-x) with hD
  have hDp : ∀ x, 0 ≤ x → D x = Dp x := fun x hx => by simp [hD, hx]
  have hDm : ∀ x, x ≤ 0 → D x = Dm (-x) := fun x hx => by
    rcases hx.eq_or_lt with h | h
    · subst h; simp [hD, hp0, hm0]
    · simp [hD, not_le.2 h]
  have hD0 : D 0 = M₀ := by rw [hDp 0 le_rfl, hp0]
  -- derivative of the reflected branch
  have hrefl : ∀ x, x < 0 → HasDerivAt (fun y => Dm (-y)) (C x (Dm (-x))) x := fun x hx => by
    have h1 := (hmd (-x) (by linarith)).scomp x (hasDerivAt_neg x)
    refine h1.congr_deriv ?_
    simp
  refine ⟨D, hD0, fun x => ?_⟩
  rcases lt_trichotomy x 0 with h | h | h
  · have hev : D =ᶠ[𝓝 x] fun y => Dm (-y) := by
      filter_upwards [Iio_mem_nhds h] with y hy using hDm y (le_of_lt hy)
    rw [hDm x h.le]
    exact (hrefl x h).congr_of_eventuallyEq hev
  · subst h
    have hR : HasDerivWithinAt D (C 0 (D 0)) (Ici 0) 0 := by
      rw [hD0]
      have := hpr
      rw [hp0] at this
      exact this.congr_of_mem (fun y hy => hDp y hy) (mem_Ici.2 le_rfl)
    have hL : HasDerivWithinAt D (C 0 (D 0)) (Iic 0) 0 := by
      rw [hD0]
      have h1 := hmr
      rw [hm0] at h1
      have h1' : HasDerivWithinAt Dm (-(C 0 M₀)) (Ici 0) (-(0 : ℝ)) := by simpa using h1
      have h2 := h1'.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ)).hasDerivWithinAt
        (fun y (hy : y ∈ Iic (0 : ℝ)) => (by simpa using hy : -y ∈ Ici (0 : ℝ)))
      have h3 := h2.congr_deriv (g' := C 0 M₀) (by simp)
      exact h3.congr_of_mem (fun y hy => hDm y hy) (mem_Iic.2 le_rfl)
    have := hR.union hL
    rw [Ici_union_Iic, hasDerivWithinAt_univ] at this
    exact this
  · have hev : D =ᶠ[𝓝 x] Dp := by
      filter_upwards [Ioi_mem_nhds h] with y hy using hDp y (le_of_lt hy)
    rw [hDp x h.le]
    exact (hpd x h).congr_of_eventuallyEq hev

end Generic

end NlsGge.NLS38
