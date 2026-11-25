import QuantumNLS.LabelKernelLimit
import QuantumNLS.SmallClusterBound

/-!
# PROP-003 `thm:B3-exact-separation`, deterministic core: the exceptional cluster argument

Source: `source/chapters/propagation/label_periods.tex:117-224` (proof of `thm:B3-exact-separation`),
the single-configuration part. For one on-shell configuration (the auxiliary construction's `OnShellBethe`,
LabelJointLimit `4120590e…`), an integer `a`, a point `x` and `δ > 0`:

* `clusterL B a x δ = {j : n_j ≤ a, q_j > x − 3δ}` (eq:B3-exceptional-cluster), `extForce`
  (eq:B3-exterior-force: `F_N^ext(z) = Lz − 2 Σ_{ℓ∉J} arctan(c/(z − q_ℓ))`, `c = κ/N`);
* `extForce_cluster`: at a cluster root, `F_N^ext(q_j) − 2πn_j = 2 Σ_{ℓ∈J, ℓ≠j} arctan(c/(q_j − q_ℓ))`
  (the Bethe relation);
* `extForce_lower`: if every exterior root has distance `≥ δ` from `y`, then
  `F_N^ext(y) ≥ Ly − 2κ N⁻¹ Σ_{ℓ∉J} h(q_ℓ) − 2κ³/(N²δ³)` for any `h` equal to `1/(y − t)` at distance
  `≥ δ` from `y` (arctangent replaced by its argument, error `≤ N(c/δ)³`);
* **`core_left`**: if `2πa < L y − 2κ N⁻¹ Σ_{ℓ∉J} h(q_ℓ) − 2κ³/(N²δ³)` (`y = x − 2δ`) and
  `3√(κ k/(LN)) < δ` (`k = |J|`), then `n_j ≤ a ⇒ q_j < x − δ` for every root. Proof as printed:
  a root `q_j ≥ x − δ` with `n_j ≤ a` forces all exterior roots to stay `δ` away from `y`
  (ordering), the exterior force is monotone between `y` and the cluster roots (eq:B3-exterior-monotone,
  used in its elementary form: each exterior arctangent is monotone on root-free intervals), giving
  eq:B3-cluster-force-application, and R-CFCD5A9D (`SmallClusterBound.small_cluster`, accepted,
  `94661e3c…`) gives eq:B3-exceptional-diameter, a contradiction;
* `reflect` (`q̃_j = −q_{N+1−j}`, `ñ_j = −n_{N+1−j}`, again on shell) and **`core_right`**: the
  reflected statement `n_j ≥ a + 1 ⇒ q_j > x + δ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open Finset
open scoped BigOperators

namespace QuantumNLS.LabelSeparationCore

open QuantumNLS.LabelJointLimit QuantumNLS.LabelKernelLimit QuantumNLS.SmallClusterBound

variable {L κ : ℝ} {N : ℕ}

/-- The exceptional cluster `J_N = {j : n_j ≤ a, q_j > x − 3δ}`. -/
def clusterL (B : OnShellBethe L κ N) (a : ℤ) (x δ : ℝ) : Finset (Fin N) :=
  univ.filter fun j => B.n j ≤ a ∧ x - 3 * δ < B.q j

/-- The mirrored cluster `{j : n_j ≥ a + 1, q_j < x + 3δ}`. -/
def clusterR (B : OnShellBethe L κ N) (a : ℤ) (x δ : ℝ) : Finset (Fin N) :=
  univ.filter fun j => a + 1 ≤ B.n j ∧ B.q j < x + 3 * δ

/-- The exterior force `F_N^ext(z) = Lz − 2 Σ_{ℓ∉J} arctan(c/(z − q_ℓ))`, `c = κ/N`. -/
def extForce (B : OnShellBethe L κ N) (J : Finset (Fin N)) (z : ℝ) : ℝ :=
  L * z - 2 * ∑ l ∈ univ.filter (· ∉ J), Real.arctan ((κ / N) / (z - B.q l))

/-- At a cluster root the exterior force is `2πn_j` plus the internal cluster force. -/
lemma extForce_cluster (B : OnShellBethe L κ N) (J : Finset (Fin N)) {j : Fin N} (hj : j ∈ J) :
    extForce B J (B.q j) = 2 * Real.pi * B.n j +
      2 * ∑ l ∈ J.erase j, Real.arctan ((κ / N) / (B.q j - B.q l)) := by
  have hb := B.bethe j
  have hs : ∑ l ∈ univ.erase j, Real.arctan ((κ / N) / (B.q j - B.q l)) =
      ∑ l ∈ J.erase j, Real.arctan ((κ / N) / (B.q j - B.q l)) +
        ∑ l ∈ univ.filter (· ∉ J), Real.arctan ((κ / N) / (B.q j - B.q l)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (univ.erase j) (· ∈ J)]
    congr 1
    · congr 1
      ext l
      simp only [mem_filter, mem_erase, mem_univ, and_true]
    · congr 1
      ext l
      simp only [mem_filter, mem_erase, mem_univ, and_true, true_and]
      exact ⟨fun h => h.2, fun h => ⟨fun hlj => h (hlj ▸ hj), h⟩⟩
  unfold extForce
  rw [hs] at hb
  linarith

lemma arctan_le_add (u : ℝ) : Real.arctan u ≤ u + |u| ^ 3 := by
  have := abs_arctan_sub_le u
  linarith [le_abs_self (Real.arctan u - u)]

/-- Lower bound for the exterior force at a point `δ` away from all exterior roots. -/
lemma extForce_lower (hκ : 0 < κ) (hN : 0 < N) (B : OnShellBethe L κ N) (J : Finset (Fin N))
    {y δ : ℝ} (hδ : 0 < δ) (h : ℝ → ℝ) (hh : ∀ t, δ ≤ |y - t| → h t = 1 / (y - t))
    (hfar : ∀ l, l ∉ J → δ ≤ |y - B.q l|) :
    L * y - 2 * κ * ((1 / (N : ℝ)) * ∑ l ∈ univ.filter (· ∉ J), h (B.q l)) -
        2 * κ ^ 3 / ((N : ℝ) ^ 2 * δ ^ 3) ≤ extForce B J y := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  set c : ℝ := κ / N with hc
  have hc0 : 0 < c := div_pos hκ hNr
  have hterm : ∀ l ∈ univ.filter (· ∉ J), Real.arctan (c / (y - B.q l)) ≤
      c * h (B.q l) + (c / δ) ^ 3 := by
    intro l hl
    have hl' : l ∉ J := (mem_filter.1 hl).2
    have hd := hfar l hl'
    have hpos : 0 < |y - B.q l| := lt_of_lt_of_le hδ hd
    have h1 : c * h (B.q l) = c / (y - B.q l) := by rw [hh _ hd, mul_one_div]
    have h2 : |c / (y - B.q l)| ≤ c / δ := by
      rw [abs_div, abs_of_pos hc0]
      exact div_le_div_of_nonneg_left hc0.le hδ hd
    have h3 : |c / (y - B.q l)| ^ 3 ≤ (c / δ) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) h2 3
    have := arctan_le_add (c / (y - B.q l))
    rw [h1]; linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hsum
  have hcard : ((univ.filter (· ∉ J)).card : ℝ) ≤ N := by
    have := Finset.card_le_univ (univ.filter (· ∉ J))
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have hcube : ((univ.filter (· ∉ J)).card : ℝ) * (c / δ) ^ 3 ≤ κ ^ 3 / ((N : ℝ) ^ 2 * δ ^ 3) := by
    calc ((univ.filter (· ∉ J)).card : ℝ) * (c / δ) ^ 3 ≤ N * (c / δ) ^ 3 := by gcongr
      _ = κ ^ 3 / ((N : ℝ) ^ 2 * δ ^ 3) := by rw [hc]; field_simp
  have hcN : 2 * κ * ((1 / (N : ℝ)) * ∑ l ∈ univ.filter (· ∉ J), h (B.q l)) =
      2 * (c * ∑ l ∈ univ.filter (· ∉ J), h (B.q l)) := by rw [hc]; ring
  unfold extForce
  rw [hcN]
  have : 2 * κ ^ 3 / ((N : ℝ) ^ 2 * δ ^ 3) = 2 * (κ ^ 3 / ((N : ℝ) ^ 2 * δ ^ 3)) := by ring
  rw [this]
  linarith

lemma arctan_mono_left {c y z q : ℝ} (hc : 0 < c) (hq : q < y) (hyz : y ≤ z) :
    Real.arctan (c / (z - q)) ≤ Real.arctan (c / (y - q)) :=
  Real.arctan_strictMono.monotone
    (div_le_div_of_nonneg_left hc.le (by linarith) (by linarith))

lemma arctan_mono_right {c y z q : ℝ} (hc : 0 < c) (hq : z < q) (hyz : y ≤ z) :
    Real.arctan (c / (z - q)) ≤ Real.arctan (c / (y - q)) := by
  refine Real.arctan_strictMono.monotone ?_
  have e1 : c / (z - q) = -(c / (q - z)) := by rw [← div_neg, neg_sub]
  have e2 : c / (y - q) = -(c / (q - y)) := by rw [← div_neg, neg_sub]
  rw [e1, e2, neg_le_neg_iff]
  exact div_le_div_of_nonneg_left hc.le (by linarith) (by linarith)

/-- **The cluster argument** (first implication of eq:B3-exact-cutoff, one configuration). -/
theorem core_left (hL : 0 < L) (hκ : 0 < κ) (hN : 0 < N) (B : OnShellBethe L κ N) (a : ℤ)
    {x δ : ℝ} (hδ : 0 < δ) (h : ℝ → ℝ)
    (hh : ∀ t, δ ≤ |x - 2 * δ - t| → h t = 1 / (x - 2 * δ - t))
    (hF : 2 * Real.pi * a < L * (x - 2 * δ) -
        2 * κ * ((1 / (N : ℝ)) * ∑ l ∈ univ.filter (· ∉ clusterL B a x δ), h (B.q l)) -
        2 * κ ^ 3 / ((N : ℝ) ^ 2 * δ ^ 3))
    (hk : 3 * Real.sqrt (κ / N * (clusterL B a x δ).card / L) < δ) :
    ∀ j, B.n j ≤ a → B.q j < x - δ := by
  intro j0 hn0
  by_contra hq0
  push Not at hq0
  set J := clusterL B a x δ with hJ
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  set c : ℝ := κ / N with hc
  have hc0 : 0 < c := div_pos hκ hNr
  set y := x - 2 * δ with hy
  have hmemJ : ∀ j, j ∈ J ↔ B.n j ≤ a ∧ x - 3 * δ < B.q j := fun j => by
    simp only [hJ, clusterL, mem_filter, mem_univ, true_and]
  have hj0 : j0 ∈ J := (hmemJ j0).2 ⟨hn0, by linarith⟩
  have hext : ∀ l, l ∉ J → B.q l ≤ x - 3 * δ ∨ ∀ j ∈ J, B.q j < B.q l := by
    intro l hl
    by_cases hnl : B.n l ≤ a
    · left
      by_contra h'
      push Not at h'
      exact hl ((hmemJ l).2 ⟨hnl, h'⟩)
    · right
      intro j hj
      have hnj := ((hmemJ j).1 hj).1
      have hlt : j < l := by
        by_contra hle
        push Not at hle
        have := B.n_mono hle
        omega
      exact B.q_strict hlt
  have hfar : ∀ l, l ∉ J → δ ≤ |y - B.q l| := by
    intro l hl
    rcases hext l hl with h1 | h1
    · rw [abs_of_nonneg (by linarith)]; linarith
    · have := h1 j0 hj0
      rw [abs_of_neg (by linarith)]; linarith
  have hFy : 2 * Real.pi * a < extForce B J y :=
    lt_of_lt_of_le hF (extForce_lower hκ hN B J hδ h hh hfar)
  have hclust : ∀ j ∈ J, y < B.q j →
      L * (B.q j - y) ≤ 2 * ∑ l ∈ J.erase j, Real.arctan (c / (B.q j - B.q l)) := by
    intro j hj hyj
    have hmono : L * (B.q j - y) ≤ extForce B J (B.q j) - extForce B J y := by
      unfold extForce
      have : ∑ l ∈ univ.filter (· ∉ J), Real.arctan (c / (B.q j - B.q l)) ≤
          ∑ l ∈ univ.filter (· ∉ J), Real.arctan (c / (y - B.q l)) :=
        Finset.sum_le_sum fun l hl => by
          have hl' : l ∉ J := (mem_filter.1 hl).2
          rcases hext l hl' with h1 | h1
          · exact arctan_mono_left hc0 (by linarith) hyj.le
          · exact arctan_mono_right hc0 (h1 j hj) hyj.le
      linarith
    have hsplit := extForce_cluster B J hj
    have hnj : (B.n j : ℝ) ≤ a := by exact_mod_cast ((hmemJ j).1 hj).1
    have hpi : 2 * Real.pi * (B.n j : ℝ) ≤ 2 * Real.pi * a := by
      have := Real.pi_pos; nlinarith
    linarith
  -- the small-cluster lemma on the shifted cluster roots
  set k := J.card
  set e : Fin k ≃ J := J.equivFin.symm
  set xs : Fin k → ℝ := fun i => B.q (e i) - y with hxs
  have hinj : Function.Injective xs := by
    intro i i' hii
    have : B.q (e i) = B.q (e i') := by simpa [hxs] using hii
    exact e.injective (Subtype.ext (B.q_strict.injective this))
  have hforce : ∀ i, 0 < xs i →
      L * xs i ≤ 2 * ∑ l ∈ univ.erase i, Real.arctan (c / (xs i - xs l)) := by
    intro i hi
    have hyi : y < B.q (e i) := by simp only [hxs] at hi; linarith
    have h1 := hclust (e i) (e i).2 hyi
    have hsum : ∑ l ∈ univ.erase i, Real.arctan (c / (xs i - xs l)) =
        ∑ l ∈ J.erase (e i), Real.arctan (c / (B.q (e i) - B.q l)) := by
      rw [Finset.sum_erase_eq_sub (mem_univ i), Finset.sum_erase_eq_sub (e i).2]
      congr 1
      · simp only [hxs, sub_sub_sub_cancel_right]
        rw [Equiv.sum_comp e (fun l : J => Real.arctan (c / (B.q (e i) - B.q l)))]
        exact Finset.sum_coe_sort J (fun l => Real.arctan (c / (B.q (e i) - B.q l)))
      · simp only [hxs, sub_sub_sub_cancel_right]
    rw [hsum]
    exact h1
  have hsc := small_cluster hinj hc0 hL hforce (e.symm ⟨j0, hj0⟩)
  simp only [hxs, Equiv.apply_symm_apply] at hsc
  have h1 : δ ≤ max (B.q j0 - y) 0 := le_max_of_le_left (by linarith)
  have h2 : 3 * Real.sqrt (c * k / L) < δ := by rw [hc]; exact hk
  linarith

/-! ## Reflection -/

/-- The reflected configuration `q̃_j = −q_{N+1−j}`, `ñ_j = −n_{N+1−j}`; it is again on shell. -/
def reflect (B : OnShellBethe L κ N) : OnShellBethe L κ N where
  q j := -B.q (Fin.rev j)
  n j := -B.n (Fin.rev j)
  q_strict := fun _ _ h => neg_lt_neg (B.q_strict (Fin.rev_lt_rev.2 h))
  n_mono := fun _ _ h => neg_le_neg (B.n_mono (Fin.rev_le_rev.2 h))
  bethe := by
    intro j
    have hb := B.bethe (Fin.rev j)
    set c : ℝ := κ / N
    have hsum : ∑ l ∈ univ.erase j, Real.arctan (c / (-B.q (Fin.rev j) - -B.q (Fin.rev l))) =
        -∑ l ∈ univ.erase (Fin.rev j), Real.arctan (c / (B.q (Fin.rev j) - B.q l)) := by
      have hg : ∀ l, Real.arctan (c / (-B.q (Fin.rev j) - -B.q (Fin.rev l))) =
          -Real.arctan (c / (B.q (Fin.rev j) - B.q (Fin.rev l))) := fun l => by
        rw [← Real.arctan_neg, show -B.q (Fin.rev j) - -B.q (Fin.rev l) =
          -(B.q (Fin.rev j) - B.q (Fin.rev l)) by ring, div_neg]
      simp only [hg, Finset.sum_neg_distrib, neg_inj]
      rw [Finset.sum_erase_eq_sub (mem_univ j), Finset.sum_erase_eq_sub (mem_univ (Fin.rev j))]
      congr 1
      exact Equiv.sum_comp Fin.revPerm (fun l => Real.arctan (c / (B.q (Fin.rev j) - B.q l)))
    rw [hsum]
    push_cast
    linarith

lemma reflect_q (B : OnShellBethe L κ N) (j : Fin N) : (reflect B).q j = -B.q (Fin.rev j) := rfl
lemma reflect_n (B : OnShellBethe L κ N) (j : Fin N) : (reflect B).n j = -B.n (Fin.rev j) := rfl

lemma clusterL_reflect (B : OnShellBethe L κ N) (a : ℤ) (x δ : ℝ) (j : Fin N) :
    j ∈ clusterL (reflect B) (-a - 1) (-x) δ ↔ Fin.rev j ∈ clusterR B a x δ := by
  rw [clusterL, clusterR, Finset.mem_filter, Finset.mem_filter, reflect_q, reflect_n]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, by linarith⟩

/-- **The reflected cluster argument** (second implication of eq:B3-exact-cutoff). -/
theorem core_right (hL : 0 < L) (hκ : 0 < κ) (hN : 0 < N) (B : OnShellBethe L κ N) (a : ℤ)
    {x δ : ℝ} (hδ : 0 < δ) (g : ℝ → ℝ)
    (hg : ∀ t, δ ≤ |x + 2 * δ - t| → g t = 1 / (x + 2 * δ - t))
    (hF : L * (x + 2 * δ) -
        2 * κ * ((1 / (N : ℝ)) * ∑ l ∈ univ.filter (· ∉ clusterR B a x δ), g (B.q l)) +
        2 * κ ^ 3 / ((N : ℝ) ^ 2 * δ ^ 3) < 2 * Real.pi * (a + 1))
    (hk : 3 * Real.sqrt (κ / N * (clusterR B a x δ).card / L) < δ) :
    ∀ j, a + 1 ≤ B.n j → x + δ < B.q j := by
  set J' := clusterL (reflect B) (-a - 1) (-x) δ
  have hcard : J'.card = (clusterR B a x δ).card := by
    refine Finset.card_bij (fun j _ => Fin.rev j) (fun j hj => (clusterL_reflect B a x δ j).1 hj)
      (fun j _ j' _ h => Fin.rev_injective h) (fun i hi => ⟨Fin.rev i, ?_, Fin.rev_rev i⟩)
    rw [clusterL_reflect, Fin.rev_rev]; exact hi
  have hsum : ∑ l ∈ univ.filter (· ∉ J'), (fun t => -g (-t)) ((reflect B).q l) =
      -∑ l ∈ univ.filter (· ∉ clusterR B a x δ), g (B.q l) := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_neg_distrib]
    rw [← Equiv.sum_comp Fin.revPerm (fun l => -(if l ∉ clusterR B a x δ then g (B.q l) else 0))]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Fin.revPerm_apply, reflect_q, neg_neg]
    by_cases hl : Fin.rev l ∈ clusterR B a x δ
    · have : l ∈ J' := (clusterL_reflect B a x δ l).2 hl
      simp [this, hl]
    · have : l ∉ J' := fun h' => hl ((clusterL_reflect B a x δ l).1 h')
      simp [this, hl]
  have hmain := core_left hL hκ hN (reflect B) (-a - 1) (x := -x) hδ (fun t => -g (-t))
    (fun t ht => by
      have ht' : δ ≤ |x + 2 * δ - -t| := by
        rw [show x + 2 * δ - -t = -(-x - 2 * δ - t) by ring, abs_neg]; exact ht
      show -g (-t) = 1 / (-x - 2 * δ - t)
      rw [hg _ ht', show x + 2 * δ - -t = -(-x - 2 * δ - t) by ring, one_div_neg_eq_neg_one_div,
        neg_neg])
    (by
      rw [hsum]
      push_cast
      linarith)
    (by rw [hcard]; exact hk)
  intro j hj
  have := hmain (Fin.rev j) (by rw [reflect_n, Fin.rev_rev]; omega)
  rw [reflect_q, Fin.rev_rev] at this
  linarith

end QuantumNLS.LabelSeparationCore

#print axioms QuantumNLS.LabelSeparationCore.extForce_cluster
#print axioms QuantumNLS.LabelSeparationCore.extForce_lower
#print axioms QuantumNLS.LabelSeparationCore.core_left
#print axioms QuantumNLS.LabelSeparationCore.reflect
#print axioms QuantumNLS.LabelSeparationCore.core_right
