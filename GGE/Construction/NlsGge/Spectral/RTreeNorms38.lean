import NlsGge.Spectral.RTreeCore38
import NlsGge.Spectral.R3cResolventL2_38
import NlsGge.Spectral.RTreeLeafBounds38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core

/-! # RTree piece T3: sup and `L²` bounds for tree evaluations and pairing integrals

Structural induction over `RTree38` (design `R3C_GENERAL_K_DESIGN.md`, sections (b), (d), Step 5).
With `b_k(T) = T.leafBound k N z` (product over the leaves of `leafFactor38`):
* `RTree38.sup_le`: no leaf of order `k` gives `‖eval T‖_∞ ≤ (2η)^{-nodes} b_k(T)`;
* `RTree38.l2_le`: at most one leaf of order `k` gives `‖eval T‖₂ ≤ (2η)^{-nodes} b_k(T)`;
* `RTree38.norm_pair_le`: the root pairing `∫ ∂^{d₀}U · eval T`;
* the connection with T4: `leafFactor38 ≤ leafOrderBound38` (`d ≤ k`), the list `leafOrders` of leaf
  orders (length `nodes`), `leafBound ≤ ∏ leafOrderBound38 over leafOrders`, and the final
  uniform-constant bounds `sup_le_uniform`, `l2_le_uniform`, `norm_pair_le_uniform`,
  `RTerm38.norm_val_le_uniform` with a constant depending only on `(k, B)` and the tree size. -/

/-! ## Node actions: sup and `L²` contraction by `(2η)⁻¹` -/

theorem RKind38.act_sup_le {η : ℝ} (hη : 0 < η) (κ : RKind38) {g : ℝ → ℂ} (hg : Continuous g)
    {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (x : ℝ) :
    ‖κ.act η g x‖ ≤ (2 * η)⁻¹ * M := by
  cases κ with
  | R =>
    rw [inv_mul_eq_div]
    exact resolv38_bound hη hg hM x
  | S =>
    have h2 : ‖(2 * (η : ℂ))‖ = 2 * η := by
      simp [abs_of_pos hη]
    show ‖g x / (2 * (η : ℂ))‖ ≤ _
    rw [norm_div, h2, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (hM x) (by positivity)

theorem l2sq38_div_const (g : ℝ → ℂ) {η : ℝ} (hη : 0 < η) :
    l2sq38 (fun x => g x / (2 * (η : ℂ))) = l2sq38 g / (2 * η) ^ 2 := by
  have h2 : ‖(2 * (η : ℂ))‖ = 2 * η := by
    simp [abs_of_pos hη]
  unfold l2sq38
  simp only [norm_div, h2, div_pow]
  rw [intervalIntegral.integral_div]

theorem RKind38.act_l2_le {η : ℝ} (hη : 0 < η) (κ : RKind38) {g : ℝ → ℂ} (hg : Continuous g)
    (hp : Function.Periodic g 1) :
    Real.sqrt (l2sq38 (κ.act η g)) ≤ (2 * η)⁻¹ * Real.sqrt (l2sq38 g) := by
  cases κ with
  | R =>
    have h := resolv38_l2sq_le hη hg hp
    have h' := Real.sqrt_le_sqrt h
    rw [Real.sqrt_div (l2sq38_nonneg g), Real.sqrt_sq (by positivity)] at h'
    show Real.sqrt (l2sq38 (resolv38 η g)) ≤ _
    rw [inv_mul_eq_div]
    exact h'
  | S =>
    show Real.sqrt (l2sq38 (fun x => g x / (2 * (η : ℂ)))) ≤ _
    rw [l2sq38_div_const g hη, Real.sqrt_div (l2sq38_nonneg g), Real.sqrt_sq (by positivity),
      inv_mul_eq_div]

/-! ## Small helper lemmas -/

theorem norm_mul3_le {a b c : ℂ} {p q r : ℝ} (ha : ‖a‖ ≤ p) (hb : ‖b‖ ≤ q) (hc : ‖c‖ ≤ r) :
    ‖a * b * c‖ ≤ p * q * r := by
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha)) hc
    (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans ha) ((norm_nonneg _).trans hb))

theorem l2_mul_le38 {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) {M : ℝ}
    (hM : ∀ x, ‖f x‖ ≤ M) :
    Real.sqrt (l2sq38 (fun x => f x * g x)) ≤ M * Real.sqrt (l2sq38 g) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  calc Real.sqrt (l2sq38 (fun x => f x * g x)) ≤ Real.sqrt (M ^ 2 * l2sq38 g) :=
        Real.sqrt_le_sqrt (l2sq38_mul_le hf hg hM)
    _ = M * Real.sqrt (l2sq38 g) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hM0]

theorem l2_of_sup38 {f : ℝ → ℂ} (hf : Continuous f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) :
    Real.sqrt (l2sq38 f) ≤ M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  calc Real.sqrt (l2sq38 f) ≤ Real.sqrt (M ^ 2) := Real.sqrt_le_sqrt (l2sq38_le_sup hf hM)
    _ = M := Real.sqrt_sq hM0

theorem RTree38.leafBound_pow_nonneg {η : ℝ} (hη : 0 < η) (k N : ℕ) (z : FourierPlane N)
    (T : RTree38) : 0 ≤ (2 * η)⁻¹ ^ T.nodes * T.leafBound k N z :=
  mul_nonneg (by positivity) (RTree38.leafBound_nonneg k N z T)

/-! ## The sup bound -/

theorem RTree38.sup_le (k : ℕ) {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N) (T : RTree38)
    (hk : T.maxd ≤ k) (h0 : T.cntEq k = 0) (x : ℝ) :
    ‖T.eval η N z x‖ ≤ (2*η)⁻¹ ^ T.nodes * T.leafBound k N z := by
  induction T generalizing x with
  | base κ d =>
    have hdk : d ≠ k := by
      intro h
      simp [RTree38.cntEq, h] at h0
    have hc := perC1_leafUbar38 N z d
    have := RKind38.act_sup_le hη κ hc.cont (M := leafSup38 N z d)
      (fun y => by
        have := norm_leafU38_le_leafSup38 N z d y
        simpa [leafUbar38] using this) x
    simpa [RTree38.eval, RTree38.nodes, RTree38.leafBound, leafFactor38, hdk] using this
  | node κ d A B ihA ihB =>
    have hkA : A.maxd ≤ k := by simp only [RTree38.maxd] at hk; omega
    have hkB : B.maxd ≤ k := by simp only [RTree38.maxd] at hk; omega
    have hdk : d ≠ k := by
      intro h
      simp [RTree38.cntEq, h] at h0
    have hA0 : A.cntEq k = 0 := by simp only [RTree38.cntEq] at h0; omega
    have hB0 : B.cntEq k = 0 := by simp only [RTree38.cntEq] at h0; omega
    have hU := perC1_leafU38 N z d
    have hAc := RTree38.eval_cont_per hη N z A
    have hBc := RTree38.eval_cont_per hη N z B
    have hg : Continuous (fun y => leafU38 N z d y * A.eval η N z y * B.eval η N z y) :=
      (hU.cont.mul hAc.1).mul hBc.1
    have hb : ∀ y, ‖leafU38 N z d y * A.eval η N z y * B.eval η N z y‖ ≤
        leafSup38 N z d * ((2 * η)⁻¹ ^ A.nodes * A.leafBound k N z) *
          ((2 * η)⁻¹ ^ B.nodes * B.leafBound k N z) := fun y =>
      norm_mul3_le (norm_leafU38_le_leafSup38 N z d y) (ihA hkA hA0 y) (ihB hkB hB0 y)
    have := RKind38.act_sup_le hη κ hg hb x
    simp only [RTree38.eval, RTree38.nodes, RTree38.leafBound, leafFactor38, hdk, ite_false]
    calc _ ≤ _ := this
      _ = _ := by rw [pow_add, pow_add, pow_one]; ring

/-! ## The `L²` bound -/

theorem RTree38.l2_le (k : ℕ) {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N) (T : RTree38)
    (hk : T.maxd ≤ k) (h1 : T.cntEq k ≤ 1) :
    Real.sqrt (l2sq38 (T.eval η N z)) ≤ (2*η)⁻¹ ^ T.nodes * T.leafBound k N z := by
  induction T with
  | base κ d =>
    by_cases hdk : d = k
    · subst hdk
      have hc := perC1_leafUbar38 N z d
      have h := RKind38.act_l2_le hη κ hc.cont hc.per
      have e : l2sq38 (leafUbar38 N z d) = l2sq38 (leafU38 N z d) := by
        simp [leafUbar38, l2sq38]
      rw [e] at h
      simpa [RTree38.eval, RTree38.nodes, RTree38.leafBound, leafFactor38, leafL2_38] using h
    · have h0 : (RTree38.base κ d).cntEq k = 0 := by simp [RTree38.cntEq, hdk]
      exact l2_of_sup38 (RTree38.eval_cont_per hη N z _).1
        (fun x => RTree38.sup_le k hη N z _ hk h0 x)
  | node κ d A B ihA ihB =>
    by_cases h0 : (RTree38.node κ d A B).cntEq k = 0
    · exact l2_of_sup38 (RTree38.eval_cont_per hη N z _).1
        (fun x => RTree38.sup_le k hη N z _ hk h0 x)
    have hkA : A.maxd ≤ k := by simp only [RTree38.maxd] at hk; omega
    have hkB : B.maxd ≤ k := by simp only [RTree38.maxd] at hk; omega
    have hU := perC1_leafU38 N z d
    have hAc := RTree38.eval_cont_per hη N z A
    have hBc := RTree38.eval_cont_per hη N z B
    have hg : Continuous (fun y => leafU38 N z d y * A.eval η N z y * B.eval η N z y) :=
      (hU.cont.mul hAc.1).mul hBc.1
    have hgp : Function.Periodic
        (fun y => leafU38 N z d y * A.eval η N z y * B.eval η N z y) 1 :=
      fun y => by simp only [hU.per y, hAc.2 y, hBc.2 y]
    have hact := RKind38.act_l2_le hη κ hg hgp
    simp only [RTree38.eval, RTree38.nodes, RTree38.leafBound]
    have hcnt : (if d = k then 1 else 0) + A.cntEq k + B.cntEq k ≤ 1 := by
      simpa only [RTree38.cntEq] using h1
    by_cases hdk : d = k
    · -- the leaf of the node itself carries the `L²` norm
      subst hdk
      have hA0 : A.cntEq d = 0 := by simp at hcnt; omega
      have hB0 : B.cntEq d = 0 := by simp at hcnt; omega
      have hAs : ∀ y, ‖A.eval η N z y * B.eval η N z y‖ ≤
          ((2 * η)⁻¹ ^ A.nodes * A.leafBound d N z) *
            ((2 * η)⁻¹ ^ B.nodes * B.leafBound d N z) := fun y => by
        rw [norm_mul]
        exact mul_le_mul (RTree38.sup_le d hη N z A hkA hA0 y)
          (RTree38.sup_le d hη N z B hkB hB0 y) (norm_nonneg _)
          (RTree38.leafBound_pow_nonneg hη d N z A)
      have e : (fun y => leafU38 N z d y * A.eval η N z y * B.eval η N z y) =
          fun y => (A.eval η N z y * B.eval η N z y) * leafU38 N z d y := by
        funext y; ring
      have hm := l2_mul_le38 (hAc.1.mul hBc.1) hU.cont hAs
      have hm' : Real.sqrt (l2sq38 (fun y => leafU38 N z d y * A.eval η N z y * B.eval η N z y))
          ≤ ((2 * η)⁻¹ ^ A.nodes * A.leafBound d N z) *
            ((2 * η)⁻¹ ^ B.nodes * B.leafBound d N z) * Real.sqrt (l2sq38 (leafU38 N z d)) := by
        rw [e]; exact hm
      have hfac : leafFactor38 d N z d = leafL2_38 N z d := by simp [leafFactor38]
      rw [hfac]
      refine hact.trans ((mul_le_mul_of_nonneg_left hm' (by positivity)).trans (le_of_eq ?_))
      show _ = _
      simp only [leafL2_38]
      rw [pow_add, pow_add, pow_one]; ring
    · have hfac : leafFactor38 k N z d = leafSup38 N z d := by simp [leafFactor38, hdk]
      simp only [hdk, ite_false, zero_add] at hcnt
      rw [hfac]
      by_cases hA1 : A.cntEq k = 0
      · -- the order-`k` leaf lies in `B`
        have hB1 : B.cntEq k ≤ 1 := by omega
        have hBl := ihB hkB hB1
        have hAs : ∀ y, ‖leafU38 N z d y * A.eval η N z y‖ ≤
            leafSup38 N z d * ((2 * η)⁻¹ ^ A.nodes * A.leafBound k N z) := fun y => by
          rw [norm_mul]
          exact mul_le_mul (norm_leafU38_le_leafSup38 N z d y)
            (RTree38.sup_le k hη N z A hkA hA1 y) (norm_nonneg _) (leafSup38_nonneg N z d)
        have e : (fun y => leafU38 N z d y * A.eval η N z y * B.eval η N z y) =
            fun y => (leafU38 N z d y * A.eval η N z y) * B.eval η N z y := rfl
        have hm := l2_mul_le38 (hU.cont.mul hAc.1) hBc.1 hAs
        have hm' : Real.sqrt (l2sq38 (fun y => leafU38 N z d y * A.eval η N z y * B.eval η N z y))
            ≤ (leafSup38 N z d * ((2 * η)⁻¹ ^ A.nodes * A.leafBound k N z)) *
              ((2 * η)⁻¹ ^ B.nodes * B.leafBound k N z) := by
          have hm0 : Real.sqrt (l2sq38 (fun y => leafU38 N z d y * A.eval η N z y * B.eval η N z y))
              ≤ (leafSup38 N z d * ((2 * η)⁻¹ ^ A.nodes * A.leafBound k N z)) *
                Real.sqrt (l2sq38 (B.eval η N z)) := hm
          refine hm0.trans ?_
          exact mul_le_mul_of_nonneg_left hBl
            (mul_nonneg (leafSup38_nonneg N z d) (RTree38.leafBound_pow_nonneg hη k N z A))
        refine hact.trans ((mul_le_mul_of_nonneg_left hm' (by positivity)).trans (le_of_eq ?_))
        rw [pow_add, pow_add, pow_one]; ring
      · -- the order-`k` leaf lies in `A`
        have hB0 : B.cntEq k = 0 := by omega
        have hA1' : A.cntEq k ≤ 1 := by omega
        have hAl := ihA hkA hA1'
        have hBs : ∀ y, ‖leafU38 N z d y * B.eval η N z y‖ ≤
            leafSup38 N z d * ((2 * η)⁻¹ ^ B.nodes * B.leafBound k N z) := fun y => by
          rw [norm_mul]
          exact mul_le_mul (norm_leafU38_le_leafSup38 N z d y)
            (RTree38.sup_le k hη N z B hkB hB0 y) (norm_nonneg _) (leafSup38_nonneg N z d)
        have e : (fun y => leafU38 N z d y * A.eval η N z y * B.eval η N z y) =
            fun y => (leafU38 N z d y * B.eval η N z y) * A.eval η N z y := by
          funext y; ring
        have hm := l2_mul_le38 (hU.cont.mul hBc.1) hAc.1 hBs
        have hm' : Real.sqrt (l2sq38 (fun y => leafU38 N z d y * A.eval η N z y * B.eval η N z y))
            ≤ (leafSup38 N z d * ((2 * η)⁻¹ ^ B.nodes * B.leafBound k N z)) *
              ((2 * η)⁻¹ ^ A.nodes * A.leafBound k N z) := by
          have hm0 : Real.sqrt (l2sq38 (fun y => leafU38 N z d y * A.eval η N z y * B.eval η N z y))
              ≤ (leafSup38 N z d * ((2 * η)⁻¹ ^ B.nodes * B.leafBound k N z)) *
                Real.sqrt (l2sq38 (A.eval η N z)) := by
            rw [e]; exact hm
          exact hm0.trans (mul_le_mul_of_nonneg_left hAl
            (mul_nonneg (leafSup38_nonneg N z d) (RTree38.leafBound_pow_nonneg hη k N z B)))
        refine hact.trans ((mul_le_mul_of_nonneg_left hm' (by positivity)).trans (le_of_eq ?_))
        rw [pow_add, pow_add, pow_one]; ring

/-! ## The root pairing -/

/-- Root pairing `∫₀¹ ∂^{d₀}U · eval T`. The leaf order `d₀` and the tree together contain at most one
leaf of order `k`: that leaf takes the `L²` norm, all other leaves the sup norm. -/
theorem RTree38.norm_pair_le (k : ℕ) {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N)
    (d0 : ℕ) (T : RTree38) (hk : T.maxd ≤ k)
    (h1 : T.cntEq k + (if d0 = k then 1 else 0) ≤ 1) :
    ‖pair38 (leafU38 N z d0) (T.eval η N z)‖ ≤
      (2 * η)⁻¹ ^ T.nodes * (leafFactor38 k N z d0 * T.leafBound k N z) := by
  have hU := perC1_leafU38 N z d0
  have hTc := RTree38.eval_cont_per hη N z T
  have hT1 : T.cntEq k ≤ 1 := by omega
  have hTl := RTree38.l2_le k hη N z T hk hT1
  by_cases hd : d0 = k
  · subst hd
    have hfac : leafFactor38 d0 N z d0 = leafL2_38 N z d0 := by simp [leafFactor38]
    rw [hfac]
    refine (norm_pair38_le_l2 hU.cont hTc.1).trans ?_
    have hL : Real.sqrt (l2sq38 (leafU38 N z d0)) = leafL2_38 N z d0 := rfl
    rw [hL]
    calc leafL2_38 N z d0 * Real.sqrt (l2sq38 (T.eval η N z))
        ≤ leafL2_38 N z d0 * ((2 * η)⁻¹ ^ T.nodes * T.leafBound d0 N z) :=
          mul_le_mul_of_nonneg_left hTl (Real.sqrt_nonneg _)
      _ = _ := by ring
  · have hfac : leafFactor38 k N z d0 = leafSup38 N z d0 := by simp [leafFactor38, hd]
    rw [hfac]
    refine (norm_pair38_le_sup hU.cont hTc.1 (norm_leafU38_le_leafSup38 N z d0)).trans ?_
    calc leafSup38 N z d0 * Real.sqrt (l2sq38 (T.eval η N z))
        ≤ leafSup38 N z d0 * ((2 * η)⁻¹ ^ T.nodes * T.leafBound k N z) :=
          mul_le_mul_of_nonneg_left hTl (leafSup38_nonneg N z d0)
      _ = _ := by ring

/-! ## Connection with T4: leaf orders and the uniform constant -/

/-- the list of leaf orders of a tree (one leaf per node) -/
def RTree38.leafOrders : RTree38 → List ℕ
  | base _ d => [d]
  | node _ d A B => d :: (leafOrders A ++ leafOrders B)

theorem RTree38.length_leafOrders : ∀ T : RTree38, T.leafOrders.length = T.nodes
  | .base _ _ => rfl
  | .node _ _ A B => by
    simp only [RTree38.leafOrders, RTree38.nodes, List.length_cons, List.length_append,
      RTree38.length_leafOrders A, RTree38.length_leafOrders B]
    omega

theorem RTree38.le_of_mem_leafOrders (k : ℕ) :
    ∀ T : RTree38, T.maxd ≤ k → ∀ d ∈ T.leafOrders, d ≤ k
  | .base _ d, hk, e, he => by
    simp only [RTree38.leafOrders, List.mem_singleton] at he
    simp only [RTree38.maxd] at hk
    omega
  | .node _ d A B, hk, e, he => by
    have hkA : A.maxd ≤ k := by simp only [RTree38.maxd] at hk; omega
    have hkB : B.maxd ≤ k := by simp only [RTree38.maxd] at hk; omega
    simp only [RTree38.leafOrders, List.mem_cons, List.mem_append] at he
    rcases he with rfl | he | he
    · simp only [RTree38.maxd] at hk; omega
    · exact RTree38.le_of_mem_leafOrders k A hkA e he
    · exact RTree38.le_of_mem_leafOrders k B hkB e he

/-- T1's leaf factor is bounded by T4's per-leaf bound for orders `d ≤ k`. -/
theorem leafFactor38_le_leafOrderBound38 (k N : ℕ) (z : FourierPlane N) {d : ℕ} (hd : d ≤ k) :
    leafFactor38 k N z d ≤ leafOrderBound38 k N z d := by
  unfold leafFactor38
  split_ifs with h
  · subst h
    exact leaf_l2_le38 _ N z
  · unfold leafSup38
    exact ciSup_le (fun x => leaf_sup_le38 k N z (lt_of_le_of_ne hd h) x)

/-- T1's `leafBound` is bounded by the product of T4's `leafOrderBound38` over the leaf orders. -/
theorem RTree38.leafBound_le_prod (k N : ℕ) (z : FourierPlane N) :
    ∀ T : RTree38, T.maxd ≤ k →
      T.leafBound k N z ≤ (T.leafOrders.map (leafOrderBound38 k N z)).prod
  | .base _ d, hk => by
    simp only [RTree38.maxd] at hk
    simpa [RTree38.leafBound, RTree38.leafOrders] using leafFactor38_le_leafOrderBound38 k N z hk
  | .node _ d A B, hk => by
    have hkA : A.maxd ≤ k := by simp only [RTree38.maxd] at hk; omega
    have hkB : B.maxd ≤ k := by simp only [RTree38.maxd] at hk; omega
    have hd : d ≤ k := by simp only [RTree38.maxd] at hk; omega
    have h1 := leafFactor38_le_leafOrderBound38 k N z hd
    have h2 := RTree38.leafBound_le_prod k N z A hkA
    have h3 := RTree38.leafBound_le_prod k N z B hkB
    have hp : ∀ T : RTree38, 0 ≤ (T.leafOrders.map (leafOrderBound38 k N z)).prod := fun T =>
      List.prod_nonneg (by
        intro a ha
        obtain ⟨e, _, rfl⟩ := List.mem_map.1 ha
        exact leafOrderBound38_nonneg k N z e)
    simp only [RTree38.leafBound, RTree38.leafOrders, List.map_cons, List.prod_cons,
      List.map_append, List.prod_append]
    rw [← mul_assoc]
    exact mul_le_mul (mul_le_mul h1 h2 (RTree38.leafBound_nonneg k N z A)
      (leafOrderBound38_nonneg k N z d)) h3 (RTree38.leafBound_nonneg k N z B)
      (mul_nonneg (leafOrderBound38_nonneg k N z d) (hp A))

/-- Uniform bound `b_k(T) ≤ C(k,B)^{nodes}`, independent of `N`, `z`, and `η`. -/
theorem RTree38.leafBound_le_const (k : ℕ) (hk : 1 ≤ k) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (z : FourierPlane N),
      ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ k * ‖z i‖ ^ 2 ≤ B ^ 2 →
      ∀ T : RTree38, T.maxd ≤ k → T.leafBound k N z ≤ C ^ T.nodes := by
  obtain ⟨C, hC, h⟩ := leafBound_le k hk B
  refine ⟨C, hC, fun N z hS T hT => ?_⟩
  refine (RTree38.leafBound_le_prod k N z T hT).trans ?_
  have := h N z hS T.leafOrders (RTree38.le_of_mem_leafOrders k T hT)
  rwa [RTree38.length_leafOrders] at this

/-! ## Final bounds with a constant depending only on `(k, B)` and the tree size -/

/-- Sup bound of a tree evaluation, uniform in `N`, `z`, `η > 0`: constant `C(k,B)` per node. -/
theorem RTree38.sup_le_uniform (k : ℕ) (hk : 1 ≤ k) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (z : FourierPlane N),
      ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ k * ‖z i‖ ^ 2 ≤ B ^ 2 →
      ∀ {η : ℝ}, 0 < η → ∀ T : RTree38, T.maxd ≤ k → T.cntEq k = 0 → ∀ x : ℝ,
        ‖T.eval η N z x‖ ≤ (C / (2 * η)) ^ T.nodes := by
  obtain ⟨C, hC, h⟩ := RTree38.leafBound_le_const k hk B
  refine ⟨C, hC, fun N z hS η hη T hT h0 x => ?_⟩
  refine (RTree38.sup_le k hη N z T hT h0 x).trans ?_
  rw [div_eq_inv_mul, mul_pow]
  exact mul_le_mul_of_nonneg_left (h N z hS T hT) (by positivity)

/-- `L²` bound of a tree evaluation with at most one order-`k` leaf, uniform in `N`, `z`, `η > 0`. -/
theorem RTree38.l2_le_uniform (k : ℕ) (hk : 1 ≤ k) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (z : FourierPlane N),
      ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ k * ‖z i‖ ^ 2 ≤ B ^ 2 →
      ∀ {η : ℝ}, 0 < η → ∀ T : RTree38, T.maxd ≤ k → T.cntEq k ≤ 1 →
        Real.sqrt (l2sq38 (T.eval η N z)) ≤ (C / (2 * η)) ^ T.nodes := by
  obtain ⟨C, hC, h⟩ := RTree38.leafBound_le_const k hk B
  refine ⟨C, hC, fun N z hS η hη T hT h1 => ?_⟩
  refine (RTree38.l2_le k hη N z T hT h1).trans ?_
  rw [div_eq_inv_mul, mul_pow]
  exact mul_le_mul_of_nonneg_left (h N z hS T hT) (by positivity)

/-- Root pairing bound, uniform: `‖∫ ∂^{d₀}U · eval T‖ ≤ C^{nodes+1} (2η)^{-nodes}`. -/
theorem RTree38.norm_pair_le_uniform (k : ℕ) (hk : 1 ≤ k) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (z : FourierPlane N),
      ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ k * ‖z i‖ ^ 2 ≤ B ^ 2 →
      ∀ {η : ℝ}, 0 < η → ∀ (d0 : ℕ) (T : RTree38), d0 ≤ k → T.maxd ≤ k →
        T.cntEq k + (if d0 = k then 1 else 0) ≤ 1 →
        ‖pair38 (leafU38 N z d0) (T.eval η N z)‖ ≤ C ^ (T.nodes + 1) * (2 * η)⁻¹ ^ T.nodes := by
  obtain ⟨C, hC, h⟩ := leafBound_le k hk B
  refine ⟨C, hC, fun N z hS η hη d0 T hd0 hT h1 => ?_⟩
  refine (RTree38.norm_pair_le k hη N z d0 T hT h1).trans ?_
  have hl := h N z hS (d0 :: T.leafOrders) (by
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact hd0
    · exact RTree38.le_of_mem_leafOrders k T hT e he)
  rw [List.length_cons, RTree38.length_leafOrders] at hl
  have hprod : leafFactor38 k N z d0 * T.leafBound k N z ≤
      ((d0 :: T.leafOrders).map (leafOrderBound38 k N z)).prod := by
    rw [List.map_cons, List.prod_cons]
    exact mul_le_mul (leafFactor38_le_leafOrderBound38 k N z hd0)
      (RTree38.leafBound_le_prod k N z T hT) (RTree38.leafBound_nonneg k N z T)
      (leafOrderBound38_nonneg k N z d0)
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (hprod.trans hl) (by positivity)

/-- Bound of a term `c (2η)^{-e} ∫ ∂^{d₀}U · eval T` by `‖c‖ C^{nodes+1} (2η)^{-weight}`, uniform in
`N`, `z` (with `S_k ≤ B²`) and `η > 0`; the constant depends only on `(k, B)` and the tree size. -/
theorem RTerm38.norm_val_le_uniform (k : ℕ) (hk : 1 ≤ k) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (z : FourierPlane N),
      ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ k * ‖z i‖ ^ 2 ≤ B ^ 2 →
      ∀ {η : ℝ}, 0 < η → ∀ t : RTerm38, t.d0 ≤ k → t.T.maxd ≤ k →
        t.T.cntEq k + (if t.d0 = k then 1 else 0) ≤ 1 →
        ‖t.val η N z‖ ≤ ‖t.c‖ * C ^ (t.T.nodes + 1) * (2 * η)⁻¹ ^ t.weight := by
  obtain ⟨C, hC, h⟩ := RTree38.norm_pair_le_uniform k hk B
  refine ⟨C, hC, fun N z hS η hη t hd0 hT h1 => ?_⟩
  have hp := h N z hS hη t.d0 t.T hd0 hT h1
  have h2 : ‖((2 * η : ℂ))‖ = 2 * η := by simp [abs_of_pos hη]
  unfold RTerm38.val RTerm38.weight
  rw [norm_mul, norm_mul, norm_pow, norm_inv, h2, pow_add]
  calc ‖t.c‖ * (2 * η)⁻¹ ^ t.e * ‖pair38 (leafU38 N z t.d0) (t.T.eval η N z)‖
      ≤ ‖t.c‖ * (2 * η)⁻¹ ^ t.e * (C ^ (t.T.nodes + 1) * (2 * η)⁻¹ ^ t.T.nodes) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

end NlsGge.SpectralFoundations
end
