import NlsGge.Spectral.RTreeBalance38
import NlsGge.Spectral.RTreeNorms38
import NlsGge.Spectral.RTreeExpandStep38
import NlsGge.Spectral.RTreeIBP38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core

/-! # RTree piece T6 (part a): infrastructure for the expansion theorem

* `RTree38.expand_step_uniform`: the one-step expansion of T5 with witnesses `T₁`, `Ts` that do
  not depend on `η`, `N`, `z` (T5 states `∃ T₁ Ts` after `η N z`; the induction needs witnesses
  that are uniform, so that finitely many fixed terms can be summed with uniform constants).
* `RTerm38.val_expand`: splitting of a term value along an expansion step.
* `ExpOK38`: the property "expansion with coefficients `c w` vanishing below `m` and remainder
  `≤ C η^{-(2k+2)}`, with `(η₀, C)` chosen before `N z`", closed under finite sums.
* the two terminal cases: all-`S` terms and weight-`(2k+2)` remainder terms. -/

/-! ## Uniform one-step expansion -/

theorem RTree38.expand_step_uniform (T : RTree38) (hR : 0 < T.numR) :
    ∃ (T₁ : RTree38) (Ts : List RTree38),
      T₁.numR + 1 = T.numR ∧ T₁.nodes = T.nodes ∧ T₁.dsum = T.dsum ∧
      (∀ T' ∈ Ts, T'.numR = T.numR ∧ T'.nodes = T.nodes ∧ T'.dsum = T.dsum + 1) ∧
      ∀ {η : ℝ}, 0 < η → ∀ (N : ℕ) (z : FourierPlane N) (x : ℝ),
        T.eval η N z x =
          T₁.eval η N z x - (2 * (η : ℂ))⁻¹ * (Ts.map (fun T' => T'.eval η N z x)).sum := by
  induction T with
  | base κ d =>
    cases κ with
    | S => simp [RTree38.numR] at hR
    | R =>
      refine ⟨.base .S d, (RTree38.base .R d).bumps, by simp [RTree38.numR],
        by simp [RTree38.nodes], by simp [RTree38.dsum], ?_,
        fun {η} hη N z x => RTree38.eval_root_R_expand hη N z d x⟩
      intro T' hT'
      exact ⟨RTree38.numR_of_mem_bumps _ T' hT', RTree38.nodes_of_mem_bumps _ T' hT',
        RTree38.dsum_of_mem_bumps _ T' hT'⟩
  | node κ d A B ihA ihB =>
    cases κ with
    | R =>
      refine ⟨.node .S d A B, (RTree38.node .R d A B).bumps, ?_, by simp [RTree38.nodes],
        by simp [RTree38.dsum], ?_, fun {η} hη N z x => RTree38.eval_node_root_R_expand hη N z d A B x⟩
      · simp [RTree38.numR]; omega
      · intro T' hT'
        exact ⟨RTree38.numR_of_mem_bumps _ T' hT', RTree38.nodes_of_mem_bumps _ T' hT',
          RTree38.dsum_of_mem_bumps _ T' hT'⟩
    | S =>
      rw [RTree38.numR_node_S] at hR
      by_cases hA : 0 < A.numR
      · obtain ⟨A₁, As, h1, h2, h3, h4, h6⟩ := ihA hA
        refine ⟨.node .S d A₁ B, As.map (fun A' => .node .S d A' B), ?_, ?_, ?_, ?_,
          fun {η} hη N z x => ?_⟩
        · simp only [RTree38.numR_node_S]; omega
        · simp only [RTree38.nodes]; omega
        · simp only [RTree38.dsum]; omega
        · intro T' hT'
          obtain ⟨A', hA', rfl⟩ := List.mem_map.mp hT'
          obtain ⟨a1, a2, a3⟩ := h4 A' hA'
          refine ⟨?_, ?_, ?_⟩
          · simp only [RTree38.numR_node_S]; omega
          · simp only [RTree38.nodes]; omega
          · simp only [RTree38.dsum]; omega
        · have hx := h6 hη N z x
          have key : ∀ (l : List RTree38) (c b e : ℂ),
              (l.map (fun A' => c * A'.eval η N z x * b / e)).sum =
                c * b / e * (l.map (fun A' => A'.eval η N z x)).sum := by
            intro l c b e
            induction l with
            | nil => simp
            | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring
          simp only [RTree38.eval, RKind38.act, List.map_map, Function.comp_def, key]
          rw [hx]
          ring
      · have hB : 0 < B.numR := by omega
        obtain ⟨B₁, Bs, h1, h2, h3, h4, h6⟩ := ihB hB
        refine ⟨.node .S d A B₁, Bs.map (fun B' => .node .S d A B'), ?_, ?_, ?_, ?_,
          fun {η} hη N z x => ?_⟩
        · simp only [RTree38.numR_node_S]; omega
        · simp only [RTree38.nodes]; omega
        · simp only [RTree38.dsum]; omega
        · intro T' hT'
          obtain ⟨B', hB', rfl⟩ := List.mem_map.mp hT'
          obtain ⟨a1, a2, a3⟩ := h4 B' hB'
          refine ⟨?_, ?_, ?_⟩
          · simp only [RTree38.numR_node_S]; omega
          · simp only [RTree38.nodes]; omega
          · simp only [RTree38.dsum]; omega
        · have hx := h6 hη N z x
          have key : ∀ (l : List RTree38) (c a e : ℂ),
              (l.map (fun B' => c * a * B'.eval η N z x / e)).sum =
                c * a / e * (l.map (fun B' => B'.eval η N z x)).sum := by
            intro l c a e
            induction l with
            | nil => simp
            | cons b l ih => simp only [List.map_cons, List.sum_cons, ih]; ring
          simp only [RTree38.eval, RKind38.act, List.map_map, Function.comp_def, key]
          rw [hx]
          ring

/-! ## Splitting a term along an expansion step -/

theorem RTerm38.val_expand {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N) (t : RTerm38)
    (T₁ : RTree38) (Ts : List RTree38)
    (h : ∀ x, t.T.eval η N z x =
      T₁.eval η N z x - (2 * (η : ℂ))⁻¹ * (Ts.map (fun T' => T'.eval η N z x)).sum) :
    t.val η N z = (⟨t.c, t.e, t.d0, T₁⟩ : RTerm38).val η N z +
      (Ts.map (fun T' => (⟨-t.c, t.e + 1, t.d0, T'⟩ : RTerm38).val η N z)).sum := by
  have hf := (perC1_leafU38 N z t.d0).cont
  have hT1 := (RTree38.eval_cont_per hη N z T₁).1
  have hs := list_sum_continuous38 Ts (fun T' x => T'.eval η N z x)
    (fun T' _ => (RTree38.eval_cont_per hη N z T').1)
  have hp : pair38 (leafU38 N z t.d0) (t.T.eval η N z) =
      pair38 (leafU38 N z t.d0) (T₁.eval η N z) -
        (2 * (η : ℂ))⁻¹ * (Ts.map (fun T' => pair38 (leafU38 N z t.d0) (T'.eval η N z))).sum := by
    rw [← pair38_list_sum_right (leafU38 N z t.d0) hf Ts (fun T' x => T'.eval η N z x)
      (fun T' _ => (RTree38.eval_cont_per hη N z T').1)]
    have e : t.T.eval η N z = fun x => T₁.eval η N z x -
        (2 * (η : ℂ))⁻¹ * (Ts.map (fun T' => T'.eval η N z x)).sum := funext h
    rw [e]
    unfold pair38
    have e2 : (fun x => leafU38 N z t.d0 x * (T₁.eval η N z x -
        (2 * (η : ℂ))⁻¹ * (Ts.map (fun T' => T'.eval η N z x)).sum)) =
        fun x => leafU38 N z t.d0 x * T₁.eval η N z x -
          (2 * (η : ℂ))⁻¹ * (leafU38 N z t.d0 x * (Ts.map (fun T' => T'.eval η N z x)).sum) := by
      funext x; ring
    have i1 : IntervalIntegrable (fun x => leafU38 N z t.d0 x * T₁.eval η N z x) volume 0 1 :=
      (hf.mul hT1).intervalIntegrable 0 1
    have i2 : IntervalIntegrable (fun x => (2 * (η : ℂ))⁻¹ * (leafU38 N z t.d0 x *
        (Ts.map (fun T' => T'.eval η N z x)).sum)) volume 0 1 :=
      (continuous_const.mul (hf.mul hs)).intervalIntegrable 0 1
    rw [e2, intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul]
  simp only [RTerm38.val]
  rw [hp]
  have e3 : ∀ T' : RTree38, -t.c * ((2 * (η : ℂ)))⁻¹ ^ (t.e + 1) *
      pair38 (leafU38 N z t.d0) (T'.eval η N z) =
      (-(t.c * ((2 * (η : ℂ)))⁻¹ ^ t.e * (2 * (η : ℂ))⁻¹)) *
        pair38 (leafU38 N z t.d0) (T'.eval η N z) := by
    intro T'; rw [pow_succ]; ring
  simp only [e3, List.sum_map_mul_left]
  ring

/-! ## The closure property `ExpOK38` -/

/-- Expansion property with `(η₀, C)` chosen before `(N, z)`. -/
def ExpOK38 (k : ℕ) (B : ℝ) (m : ℕ) (F : (N : ℕ) → FourierPlane N → ℝ → ℂ) : Prop :=
  ∃ η₀ C : ℝ, 0 < η₀ ∧ 0 ≤ C ∧ ∀ (N : ℕ) (z : FourierPlane N),
    ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ k * ‖z i‖ ^ 2 ≤ B ^ 2 →
    ∃ c : ℕ → ℂ, (∀ w < m, c w = 0) ∧ ∀ η : ℝ, η₀ ≤ η →
      ‖F N z η - ∑ w ∈ Finset.range (2 * k + 2), c w * (η : ℂ)⁻¹ ^ w‖ ≤ C * η⁻¹ ^ (2 * k + 2)

theorem ExpOK38.zero (k : ℕ) (B : ℝ) (m : ℕ) : ExpOK38 k B m (fun _ _ _ => 0) :=
  ⟨1, 0, one_pos, le_refl _, fun N z _ =>
    ⟨fun _ => 0, fun _ _ => rfl, fun η _ => by simp⟩⟩

theorem ExpOK38.add {k : ℕ} {B : ℝ} {m : ℕ} {F G : (N : ℕ) → FourierPlane N → ℝ → ℂ}
    (hF : ExpOK38 k B m F) (hG : ExpOK38 k B m G) :
    ExpOK38 k B m (fun N z η => F N z η + G N z η) := by
  obtain ⟨η₁, C₁, h1, hC1, hF⟩ := hF
  obtain ⟨η₂, C₂, h2, hC2, hG⟩ := hG
  refine ⟨max η₁ η₂, C₁ + C₂, lt_max_of_lt_left h1, add_nonneg hC1 hC2, fun N z hS => ?_⟩
  obtain ⟨c₁, hc₁, hb₁⟩ := hF N z hS
  obtain ⟨c₂, hc₂, hb₂⟩ := hG N z hS
  refine ⟨fun w => c₁ w + c₂ w, fun w hw => by simp [hc₁ w hw, hc₂ w hw], fun η hη => ?_⟩
  have e : F N z η + G N z η - ∑ w ∈ Finset.range (2 * k + 2), (c₁ w + c₂ w) * (η : ℂ)⁻¹ ^ w =
      (F N z η - ∑ w ∈ Finset.range (2 * k + 2), c₁ w * (η : ℂ)⁻¹ ^ w) +
        (G N z η - ∑ w ∈ Finset.range (2 * k + 2), c₂ w * (η : ℂ)⁻¹ ^ w) := by
    simp only [add_mul, Finset.sum_add_distrib]; ring
  rw [e]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ C₁ * η⁻¹ ^ (2 * k + 2) + C₂ * η⁻¹ ^ (2 * k + 2) :=
        add_le_add (hb₁ η (le_trans (le_max_left _ _) hη)) (hb₂ η (le_trans (le_max_right _ _) hη))
    _ = _ := by ring

theorem ExpOK38.list_sum {k : ℕ} {B : ℝ} {m : ℕ} {ι : Type*} (L : List ι)
    (F : ι → (N : ℕ) → FourierPlane N → ℝ → ℂ) (h : ∀ i ∈ L, ExpOK38 k B m (F i)) :
    ExpOK38 k B m (fun N z η => (L.map (fun i => F i N z η)).sum) := by
  induction L with
  | nil => simpa using ExpOK38.zero k B m
  | cons a L ih =>
    have := ExpOK38.add (h a (by simp)) (ih (fun i hi => h i (by simp [hi])))
    simpa only [List.map_cons, List.sum_cons] using this

theorem ExpOK38.congr {k : ℕ} {B : ℝ} {m : ℕ} {F G : (N : ℕ) → FourierPlane N → ℝ → ℂ}
    (hF : ExpOK38 k B m F) (hFG : ∀ N z η, 0 < η → F N z η = G N z η) :
    ExpOK38 k B m G := by
  obtain ⟨η₀, C, h0, hC, h⟩ := hF
  refine ⟨η₀, C, h0, hC, fun N z hS => ?_⟩
  obtain ⟨c, hc, hb⟩ := h N z hS
  exact ⟨c, hc, fun η hη => by rw [← hFG N z η (lt_of_lt_of_le h0 hη)]; exact hb η hη⟩

theorem ExpOK38.mono {k : ℕ} {B : ℝ} {m m' : ℕ} {F : (N : ℕ) → FourierPlane N → ℝ → ℂ}
    (hm : m ≤ m') (hF : ExpOK38 k B m' F) : ExpOK38 k B m F := by
  obtain ⟨η₀, C, h0, hC, h⟩ := hF
  refine ⟨η₀, C, h0, hC, fun N z hS => ?_⟩
  obtain ⟨c, hc, hb⟩ := h N z hS
  exact ⟨c, fun w hw => hc w (lt_of_lt_of_le hw hm), hb⟩

/-! ## Terminal case (i): all-`S` terms -/

theorem RTree38.eval_of_numR_zero (N : ℕ) (z : FourierPlane N) :
    ∀ T : RTree38, T.numR = 0 →
      ∃ g : ℝ → ℂ, ∀ (η : ℝ) (x : ℝ), T.eval η N z x = (2 * (η : ℂ))⁻¹ ^ T.nodes * g x
  | .base κ d, h => by
    cases κ with
    | R => simp [RTree38.numR] at h
    | S =>
      refine ⟨leafUbar38 N z d, fun η x => ?_⟩
      simp only [RTree38.eval, RKind38.act, RTree38.nodes, pow_one, div_eq_mul_inv]
      ring
  | .node κ d A B, h => by
    cases κ with
    | R => simp [RTree38.numR] at h
    | S =>
      rw [RTree38.numR_node_S] at h
      obtain ⟨gA, hA⟩ := RTree38.eval_of_numR_zero N z A (by omega)
      obtain ⟨gB, hB⟩ := RTree38.eval_of_numR_zero N z B (by omega)
      refine ⟨fun x => leafU38 N z d x * gA x * gB x, fun η x => ?_⟩
      simp only [RTree38.eval, RKind38.act, RTree38.nodes, hA, hB, div_eq_mul_inv, pow_add, pow_one]
      ring

theorem RTerm38.expOK_allS (k : ℕ) (B : ℝ) (t : RTerm38) (h0 : t.T.numR = 0)
    (hw : t.weight ≤ 2 * k + 1) :
    ExpOK38 k B t.weight (fun N z η => t.val η N z) := by
  refine ⟨1, 0, one_pos, le_refl _, fun N z _ => ?_⟩
  obtain ⟨g, hg⟩ := RTree38.eval_of_numR_zero N z t.T h0
  set P := pair38 (leafU38 N z t.d0) g with hP
  refine ⟨fun w => if w = t.weight then t.c * (((2 : ℂ))⁻¹ ^ t.weight * P) else 0,
    fun w hw' => by simp [Nat.ne_of_lt hw'], fun η hη => ?_⟩
  have hmem : t.weight ∈ Finset.range (2 * k + 2) := Finset.mem_range.mpr (by omega)
  have hsum : ∑ w ∈ Finset.range (2 * k + 2),
      (fun w => if w = t.weight then t.c * (((2 : ℂ))⁻¹ ^ t.weight * P) else 0) w *
        (η : ℂ)⁻¹ ^ w = t.c * (((2 : ℂ))⁻¹ ^ t.weight * P) * (η : ℂ)⁻¹ ^ t.weight := by
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq' (Finset.range (2 * k + 2)) t.weight]
    simp only [hmem, ite_true]
  have hpair : pair38 (leafU38 N z t.d0) (t.T.eval η N z) =
      (2 * (η : ℂ))⁻¹ ^ t.T.nodes * P := by
    have e : t.T.eval η N z = fun x => (2 * (η : ℂ))⁻¹ ^ t.T.nodes * g x :=
      funext (hg η)
    rw [e, hP]
    unfold pair38
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext x; ring
  have heq : t.val η N z = t.c * (((2 : ℂ))⁻¹ ^ t.weight * P) * (η : ℂ)⁻¹ ^ t.weight := by
    unfold RTerm38.val
    rw [hpair]
    simp only [RTerm38.weight, mul_inv, mul_pow, pow_add]
    ring
  rw [hsum, ← heq]
  simp

/-! ## Terminal case (ii): weight `2k+2` remainder terms -/

theorem list_norm_sum_le38 {ι : Type*} (f : ι → ℂ) (M : ℝ) :
    ∀ L : List ι, (∀ s ∈ L, ‖f s‖ ≤ M) → ‖(L.map f).sum‖ ≤ L.length * M
  | [], _ => by simp
  | a :: L, h => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc ‖f a + (L.map f).sum‖ ≤ ‖f a‖ + ‖(L.map f).sum‖ := norm_add_le _ _
      _ ≤ M + L.length * M :=
          add_le_add (h a (by simp)) (list_norm_sum_le38 f M L (fun s hs => h s (by simp [hs])))
      _ = _ := by ring

theorem RTerm38.expOK_remainder (k : ℕ) (hk : 1 ≤ k) (B : ℝ) (t : RTerm38)
    (hw : t.weight = 2 * k + 2) (hn : 3 ≤ t.T.nodes) (hDe : t.d0 + t.T.dsum = t.e) :
    ExpOK38 k B t.weight (fun N z η => t.val η N z) := by
  obtain ⟨C, hC, hbd⟩ := RTerm38.norm_val_le_uniform k hk B
  have hD : t.d0 + t.T.dsum + 1 ≤ 2 * k := by
    simp only [RTerm38.weight] at hw; omega
  set K : ℝ := ((t.T.nodes + 1) ^ (t.d0 + t.T.dsum) : ℕ) *
    (‖t.c‖ * C ^ (t.T.nodes + 1) * (2⁻¹) ^ (2 * k + 2)) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨1, K, one_pos, hK0, fun N z hS => ⟨fun _ => 0, fun _ _ => rfl, fun η hη => ?_⟩⟩
  have hη' : 0 < η := lt_of_lt_of_le one_pos hη
  simp only [zero_mul, Finset.sum_const_zero, sub_zero]
  obtain ⟨L, hl, hP, he⟩ := RTerm38.balance_one k η hη' N z t hD
  set M : ℝ := ‖t.c‖ * C ^ (t.T.nodes + 1) * (2 * η)⁻¹ ^ (2 * k + 2) with hM
  have hM0 : 0 ≤ M := by positivity
  have hterm : ∀ s ∈ L, ‖s.val η N z‖ ≤ M := by
    intro s hs
    obtain ⟨a, b, c, d, e, f, g, h⟩ := hP s hs
    have := hbd N z hS hη' s d e (by rw [add_comm]; exact g)
    rw [a, c, h, hw] at this
    exact this
  rw [he]
  calc ‖(L.map (fun s => s.val η N z)).sum‖ ≤ (L.length : ℝ) * M :=
        list_norm_sum_le38 _ M L hterm
    _ ≤ (((t.T.nodes + 1) ^ (t.d0 + t.T.dsum) : ℕ) : ℝ) * M :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hl) hM0
    _ = K * η⁻¹ ^ (2 * k + 2) := by
        rw [hK, hM, mul_inv, mul_pow]; ring

/-! ## The lexicographic induction on `(2k+2 - weight, numR)` -/

theorem RTerm38.expOK_main (k : ℕ) (hk : 1 ≤ k) (B : ℝ) :
    ∀ r : ℕ, ∀ t : RTerm38, t.weight ≤ 2 * k + 2 → 3 ≤ t.T.nodes → t.d0 + t.T.dsum = t.e →
      2 * k + 2 - t.weight = r → ExpOK38 k B t.weight (fun N z η => t.val η N z) := by
  intro r
  induction r with
  | zero =>
    intro t hw hn hD hr
    exact RTerm38.expOK_remainder k hk B t (by omega) hn hD
  | succ r ihr =>
    suffices H : ∀ n : ℕ, ∀ t : RTerm38, t.T.numR = n → t.weight ≤ 2 * k + 2 → 3 ≤ t.T.nodes →
        t.d0 + t.T.dsum = t.e → 2 * k + 2 - t.weight = r + 1 →
        ExpOK38 k B t.weight (fun N z η => t.val η N z) by
      intro t hw hn hD hr
      exact H _ t rfl hw hn hD hr
    intro n
    induction n with
    | zero =>
      intro t h0 hw hn hD hr
      exact RTerm38.expOK_allS k B t h0 (by omega)
    | succ n ihn =>
      intro t hn1 hw hn hD hr
      obtain ⟨T₁, Ts, h1, h2, h3, h4, h5⟩ := RTree38.expand_step_uniform t.T (by omega)
      have hA : ExpOK38 k B t.weight (fun N z η => (⟨t.c, t.e, t.d0, T₁⟩ : RTerm38).val η N z) := by
        have := ihn ⟨t.c, t.e, t.d0, T₁⟩ (by simp only; omega)
          (by simp only [RTerm38.weight]; simp only [RTerm38.weight] at hw; omega)
          (by simp only; omega) (by simp only; omega)
          (by simp only [RTerm38.weight]; simp only [RTerm38.weight] at hr; omega)
        simpa only [RTerm38.weight, h2] using this
      have hB : ExpOK38 k B t.weight (fun N z η =>
          (Ts.map (fun T' => (⟨-t.c, t.e + 1, t.d0, T'⟩ : RTerm38).val η N z)).sum) := by
        refine ExpOK38.list_sum Ts (fun T' N z η =>
          (⟨-t.c, t.e + 1, t.d0, T'⟩ : RTerm38).val η N z) (fun T' hT' => ?_)
        obtain ⟨a1, a2, a3⟩ := h4 T' hT'
        have := ihr ⟨-t.c, t.e + 1, t.d0, T'⟩
          (by simp only [RTerm38.weight]; simp only [RTerm38.weight] at hr hw; omega)
          (by simp only; omega) (by simp only; omega)
          (by simp only [RTerm38.weight]; simp only [RTerm38.weight] at hr; omega)
        refine ExpOK38.mono ?_ this
        simp only [RTerm38.weight]; omega
      exact (hA.add hB).congr (fun N z η hη =>
        (RTerm38.val_expand hη N z t T₁ Ts (h5 hη N z)).symm)

/-- T6: the expansion theorem (design (b), verbatim apart from `S_k(z)` written out and the
bound variables' types). -/
theorem RTerm38.expansion (k : ℕ) (hk : 1 ≤ k) (t : RTerm38) (hw : t.weight ≤ 2 * k + 2)
    (hn : 3 ≤ t.T.nodes) (hDe : t.d0 + t.T.dsum = t.e) (B : ℝ) :
    ∃ η₀ C : ℝ, 0 < η₀ ∧ 0 ≤ C ∧ ∀ (N : ℕ) (z : FourierPlane N),
      ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ k * ‖z i‖ ^ 2 ≤ B ^ 2 →
      ∃ c : ℕ → ℂ, ∀ η : ℝ, η ≥ η₀ →
        ‖t.val η N z - ∑ w ∈ Finset.Icc t.weight (2 * k + 1), c w * (η : ℂ)⁻¹ ^ w‖ ≤
          C * η⁻¹ ^ (2 * k + 2) := by
  obtain ⟨η₀, C, h0, hC, h⟩ := RTerm38.expOK_main k hk B _ t hw hn hDe rfl
  refine ⟨η₀, C, h0, hC, fun N z hS => ?_⟩
  obtain ⟨c, hc, hb⟩ := h N z hS
  refine ⟨c, fun η hη => ?_⟩
  have hsub : ∑ w ∈ Finset.Icc t.weight (2 * k + 1), c w * (η : ℂ)⁻¹ ^ w =
      ∑ w ∈ Finset.range (2 * k + 2), c w * (η : ℂ)⁻¹ ^ w := by
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_Icc] at hx
      simp only [Finset.mem_range]; omega
    · intro x hx hx'
      simp only [Finset.mem_range] at hx
      simp only [Finset.mem_Icc, not_and, not_le] at hx'
      have : x < t.weight := by
        by_contra hcon
        have := hx' (not_lt.mp hcon); omega
      simp [hc x this]
  rw [hsub]
  exact hb η hη

end NlsGge.SpectralFoundations
end
