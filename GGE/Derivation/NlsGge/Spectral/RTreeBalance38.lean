import NlsGge.Spectral.RTreeCore38
import NlsGge.Spectral.RTreeIBP38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Pilot NlsGge.HierarchyRiccati.Core

/-! # RTree piece T2b: derivative balancing

For a term `c (2η)^{-e} ∫ ∂^{d0}U · eval T` with total derivative count
`D = d0 + dsum T ≤ 2k - 1`, the integration-by-parts relation of `RTerm38.ibp` moves derivatives
until every leaf (root included) has order at most `k`. Each step lowers the excess
`exc38 = Σ_leaves (d - k)⁺` by exactly one and replaces a term by `nodes` terms, up to sign.
Finally, `k · #(order-`k` leaves) ≤ D ≤ 2k - 1` shows that at most one leaf has order exactly `k`.
-/

namespace RTree38

/-- excess of the leaf orders over `k`: `Σ_leaves (d - k)⁺` -/
def exc38 (k : ℕ) : RTree38 → ℕ
  | base _ d => d - k
  | node _ d A B => (d - k) + exc38 k A + exc38 k B

theorem maxd_le_dsum : ∀ T : RTree38, T.maxd ≤ T.dsum
  | .base _ _ => le_refl _
  | .node _ d A B => by
    have h1 := maxd_le_dsum A
    have h2 := maxd_le_dsum B
    simp only [maxd, dsum]
    omega

theorem exc38_le_dsum (k : ℕ) : ∀ T : RTree38, exc38 k T ≤ T.dsum
  | .base _ _ => by simp only [exc38, dsum]; omega
  | .node _ d A B => by
    have h1 := exc38_le_dsum k A
    have h2 := exc38_le_dsum k B
    simp only [exc38, dsum]
    omega

theorem exc38_eq_zero_of_maxd_le (k : ℕ) : ∀ T : RTree38, T.maxd ≤ k → exc38 k T = 0
  | .base _ d, h => by simp only [exc38, maxd] at *; omega
  | .node _ d A B, h => by
    simp only [maxd, max_le_iff] at h
    have h1 := exc38_eq_zero_of_maxd_le k A h.2.1
    have h2 := exc38_eq_zero_of_maxd_le k B h.2.2
    simp only [exc38]
    omega

theorem maxd_le_of_exc38_eq_zero (k : ℕ) : ∀ T : RTree38, exc38 k T = 0 → T.maxd ≤ k
  | .base _ d, h => by simp only [exc38, maxd] at *; omega
  | .node _ d A B, h => by
    simp only [exc38] at h
    have h1 := maxd_le_of_exc38_eq_zero k A (by omega)
    have h2 := maxd_le_of_exc38_eq_zero k B (by omega)
    simp only [maxd, max_le_iff]
    omega

theorem cntEq_mul_le_dsum (k : ℕ) : ∀ T : RTree38, k * T.cntEq k ≤ T.dsum
  | .base _ d => by
    simp only [cntEq, dsum]
    split_ifs with h <;> omega
  | .node _ d A B => by
    have h1 := cntEq_mul_le_dsum k A
    have h2 := cntEq_mul_le_dsum k B
    simp only [cntEq, dsum]
    rw [mul_add, mul_add]
    split_ifs with h <;> simp <;> omega

theorem nodup_bumps : ∀ T : RTree38, T.bumps.Nodup
  | .base κ d => by simp [bumps]
  | .node κ d A B => by
    have hA := nodup_bumps A
    have hB := nodup_bumps B
    simp only [bumps]
    rw [List.nodup_cons]
    refine ⟨?_, ?_⟩
    · intro h
      simp only [List.mem_append, List.mem_map] at h
      rcases h with ⟨A', _, h⟩ | ⟨B', _, h⟩
      · simp only [node.injEq] at h; omega
      · simp only [node.injEq] at h; omega
    · rw [List.nodup_append]
      refine ⟨hA.map ?_, hB.map ?_, ?_⟩
      · intro x y hxy; simpa using hxy
      · intro x y hxy; simpa using hxy
      · intro T' h1 T'' h2 hh
        obtain ⟨A', hA', rfl⟩ := List.mem_map.mp h1
        obtain ⟨B', hB', rfl⟩ := List.mem_map.mp h2
        have h := hh
        simp only [node.injEq, true_and] at h
        obtain ⟨rfl, -⟩ := h
        have := dsum_of_mem_bumps _ _ hA'
        omega

end RTree38

/-! ## Pairs (root order, tree) -/

/-- the pairing functional attached to a (root order, tree) pair -/
def balPhi38 (η : ℝ) (N : ℕ) (z : FourierPlane N) (p : ℕ × RTree38) : ℂ :=
  pair38 (leafU38 N z p.1) (p.2.eval η N z)

/-- single-leaf bumps of a pair: the root bump, then the bumps inside the tree -/
def pbumps38 (p : ℕ × RTree38) : List (ℕ × RTree38) :=
  (p.1 + 1, p.2) :: p.2.bumps.map (fun T' => (p.1, T'))

/-- excess of a pair, root included -/
def excP38 (k : ℕ) (p : ℕ × RTree38) : ℕ := (p.1 - k) + p.2.exc38 k

theorem pbumps38_nodup (p : ℕ × RTree38) : (pbumps38 p).Nodup := by
  unfold pbumps38
  rw [List.nodup_cons]
  refine ⟨?_, (RTree38.nodup_bumps p.2).map ?_⟩
  · intro h
    simp only [List.mem_map] at h
    obtain ⟨T', _, h⟩ := h
    have := congrArg Prod.fst h
    simp at this
  · intro x y hxy; simpa using hxy

theorem length_pbumps38 (p : ℕ × RTree38) : (pbumps38 p).length = p.2.nodes + 1 := by
  simp [pbumps38, RTree38.length_bumps]

theorem pbumps38_prop (p : ℕ × RTree38) : ∀ q ∈ pbumps38 p,
    q.2.nodes = p.2.nodes ∧ q.1 + q.2.dsum = p.1 + p.2.dsum + 1 := by
  intro q hq
  unfold pbumps38 at hq
  rcases List.mem_cons.mp hq with rfl | h
  · simp; omega
  · obtain ⟨T', hT', rfl⟩ := List.mem_map.mp h
    refine ⟨RTree38.nodes_of_mem_bumps _ _ hT', ?_⟩
    have := RTree38.dsum_of_mem_bumps _ _ hT'
    simp only
    omega

theorem balPhi38_pbumps_sum {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N) (p : ℕ × RTree38) :
    ((pbumps38 p).map (balPhi38 η N z)).sum = 0 := by
  have h := RTerm38.ibp hη N z p.1 p.2
  simpa [pbumps38, balPhi38, List.map_map, Function.comp_def] using h

/-! ## Finding the decrement -/

theorem RTree38.exists_dec (k : ℕ) : ∀ (T : RTree38) (ctx : ℕ), 0 < T.exc38 k →
    ctx + T.dsum + 1 ≤ 2 * k →
    ∃ T₀ : RTree38, T ∈ T₀.bumps ∧ T₀.exc38 k + 1 = T.exc38 k ∧
      ∀ q ∈ T₀.bumps, q ≠ T → q.exc38 k + 1 = T.exc38 k := by
  intro T
  induction T with
  | base κ d =>
    intro ctx h0 hD
    simp only [RTree38.exc38] at h0
    refine ⟨RTree38.base κ (d - 1), ?_, ?_, ?_⟩
    · simp only [RTree38.bumps, List.mem_singleton]
      congr 1; omega
    · simp only [RTree38.exc38]; omega
    · intro q hq hne
      simp only [RTree38.bumps, List.mem_singleton] at hq
      exfalso; apply hne; rw [hq]; congr 1; omega
  | node κ d A B ihA ihB =>
    intro ctx h0 hD
    simp only [RTree38.exc38] at h0
    simp only [RTree38.dsum] at hD
    by_cases hd : k < d
    · -- the big leaf is the node's own leaf
      have hA := RTree38.maxd_le_dsum A
      have hB := RTree38.maxd_le_dsum B
      have eA := RTree38.exc38_eq_zero_of_maxd_le k A (by omega)
      have eB := RTree38.exc38_eq_zero_of_maxd_le k B (by omega)
      refine ⟨RTree38.node κ (d - 1) A B, ?_, ?_, ?_⟩
      · rw [RTree38.mem_bumps_node]
        left; congr 1; omega
      · simp only [RTree38.exc38]; omega
      · intro q hq hne
        rcases RTree38.mem_bumps_node.mp hq with h | ⟨A', hA', h⟩ | ⟨B', hB', h⟩
        · exfalso; apply hne; rw [h]; congr 1; omega
        · subst h
          have := RTree38.maxd_of_mem_bumps_le A A' hA'
          have eA' := RTree38.exc38_eq_zero_of_maxd_le k A' (by omega)
          simp only [RTree38.exc38]; omega
        · subst h
          have := RTree38.maxd_of_mem_bumps_le B B' hB'
          have eB' := RTree38.exc38_eq_zero_of_maxd_le k B' (by omega)
          simp only [RTree38.exc38]; omega
    · have hdk : d - k = 0 := by omega
      by_cases hAe : 0 < A.exc38 k
      · -- the big leaf is inside `A`
        have hAk : k < A.maxd := by
          by_contra hc
          have := RTree38.exc38_eq_zero_of_maxd_le k A (by omega)
          omega
        have hAd := RTree38.maxd_le_dsum A
        have hBd := RTree38.maxd_le_dsum B
        obtain ⟨A₀, hmem, hexc, hoth⟩ := ihA (ctx + d + B.dsum) hAe (by omega)
        have eB := RTree38.exc38_eq_zero_of_maxd_le k B (by omega)
        refine ⟨RTree38.node κ d A₀ B, ?_, ?_, ?_⟩
        · rw [RTree38.mem_bumps_node]
          right; left; exact ⟨A, hmem, rfl⟩
        · simp only [RTree38.exc38]; omega
        · intro q hq hne
          rcases RTree38.mem_bumps_node.mp hq with h | ⟨A', hA', h⟩ | ⟨B', hB', h⟩
          · subst h
            simp only [RTree38.exc38]; omega
          · subst h
            have hne' : A' ≠ A := fun h => hne (by rw [h])
            have := hoth A' hA' hne'
            simp only [RTree38.exc38]; omega
          · subst h
            have := RTree38.maxd_of_mem_bumps_le B B' hB'
            have eB' := RTree38.exc38_eq_zero_of_maxd_le k B' (by omega)
            simp only [RTree38.exc38]; omega
      · have hBe : 0 < B.exc38 k := by omega
        have hBk : k < B.maxd := by
          by_contra hc
          have := RTree38.exc38_eq_zero_of_maxd_le k B (by omega)
          omega
        have hAd := RTree38.maxd_le_dsum A
        have hBd := RTree38.maxd_le_dsum B
        obtain ⟨B₀, hmem, hexc, hoth⟩ := ihB (ctx + d + A.dsum) hBe (by omega)
        have eA : A.exc38 k = 0 := by omega
        refine ⟨RTree38.node κ d A B₀, ?_, ?_, ?_⟩
        · rw [RTree38.mem_bumps_node]
          right; right; exact ⟨B, hmem, rfl⟩
        · simp only [RTree38.exc38]; omega
        · intro q hq hne
          rcases RTree38.mem_bumps_node.mp hq with h | ⟨A', hA', h⟩ | ⟨B', hB', h⟩
          · subst h
            simp only [RTree38.exc38]; omega
          · subst h
            have := RTree38.maxd_of_mem_bumps_le A A' hA'
            have eA' := RTree38.exc38_eq_zero_of_maxd_le k A' (by omega)
            simp only [RTree38.exc38]; omega
          · subst h
            have hne' : B' ≠ B := fun h => hne (by rw [h])
            have := hoth B' hB' hne'
            simp only [RTree38.exc38]; omega


theorem exists_dec_pair38 (k : ℕ) (p : ℕ × RTree38) (h0 : 0 < excP38 k p)
    (hD : p.1 + p.2.dsum + 1 ≤ 2 * k) :
    ∃ p₀ : ℕ × RTree38, p ∈ pbumps38 p₀ ∧
      ∀ q ∈ pbumps38 p₀, q ≠ p → excP38 k q + 1 = excP38 k p := by
  obtain ⟨d0, T⟩ := p
  simp only [excP38] at h0 ⊢
  simp only at hD
  by_cases hd : k < d0
  · have hm := RTree38.maxd_le_dsum T
    refine ⟨(d0 - 1, T), ?_, ?_⟩
    · simp only [pbumps38, List.mem_cons]
      left; ext <;> simp; omega
    · intro q hq hne
      simp only [pbumps38, List.mem_cons, List.mem_map] at hq
      rcases hq with rfl | ⟨T', hT', rfl⟩
      · exfalso; apply hne; ext <;> simp; omega
      · have := RTree38.maxd_of_mem_bumps_le T T' hT'
        have e1 := RTree38.exc38_eq_zero_of_maxd_le k T' (by omega)
        have e2 := RTree38.exc38_eq_zero_of_maxd_le k T (by omega)
        simp only; omega
  · have hT : 0 < T.exc38 k := by omega
    have hm := RTree38.maxd_le_dsum T
    have hk : k < T.maxd := by
      by_contra hc
      have := RTree38.exc38_eq_zero_of_maxd_le k T (by omega)
      omega
    obtain ⟨T₀, hmem, hexc, hoth⟩ := RTree38.exists_dec k T d0 hT hD
    refine ⟨(d0, T₀), ?_, ?_⟩
    · simp only [pbumps38, List.mem_cons, List.mem_map]
      right; exact ⟨T, hmem, rfl⟩
    · intro q hq hne
      simp only [pbumps38, List.mem_cons, List.mem_map] at hq
      rcases hq with rfl | ⟨T', hT', rfl⟩
      · simp only; omega
      · have hne' : T' ≠ T := fun h => hne (by rw [h])
        have := hoth T' hT' hne'
        simp only; omega

/-! ## The balancing induction -/

theorem list_sum_combine38 {α β : Type*} (f : α → ℂ) (g : β → ℂ) (s : ℂ) (b : ℕ) (P : β → Prop)
    (Q : List α) (h : ∀ q ∈ Q, ∃ L : List β, L.length ≤ b ∧ (∀ x ∈ L, P x) ∧
      f q = s * (L.map g).sum) :
    ∃ L : List β, L.length ≤ Q.length * b ∧ (∀ x ∈ L, P x) ∧
      (Q.map f).sum = s * (L.map g).sum := by
  induction Q with
  | nil => exact ⟨[], by simp, by simp, by simp⟩
  | cons a Q ih =>
    obtain ⟨L1, hl1, hP1, he1⟩ := h a (by simp)
    obtain ⟨L2, hl2, hP2, he2⟩ := ih (fun q hq => h q (by simp [hq]))
    refine ⟨L1 ++ L2, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons]
      nlinarith
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hP1 x h
      · exact hP2 x h
    · simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append]
      rw [he1, he2]; ring

theorem balance_aux38 (k : ℕ) {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N) :
    ∀ (m : ℕ) (p : ℕ × RTree38), excP38 k p = m → p.1 + p.2.dsum + 1 ≤ 2 * k →
      ∃ L : List (ℕ × RTree38), L.length ≤ p.2.nodes ^ m ∧
        (∀ q ∈ L, q.2.nodes = p.2.nodes ∧ q.1 ≤ k ∧ q.2.maxd ≤ k ∧
          q.1 + q.2.dsum = p.1 + p.2.dsum) ∧
        balPhi38 η N z p = (-1) ^ m * (L.map (balPhi38 η N z)).sum := by
  intro m
  induction m with
  | zero =>
    intro p hp hD
    refine ⟨[p], by simp, ?_, by simp⟩
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    simp only [excP38] at hp
    have := RTree38.maxd_le_of_exc38_eq_zero k q.2 (by omega)
    exact ⟨rfl, by omega, this, rfl⟩
  | succ m ih =>
    intro p hp hD
    obtain ⟨p₀, hmem, hoth⟩ := exists_dec_pair38 k p (by omega) hD
    have hsum := balPhi38_pbumps_sum hη N z p₀
    have hperm := (List.perm_cons_erase hmem)
    have hsum' : balPhi38 η N z p + (((pbumps38 p₀).erase p).map (balPhi38 η N z)).sum = 0 := by
      rw [← hsum, (hperm.map (balPhi38 η N z)).sum_eq]
      simp
    have hQ : ∀ q ∈ (pbumps38 p₀).erase p, ∃ L : List (ℕ × RTree38),
        L.length ≤ p.2.nodes ^ m ∧
        (∀ x ∈ L, x.2.nodes = p.2.nodes ∧ x.1 ≤ k ∧ x.2.maxd ≤ k ∧
          x.1 + x.2.dsum = p.1 + p.2.dsum) ∧
        balPhi38 η N z q = (-1) ^ m * (L.map (balPhi38 η N z)).sum := by
      intro q hq
      have hq' := (List.Nodup.mem_erase_iff (pbumps38_nodup p₀)).mp hq
      have hqe := hoth q hq'.2 hq'.1
      have hq1 := pbumps38_prop p₀ q hq'.2
      have hp1 := pbumps38_prop p₀ p hmem
      obtain ⟨L, hl, hP, he⟩ := ih q (by omega) (by omega)
      refine ⟨L, by rw [hq1.1.trans hp1.1.symm] at hl; exact hl, ?_, he⟩
      intro x hx
      obtain ⟨a, b, c, d⟩ := hP x hx
      exact ⟨a.trans (hq1.1.trans hp1.1.symm), b, c, by omega⟩
    obtain ⟨L, hl, hP, he⟩ := list_sum_combine38 (balPhi38 η N z) (balPhi38 η N z) ((-1) ^ m)
      (p.2.nodes ^ m) (fun x : ℕ × RTree38 => x.2.nodes = p.2.nodes ∧ x.1 ≤ k ∧ x.2.maxd ≤ k ∧
          x.1 + x.2.dsum = p.1 + p.2.dsum) _ hQ
    refine ⟨L, ?_, hP, ?_⟩
    · have hlen : ((pbumps38 p₀).erase p).length = p.2.nodes := by
        rw [List.length_erase_of_mem hmem, length_pbumps38]
        have hp1 := pbumps38_prop p₀ p hmem
        simp only [Nat.add_sub_cancel]
        rw [← hp1.1]
      rw [hlen] at hl
      calc L.length ≤ p.2.nodes * p.2.nodes ^ m := hl
        _ = p.2.nodes ^ (m + 1) := by ring
    · have : balPhi38 η N z p = -(((pbumps38 p₀).erase p).map (balPhi38 η N z)).sum :=
        eq_neg_of_add_eq_zero_left hsum'
      rw [this, he]; ring

/-- Derivative balancing (design (b), T2b). -/
theorem RTerm38.balance (k : ℕ) (η : ℝ) (hη : 0 < η) (N : ℕ) (z : FourierPlane N)
    (t : RTerm38) (hD : t.d0 + t.T.dsum + 1 ≤ 2 * k) :
    ∃ L : List RTerm38, L.length ≤ (t.T.nodes + 1) ^ (t.d0 + t.T.dsum) ∧
      (∀ s ∈ L, s.T.nodes = t.T.nodes ∧ s.e = t.e ∧ ‖s.c‖ = ‖t.c‖ ∧
        s.d0 ≤ k ∧ s.T.maxd ≤ k ∧ s.d0 + s.T.dsum = t.d0 + t.T.dsum) ∧
      t.val η N z = (L.map (·.val η N z)).sum := by
  obtain ⟨L, hl, hP, he⟩ := balance_aux38 k hη N z (excP38 k (t.d0, t.T)) (t.d0, t.T) rfl hD
  set m := excP38 k (t.d0, t.T) with hm
  refine ⟨L.map (fun q => (⟨(-1) ^ m * t.c, t.e, q.1, q.2⟩ : RTerm38)), ?_, ?_, ?_⟩
  · rw [List.length_map]
    have h1 : m ≤ t.d0 + t.T.dsum := by
      have := RTree38.exc38_le_dsum k t.T
      simp only [hm, excP38]; omega
    calc L.length ≤ t.T.nodes ^ m := hl
      _ ≤ (t.T.nodes + 1) ^ m := Nat.pow_le_pow_left (Nat.le_succ _) _
      _ ≤ (t.T.nodes + 1) ^ (t.d0 + t.T.dsum) := Nat.pow_le_pow_right (Nat.succ_pos _) h1
  · intro s hs
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hs
    obtain ⟨a, b, c, d⟩ := hP q hq
    exact ⟨a, rfl, by simp, b, c, d⟩
  · have e1 : ∀ q : ℕ × RTree38, RTerm38.val η N z (⟨(-1) ^ m * t.c, t.e, q.1, q.2⟩ : RTerm38) =
        (-1) ^ m * (t.c * ((2 * η : ℂ))⁻¹ ^ t.e) * balPhi38 η N z q := by
      intro q
      simp only [RTerm38.val, balPhi38]; ring
    have e2 : (L.map (fun q => RTerm38.val η N z (⟨(-1) ^ m * t.c, t.e, q.1, q.2⟩ : RTerm38))).sum =
        (-1) ^ m * (t.c * ((2 * η : ℂ))⁻¹ ^ t.e) * (L.map (balPhi38 η N z)).sum := by
      simp only [e1, List.sum_map_mul_left]
    simp only [List.map_map, Function.comp_def]
    rw [e2]
    have : t.val η N z = t.c * ((2 * η : ℂ))⁻¹ ^ t.e * balPhi38 η N z (t.d0, t.T) := by
      simp only [RTerm38.val, balPhi38]
    rw [this, he]; ring

/-- At most one leaf (root included) has order exactly `k` once `D ≤ 2k - 1`. -/
theorem RTerm38.cnt_atMostOne (k : ℕ) (s : RTerm38) (hD : s.d0 + s.T.dsum + 1 ≤ 2 * k) :
    (if s.d0 = k then 1 else 0) + s.T.cntEq k ≤ 1 := by
  have h := RTree38.cntEq_mul_le_dsum k s.T
  have hk : 1 ≤ k := by omega
  by_cases h0 : s.d0 = k
  · simp only [h0, ite_true]
    by_contra hc
    have : 1 ≤ s.T.cntEq k := by omega
    nlinarith
  · simp only [h0, ite_false, zero_add]
    by_contra hc
    have : 2 ≤ s.T.cntEq k := by omega
    nlinarith

/-- Balancing with the extra conclusion: at most one order-`k` leaf, root included. -/
theorem RTerm38.balance_one (k : ℕ) (η : ℝ) (hη : 0 < η) (N : ℕ) (z : FourierPlane N)
    (t : RTerm38) (hD : t.d0 + t.T.dsum + 1 ≤ 2 * k) :
    ∃ L : List RTerm38, L.length ≤ (t.T.nodes + 1) ^ (t.d0 + t.T.dsum) ∧
      (∀ s ∈ L, s.T.nodes = t.T.nodes ∧ s.e = t.e ∧ ‖s.c‖ = ‖t.c‖ ∧
        s.d0 ≤ k ∧ s.T.maxd ≤ k ∧ s.d0 + s.T.dsum = t.d0 + t.T.dsum ∧
        (if s.d0 = k then 1 else 0) + s.T.cntEq k ≤ 1 ∧
        s.weight = t.weight) ∧
      t.val η N z = (L.map (·.val η N z)).sum := by
  obtain ⟨L, hl, hP, he⟩ := RTerm38.balance k η hη N z t hD
  refine ⟨L, hl, fun s hs => ?_, he⟩
  obtain ⟨a, b, c, d, e, f⟩ := hP s hs
  refine ⟨a, b, c, d, e, f, RTerm38.cnt_atMostOne k s (by omega), ?_⟩
  simp only [RTerm38.weight, a, b]

end NlsGge.SpectralFoundations
end
