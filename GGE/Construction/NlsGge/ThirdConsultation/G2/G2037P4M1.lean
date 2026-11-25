import Mathlib
import NlsGge.Atomic.Support.ContourCycleCauchy

                                                                                            
                                                                                        
                                                                                   
                                                                                          
                                                                                             
                                                                                           

set_option autoImplicit false

namespace NlsGge.G2037P4M1
noncomputable section

open NlsGge.Atomic.ContourChain
open scoped Topology

local notation "CYC" => NlsGge.Atomic.ContourChain.Cycle

/-- `n` consecutive copies of a finite cycle. -/
def ntimes (G : CYC) : ℕ → CYC
  | 0 => NlsGge.Atomic.ContourChain.Cycle.empty
  | n + 1 => NlsGge.Atomic.ContourChain.Cycle.append (ntimes G n) G

/-- Integer multiple: `m` copies of `G` if `0 ≤ m`, else `|m|` copies of the reverse of `G`. -/
def zmul (m : ℤ) (G : CYC) : CYC :=
  if 0 ≤ m then ntimes G m.toNat else ntimes G.reverse (-m).toNat

lemma range_ntimes_subset (G : CYC) : ∀ n : ℕ, (ntimes G n).range ⊆ G.range
  | 0 => by simp [ntimes]
  | n + 1 => by
      show (NlsGge.Atomic.ContourChain.Cycle.append (ntimes G n) G).range ⊆ G.range
      rw [NlsGge.Atomic.ContourChain.Cycle.range_append]
      exact Set.union_subset (range_ntimes_subset G n) subset_rfl

lemma range_zmul_subset (m : ℤ) (G : CYC) : (zmul m G).range ⊆ G.range := by
  unfold zmul
  split_ifs
  · exact range_ntimes_subset G _
  · exact (range_ntimes_subset G.reverse _).trans
      (NlsGge.Atomic.ContourChain.Cycle.range_reverse G).subset

section Integrals
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {ω : ℂ → ℂ →L[ℂ] F}

lemma integral_ntimes_zero {G : CYC} (hG : G.integral ω = 0) :
    ∀ n : ℕ, (ntimes G n).integral ω = 0
  | 0 => by simp [ntimes]
  | n + 1 => by
      show (NlsGge.Atomic.ContourChain.Cycle.append (ntimes G n) G).integral ω = 0
      rw [NlsGge.Atomic.ContourChain.Cycle.integral_append, integral_ntimes_zero hG n, hG,
        add_zero]

lemma integral_zmul_zero {G : CYC} (hGi : G.Integrable ω) (hG : G.integral ω = 0) (m : ℤ) :
    (zmul m G).integral ω = 0 := by
  unfold zmul
  split_ifs
  · exact integral_ntimes_zero hG _
  · apply integral_ntimes_zero
    rw [NlsGge.Atomic.ContourChain.Cycle.integral_reverse hGi, hG, neg_zero]

end Integrals

lemma index_ntimes (G : CYC) {w : ℂ} (hw : w ∉ G.range) :
    ∀ n : ℕ, (ntimes G n).index w = (n : ℂ) * G.index w
  | 0 => by simp [ntimes]
  | n + 1 => by
      show (NlsGge.Atomic.ContourChain.Cycle.append (ntimes G n) G).index w = _
      rw [NlsGge.Atomic.ContourChain.Cycle.index_append, index_ntimes G hw n]
      push_cast
      ring

lemma index_zmul (m : ℤ) (G : CYC) {w : ℂ} (hw : w ∉ G.range) :
    (zmul m G).index w = (m : ℂ) * G.index w := by
  unfold zmul
  split_ifs with h
  · rw [index_ntimes G hw]
    have h1 : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg h
    have hc : ((m.toNat : ℕ) : ℂ) = (m : ℂ) := by
      rw [← Int.cast_natCast, h1]
    rw [hc]
  · have hw' : w ∉ G.reverse.range := by
      rw [NlsGge.Atomic.ContourChain.Cycle.range_reverse]
      exact hw
    rw [index_ntimes G.reverse hw', NlsGge.Atomic.ContourChain.Cycle.index_reverse G hw]
    have h1 : (((-m).toNat : ℕ) : ℤ) = -m := Int.toNat_of_nonneg (by omega)
    have hc : (((-m).toNat : ℕ) : ℂ) = -(m : ℂ) := by
      rw [← Int.cast_natCast, h1, Int.cast_neg]
    rw [hc]
    ring

section Combo
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {ω : ℂ → ℂ →L[ℂ] F}

/-- Finite combination: a cycle with range in the union of the `G k`, zero integral, and
index the `m`-weighted sum of the `G k` indices off their ranges. -/
theorem exists_combo (m : ℤ → ℤ) (G : ℤ → CYC) (S : Finset ℤ) :
    (∀ k ∈ S, (G k).Integrable ω ∧ (G k).integral ω = 0) →
      ∃ Δ : CYC, Δ.range ⊆ ⋃ k ∈ S, (G k).range ∧ Δ.integral ω = 0 ∧
        ∀ w : ℂ, (∀ k ∈ S, w ∉ (G k).range) →
          Δ.index w = ∑ k ∈ S, (m k : ℂ) * (G k).index w := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨NlsGge.Atomic.ContourChain.Cycle.empty, ?_, ?_, ?_⟩
      · simp
      · exact NlsGge.Atomic.ContourChain.Cycle.integral_empty ω
      · intro w _
        simp
  | @insert a T haT ih =>
      intro hyp
      obtain ⟨Δ, hΔr, hΔi, hΔx⟩ := ih (fun k hk => hyp k (Finset.mem_insert_of_mem hk))
      have ha := hyp a (Finset.mem_insert_self a T)
      refine ⟨NlsGge.Atomic.ContourChain.Cycle.append Δ (zmul (m a) (G a)), ?_, ?_, ?_⟩
      · rw [NlsGge.Atomic.ContourChain.Cycle.range_append]
        refine Set.union_subset ?_ ?_
        · intro z hz
          obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.1 (hΔr hz)
          exact Set.mem_iUnion₂.2 ⟨k, Finset.mem_insert_of_mem hk, hzk⟩
        · intro z hz
          exact Set.mem_iUnion₂.2 ⟨a, Finset.mem_insert_self a T, range_zmul_subset _ _ hz⟩
      · rw [NlsGge.Atomic.ContourChain.Cycle.integral_append, hΔi,
          integral_zmul_zero ha.1 ha.2, add_zero]
      · intro w hw
        have hΔw := hΔx w (fun k hk => hw k (Finset.mem_insert_of_mem hk))
        rw [NlsGge.Atomic.ContourChain.Cycle.index_append, hΔw,
          index_zmul _ _ (hw a (Finset.mem_insert_self a T)), Finset.sum_insert haT]
        ring

end Combo

section Cancel

/-- **Homology cancellation.** Let `U = (⋃_{k∈S} cut k)ᶜ` be open with each `cut k` (k ∈ S)
preconnected and the union closed. Let `G k` (k ∈ S) be cycles in `U` with index `1` on cut `k`
and `0` on every other cut of `S`, and zero integral of `f`. Then every cycle `Γ` in `U` has
zero integral of every holomorphic `f` on `U`. -/
theorem cancel_integral_zero
    {cut : ℤ → Set ℂ} {S : Finset ℤ} {U : Set ℂ}
    (hU : U = (⋃ k ∈ S, cut k)ᶜ) (hclosed : IsClosed (⋃ k ∈ S, cut k))
    (hpre : ∀ k ∈ S, IsPreconnected (cut k)) {c : ℤ → ℂ} (hc : ∀ k ∈ S, c k ∈ cut k)
    (G : ℤ → CYC) (hGU : ∀ k ∈ S, (G k).range ⊆ U)
    (hGpat : ∀ k ∈ S, ∀ j ∈ S, ∀ z ∈ cut j, (G k).index z = if j = k then 1 else 0)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hG0 : ∀ k ∈ S, (G k).integral (fun w => ContinuousLinearMap.toSpanSingleton ℂ (f w)) = 0)
    (Γ : CYC) (hΓU : Γ.range ⊆ U) :
    Γ.integral (fun w => ContinuousLinearMap.toSpanSingleton ℂ (f w)) = 0 := by
  classical
  have hcutsub : ∀ j ∈ S, ∀ z ∈ cut j, z ∉ U := by
    intro j hj z hz hzU
    rw [hU] at hzU
    exact hzU (Set.mem_iUnion₂.2 ⟨j, hj, hz⟩)
  have hΓcut : ∀ j ∈ S, cut j ⊆ (Γ.range)ᶜ := fun j hj z hz hzΓ =>
    hcutsub j hj z hz (hΓU hzΓ)
  have hGcut : ∀ k ∈ S, ∀ j ∈ S, ∀ z ∈ cut j, z ∉ (G k).range := fun k hk j hj z hz hzG =>
    hcutsub j hj z hz (hGU k hk hzG)
  have hn : ∀ k : ℤ, ∃ n : ℤ, k ∈ S → Γ.index (c k) = n := by
    intro k
    by_cases hk : k ∈ S
    · obtain ⟨n, hn⟩ := NlsGge.Atomic.ContourChain.Cycle.exists_int_index Γ
        (hΓcut k hk (hc k hk))
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose n hn using hn
  have hGi : ∀ k ∈ S, (G k).Integrable
      (fun w => ContinuousLinearMap.toSpanSingleton ℂ (f w)) := fun k hk =>
    (G k).integrable_toSpanSingleton_of_continuousOn hf.continuousOn (hGU k hk)
  obtain ⟨Δ0, hΔ0r, hΔ0i, hΔ0x⟩ := exists_combo (fun k => -(n k)) G S
    (fun k hk => ⟨hGi k hk, hG0 k hk⟩)
  have hΔ0x' : ∀ w : ℂ, (∀ k ∈ S, w ∉ (G k).range) →
      Δ0.index w = ∑ k ∈ S, ((-(n k) : ℤ) : ℂ) * (G k).index w := hΔ0x
  have hopen : IsOpen U := by
    rw [hU]
    exact hclosed.isOpen_compl
  have hΔU : (NlsGge.Atomic.ContourChain.Cycle.append Γ Δ0).range ⊆ U := by
    rw [NlsGge.Atomic.ContourChain.Cycle.range_append]
    exact Set.union_subset hΓU (hΔ0r.trans (Set.iUnion₂_subset fun k hk => hGU k hk))
  have hind : ∀ w, w ∉ U →
      (NlsGge.Atomic.ContourChain.Cycle.append Γ Δ0).index w = 0 := by
    intro w hwU
    have hw' : w ∈ ⋃ k ∈ S, cut k := by
      by_contra h
      exact hwU (by rw [hU]; exact h)
    obtain ⟨j, hj, hwj⟩ := Set.mem_iUnion₂.1 hw'
    have hΓw : Γ.index w = (n j : ℂ) := by
      rw [Γ.index_eq_of_isPreconnected (hpre j hj) (hΓcut j hj) hwj (hc j hj), hn j hj]
    have hsum : ∑ k ∈ S, ((-(n k) : ℤ) : ℂ) * (G k).index w = -(n j : ℂ) := by
      rw [Finset.sum_eq_single j]
      · rw [hGpat j hj j hj w hwj]
        simp
      · intro k hk hkj
        rw [hGpat k hk j hj w hwj, if_neg (Ne.symm hkj)]
        simp
      · intro h
        exact absurd hj h
    have hΔ0w : Δ0.index w = -(n j : ℂ) := by
      rw [hΔ0x' w (fun k hk => hGcut k hk j hj w hwj), hsum]
    rw [NlsGge.Atomic.ContourChain.Cycle.index_append, hΓw, hΔ0w]
    ring
  have hCauchy := NlsGge.Atomic.ContourChain.Cycle.integral_eq_zero
    (NlsGge.Atomic.ContourChain.Cycle.append Γ Δ0) hopen hΔU hind hf
  rw [NlsGge.Atomic.ContourChain.Cycle.integral_append, hΔ0i, add_zero] at hCauchy
  exact hCauchy

end Cancel

end

end NlsGge.G2037P4M1
