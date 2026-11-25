import NlsGge.GK38.Lib.EntireProductsCore

/-!
# L4a, part 3: the zeros of `∏'[symmetricIcc ℤ] (σ_m - z)/π_m` (GKP Lemma 20.1, book Lemma C.1)

The analytic order at `w` equals the number of `n` with `σ n = w` (an `ℕ∞`-valued `encard`).
Proof: near `w` the product is a finite product of linear factors times a tail
`∏' (1 + pairTerm σ z (m + M))` which does not vanish at `w` because `‖pairTerm‖ < 1` for `m ≥ M`.
-/

set_option autoImplicit false

open Filter Topology SummationFilter

namespace NlsGge.GK38.Lib

noncomputable section

theorem analyticOrderAt_prodFactor (σ : ℤ → ℂ) (n : ℤ) (w : ℂ) :
    analyticOrderAt (fun z => prodFactor σ z n) w = if σ n = w then 1 else 0 := by
  have hc : (piN n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (piN_ne_zero n)
  have e : (fun z => prodFactor σ z n) = (fun _ => (-(1 / (piN n : ℂ)))) * (fun z => z - σ n) := by
    funext z
    simp only [prodFactor, Pi.mul_apply]
    field_simp
    ring
  rw [e, analyticOrderAt_mul analyticAt_const (by fun_prop)]
  have h0 : analyticOrderAt (fun _ : ℂ => (-(1 / (piN n : ℂ)))) w = 0 := by
    rw [analyticOrderAt_eq_zero]
    right
    simpa using hc
  rw [h0, zero_add]
  by_cases h : σ n = w
  · subst h
    simp
  · simp only [h, ↓reduceIte]
    exact analyticOrderAt_id_sub_const_of_ne (Ne.symm h)

theorem analyticOrderAt_finset_prod (σ : ℤ → ℂ) (S : Finset ℤ) (w : ℂ) :
    analyticOrderAt (fun z => ∏ n ∈ S, prodFactor σ z n) w
      = ((S.filter fun n => σ n = w).card : ℕ∞) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
    rw [analyticOrderAt_eq_zero]
    right
    simp
  | insert a S ha ih =>
    have e : (fun z => ∏ n ∈ insert a S, prodFactor σ z n)
        = (fun z => prodFactor σ z a) * (fun z => ∏ n ∈ S, prodFactor σ z n) := by
      funext z
      simp [Finset.prod_insert ha]
    have hA : AnalyticAt ℂ (fun z => prodFactor σ z a) w :=
      (differentiable_prodFactor σ a).analyticAt w
    have hS : AnalyticAt ℂ (fun z => ∏ n ∈ S, prodFactor σ z n) w :=
      (Differentiable.fun_finsetProd fun n _ => differentiable_prodFactor σ n).analyticAt w
    rw [e, analyticOrderAt_mul hA hS, analyticOrderAt_prodFactor, ih, Finset.filter_insert]
    by_cases h : σ a = w
    · simp only [h, ↓reduceIte]
      rw [Finset.card_insert_of_notMem (by simp [ha])]
      push_cast
      ring
    · simp [h]

theorem analyticOrderAt_entProd {σ : ℤ → ℂ} (hσ : Summable fun n : ℤ => ‖prodDev σ n‖ ^ 2) (w : ℂ) :
    analyticOrderAt (fun z => ∏'[symmetricIcc ℤ] m, prodFactor σ z m) w
      = Set.encard {n : ℤ | σ n = w} := by
  classical
  obtain ⟨u, hu, hb⟩ := exists_pairBound hσ (‖w‖ + 1)
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hu.tendsto_atTop_zero.eventually (gt_mem_nhds one_pos))
  have hq : ∀ k : ℕ, M ≤ k → 1 + pairTerm σ w k ≠ 0 := by
    intro k hk h0
    have h1 : pairTerm σ w k = -1 := by linear_combination h0
    have hb' : ‖pairTerm σ w k‖ ≤ u k := hb k w (by linarith)
    have hlt : ‖pairTerm σ w k‖ < 1 := lt_of_le_of_lt hb' (hM k hk)
    rw [h1] at hlt
    simp at hlt
  have hqe : ∀ k : ℕ, 1 + pairTerm σ w k
      = prodFactor σ w ((k : ℤ) + 1) * prodFactor σ w (-((k : ℤ) + 1)) := by
    intro k; simp [pairTerm]
  have hF : (fun z => ∏'[symmetricIcc ℤ] m, prodFactor σ z m)
      = (fun z => ∏ n ∈ Finset.Icc (-(M : ℤ)) M, prodFactor σ z n)
        * (fun z => ∏' m : ℕ, (1 + pairTerm σ z (m + M))) := by
    funext z
    have hshift : Multipliable fun n : ℕ => 1 + pairTerm σ z (n + M) :=
      multipliable_one_add_of_summable ((summable_nat_add_iff M).mpr (summable_norm_pairTerm hσ z))
    have hsplit := Multipliable.prod_mul_tprod_nat_mul' (f := fun k : ℕ => 1 + pairTerm σ z k)
      (k := M) hshift
    have hprod : ∏ k ∈ Finset.range M, (1 + pairTerm σ z k)
        = ∏ k ∈ Finset.range M, (prodFactor σ z ((k : ℤ) + 1) * prodFactor σ z (-((k : ℤ) + 1))) :=
      Finset.prod_congr rfl fun k _ => by simp [pairTerm]
    rw [tprod_prodFactor hσ, Pi.mul_apply, prod_Icc_symm_eq, ← hsplit, hprod, mul_assoc]
  have hTan : AnalyticAt ℂ (fun z => ∏' m : ℕ, (1 + pairTerm σ z (m + M))) w :=
    (differentiable_tail hσ M).analyticAt w
  have hTne : ∏' m : ℕ, (1 + pairTerm σ w (m + M)) ≠ 0 := by
    refine tprod_one_add_ne_zero_of_summable (f := fun m : ℕ => pairTerm σ w (m + M))
      (fun i => hq _ (by omega)) ?_
    exact (summable_nat_add_iff M).mpr (summable_norm_pairTerm hσ w)
  have hPan : AnalyticAt ℂ (fun z => ∏ n ∈ Finset.Icc (-(M : ℤ)) M, prodFactor σ z n) w :=
    (Differentiable.fun_finsetProd fun n _ => differentiable_prodFactor σ n).analyticAt w
  rw [hF, analyticOrderAt_mul hPan hTan, hTan.analyticOrderAt_eq_zero.mpr hTne, add_zero,
    analyticOrderAt_finset_prod]
  have hset : {n : ℤ | σ n = w}
      = ↑((Finset.Icc (-(M : ℤ)) M).filter fun n => σ n = w) := by
    ext n
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_Icc]
    refine ⟨fun hn => ⟨?_, hn⟩, fun h => h.2⟩
    by_contra hnot
    have hz : ∀ k : ℕ, M ≤ k → ((k : ℤ) + 1 = n ∨ -((k : ℤ) + 1) = n) → False := by
      intro k hk hkn
      have h0 : prodFactor σ w n = 0 := by simp [prodFactor, hn]
      have := hq k hk
      rw [hqe] at this
      rcases hkn with rfl | rfl
      · exact this (by rw [h0, zero_mul])
      · exact this (by rw [h0, mul_zero])
    have hlt : (M : ℤ) < n.natAbs := by omega
    obtain ⟨k, hk⟩ : ∃ k : ℕ, n.natAbs = k + 1 := ⟨n.natAbs - 1, by omega⟩
    exact hz k (by omega) (by omega)
  rw [hset, Set.encard_coe_eq_coe_finsetCard]

end

end NlsGge.GK38.Lib
