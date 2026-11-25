import Mathlib
import NlsGge.Atomic.G1.G1034
import NlsGge.ThirdConsultation.G1.Round6
import NlsGge.Atomic.G2.G2045SupB2
import NlsGge.Atomic.G2.G2045SupB3

/- G2-045 support kit G2045SupB4 (proof development, AUTHOR; not reviewed).
   Target NlsGge/Atomic/G2/G2045SupB4.lean, namespace NlsGge.GKDefinitionDesign.
   Continuity of phi |-> hierarchyHamiltonian k phi in the pairSobolev (H^(k-1)) topology.
   Route (a different route from a direct Lipschitz induction through wkbR; see G2045SUPB4_ROUTE.md):
   (1) L2 bound of wkbR phi (N+1) from G1-034's wkb_bound plus one more recursion step;
   (2) |H_k phi| <= ||phi.1|| ||wkbR phi k|| (L2 pairing), so H_k is bounded on Sobolev balls;
   (3) SupB3: t |-> H_k(phi0 + t v) is entire; the Schwarz lemma on a disc of radius 1/||v|| gives
       |H_k(phi0+v) - H_k(phi0)| <= 2 M0 ||v||_{H^(k-1)} for ||v|| < 1. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38

namespace NlsGge.GKDefinitionDesign
attribute [local instance] Classical.propDecidable

theorem g2045b_psn_zero (u : PhysicalL2) : physicalSobolevNorm ((0 : ℕ) : ℝ) u = ‖u‖ := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) (reflectedFourierL2 u)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [← reflectedFourierL2.norm_map u, ← Real.sqrt_sq (norm_nonneg (reflectedFourierL2 u)), h]
  unfold physicalSobolevNorm
  congr 1
  refine tsum_congr (fun n => ?_)
  simp

theorem g2045b_B_le (x y : PhysicalL2) : ‖g2045bB x y‖ ≤ ‖x‖ * ‖y‖ := by
  show ‖inner ℂ (star x) y‖ ≤ _
  have h := norm_inner_le_norm (𝕜 := ℂ) (star x) y
  rwa [show ‖star x‖ = ‖x‖ from starLp.norm_map x] at h

theorem g2045b_comp_le (N : ℕ) (φ : PotPair) (hφ : pairSobolev (N : ℝ) φ) :
    ‖φ.1‖ ≤ pairSobolevNorm (N : ℝ) φ ∧ ‖φ.2‖ ≤ pairSobolevNorm (N : ℝ) φ := by
  obtain ⟨-, h1, h2⟩ := pairSobolevNorm_ge N φ
  refine ⟨?_, ?_⟩
  · calc ‖φ.1‖ = physicalSobolevNorm ((0 : ℕ) : ℝ) φ.1 := (g2045b_psn_zero _).symm
      _ ≤ physicalSobolevNorm (N : ℝ) φ.1 := (psn_mono (Nat.zero_le N) hφ.1).2
      _ ≤ _ := h1
  · calc ‖φ.2‖ = physicalSobolevNorm ((0 : ℕ) : ℝ) φ.2 := (g2045b_psn_zero _).symm
      _ ≤ physicalSobolevNorm (N : ℝ) φ.2 := (psn_mono (Nat.zero_le N) hφ.2).2
      _ ≤ _ := h2

/-- L2 bound of the top wkb coefficient `wkbR φ (N+1)` for `φ ∈ H^N × H^N`. -/
theorem g2045b_wkb_top (N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∃ p : ℕ, ∃ C1 : ℝ, 0 < C1 ∧ ∀ φ : PotPair, pairSobolev (N : ℝ) φ →
      ‖wkbR φ (N + 1)‖ ≤ 2 * Real.pi * (C * (1 + pairSobolevNorm (N : ℝ) φ) ^ p) +
        C1 * pairSobolevNorm (N : ℝ) φ * (((N - 1 : ℕ) : ℝ) *
          (C1 * (C * (1 + pairSobolevNorm (N : ℝ) φ) ^ p) * (C * (1 + pairSobolevNorm (N : ℝ) φ) ^ p))) := by
  obtain ⟨C, hC, p, h⟩ := wkb_bound N N hN le_rfl
  obtain ⟨C1, hC1, hprod⟩ := psn_prod 1 le_rfl
  refine ⟨C, hC, p, C1, hC1, fun φ hφ => ?_⟩
  obtain ⟨hx0, hxφ1, -⟩ := pairSobolevNorm_ge N φ
  set x := pairSobolevNorm (N : ℝ) φ with hxdef
  set B := C * (1 + x) ^ p with hB
  have hBnn : 0 ≤ B := by positivity
  have hr : ∀ j, 1 ≤ j → j ≤ N → physicalSobolev ((N + 1 - j : ℕ) : ℝ) (wkbR φ j) ∧
      physicalSobolevNorm ((N + 1 - j : ℕ) : ℝ) (wkbR φ j) ≤ B := fun j h1 h2 => h φ hφ j h1 h2
  -- the derivative term
  obtain ⟨hN1, hN2⟩ := hr N hN le_rfl
  have e1 : N + 1 - N = 0 + 1 := by omega
  rw [e1] at hN1 hN2
  obtain ⟨d1, d2⟩ := psn_deriv 0 hN1
  have d3 : physicalSobolevNorm ((0 : ℕ) : ℝ) (weakDerivative (wkbR φ N)) ≤ 2 * Real.pi * B :=
    d2.trans (mul_le_mul_of_nonneg_left hN2 (by positivity))
  -- the product term, at level 1
  have hr1 : ∀ j, 1 ≤ j → j ≤ N - 1 → physicalSobolev ((1 : ℕ) : ℝ) (wkbR φ j) ∧
      physicalSobolevNorm ((1 : ℕ) : ℝ) (wkbR φ j) ≤ B := by
    intro j h1 h2
    obtain ⟨a1, a2⟩ := hr j h1 (by omega)
    obtain ⟨b1, b2⟩ := psn_mono (show 1 ≤ N + 1 - j by omega) a1
    exact ⟨b1, b2.trans a2⟩
  have hterm : ∀ j ∈ Finset.Icc 1 (N - 1),
      physicalSobolev ((1 : ℕ) : ℝ) (physicalProduct (wkbR φ j) (wkbR φ (N - j))) ∧
      physicalSobolevNorm ((1 : ℕ) : ℝ) (physicalProduct (wkbR φ j) (wkbR φ (N - j))) ≤
        C1 * B * B := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    obtain ⟨a1, a2⟩ := hr1 j hj.1 hj.2
    obtain ⟨b1, b2⟩ := hr1 (N - j) (by omega) (by omega)
    obtain ⟨c1, c2⟩ := hprod _ _ a1 b1
    refine ⟨c1, c2.trans ?_⟩
    have := psn_nonneg 1 (wkbR φ j)
    have := psn_nonneg 1 (wkbR φ (N - j))
    gcongr
  obtain ⟨s1, s2⟩ := psn_sum 1 (Finset.Icc 1 (N - 1))
    (fun j => physicalProduct (wkbR φ j) (wkbR φ (N - j))) (fun j hj => (hterm j hj).1)
  have s3 : physicalSobolevNorm ((1 : ℕ) : ℝ) (∑ j ∈ Finset.Icc 1 (N - 1),
      physicalProduct (wkbR φ j) (wkbR φ (N - j))) ≤ ((N - 1 : ℕ) : ℝ) * (C1 * B * B) := by
    refine s2.trans ?_
    refine (Finset.sum_le_sum (fun j hj => (hterm j hj).2)).trans ?_
    simp
  obtain ⟨f1, f2⟩ := psn_mono (show 1 ≤ N from hN) hφ.1
  have f3 : physicalSobolevNorm ((1 : ℕ) : ℝ) φ.1 ≤ x := f2.trans hxφ1
  obtain ⟨g1, g2⟩ := hprod _ _ f1 s1
  have g3 : physicalSobolevNorm ((1 : ℕ) : ℝ) (physicalProduct φ.1 (∑ j ∈ Finset.Icc 1 (N - 1),
      physicalProduct (wkbR φ j) (wkbR φ (N - j)))) ≤
        C1 * x * (((N - 1 : ℕ) : ℝ) * (C1 * B * B)) := by
    refine g2.trans ?_
    have := psn_nonneg 1 φ.1
    have := psn_nonneg 1 (∑ j ∈ Finset.Icc 1 (N - 1), physicalProduct (wkbR φ j) (wkbR φ (N - j)))
    gcongr
  obtain ⟨p1, p2⟩ := psn_mono (show 0 ≤ 1 by omega) g1
  rw [wkbR_succ φ N hN, ← g2045b_psn_zero]
  refine (psn_add 0 d1 p1).2.trans (add_le_add d3 (p2.trans g3))

theorem g2045b_H_bound (N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∃ p : ℕ, ∃ C1 : ℝ, 0 < C1 ∧ ∀ φ : PotPair, pairSobolev (N : ℝ) φ →
      ‖hierarchyHamiltonian (N + 1) φ‖ ≤ pairSobolevNorm (N : ℝ) φ *
        (2 * Real.pi * (C * (1 + pairSobolevNorm (N : ℝ) φ) ^ p) +
        C1 * pairSobolevNorm (N : ℝ) φ * (((N - 1 : ℕ) : ℝ) *
          (C1 * (C * (1 + pairSobolevNorm (N : ℝ) φ) ^ p) * (C * (1 + pairSobolevNorm (N : ℝ) φ) ^ p)))) := by
  obtain ⟨C, hC, p, C1, hC1, h⟩ := g2045b_wkb_top N hN
  refine ⟨C, hC, p, C1, hC1, fun φ hφ => ?_⟩
  have hH : hierarchyHamiltonian (N + 1) φ = g2045bB φ.1 (wkbR φ (N + 1)) := by
    rw [g2045bB_eq]
    unfold hierarchyHamiltonian
    rw [if_neg (by omega)]
  rw [hH]
  refine (g2045b_B_le _ _).trans ?_
  exact mul_le_mul (g2045b_comp_le N φ hφ).1 (h φ hφ) (norm_nonneg _)
    (pairSobolevNorm_ge N φ).1

/-- Local Lipschitz estimate at a point of `H^(k-1)` for `hierarchyHamiltonian k`, in the
`pairSobolevNorm (k-1)` topology. -/
theorem g2045b_hamiltonian_locLip (k : ℕ) (hk : 2 ≤ k) (φ0 : PotPair)
    (hφ0 : pairSobolev ((k - 1 : ℕ) : ℝ) φ0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ φ : PotPair, pairSobolev ((k - 1 : ℕ) : ℝ) φ →
      pairSobolevNorm ((k - 1 : ℕ) : ℝ) (φ - φ0) < 1 →
      ‖hierarchyHamiltonian k φ - hierarchyHamiltonian k φ0‖ ≤
        M * pairSobolevNorm ((k - 1 : ℕ) : ℝ) (φ - φ0) := by
  obtain ⟨N, rfl⟩ : ∃ N, k = N + 1 := ⟨k - 1, by omega⟩
  have hN : 1 ≤ N := by omega
  simp only [Nat.add_sub_cancel] at hφ0 ⊢
  obtain ⟨C, hC, p, C1, hC1, hb⟩ := g2045b_H_bound N hN
  set Tb : ℝ → ℝ := fun x => x * (2 * Real.pi * (C * (1 + x) ^ p) +
    C1 * x * (((N - 1 : ℕ) : ℝ) * (C1 * (C * (1 + x) ^ p) * (C * (1 + x) ^ p)))) with hTb
  have hmono : ∀ x x' : ℝ, 0 ≤ x → x ≤ x' → Tb x ≤ Tb x' := by
    intro x x' hx hxx
    simp only [hTb]
    have hx' : 0 ≤ x' := hx.trans hxx
    have h1 : (1 + x) ^ p ≤ (1 + x') ^ p := pow_le_pow_left₀ (by linarith) (by linarith) p
    gcongr
  have hx0 : 0 ≤ pairSobolevNorm (N : ℝ) φ0 := (pairSobolevNorm_ge N φ0).1
  set x0 := pairSobolevNorm (N : ℝ) φ0 with hx0def
  set M0 := Tb (x0 + 1) with hM0def
  have hM0 : 0 ≤ M0 := by
    simp only [hM0def, hTb]
    positivity
  refine ⟨2 * M0, by positivity, fun φ hφ hs => ?_⟩
  have hv : pairSobolev (N : ℝ) (φ - φ0) := (pairSobolevSub N).sub_mem hφ hφ0
  set v := φ - φ0 with hvdef
  set s := pairSobolevNorm (N : ℝ) v with hsdef
  have hs0 : 0 ≤ s := (pairSobolevNorm_ge N v).1
  rcases hs0.eq_or_lt with h0 | hpos
  · have hv1 : ‖v.1‖ = 0 := le_antisymm (by rw [h0]; exact (g2045b_comp_le N v hv).1) (norm_nonneg _)
    have hv2 : ‖v.2‖ = 0 := le_antisymm (by rw [h0]; exact (g2045b_comp_le N v hv).2) (norm_nonneg _)
    have e1 : φ.1 = φ0.1 := sub_eq_zero.1 (norm_eq_zero.1 hv1)
    have e2 : φ.2 = φ0.2 := sub_eq_zero.1 (norm_eq_zero.1 hv2)
    have : φ = φ0 := Prod.ext e1 e2
    subst this
    rw [sub_self, norm_zero]
    exact mul_nonneg (by positivity) hs0
  · have hline := g2045b_hamiltonian_line_analytic (N + 1) hk φ0 v (by simpa using hφ0)
      (by simpa using hv)
    set g : ℂ → ℂ := fun t => hierarchyHamiltonian (N + 1) (φ0 + t • v) with hg
    have hdiff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) (1 / s)) :=
      hline.differentiableOn.mono (Set.subset_univ _)
    have hgbound : ∀ t : ℂ, ‖t‖ * s ≤ 1 → ‖g t‖ ≤ M0 := by
      intro t ht
      have htv : pairSobolev (N : ℝ) (t • v) := (pairSobolevSub N).smul_mem t hv
      have hmem : pairSobolev (N : ℝ) (φ0 + t • v) := (pairSobolevSub N).add_mem hφ0 htv
      have h1 := g2045b_pn_add N hφ0 htv
      rw [g2045b_pn_smul] at h1
      have h2 := hb _ hmem
      refine h2.trans ?_
      exact hmono _ _ (pairSobolevNorm_ge N _).1 (by linarith)
    have hg0 : g 0 = hierarchyHamiltonian (N + 1) φ0 := by simp [hg]
    have hg0b : ‖g 0‖ ≤ M0 := by
      rw [hg0]
      refine (hb φ0 hφ0).trans ?_
      exact hmono _ _ hx0 (by linarith)
    have hmaps : Set.MapsTo g (Metric.ball (0 : ℂ) (1 / s)) (Metric.closedBall (g 0) (2 * M0)) := by
      intro t ht
      rw [Metric.mem_ball, dist_zero_right] at ht
      have : ‖t‖ * s ≤ 1 := by
        have := (lt_div_iff₀ hpos).1 ht
        linarith
      rw [Metric.mem_closedBall, dist_eq_norm]
      calc ‖g t - g 0‖ ≤ ‖g t‖ + ‖g 0‖ := norm_sub_le _ _
        _ ≤ 2 * M0 := by linarith [hgbound t this]
    have h1mem : (1 : ℂ) ∈ Metric.ball (0 : ℂ) (1 / s) := by
      rw [Metric.mem_ball, dist_zero_right, norm_one]
      exact (one_lt_div hpos).2 hs
    have hS := Complex.dist_le_div_mul_dist_of_mapsTo_ball hdiff hmaps h1mem
    have e1 : g 1 = hierarchyHamiltonian (N + 1) φ := by
      simp only [hg, one_smul, hvdef]
      rw [add_sub_cancel]
    rw [e1, hg0, dist_eq_norm, dist_zero_right, norm_one, mul_one] at hS
    calc ‖hierarchyHamiltonian (N + 1) φ - hierarchyHamiltonian (N + 1) φ0‖
        ≤ 2 * M0 / (1 / s) := hS
      _ = 2 * M0 * s := by field_simp

/-- `ε`-`δ` continuity of `hierarchyHamiltonian k` on `H^(k-1) × H^(k-1)`, `k ≥ 2`. -/
theorem g2045b_hamiltonian_continuous (k : ℕ) (hk : 2 ≤ k) (φ0 : PotPair)
    (hφ0 : pairSobolev ((k - 1 : ℕ) : ℝ) φ0) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ φ : PotPair, pairSobolev ((k - 1 : ℕ) : ℝ) φ →
      pairSobolevNorm ((k - 1 : ℕ) : ℝ) (φ - φ0) < δ →
      ‖hierarchyHamiltonian k φ - hierarchyHamiltonian k φ0‖ < ε := by
  intro ε hε
  obtain ⟨M, hM, h⟩ := g2045b_hamiltonian_locLip k hk φ0 hφ0
  refine ⟨min 1 (ε / (M + 1)), lt_min one_pos (by positivity), fun φ hφ hs => ?_⟩
  have hs1 : pairSobolevNorm ((k - 1 : ℕ) : ℝ) (φ - φ0) < 1 := lt_of_lt_of_le hs (min_le_left _ _)
  have hs2 : pairSobolevNorm ((k - 1 : ℕ) : ℝ) (φ - φ0) < ε / (M + 1) :=
    lt_of_lt_of_le hs (min_le_right _ _)
  have hs0 := (pairSobolevNorm_ge (k - 1) (φ - φ0)).1
  calc ‖hierarchyHamiltonian k φ - hierarchyHamiltonian k φ0‖
      ≤ M * pairSobolevNorm ((k - 1 : ℕ) : ℝ) (φ - φ0) := h φ hφ hs1
    _ ≤ (M + 1) * pairSobolevNorm ((k - 1 : ℕ) : ℝ) (φ - φ0) := by nlinarith
    _ < (M + 1) * (ε / (M + 1)) := mul_lt_mul_of_pos_left hs2 (by positivity)
    _ = ε := by field_simp

end NlsGge.GKDefinitionDesign
end
