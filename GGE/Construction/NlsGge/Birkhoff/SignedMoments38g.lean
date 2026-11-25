import NlsGge.Birkhoff.SignedMoments38f
import NlsGge.Birkhoff.S04Moments38e

/-! # SIGNED-MOMENTS.05 (`F:rem:signed`): finite moments and mixed products of the signed charges (`B`, `O`)

Source: `paper/v2.tex` l.1822-1829 (the remark) together with `F:cor:charge` (NEW-F11, `F11_chargeexp38`).

Reading. `c : BoundedCoefficients lower upper`, `ν_{W,N} = nuWN38 c N`, `μ_W = B.muW38 c.val`, `m ≥ 2`,
`C_k = signedChargeFn38 m k` (`k ≤ 2m-2`): `C_{2j} = Q_{2j}`, `C_{2j+1}` the odd local charge, both the continuous
extensions to `H^{m-1}` of the local polynomial representatives. `signedMoments_38`: for every finite family
`k_i ≤ 2m-2` and powers `p_i`, `∏ C_{k_i}^{p_i}` is integrable under every `ν_{W,N}` and under `μ_W`, and
`∫ ∏ C_{k_i}^{p_i} dν_{W,N} → ∫ ∏ C_{k_i}^{p_i} dμ_W` (`n = 1`: all finite moments of one signed charge).
The proof is the truncation + uniform-integrability argument of NEW-F11 applied to `F = F⁺ - F⁻`, with
`F² ≤ K exp(Σ t_j Q_{2j})` from `|C_k| ≤ Σ_j Q_{2j}` (AM-GM, SIGNED-MOMENTS.03).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.HierarchyRiccati.Core NlsGge.HierarchyRiccati Filter Topology
open scoped ENNReal Real ContDiff

section Signed

variable {X : Type*} [MeasurableSpace X]

/-- Truncation + uniform integrability for a signed `F`: `F = F⁺ - F⁻`. -/
theorem tendsto_integral_signed38 (ν : ℕ → Measure X) (μ : Measure X)
    (hν : ∀ N, IsProbabilityMeasure (ν N)) [IsProbabilityMeasure μ]
    (F : X → ℝ) (hFm : Measurable F) (M : ℝ)
    (hM : ∀ N, Integrable (fun x => F x ^ 2) (ν N) ∧ ∫ x, F x ^ 2 ∂(ν N) ≤ M)
    (hweak : ∀ H : ℝ → ℝ, Continuous H → (∃ B : ℝ, ∀ t, |H t| ≤ B) →
      Tendsto (fun N => ∫ x, H (F x) ∂(ν N)) atTop (𝓝 (∫ x, H (F x) ∂μ))) :
    Integrable F μ ∧ (∀ N, Integrable F (ν N)) ∧
      Tendsto (fun N => ∫ x, F x ∂(ν N)) atTop (𝓝 (∫ x, F x ∂μ)) := by
  have key : ∀ P : ℝ → ℝ, Continuous P → (∀ t, 0 ≤ P t) → (∀ t, P t ^ 2 ≤ t ^ 2) →
      Integrable (fun x => P (F x)) μ ∧ (∀ N, Integrable (fun x => P (F x)) (ν N)) ∧
      Tendsto (fun N => ∫ x, P (F x) ∂(ν N)) atTop (𝓝 (∫ x, P (F x) ∂μ)) := by
    intro P hP hP0 hPsq
    have hPm : Measurable (fun x => P (F x)) := hP.measurable.comp hFm
    have hsq : ∀ N, Integrable (fun x => P (F x) ^ 2) (ν N) ∧ ∫ x, P (F x) ^ 2 ∂(ν N) ≤ M := by
      intro N
      have hI : Integrable (fun x => P (F x) ^ 2) (ν N) :=
        (hM N).1.mono' (hPm.pow_const 2).aestronglyMeasurable
          (Filter.Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hPsq _)
      refine ⟨hI, (integral_mono hI (hM N).1 fun x => hPsq _).trans (hM N).2⟩
    obtain ⟨-, hFμ, hFν, hlim⟩ := tendsto_integral_of_sq_bounded38 ν μ hν (fun x => P (F x))
      (fun x => hP0 _) (fun N => hPm.aestronglyMeasurable) hPm.aestronglyMeasurable M hsq
      (fun R hR => hweak (fun t => min (P t) R) (hP.min continuous_const)
        ⟨R, fun t => by rw [abs_of_nonneg (le_min (hP0 _) hR.le)]; exact min_le_right _ _⟩)
      (fun R hR => hweak (fun t => min (P t ^ 2) R) ((hP.pow 2).min continuous_const)
        ⟨R, fun t => by rw [abs_of_nonneg (le_min (sq_nonneg _) hR.le)]; exact min_le_right _ _⟩)
    exact ⟨hFμ, hFν, hlim⟩
  obtain ⟨i1, j1, l1⟩ := key (fun t => max t 0) (continuous_id.max continuous_const)
    (fun t => le_max_right _ _)
    (fun t => by
      rcases le_total t 0 with h | h
      · rw [max_eq_right h]; nlinarith
      · rw [max_eq_left h])
  obtain ⟨i2, j2, l2⟩ := key (fun t => max (-t) 0) (continuous_id.neg.max continuous_const)
    (fun t => le_max_right _ _)
    (fun t => by
      rcases le_total t 0 with h | h
      · rw [max_eq_left (by linarith)]; nlinarith
      · rw [max_eq_right (by linarith)]; nlinarith)
  have hF : ∀ x, F x = max (F x) 0 - max (-F x) 0 := fun x => by
    rcases le_total (F x) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have hFfun : F = fun x => max (F x) 0 - max (-F x) 0 := funext hF
  refine ⟨?_, fun N => ?_, ?_⟩
  · rw [hFfun]; exact i1.sub i2
  · rw [hFfun]; exact (j1 N).sub (j2 N)
  · have hh : ∀ (ρ : Measure X), Integrable (fun x => max (F x) 0) ρ →
        Integrable (fun x => max (-F x) 0) ρ →
        ∫ x, F x ∂ρ = ∫ x, max (F x) 0 ∂ρ - ∫ x, max (-F x) 0 ∂ρ := by
      intro ρ a b
      rw [← integral_sub a b]
      exact integral_congr_ae (Filter.Eventually.of_forall hF)
    have e1 : ∀ N, ∫ x, F x ∂(ν N) = ∫ x, max (F x) 0 ∂(ν N) - ∫ x, max (-F x) 0 ∂(ν N) :=
      fun N => hh _ (j1 N) (j2 N)
    rw [hh μ i1 i2]
    simp_rw [e1]
    exact l1.sub l2

/-- Polynomial-in-charges bound: if `|C_i| ≤ Σ_{j ≤ J} Q_j` then `(∏ C_i^{p_i})² ≤ K exp(Σ t_j Q_j)`. -/
theorem signed_prod_sq_le_exp38 (Q : ℕ → X → ℝ) (J : ℕ) (hQ : ∀ j ≤ J, ∀ x, 0 ≤ Q j x)
    (t : ℕ → ℝ) (ht : ∀ j ≤ J, 0 < t j) (n : ℕ) (C : Fin n → X → ℝ)
    (hC : ∀ i x, |C i x| ≤ ∑ j ∈ Finset.range (J + 1), Q j x) (p : Fin n → ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : X, (∏ i, C i x ^ p i) ^ 2 ≤
      K * Real.exp (∑ j ∈ Finset.range (J + 1), t j * Q j x) := by
  obtain ⟨τ, hτ, hτt⟩ : ∃ τ : ℝ, 0 < τ ∧ ∀ j ≤ J, τ ≤ t j := by
    refine ⟨(Finset.range (J + 1)).inf' (Finset.nonempty_range_iff.2 (Nat.succ_ne_zero J)) t, ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      intro j hj
      exact ht j (by simpa [Nat.lt_succ_iff] using hj)
    · intro j hj
      exact Finset.inf'_le _ (by simpa [Nat.lt_succ_iff] using hj)
  set P : ℕ := ∑ i, p i with hP
  set S : X → ℝ := fun x => ∑ j ∈ Finset.range (J + 1), Q j x with hS
  have hS0 : ∀ x, 0 ≤ S x := fun x => Finset.sum_nonneg fun j hj =>
    hQ j (by simpa [Nat.lt_succ_iff] using hj) x
  obtain ⟨K, hK, hKb⟩ := prod_sq_le_exp38 (fun _ x => S x) 0 (fun _ _ x => hS0 x) (fun _ => τ)
    (fun _ _ => hτ) 1 (fun _ => 0) (fun _ => le_rfl) (fun _ => P)
  refine ⟨K, hK, fun x => ?_⟩
  have habs : |∏ i, C i x ^ p i| ≤ S x ^ P := by
    rw [Finset.abs_prod]
    calc ∏ i, |C i x ^ p i| = ∏ i, |C i x| ^ p i := by simp only [abs_pow]
      _ ≤ ∏ i, S x ^ p i :=
          Finset.prod_le_prod₀ (fun i _ => by positivity)
            (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hC i x) _)
      _ = S x ^ P := Finset.prod_pow_eq_pow_sum _ _ _
  have h1 : (∏ i, C i x ^ p i) ^ 2 ≤ (S x ^ P) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have h2 := hKb x
  simp only [Finset.univ_unique, Finset.prod_singleton, zero_add, Finset.sum_range_one] at h2
  have h3 : τ * S x ≤ ∑ j ∈ Finset.range (J + 1), t j * Q j x := by
    simp only [hS, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' : j ≤ J := by simpa [Nat.lt_succ_iff] using hj
    exact mul_le_mul_of_nonneg_right (hτt j hj') (hQ j hj' x)
  calc (∏ i, C i x ^ p i) ^ 2 ≤ (S x ^ P) ^ 2 := h1
    _ ≤ K * Real.exp (τ * S x) := h2
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h3) hK.le

end Signed

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lower upper : ℝ}
  (c : BoundedCoefficients lower upper)

include B O in
/-- **SIGNED-MOMENTS.05** (`F:rem:signed`, conditional on `B : BirkhoffInput38`, `O : OneSmoothingInput38 B`):
finite mixed products of the signed local moments `C_k`, `k ≤ 2m-2`, are integrable under every `ν_{W,N}` and under
`μ_W`, and their integrals under `ν_{W,N}` converge to those under `μ_W`. -/
theorem signedMoments_38 (m : ℕ) (hm : 2 ≤ m) (n : ℕ) (kk : Fin n → ℕ) (hkk : ∀ i, kk i ≤ 2 * m - 2)
    (p : Fin n → ℕ) :
    (∀ N : ℕ, Integrable (fun u => ∏ i, signedChargeFn38 m (kk i) u ^ p i) (nuWN38 c N)) ∧
      Integrable (fun u => ∏ i, signedChargeFn38 m (kk i) u ^ p i) (B.muW38 c.val) ∧
      Tendsto (fun N : ℕ => ∫ u, ∏ i, signedChargeFn38 m (kk i) u ^ p i ∂(nuWN38 c N)) atTop
        (𝓝 (∫ u, ∏ i, signedChargeFn38 m (kk i) u ^ p i ∂(B.muW38 c.val))) := by
  have hs : (1 : ℝ) / 2 < 5 / 8 := by norm_num
  have hs' : (5 / 8 : ℝ) < 3 / 4 := by norm_num
  have hlower := c.property.1
  have : IsProbabilityMeasure (B.muW38 c.val) :=
    B.isProbabilityMeasure_muW38 lower upper c.val hlower (fun j => (c.property.2.2 j).1)
      (fun j => (c.property.2.2 j).2)
  have : ∀ N, IsProbabilityMeasure (nuWN38 c N) := fun N => isProbabilityMeasure_nuWN38 c N
  set F : PhysicalL2 → ℝ := fun u => ∏ i, signedChargeFn38 m (kk i) u ^ p i with hFdef
  have hFmeas : Measurable F :=
    Finset.measurable_prod _ fun i _ =>
      (measurable_signedChargeFn38 m (kk i) hm (hkk i)).pow_const _
  have hcoef : ∀ j, 0 < NlsGge.coefficient c.val j := fun j => by
    have := hlower.trans_le (c.property.2.2 j).1
    unfold NlsGge.coefficient; positivity
  set t : ℕ → ℝ := fun j => NlsGge.coefficient c.val j / 2 with htdef
  have htpos : ∀ j ≤ m - 1, 0 < t j := fun j _ => by
    have := hcoef j; simp only [htdef]; positivity
  have htad : ∀ j ≤ m - 1, 0 ≤ t j ∧ t j < NlsGge.coefficient c.val j := fun j hj =>
    ⟨(htpos j hj).le, by have := hcoef j; simp only [htdef]; linarith⟩
  obtain ⟨Cexp, hCexp⟩ := B.F11_chargeexp38 O c m hm (m - 1) le_rfl t htad
  have hrange : m - 1 + 1 = m := by omega
  obtain ⟨K, hK, hKb⟩ := signed_prod_sq_le_exp38 (fun j u => chargeFn38 m j u) (m - 1)
    (fun j hj u => chargeFn38_nonneg m j hm hj u) t htpos n
    (fun i u => signedChargeFn38 m (kk i) u)
    (fun i u => by rw [hrange]; exact signedChargeFn_abs_le38 m (kk i) hm (hkk i) u) p
  set M : ℝ := K * Cexp with hM
  have hsq : ∀ N, Integrable (fun u => F u ^ 2) (nuWN38 c N) ∧
      ∫ u, F u ^ 2 ∂(nuWN38 c N) ≤ M := by
    intro N
    obtain ⟨hI, hC⟩ := hCexp N
    have hdom : Integrable (fun u => K * Real.exp (∑ j ∈ Finset.range (m - 1 + 1), t j * chargeFn38 m j u))
        (nuWN38 c N) := hI.const_mul K
    have hint : Integrable (fun u => F u ^ 2) (nuWN38 c N) :=
      hdom.mono' (hFmeas.pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun u => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact hKb u)
    refine ⟨hint, ?_⟩
    calc ∫ u, F u ^ 2 ∂(nuWN38 c N)
        ≤ ∫ u, K * Real.exp (∑ j ∈ Finset.range (m - 1 + 1), t j * chargeFn38 m j u) ∂(nuWN38 c N) :=
          integral_mono hint hdom fun u => hKb u
      _ = K * ∫ u, Real.exp (∑ j ∈ Finset.range (m - 1 + 1), t j * chargeFn38 m j u) ∂(nuWN38 c N) :=
          integral_const_mul _ _
      _ ≤ M := mul_le_mul_of_nonneg_left hC hK.le
  have hr : (0 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcont : Continuous (fun y : SobolevCarrier38 ((m - 1 : ℕ) : ℝ) =>
      F (physOfCarrier38 ((m - 1 : ℕ) : ℝ) hr y)) := by
    simp only [hFdef]
    exact continuous_finsetProd _ fun i _ =>
      (continuous_signedChargeFn_physOfCarrier38 m (kk i) hm (hkk i)).pow _
  have hweak : ∀ H : ℝ → ℝ, Continuous H → (∃ Bd : ℝ, ∀ t, |H t| ≤ Bd) →
      Tendsto (fun N : ℕ => ∫ u, H (F u) ∂(nuWN38 c N)) atTop (𝓝 (∫ u, H (F u) ∂(B.muW38 c.val))) := by
    intro H hH ⟨Bd, hBd⟩
    exact B.weak_Sobolev38 O c hs hs' _ hr (fun u => H (F u)) (hH.comp hcont)
      ⟨Bd, fun y => hBd _⟩
  obtain ⟨hFμ, hFν, hlim⟩ := tendsto_integral_signed38 (nuWN38 c) (B.muW38 c.val)
    (fun N => inferInstance) F hFmeas M hsq hweak
  exact ⟨hFν, hFμ, hlim⟩

include B O in
/-- "All finite moments of each signed local charge" (`n = 1` of `signedMoments_38`). -/
theorem signedMoment_single_38 (m : ℕ) (hm : 2 ≤ m) (k : ℕ) (hk : k ≤ 2 * m - 2) (p : ℕ) :
    (∀ N : ℕ, Integrable (fun u => signedChargeFn38 m k u ^ p) (nuWN38 c N)) ∧
      Integrable (fun u => signedChargeFn38 m k u ^ p) (B.muW38 c.val) ∧
      Tendsto (fun N : ℕ => ∫ u, signedChargeFn38 m k u ^ p ∂(nuWN38 c N)) atTop
        (𝓝 (∫ u, signedChargeFn38 m k u ^ p ∂(B.muW38 c.val))) := by
  have h := B.signedMoments_38 O c m hm 1 (fun _ => k) (fun _ => hk) (fun _ => p)
  simpa using h

include B O in
/-- **SIGNED-MOMENTS.01 (identification under `μ_W`).** For `2 ≤ m`, `k ≤ 2m-2`, `μ_W`-a.e. field `u` has
`C_k(u) = (2/π)∫(2λ)^k v(λ;u) dλ`, the signed spectral moment (`C_{2j} = Q_{2j}`, odd `k` included). -/
theorem signedChargeFn_ae_spectral_38 (m : ℕ) (hm : 2 ≤ m) (k : ℕ) (hk : k ≤ 2 * m - 2) :
    ∀ᵐ u : PhysicalL2 ∂(B.muW38 c.val), signedChargeFn38 m k u = signedSpectralMoment38 u k := by
  have hlower := c.property.1
  filter_upwards [B.ae_muW38_allSobolev lower upper c.val hlower (fun j => (c.property.2.2 j).1)
    (fun j => (c.property.2.2 j).2)] with u hu
  obtain ⟨U, hU, hper, hUu⟩ := exists_smooth_rep38 u hu
  exact signedChargeFn38_smooth m k hm hk u hu U hU hper hUu

end BirkhoffInput38

end NlsGge.Birkhoff
end
