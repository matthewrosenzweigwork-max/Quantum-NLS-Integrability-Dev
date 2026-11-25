import Armstrong.Work.RawBetaSum

/-!
# Literal source-beta series transport

SPECULATIVE_PARENT_UNACCEPTED: parent 7858dda4, candidate beta-series 5a5852ac.
This module identifies the working sum with the literal same-W/F source sum,
then transports the existing four scoped series outputs. It proves no new
convergence estimate and makes no full Theorem 15.3 or Cartesian-map claim.
-/
set_option autoImplicit false
open Set Metric Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem gk151BetaSum_eq_source_tsum38
    (W : Set PotPair) (hWopen : IsOpen W)
    (hreal : range realSlice ⊆ W) (hWgk : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W)
    (hFn : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      p2Fn38 n (phi, F n phi) = 0)
    (hperiod : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W → ∀ m : ℤ,
      abelianPeriod38 m phi (p6PsiNumerator38 n (F n) phi) =
        if m = n then 2 * (Real.pi : ℂ) else 0)
    (n : ℤ) (phi : {psi : PotPair // psi ∈ W}) :
    gk151BetaSum38 W hWopen hreal hWgk F
      hFanalytic hFn hperiod n phi.1 =
      ∑' m : P2Index38 n,
        gkSourceBeta38 W hWopen hreal hWgk F
          hFanalytic hFn hperiod n m.1 m.2 phi := by
  have hdiag : gk151BetaAmbient38 W hWopen hreal hWgk F
      hFanalytic hFn hperiod n n phi.1 = 0 :=
    congrFun (gk151BetaAmbient_diag38 W hWopen hreal hWgk F
      hFanalytic hFn hperiod n) phi.1
  have hsupp : Function.support
      (fun m : ℤ => gk151BetaAmbient38 W hWopen hreal hWgk F
        hFanalytic hFn hperiod n m phi.1) ⊆ {m : ℤ | m ≠ n} := by
    intro m hm hmn
    subst m
    exact hm hdiag
  change (∑' m : ℤ, gk151BetaAmbient38 W hWopen hreal hWgk F
    hFanalytic hFn hperiod n m phi.1) = _
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  apply tsum_congr
  intro m
  exact gk151BetaAmbient_eq_source38 W hWopen hreal hWgk F
    hFanalytic hFn hperiod n m.1 m.2 phi

/-- Remove one identically zero mode from the finite-subset net. This is only
an index transport; no convergence estimate is introduced. -/
private theorem gk151_hasSumLocallyUniformlyOn_omit_zero38
    {X : Type*} [TopologicalSpace X] (n : ℤ)
    (f : ℤ → X → ℂ) (g : X → ℂ) (U : Set X)
    (hzero : f n = 0) (h : HasSumLocallyUniformlyOn f g U) :
    HasSumLocallyUniformlyOn (fun m : P2Index38 n => f m.1) g U := by
  classical
  intro e he x hx
  obtain ⟨V, hV, hs⟩ := h e he x hx
  obtain ⟨s, hs⟩ := eventually_atTop.mp hs
  let s0 : Finset (P2Index38 n) :=
    s.preimage Subtype.val Subtype.val_injective.injOn
  refine ⟨V, hV, eventually_atTop.mpr ⟨s0, ?_⟩⟩
  intro t ht y hy
  let emb : P2Index38 n ↪ ℤ := ⟨Subtype.val, Subtype.val_injective⟩
  let t0 : Finset ℤ := insert n (t.map emb)
  have hst : s ⊆ t0 := by
    intro k hk
    by_cases hkn : k = n
    · subst k
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_map.mpr ⟨⟨k, hkn⟩,
        ht (Finset.mem_preimage.mpr hk), rfl⟩
  have hn : n ∉ t.map emb := by
    intro hn
    obtain ⟨k, _hk, hkn⟩ := Finset.mem_map.mp hn
    exact k.2 hkn
  have heq : (∑ k ∈ t0, f k y) = ∑ k ∈ t, f k.1 y := by
    dsimp only [t0]
    rw [Finset.sum_insert hn, Finset.sum_map]
    change f n y + (∑ k ∈ t, f k.1 y) = _
    simp only [hzero, Pi.zero_apply, zero_add]
  have hh := hs t0 hst y hy
  change (g y, ∑ k ∈ t0, f k y) ∈ e at hh
  change (g y, ∑ k ∈ t, f k.1 y) ∈ e
  rw [heq] at hh
  exact hh

theorem gk151_source_beta_series38
    (W : Set PotPair) (hWopen : IsOpen W)
    (hreal : range realSlice ⊆ W) (hWgk : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W)
    (hFn : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      p2Fn38 n (phi, F n phi) = 0)
    (hFinv : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      (fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (phi,y))
        (F n phi)).IsInvertible)
    (hperiod : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W → ∀ m : ℤ,
      abelianPeriod38 m phi (p6PsiNumerator38 n (F n) phi) =
        if m = n then 2 * (Real.pi : ℂ) else 0)
    (hFreal : ∀ (n : ℤ) (u : PhysicalL2), ∃ t : P3RealSpace38 n,
      t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t = 0 ∧
        F n (realSlice u) = p3RealInclude38 n t) :
    ∃ Wbeta : Set PotPair,
      IsOpen Wbeta ∧ range realSlice ⊆ Wbeta ∧ Wbeta ⊆ W ∧
      (∀ n : ℤ, ∀ phi : {psi : PotPair // psi ∈ W}, phi.1 ∈ Wbeta →
        Summable (fun m : P2Index38 n =>
          ‖gkSourceBeta38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n m.1 m.2 phi‖)) ∧
      (∀ n : ℤ,
        HasSumLocallyUniformlyOn
          (fun (m : P2Index38 n) (phi : {psi : PotPair // psi ∈ W}) =>
            gkSourceBeta38 W hWopen hreal hWgk F
              hFanalytic hFn hperiod n m.1 m.2 phi)
          (fun phi : {psi : PotPair // psi ∈ W} =>
            ∑' m : P2Index38 n,
              gkSourceBeta38 W hWopen hreal hWgk F
                hFanalytic hFn hperiod n m.1 m.2 phi)
          {phi : {psi : PotPair // psi ∈ W} | phi.1 ∈ Wbeta}) ∧
      (∃ B : ℤ → PotPair → ℂ,
        (∀ n : ℤ, AnalyticOnNhd ℂ (B n) Wbeta) ∧
        ∀ n : ℤ, ∀ phi : {psi : PotPair // psi ∈ W}, phi.1 ∈ Wbeta →
          B n phi.1 =
            ∑' m : P2Index38 n,
              gkSourceBeta38 W hWopen hreal hWgk F
                hFanalytic hFn hperiod n m.1 m.2 phi) ∧
      (∀ phi : {psi : PotPair // psi ∈ W}, phi.1 ∈ Wbeta →
        Tendsto
          (fun n : ℤ =>
            ∑' m : P2Index38 n,
              gkSourceBeta38 W hWopen hreal hWgk F
                hFanalytic hFn hperiod n m.1 m.2 phi)
          cofinite (𝓝 (0 : ℂ))) := by
  obtain ⟨Wbeta, hWbetaOpen, hrealBeta, hbetaW, hsum, hunif, hanalytic, hdecay⟩ :=
    gk151_beta_series38 W hWopen hreal hWgk F
      hFanalytic hFn hFinv hperiod hFreal
  refine ⟨Wbeta, hWbetaOpen, hrealBeta, hbetaW, ?_, ?_, ?_, ?_⟩
  · intro n phi hphi
    have hsub := (hsum n phi.1 hphi).subtype (fun m : ℤ => m ≠ n)
    exact hsub.congr (fun m => congrArg norm
      (gk151BetaAmbient_eq_source38 W hWopen hreal hWgk F
        hFanalytic hFn hperiod n m.1 m.2 phi))
  · intro n
    have hpull := (hunif n).comp
      (fun phi : {psi : PotPair // psi ∈ W} => phi.1)
      (t := {phi : {psi : PotPair // psi ∈ W} | phi.1 ∈ Wbeta})
      (fun phi hphi => hphi) continuous_subtype_val.continuousOn
    have hzero : (fun phi : {psi : PotPair // psi ∈ W} =>
        gk151BetaAmbient38 W hWopen hreal hWgk F
          hFanalytic hFn hperiod n n phi.1) = 0 := by
      funext phi
      exact congrFun (gk151BetaAmbient_diag38 W hWopen hreal hWgk F
        hFanalytic hFn hperiod n) phi.1
    have hremoved := gk151_hasSumLocallyUniformlyOn_omit_zero38 n
      (fun m (phi : {psi : PotPair // psi ∈ W}) =>
        gk151BetaAmbient38 W hWopen hreal hWgk F
          hFanalytic hFn hperiod n m phi.1)
      (fun phi : {psi : PotPair // psi ∈ W} =>
        gk151BetaSum38 W hWopen hreal hWgk F
          hFanalytic hFn hperiod n phi.1)
      {phi : {psi : PotPair // psi ∈ W} | phi.1 ∈ Wbeta} hzero hpull
    have hsource : HasSumLocallyUniformlyOn
        (fun (m : P2Index38 n) (phi : {psi : PotPair // psi ∈ W}) =>
          gkSourceBeta38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n m.1 m.2 phi)
        (fun phi : {psi : PotPair // psi ∈ W} =>
          gk151BetaSum38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n phi.1)
        {phi : {psi : PotPair // psi ∈ W} | phi.1 ∈ Wbeta} :=
      hremoved.congr (fun s phi _hphi =>
        Finset.sum_congr rfl (fun m _hm =>
          gk151BetaAmbient_eq_source38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n m.1 m.2 phi))
    exact hsource.congr_right (fun phi _hphi =>
      gk151BetaSum_eq_source_tsum38 W hWopen hreal hWgk F
        hFanalytic hFn hperiod n phi)
  · refine ⟨gk151BetaSum38 W hWopen hreal hWgk F
      hFanalytic hFn hperiod, hanalytic, ?_⟩
    intro n phi _hphi
    exact gk151BetaSum_eq_source_tsum38 W hWopen hreal hWgk F
      hFanalytic hFn hperiod n phi
  · intro phi hphi
    have heq : (fun n : ℤ => ∑' m : P2Index38 n,
        gkSourceBeta38 W hWopen hreal hWgk F
          hFanalytic hFn hperiod n m.1 m.2 phi) =
        (fun n : ℤ => gk151BetaSum38 W hWopen hreal hWgk F
          hFanalytic hFn hperiod n phi.1) := by
      funext n
      exact (gk151BetaSum_eq_source_tsum38 W hWopen hreal hWgk F
        hFanalytic hFn hperiod n phi).symm
    rw [heq]
    exact hdecay phi.1 hphi

end
end NlsGge.GK38
