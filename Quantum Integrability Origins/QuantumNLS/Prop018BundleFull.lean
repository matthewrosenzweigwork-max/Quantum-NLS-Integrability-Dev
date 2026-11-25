import QuantumNLS.Prop017MovingContour

/-!
# PROP-018 moving-contour bundle, FULL version: the same bundle, additionally exporting the all-`p` probability bound for the SAME packet radius `ρ`

Terra/integrator (Prop020 rate): `Prop018Bundle.moving_contour_bundle` builds the eventual `propBound` estimate and discards it. This NEW module re-runs the identical proof
and keeps it: for the chosen `ρ`, every `p ≥ 1` has `P_{N,u}(𝓔_N^c) ≤ propBound (C_p) (D_p) (C_b) p N R_N a_N ε_N` eventually. (Original bundle docstring follows.)

# (original) PROP-018 (`Q7A:prop:reconstruct`): the moving-contour bundle with one common packet radius

Source: `window_reconstruction.tex`, proof of `Q7A:prop:packet` and of `Q7A:prop:reconstruct`. The reconstruction proof uses, on
the same event `𝓔_N` and the same contour neighbourhood, simultaneously:
* the local expansion `ℓ_N = log a_N − (iκ/N) e a_N'/(a_N(a_N² − e)) + O(N^{−2})` (`Q7A:eq:twoterm`),
* "all roots lie within the large contour" (`Q7A:eq:allroots`, `R ≤ a/2`),
* the resolvent comparison `eq:Gneighbor`, the common root distance, and the uniform bounds for `G, e, A^{±1}, D`.

`Prop017MovingContour.moving_contour_uniform` (frozen, M2) exports only the first item, with an existential radius `ρ`.
**`moving_contour_bundle`** re-runs the same proof (verbatim, from `prop017_physical` and `haar_core_bdd`) and exports all of
these facts for one common `ρ`, which the period reconstruction needs.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Complex
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.Prop018BundleFull

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.RootMeasureConcentrationSharp (Csharp)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis IsLimitingRapidityMeasure)
open QuantumNLS.Extrapolation (Gfull GN)
open QuantumNLS.RootEvent (EN prop017Cb)
open QuantumNLS.ResolventNeighborhood (GammaN NbhdN rNbhd KGN nbhd_dist norm_Gfull_le Gfull_hasDerivAt_of_dist sNsrc sLimsrc)
open QuantumNLS.NonvanishingD (Dsrc)
open QuantumNLS.PROP017UniformN (cutSeq)
open QuantumNLS.PROP018Probability (cutN cutIdx propBound regime_eventually tendsto_of_bound)
open QuantumNLS.Prop017Quantum (qAct eta0 eta0_pos Ctail Dtail)
open QuantumNLS.Prop017Physical (RootSpectralInputs prop017_physical)
open QuantumNLS.PeriodReconstructionCore QuantumNLS.PeriodTwoTerm QuantumNLS.HaarSummableCore
open QuantumNLS.Prop017MovingContour (nbhd_mono ball_nbhd Df_eq_Dsrc Idx)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- **The moving-contour bundle** (one common packet radius `ρ`): the probability statement and the local expansion of
`moving_contour_uniform`, together with the root window `|q_j| ≤ N^θ`, `eq:Gneighbor`, the common root distance `r`, the
differentiability of `G_μ`, and the bounds `|D| ≥ η`, `|A^{±1}|, |e| ≤ M`, all on the `ρ/8`-neighbourhood of `Γ_N`. -/
theorem moving_contour_bundle_full (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc)
    (θ γ : ℝ) (hθ : 0 < θ) (hγ : 0 < γ) (hsum : 3 * γ + θ < 1) (p : ℕ) (hp : 1 < 2 * (p : ℝ) * θ) :
    ∃ ρ : ℝ, 0 < ρ ∧ 2 * ρ < h ∧
      Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real
        (EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h (eta0 L κ) ((N : ℝ) ^ (-γ)) b)ᶜ)
        atTop (𝓝 0) ∧
      (∀ p' : ℕ, 1 ≤ p' → ∀ᶠ N : ℕ in atTop,
        (bornMeasure (physBasis L hκ N) u hu).real
            (EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h (eta0 L κ) ((N : ℝ) ^ (-γ)) b)ᶜ ≤
          propBound (Ctail (μ : Measure ℝ) p') (Dtail κ p') (prop017Cb (eta0 L κ) h ρ Csharp b) p' (N : ℝ)
            ((N : ℝ) ^ θ) (cutN L θ N) ((N : ℝ) ^ (-γ))) ∧
      ∃ C M η r K Kd : ℝ, 1 ≤ M ∧ 0 < η ∧ 0 < r ∧ 0 ≤ K ∧
        ∀ᶠ N : ℕ in atTop, ∀ m ∈ EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h (eta0 L κ)
          ((N : ℝ) ^ (-γ)) b, ∀ z ∈ NbhdN (cutN L θ N) h (ρ / 8),
          ((∀ j, 2 * |κ / (N : ℝ)| < ‖z - (qAct L κ N m j : ℂ)‖) ∧
          ‖Wf L κ (κ / N) (Gfull (μ : Measure ℝ)) (qAct L κ N m) z‖ ≤ 1 / 2 ∧
          1 / (2 * M) ≤ ‖aNf L κ (κ / N) (Gfull (μ : Measure ℝ)) (qAct L κ N m) z‖ ∧
          3 * η / 4 ≤ ‖DNf L κ (κ / N) (Gfull (μ : Measure ℝ)) (qAct L κ N m) z‖ ∧
          ‖aNf L κ (κ / N) (Gfull (μ : Measure ℝ)) (qAct L κ N m) z - Af κ (Gfull (μ : Measure ℝ)) z‖ ≤
            1 / (2 * M) ∧
          ‖ellf (κ / N) (qAct L κ N m) z - logaNf L κ (κ / N) (Gfull (μ : Measure ℝ)) (qAct L κ N m) z +
              I * κ / (N : ℂ) * corrf L κ (κ / N) (Gfull (μ : Measure ℝ)) (qAct L κ N m) z‖ ≤
            C / (N : ℝ) ^ 2) ∧
          (∀ j, |qAct L κ N m j| ≤ (N : ℝ) ^ θ) ∧
          ‖Gfull (μ : Measure ℝ) z - GN (qAct L κ N m) z‖ ≤ K * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b) ∧
          (∀ j, r ≤ ‖z - (qAct L κ N m j : ℂ)‖) ∧
          DifferentiableAt ℂ (Gfull (μ : Measure ℝ)) z ∧
          η ≤ ‖Df L κ (Gfull (μ : Measure ℝ)) z‖ ∧
          ‖Af κ (Gfull (μ : Measure ℝ)) z‖ ≤ M ∧ ‖(Af κ (Gfull (μ : Measure ℝ)) z)⁻¹‖ ≤ M ∧
          ‖ef L z‖ ≤ M ∧
          ∀ n : ℕ, ‖iteratedDeriv n (fun w => sNsrc κ L (qAct L κ N m) w - sLimsrc κ L (μ : Measure ℝ) w) z‖ ≤
            n.factorial * (Kd * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b + 1 / (N : ℝ))) / (ρ / 2) ^ n := by
  have hL : 0 < L := Fact.out
  obtain ⟨ρ, hρ0, R0, hR01, r, hr0, hrad, N0, hfam⟩ :=
    prop017_physical hκ u hu hμ hηh hδ hd0 hin b pc hb hbpc
  have hCms : 0 ≤ Csharp := by
    unfold Csharp; have := QuantumNLS.RootMeasureConcentrationSharp.Kc_nonneg; linarith
  have hCb : 0 ≤ prop017Cb (eta0 L κ) h ρ Csharp b := QuantumNLS.PROP017UniformN.prop017Cb_nonneg hρ0 hCms
  have hp1 : 1 ≤ p := by
    by_contra hcon
    have h0 : p = 0 := by omega
    subst h0
    norm_num at hp
  have hmainAll : ∀ p' : ℕ, 1 ≤ p' → ∀ᶠ N : ℕ in atTop,
      (bornMeasure (physBasis L hκ N) u hu).real
          (EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h (eta0 L κ) ((N : ℝ) ^ (-γ)) b)ᶜ ≤
        propBound (Ctail (μ : Measure ℝ) p') (Dtail κ p') (prop017Cb (eta0 L κ) h ρ Csharp b) p' (N : ℝ)
          ((N : ℝ) ^ θ) (cutN L θ N) ((N : ℝ) ^ (-γ)) := by
    intro p' hp1'
    filter_upwards [regime_eventually hL hθ hγ (max R0 (eta0 L κ)) l0, eventually_ge_atTop N0,
      eventually_ge_atTop 1] with N hreg hN0 hN1
    have hle := hfam ((N : ℝ) ^ (-γ)) hreg.2.2.2.1 hreg.2.2.2.2 N hN0 hN1 ((N : ℝ) ^ θ)
      (le_trans (le_max_left _ _) hreg.1) (cutIdx L θ N) hreg.2.1 (cutN L θ N) rfl hreg.2.2.1
    refine (hle.1 p' hp1' (le_trans (le_max_right _ _) hreg.1)).trans (le_of_eq ?_)
    unfold propBound; ring
  have hprob : Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real
        (EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h (eta0 L κ) ((N : ℝ) ^ (-γ)) b)ᶜ)
        atTop (𝓝 0) :=
    tendsto_of_bound hL hθ hγ hsum p hp (Ctail (μ : Measure ℝ) p) (Dtail κ p)
      (prop017Cb (eta0 L κ) h ρ Csharp b) hCb _ (Eventually.of_forall fun N => measureReal_nonneg) (hmainAll p hp1)
  -- the uniform local expansion
  set KG : ℝ := 2 * KGN (eta0 L κ) δ ρ (h + 5) Csharp b pc (μ : Measure ℝ) with hKG
  set M : ℝ := max 1 (max (Real.exp (κ / r)) (Real.exp (L * (h + 2 * ρ)))) with hMdef
  have hM1 : 1 ≤ M := le_max_left _ _
  set η : ℝ := d0 / 2 with hηdef
  have hη : 0 < η := by positivity
  set K : ℝ := (r ^ 2)⁻¹ + (r ^ 3)⁻¹ with hKdef
  have hK : 0 ≤ K := by positivity
  set S : Set Idx := {i | i.2.1 ∈ EN (μ : Measure ℝ) (qAct L κ (i.1 + 1)) (((i.1 + 1 : ℕ) : ℝ) ^ θ)
      (cutN L θ (i.1 + 1)) ρ h (eta0 L κ) (((i.1 + 1 : ℕ) : ℝ) ^ (-γ)) b ∧
      i.2.2 ∈ NbhdN (cutN L θ (i.1 + 1)) h (ρ / 8)} with hSdef
  set l : Filter Idx := comap (fun i : Idx => i.1) atTop ⊓ 𝓟 S with hldef
  have hk : Tendsto (fun i : Idx => i.1) l atTop := tendsto_comap.mono_left inf_le_left
  have hNt : Tendsto (fun i : Idx => i.1 + 1) l atTop := (tendsto_add_atTop_nat 1).comp hk
  have hSev : ∀ᶠ i in l, i ∈ S := mem_inf_of_right (mem_principal_self S)
  -- the regime and the event facts, eventually along `l`
  have hregN := regime_eventually hL hθ hγ R0 l0
  have hgood : ∀ᶠ i in l,
      (∀ j, |qAct L κ (i.1 + 1) i.2.1 j| ≤ ((i.1 + 1 : ℕ) : ℝ) ^ θ) ∧
      (∀ z ∈ NbhdN (cutN L θ (i.1 + 1)) h ρ, ‖Gfull (μ : Measure ℝ) z - GN (qAct L κ (i.1 + 1) i.2.1) z‖ ≤
        KG * (((i.1 + 1 : ℕ) : ℝ) ^ (-γ) + 1 / (((i.1 + 1 : ℕ) : ℝ) ^ θ) ^ b)) ∧
      (∀ z ∈ NbhdN (cutN L θ (i.1 + 1)) h (ρ / 4), d0 / 2 ≤ ‖Dsrc κ L (μ : Measure ℝ) z‖) ∧
      r ≤ rNbhd (cutN L θ (i.1 + 1)) h ρ (((i.1 + 1 : ℕ) : ℝ) ^ θ) δ ∧
      0 < cutN L θ (i.1 + 1) ∧
      (∀ᵐ (x : ℝ) ∂(μ : Measure ℝ), δ ≤ |x - cutN L θ (i.1 + 1)| ∧ δ ≤ |x + cutN L θ (i.1 + 1)|) ∧
      i.2.2 ∈ NbhdN (cutN L θ (i.1 + 1)) h (ρ / 8) := by
    filter_upwards [hSev, hNt.eventually hregN, hNt.eventually (eventually_ge_atTop N0)] with i hi hreg hN0
    have hle := hfam (((i.1 + 1 : ℕ) : ℝ) ^ (-γ)) hreg.2.2.2.1 hreg.2.2.2.2 (i.1 + 1) hN0 (by omega)
      (((i.1 + 1 : ℕ) : ℝ) ^ θ) hreg.1 (cutIdx L θ (i.1 + 1)) hreg.2.1 (cutN L θ (i.1 + 1)) rfl hreg.2.2.1
    obtain ⟨-, hev, hD⟩ := hle
    have hRpos : 0 < ((i.1 + 1 : ℕ) : ℝ) ^ θ := Real.rpow_pos_of_pos (by positivity) θ
    refine ⟨(hev i.2.1 hi.1).1, (hev i.2.1 hi.1).2.1, hD, hrad _ hreg.1 _ hreg.2.2.1,
      by linarith [hreg.2.2.1], ?_, hi.2⟩
    exact hin.gap _ hreg.2.1
  -- the derivative estimate `eq:derivative` of `prop017_physical`, on the same event
  set Kd : ℝ := Real.exp (|κ| / r) * (1 + Real.exp (|L| * (h + 2 * ρ))) *
    max (κ ^ 2 / r ^ 2) (|κ| * KG) with hKd
  have hder : ∀ᶠ i in l, ∀ n : ℕ,
      ‖iteratedDeriv n (fun w => sNsrc κ L (qAct L κ (i.1 + 1) i.2.1) w - sLimsrc κ L (μ : Measure ℝ) w) i.2.2‖ ≤
        n.factorial * (Kd * (((i.1 + 1 : ℕ) : ℝ) ^ (-γ) + 1 / (((i.1 + 1 : ℕ) : ℝ) ^ θ) ^ b +
          1 / ((i.1 + 1 : ℕ) : ℝ))) / (ρ / 2) ^ n := by
    filter_upwards [hSev, hNt.eventually hregN, hNt.eventually (eventually_ge_atTop N0)] with i hi hreg hN0
    have hle := hfam (((i.1 + 1 : ℕ) : ℝ) ^ (-γ)) hreg.2.2.2.1 hreg.2.2.2.2 (i.1 + 1) hN0 (by omega)
      (((i.1 + 1 : ℕ) : ℝ) ^ θ) hreg.1 (cutIdx L θ (i.1 + 1)) hreg.2.1 (cutN L θ (i.1 + 1)) rfl hreg.2.2.1
    obtain ⟨-, hev, -⟩ := hle
    intro n
    have := (hev i.2.1 hi.1).2.2 i.2.2 (nbhd_mono (by linarith) hi.2) n
    refine this.trans (le_of_eq ?_)
    rw [hKd, hKG]
  -- distances on the event
  have hdist : ∀ᶠ i in l, (∀ᵐ (x : ℝ) ∂(μ : Measure ℝ), r ≤ ‖i.2.2 - (x : ℂ)‖) ∧
      (∀ j, r ≤ ‖i.2.2 - (qAct L κ (i.1 + 1) i.2.1 j : ℂ)‖) ∧ |i.2.2.im| ≤ h + 2 * ρ := by
    filter_upwards [hgood] with i hg
    obtain ⟨hroots, -, -, hr, ha, hgap, hz⟩ := hg
    have hb0 : 0 < h - 2 * ρ := lt_of_lt_of_le hr0 (hr.trans (min_le_left _ _))
    have hnd := nbhd_dist (qAct L κ (i.1 + 1) i.2.1) (μ : Measure ℝ) (R := ((i.1 + 1 : ℕ) : ℝ) ^ θ) ha hρ0 hb0
      (hgap.mono fun x hx => hx.1) (hgap.mono fun x hx => hx.2) (nbhd_mono (by linarith) hz)
    exact ⟨hnd.1.mono fun x hx => hr.trans hx, fun j => hr.trans (hnd.2.1 j (hroots j)), hnd.2.2⟩
  -- the hypotheses of `haar_core_bdd`
  have hνt : Tendsto (fun i : Idx => (((i.1 + 1 : ℕ) : ℝ))⁻¹) l (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop : Tendsto (Nat.cast : ℕ → ℝ) atTop atTop).comp hNt)
  have hroot : ∀ᶠ i in l, ∀ j, r ≤ ‖i.2.2 - (qAct L κ (i.1 + 1) i.2.1 j : ℂ)‖ :=
    hdist.mono fun i h => h.2.1
  have hmom : ∀ s : ℕ, ∀ᶠ i in l, (((i.1 + 1 : ℕ) : ℝ))⁻¹ *
      ∑ j, (‖i.2.2 - (qAct L κ (i.1 + 1) i.2.1 j : ℂ)‖ ^ s)⁻¹ ≤ (r ^ s)⁻¹ := by
    intro s
    filter_upwards [hroot] with i hi
    have hNr : (0 : ℝ) < ((i.1 + 1 : ℕ) : ℝ) := by positivity
    calc (((i.1 + 1 : ℕ) : ℝ))⁻¹ * ∑ j, (‖i.2.2 - (qAct L κ (i.1 + 1) i.2.1 j : ℂ)‖ ^ s)⁻¹
        ≤ (((i.1 + 1 : ℕ) : ℝ))⁻¹ * ∑ _j : Fin (i.1 + 1), (r ^ s)⁻¹ := by
          gcongr with j
          exact hi j
      _ = (r ^ s)⁻¹ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
            inv_mul_cancel₀ hNr.ne', one_mul]
  have hm2 : ∀ᶠ i in l, (((i.1 + 1 : ℕ) : ℝ))⁻¹ *
      ∑ j, (‖i.2.2 - (qAct L κ (i.1 + 1) i.2.1 j : ℂ)‖ ^ 2)⁻¹ ≤ K * (fun _ : Idx => (1 : ℝ)) i ^ 2 :=
    (hmom 2).mono fun i h => h.trans (by simp only [one_pow, mul_one, hKdef]; linarith [inv_nonneg.2 (pow_nonneg hr0.le 3)])
  have hm3 : ∀ᶠ i in l, (((i.1 + 1 : ℕ) : ℝ))⁻¹ *
      ∑ j, (‖i.2.2 - (qAct L κ (i.1 + 1) i.2.1 j : ℂ)‖ ^ 3)⁻¹ ≤ K * (fun _ : Idx => (1 : ℝ)) i ^ 2 :=
    (hmom 3).mono fun i h => h.trans (by simp only [one_pow, mul_one, hKdef]; linarith [inv_nonneg.2 (pow_nonneg hr0.le 2)])
  have hU : Tendsto (fun i : Idx => (∑ j, I * ((κ / ((i.1 + 1 : ℕ) : ℝ) : ℝ) : ℂ) /
      (i.2.2 - (qAct L κ (i.1 + 1) i.2.1 j : ℂ))) - I * κ * Gfull (μ : Measure ℝ) i.2.2) l (𝓝 0) := by
    have hb0 : b ≠ 0 := by omega
    have hε : Tendsto (fun N : ℕ => (N : ℝ) ^ (-γ)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hγ).comp tendsto_natCast_atTop_atTop
    have hR' : Tendsto (fun N : ℕ => (N : ℝ) ^ θ) atTop atTop :=
      (tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop
    have hRb : Tendsto (fun N : ℕ => 1 / ((N : ℝ) ^ θ) ^ b) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop hb0).comp hR')
    have hlim : Tendsto (fun N : ℕ => κ * (KG * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b))) atTop (𝓝 0) := by
      have := ((hε.add hRb).const_mul KG).const_mul κ
      simpa using this
    refine squeeze_zero_norm' ?_ (hlim.comp hNt)
    filter_upwards [hgood] with i hg
    have hz := nbhd_mono (show ρ / 8 ≤ ρ by linarith) hg.2.2.2.2.2.2
    have hG := hg.2.1 _ hz
    have hNr : (0 : ℝ) < ((i.1 + 1 : ℕ) : ℝ) := by positivity
    have e : (∑ j, I * ((κ / ((i.1 + 1 : ℕ) : ℝ) : ℝ) : ℂ) / (i.2.2 - (qAct L κ (i.1 + 1) i.2.1 j : ℂ))) -
        I * κ * Gfull (μ : Measure ℝ) i.2.2 =
        -(I * κ) * (Gfull (μ : Measure ℝ) i.2.2 - GN (qAct L κ (i.1 + 1) i.2.1) i.2.2) := by
      unfold GN
      rw [Finset.mul_sum]
      have hNc : ((((i.1 + 1 : ℕ) : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hNr.ne'
      have : ∀ j, I * ((κ / ((i.1 + 1 : ℕ) : ℝ) : ℝ) : ℂ) / (i.2.2 - (qAct L κ (i.1 + 1) i.2.1 j : ℂ)) =
          I * κ * (1 / (((i.1 + 1 : ℕ) : ℂ)) * (1 / (i.2.2 - (qAct L κ (i.1 + 1) i.2.1 j : ℂ)))) := fun j => by
        push_cast; ring
      simp_rw [this, ← Finset.mul_sum]
      ring
    rw [e, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hκ.le]
    exact mul_le_mul_of_nonneg_left hG hκ.le
  have hGd : ∀ᶠ i in l, DifferentiableAt ℂ (Gfull (μ : Measure ℝ)) i.2.2 :=
    hdist.mono fun i h => (Gfull_hasDerivAt_of_dist (μ : Measure ℝ) hr0 h.1).differentiableAt
  have hDev : ∀ᶠ i in l, ∀ᶠ w in 𝓝 i.2.2, Df L κ (Gfull (μ : Measure ℝ)) w ≠ 0 := by
    filter_upwards [hgood] with i hg
    filter_upwards [Metric.ball_mem_nhds i.2.2 (show 0 < ρ / 8 by positivity)] with w hw
    rw [Df_eq_Dsrc]
    intro h0
    have := hg.2.2.1 w (ball_nbhd hg.2.2.2.2.2.2 hw)
    rw [h0, norm_zero] at this; linarith
  have hMb : ∀ᶠ i in l, ‖Af κ (Gfull (μ : Measure ℝ)) i.2.2‖ ≤ M ∧
      ‖(Af κ (Gfull (μ : Measure ℝ)) i.2.2)⁻¹‖ ≤ M ∧ ‖ef L i.2.2‖ ≤ M ∧
      η ≤ ‖Df L κ (Gfull (μ : Measure ℝ)) i.2.2‖ := by
    filter_upwards [hgood, hdist] with i hg hd
    have hGb : ‖Gfull (μ : Measure ℝ) i.2.2‖ ≤ 1 / r := norm_Gfull_le _ _ hr0 hd.1
    have hx : ‖I * (κ : ℂ) * Gfull (μ : Measure ℝ) i.2.2‖ ≤ κ / r := by
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hκ.le]
      calc κ * ‖Gfull (μ : Measure ℝ) i.2.2‖ ≤ κ * (1 / r) := mul_le_mul_of_nonneg_left hGb hκ.le
        _ = κ / r := by ring
    have hexp : ‖exp (I * (κ : ℂ) * Gfull (μ : Measure ℝ) i.2.2)‖ ≤ Real.exp (κ / r) :=
      (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 hx)
    have hexp' : ‖(exp (I * (κ : ℂ) * Gfull (μ : Measure ℝ) i.2.2))⁻¹‖ ≤ Real.exp (κ / r) := by
      rw [← Complex.exp_neg]
      exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 (by rw [norm_neg]; exact hx))
    have hM2 : Real.exp (κ / r) ≤ M := (le_max_left _ _).trans (le_max_right _ _)
    have hM3 : Real.exp (L * (h + 2 * ρ)) ≤ M := (le_max_right _ _).trans (le_max_right _ _)
    refine ⟨hexp.trans hM2, hexp'.trans hM2, ?_, ?_⟩
    · rw [HaarSummableReconstruction.norm_ef_eq]
      refine (Real.exp_le_exp.2 ?_).trans hM3
      have := neg_abs_le i.2.2.im
      have h1 : -(L * i.2.2.im) ≤ L * |i.2.2.im| := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hd.2.2 hL.le]
    · rw [Df_eq_Dsrc]
      exact hg.2.2.1 _ (nbhd_mono (by linarith) hg.2.2.2.2.2.2)
  -- apply the bounded-θ core
  obtain ⟨hremO, -, hprops⟩ := QuantumNLS.HaarSummableCoreBdd.haar_core_bdd (ι := Idx) (l := l) (κ := κ) (L := L)
    (Nf := fun i => i.1 + 1) (qf := fun i => qAct L κ (i.1 + 1) i.2.1) (zf := fun i => i.2.2)
    (θ := fun _ => 1) (G := Gfull (μ : Measure ℝ)) hκ (fun i => Nat.succ_pos _) hνt (fun _ => zero_le_one)
    (Eventually.of_forall fun _ => le_rfl) hr0 hroot hK hm2 hm3 hU hGd hDev hM1 hη hMb
  obtain ⟨C, hC⟩ := hremO.bound
  have h2ρ : 2 * ρ < h := by
    have h1 := hrad R0 le_rfl (2 * R0) le_rfl
    have h2 : rNbhd (2 * R0) h ρ R0 δ ≤ h - 2 * ρ := min_le_left _ _
    linarith
  refine ⟨ρ, hρ0, h2ρ, hprob, hmainAll, max C 0, M, η, r, max KG 0, Kd, hM1, hη, hr0, le_max_right _ _, ?_⟩
  have hall := (hC.and hprops).and (hgood.and (hdist.and (hMb.and (hGd.and hder))))
  rw [hldef, eventually_inf_principal, eventually_comap, eventually_atTop] at hall
  obtain ⟨k0, hk0⟩ := hall
  filter_upwards [eventually_ge_atTop (k0 + 1)] with N hN m hm z hz
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  have hi := hk0 k (by omega) ⟨k, (m, z)⟩ rfl ⟨hm, hz⟩
  obtain ⟨⟨hrem, hpr⟩, hg, hd, hmb, hgd, hdr⟩ := hi
  have hNr : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  refine ⟨⟨hpr.1, hpr.2.1, hpr.2.2.1, hpr.2.2.2.1, hpr.2.2.2.2, ?_⟩, hg.1, ?_, hd.2.1, hgd, hmb.2.2.2,
    hmb.1, hmb.2.1, hmb.2.2.1, hdr⟩
  · refine hrem.trans ?_
    show C * ‖(((k + 1 : ℕ) : ℝ))⁻¹ * ((((k + 1 : ℕ) : ℝ))⁻¹ * 1 ^ 2)‖ ≤ _
    rw [one_pow, mul_one, Real.norm_of_nonneg (by positivity)]
    calc C * ((((k + 1 : ℕ) : ℝ))⁻¹ * (((k + 1 : ℕ) : ℝ))⁻¹)
        ≤ max C 0 * ((((k + 1 : ℕ) : ℝ))⁻¹ * (((k + 1 : ℕ) : ℝ))⁻¹) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = max C 0 / ((k + 1 : ℕ) : ℝ) ^ 2 := by field_simp
  · have hG := hg.2.1 z (nbhd_mono (by linarith) hz)
    rw [norm_sub_rev] at hG ⊢
    refine hG.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    have : 0 < (((k + 1 : ℕ) : ℝ)) ^ θ := Real.rpow_pos_of_pos hNr θ
    have : 0 < (((k + 1 : ℕ) : ℝ)) ^ (-γ) := Real.rpow_pos_of_pos hNr _
    positivity

end QuantumNLS.Prop018BundleFull

#print axioms QuantumNLS.Prop018BundleFull.moving_contour_bundle_full
