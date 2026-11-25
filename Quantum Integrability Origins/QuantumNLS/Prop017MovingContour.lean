import QuantumNLS.Prop017Physical
import QuantumNLS.HaarSummableCoreBdd
import QuantumNLS.HaarSummableReconstruction

/-!
# PROP-017 / PROP-018: moving-contour uniformity of the local reconstruction expansion (Terra r127 qualification)

Source: `window_reconstruction.tex`, proof of `Q7A:prop:reconstruct` (PROP-018): "Its proof is local on three nested contour
neighborhoods and uses only a common root distance, bounds on `G_N, G, e` and their derivatives, and a nonzero lower bound for `|D|`.
Proposition `Q7A:prop:packet` supplies all of those bounds independently of `a` on the moving contours. Consequently its remainder is
uniformly `O(N^{-2})` here."

**`moving_contour_uniform`**: for the actual model (`Prop017Physical.prop017_physical`, ε-indexed events, designated cuts) along
`R_N = N^θ`, `ε_N = N^{−γ}`, `a_N = cutN L θ N` (`θ, γ > 0`, `3γ + θ < 1`, `1 < 2pθ`), with the same packet radius `ρ`:
* `P_{N,u}(𝓔_N(ε_N)ᶜ) → 0`;
* there are `C, M ≥ 1, η > 0` such that eventually in `N`, for every label `m ∈ 𝓔_N(ε_N)` and every `z` in the `ρ/8`-neighbourhood
  of the moving contour `Γ_N`: the roots are at distance `> 2κ/N` from `z`, `|W| ≤ 1/2`, `|a_N| ≥ 1/(2M)`, `|D_N| ≥ 3η/4`,
  `|a_N − A| ≤ 1/(2M)`, and
  `|ℓ_N(z) − log a_N(z) + (iκ/N) e a_N'/(a_N(a_N² − e))| ≤ C/N²` (`eq:B3-log-reconstruction` / `Q7A:eq:twoterm` with `G = G_μ`).
  The constant `C` is independent of `N`, of the cut `a_N`, of the label and of `z`.

Route: `HaarSummableCoreBdd.haar_core_bdd` (θ ≡ 1) along the filter `comap N atTop ⊓ 𝓟{(N, m, z) : m ∈ 𝓔_N, z ∈ ρ/8-nbhd}`, with
the root distance `r` and support distance from `prop017_physical` (`ResolventNeighborhood.nbhd_dist`), uniform resolvent moments
`≤ r^{−s}`, `Σ ic/(z − q_j) − iκG(z) = iκ(G_N − G)(z) → 0` by `eq:Gneighbor`, `|D| ≥ d₀/2` on the `ρ/4`-neighbourhood, and
`|A^{±1}| ≤ e^{κ/r}`, `|e| ≤ e^{L(h+2ρ)}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Complex
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.Prop017MovingContour

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.RootMeasureConcentrationSharp (Csharp)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis IsLimitingRapidityMeasure)
open QuantumNLS.Extrapolation (Gfull GN)
open QuantumNLS.RootEvent (EN prop017Cb)
open QuantumNLS.ResolventNeighborhood (GammaN NbhdN rNbhd KGN nbhd_dist norm_Gfull_le Gfull_hasDerivAt_of_dist)
open QuantumNLS.NonvanishingD (Dsrc)
open QuantumNLS.PROP017UniformN (cutSeq)
open QuantumNLS.PROP018Probability (cutN cutIdx propBound regime_eventually tendsto_of_bound)
open QuantumNLS.Prop017Quantum (qAct eta0 eta0_pos Ctail Dtail)
open QuantumNLS.Prop017Physical (RootSpectralInputs prop017_physical)
open QuantumNLS.PeriodReconstructionCore QuantumNLS.PeriodTwoTerm QuantumNLS.HaarSummableCore

lemma nbhd_mono {a h ρ ρ' : ℝ} (hρ : ρ' ≤ ρ) {z : ℂ} (hz : z ∈ NbhdN a h ρ') : z ∈ NbhdN a h ρ := by
  obtain ⟨w, hw, hzw⟩ := hz
  exact ⟨w, hw, hzw.trans hρ⟩

lemma ball_nbhd {a h ρ : ℝ} {z w : ℂ} (hz : z ∈ NbhdN a h (ρ / 8)) (hw : w ∈ Metric.ball z (ρ / 8)) :
    w ∈ NbhdN a h (ρ / 4) := by
  obtain ⟨v, hv, hzv⟩ := hz
  refine ⟨v, hv, ?_⟩
  have h1 : ‖w - z‖ < ρ / 8 := by rwa [Metric.mem_ball, dist_eq_norm] at hw
  calc ‖w - v‖ = ‖(w - z) + (z - v)‖ := by ring_nf
    _ ≤ ‖w - z‖ + ‖z - v‖ := norm_add_le _ _
    _ ≤ ρ / 4 := by linarith

lemma Df_eq_Dsrc (L κ : ℝ) (μ : Measure ℝ) (w : ℂ) : Df L κ (Gfull μ) w = Dsrc κ L μ w := rfl

/-- The index: a label at `N = k + 1` and a contour point. -/
abbrev Idx := Σ k : ℕ, MArr (k + 1) × ℂ

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- **Moving-contour uniformity of the local reconstruction expansion** (r127). -/
theorem moving_contour_uniform (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc)
    (θ γ : ℝ) (hθ : 0 < θ) (hγ : 0 < γ) (hsum : 3 * γ + θ < 1) (p : ℕ) (hp : 1 < 2 * (p : ℝ) * θ) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real
        (EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h (eta0 L κ) ((N : ℝ) ^ (-γ)) b)ᶜ)
        atTop (𝓝 0) ∧
      ∃ C M η : ℝ, 1 ≤ M ∧ 0 < η ∧
        ∀ᶠ N : ℕ in atTop, ∀ m ∈ EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h (eta0 L κ)
          ((N : ℝ) ^ (-γ)) b, ∀ z ∈ NbhdN (cutN L θ N) h (ρ / 8),
          (∀ j, 2 * |κ / (N : ℝ)| < ‖z - (qAct L κ N m j : ℂ)‖) ∧
          ‖Wf L κ (κ / N) (Gfull (μ : Measure ℝ)) (qAct L κ N m) z‖ ≤ 1 / 2 ∧
          1 / (2 * M) ≤ ‖aNf L κ (κ / N) (Gfull (μ : Measure ℝ)) (qAct L κ N m) z‖ ∧
          3 * η / 4 ≤ ‖DNf L κ (κ / N) (Gfull (μ : Measure ℝ)) (qAct L κ N m) z‖ ∧
          ‖aNf L κ (κ / N) (Gfull (μ : Measure ℝ)) (qAct L κ N m) z - Af κ (Gfull (μ : Measure ℝ)) z‖ ≤
            1 / (2 * M) ∧
          ‖ellf (κ / N) (qAct L κ N m) z - logaNf L κ (κ / N) (Gfull (μ : Measure ℝ)) (qAct L κ N m) z +
              I * κ / (N : ℂ) * corrf L κ (κ / N) (Gfull (μ : Measure ℝ)) (qAct L κ N m) z‖ ≤
            C / (N : ℝ) ^ 2 := by
  have hL : 0 < L := Fact.out
  obtain ⟨ρ, hρ0, R0, hR01, r, hr0, hrad, N0, hfam⟩ :=
    prop017_physical hκ u hu hμ hηh hδ hd0 hin b pc hb hbpc
  refine ⟨ρ, hρ0, ?_, ?_⟩
  · -- the probability (as in `prop017_physical_diagonal`, with the same `ρ`)
    have hCms : 0 ≤ Csharp := by
      unfold Csharp; have := QuantumNLS.RootMeasureConcentrationSharp.Kc_nonneg; linarith
    have hCb : 0 ≤ prop017Cb (eta0 L κ) h ρ Csharp b := QuantumNLS.PROP017UniformN.prop017Cb_nonneg hρ0 hCms
    have hp1 : 1 ≤ p := by
      by_contra hcon
      have h0 : p = 0 := by omega
      subst h0
      norm_num at hp
    have hmain : ∀ᶠ N : ℕ in atTop,
        (bornMeasure (physBasis L hκ N) u hu).real
            (EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h (eta0 L κ) ((N : ℝ) ^ (-γ)) b)ᶜ ≤
          propBound (Ctail (μ : Measure ℝ) p) (Dtail κ p) (prop017Cb (eta0 L κ) h ρ Csharp b) p (N : ℝ)
            ((N : ℝ) ^ θ) (cutN L θ N) ((N : ℝ) ^ (-γ)) := by
      filter_upwards [regime_eventually hL hθ hγ (max R0 (eta0 L κ)) l0, eventually_ge_atTop N0,
        eventually_ge_atTop 1] with N hreg hN0 hN1
      have hle := hfam ((N : ℝ) ^ (-γ)) hreg.2.2.2.1 hreg.2.2.2.2 N hN0 hN1 ((N : ℝ) ^ θ)
        (le_trans (le_max_left _ _) hreg.1) (cutIdx L θ N) hreg.2.1 (cutN L θ N) rfl hreg.2.2.1
      refine (hle.1 p hp1 (le_trans (le_max_right _ _) hreg.1)).trans (le_of_eq ?_)
      unfold propBound; ring
    exact tendsto_of_bound hL hθ hγ hsum p hp (Ctail (μ : Measure ℝ) p) (Dtail κ p)
      (prop017Cb (eta0 L κ) h ρ Csharp b) hCb _ (Eventually.of_forall fun N => measureReal_nonneg) hmain
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
  refine ⟨max C 0, M, η, hM1, hη, ?_⟩
  have hall := hC.and hprops
  rw [hldef, eventually_inf_principal, eventually_comap, eventually_atTop] at hall
  obtain ⟨k0, hk0⟩ := hall
  filter_upwards [eventually_ge_atTop (k0 + 1)] with N hN m hm z hz
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  have hi := hk0 k (by omega) ⟨k, (m, z)⟩ rfl ⟨hm, hz⟩
  obtain ⟨hrem, hpr⟩ := hi
  refine ⟨hpr.1, hpr.2.1, hpr.2.2.1, hpr.2.2.2.1, hpr.2.2.2.2, ?_⟩
  have hNr : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  refine hrem.trans ?_
  show C * ‖(((k + 1 : ℕ) : ℝ))⁻¹ * ((((k + 1 : ℕ) : ℝ))⁻¹ * 1 ^ 2)‖ ≤ _
  rw [one_pow, mul_one, Real.norm_of_nonneg (by positivity)]
  calc C * ((((k + 1 : ℕ) : ℝ))⁻¹ * (((k + 1 : ℕ) : ℝ))⁻¹)
      ≤ max C 0 * ((((k + 1 : ℕ) : ℝ))⁻¹ * (((k + 1 : ℕ) : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ = max C 0 / ((k + 1 : ℕ) : ℝ) ^ 2 := by field_simp

end QuantumNLS.Prop017MovingContour

#print axioms QuantumNLS.Prop017MovingContour.moving_contour_uniform
