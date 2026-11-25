import Mathlib
import QuantumNLS.PROP018Probability
import QuantumNLS.PROP017CutFamily

/-!
# PROP-017 with uniform `N₀`, and the actual ε-indexed family along the PROP-018 diagonal

Owner: haiku_inventory (round 18). Technical packaging only; no owner policy is decided here.

**Uniform-`N₀` quantifier order (`prop017_uniform`).** The frozen `PROP017CutFamily_80430db0` states
`∀ ε, ∃ N₀, ∀ N ≥ N₀ …`. Its proof already fixes `N₀ = ⌈2|κ|/r⌉₊+1` after `ρ, R₀, r` and before `ε`, so
`N₀` is `ε`-independent. `prop017_uniform` is the same theorem with the quantifiers in the uniform order
`∃ ρ, ∃ R₀, ∃ r, ∃ N₀, ∀ ε, …`. The proof body is the frozen proof with only the introduction order of
`ε` and `N₀` changed; no mathematical step differs.

**Diagonal corollary (`prop017_diagonal`).** Along `ε_N = N^{−γ}`, `R_N = N^θ`, `a_N = cutN L θ N` (designated
cut), with `3γ+θ<1`, `1<2pθ`: the probability `P_N(𝓔_N(ε_N)^c)` tends to `0` (the actual ε-indexed event,
evaluated at `ε_N`), and the Gneighbor error `2K(ε_N + R_N^{−b})` on the event tends to `0`.

Unresolved and not promoted: the printed event interpretation (ε-indexed vs common event; see
`haiku_event_quantifier_diagnosis_round17.md`). This module proves the ε-indexed reading only.
-/

namespace QuantumNLS.PROP017UniformN

open MeasureTheory Set Metric
open QuantumNLS.RootEvent QuantumNLS.Extrapolation QuantumNLS.ResolventNeighborhood
  QuantumNLS.NonvanishingD

/-- The designated cut sequence `a_ℓ = (2ℓ+1)π/L` (source line 30). -/
noncomputable def cutSeq (L : ℝ) (l : ℕ) : ℝ := (2 * (l : ℝ) + 1) * Real.pi / L

theorem prop017_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (κ L h η0 δ d0 : ℝ) (_hL : 0 < L) (l0 b pc : ℕ) (_hb : 1 ≤ b) (hbpc : b ≤ 2 * pc)
    (hmom : ∀ p : ℕ, Integrable (fun x : ℝ => x ^ (2 * p)) μ)
    (hη0 : 0 < η0) (hηh : η0 < h) (hδ : 0 < δ) (hd0 : 0 < d0)
    (hcut : ∀ l : ℕ, l0 ≤ l →
      (∀ᵐ (x : ℝ) ∂μ, δ ≤ |x - cutSeq L l| ∧ δ ≤ |x + cutSeq L l|) ∧
        (∀ w ∈ GammaN (cutSeq L l) h, d0 ≤ ‖Dsrc κ L μ w‖))
    (Cp Dp Rt : ℕ → ℝ) (Cms : ℝ) (hCms : 0 ≤ Cms) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ R0 : ℝ, 1 ≤ R0 ∧ ∃ r : ℝ, 0 < r ∧
      (∀ R : ℝ, R0 ≤ R → ∀ a : ℝ, 2 * R ≤ a → r ≤ rNbhd a h ρ R δ) ∧
      ∃ N0 : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ N : ℕ, N0 ≤ N →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (q : Ω → Fin N → ℝ), Measurable q →
          (∀ p : ℕ, 1 ≤ p → ∀ R' : ℝ, Rt p ≤ R' → 0 < R' →
            ∫ ω, tailFraction q R' ω ∂P ≤ Cp p * (1 / R' ^ (2 * p)) + Dp p / ((N : ℝ) * R')) →
          (∀ x y : ℝ, η0 ≤ y → ∫ ω, ‖Gfull μ ((x : ℂ) + (y : ℂ) * Complex.I)
              - GN (q ω) ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 ∂P ≤ Cms / ((N : ℝ) * y ^ 2)) →
          ∀ R : ℝ, R0 ≤ R → ∀ l : ℕ, l0 ≤ l → ∀ a : ℝ, a = cutSeq L l → 2 * R ≤ a →
            (∀ p : ℕ, 1 ≤ p → Rt p ≤ R →
                P.real (EN μ q R a ρ h η0 ε b)ᶜ
                  ≤ (N : ℝ) * (Cp p * (1 / R ^ (2 * p))) + Dp p / R
                    + prop017Cb η0 h ρ Cms b * (1 + a) / ((N : ℝ) * ε ^ 3)) ∧
            (∀ ω ∈ EN μ q R a ρ h η0 ε b,
                (∀ j, |q ω j| ≤ R) ∧
                (∀ z ∈ NbhdN a h ρ, ‖Gfull μ z - GN (q ω) z‖ ≤
                  2 * KGN η0 δ ρ (h + 5) Cms b pc μ * (ε + 1 / R ^ b)) ∧
                (∀ z ∈ NbhdN a h (ρ / 2), ∀ n : ℕ,
                  ‖iteratedDeriv n (fun w => sNsrc κ L (q ω) w - sLimsrc κ L μ w) z‖ ≤
                    n.factorial * (Real.exp (|κ| / r) * (1 + Real.exp (|L| * (h + 2 * ρ)))
                      * max (κ ^ 2 / r ^ 2) (|κ| * (2 * KGN η0 δ ρ (h + 5) Cms b pc μ))
                      * (ε + 1 / R ^ b + 1 / (N : ℝ))) / (ρ / 2) ^ n)) ∧
            (∀ z ∈ NbhdN a h (ρ / 4), d0 / 2 ≤ ‖Dsrc κ L μ z‖) := by
  have hh : 0 < h := by linarith
  -- fixed scale `s = min(h, δ, 1)/8` (independent of ρ, a, R, ε, N)
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = min (min h δ) 1 / 8 := ⟨_, rfl⟩
  have hs0 : 0 < s := by
    rw [hs_def]
    exact div_pos (lt_min (lt_min hh hδ) one_pos) (by norm_num)
  have hm_h : min (min h δ) 1 ≤ h := le_trans (min_le_left _ _) (min_le_left _ _)
  have hm_δ : min (min h δ) 1 ≤ δ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hm_1 : min (min h δ) 1 ≤ 1 := min_le_right _ _
  have hs4h : 4 * s ≤ h / 2 := by rw [hs_def]; linarith
  have hs4δ : 4 * s ≤ δ / 2 := by rw [hs_def]; linarith
  have hs4one : 4 * s ≤ 1 / 2 := by rw [hs_def]; linarith
  -- fixed lower bound `rS` for the nbhd of radius `2s`
  obtain ⟨rS, hrS_def⟩ : ∃ rS : ℝ, rS = min (min h δ / 2) (1 / 2) := ⟨_, rfl⟩
  have hmhd : 0 < min h δ := lt_min hh hδ
  have hrS0 : 0 < rS := by
    rw [hrS_def]
    exact lt_min (by linarith) (by norm_num)
  have hrS_h : rS ≤ h / 2 := by
    have := min_le_left (min h δ / 2) (1 / 2)
    have := min_le_left h δ
    rw [hrS_def]; linarith
  have hrS_δ : rS ≤ δ / 2 := by
    have := min_le_left (min h δ / 2) (1 / 2)
    have := min_le_right h δ
    rw [hrS_def]; linarith
  have hrS_half : rS ≤ 1 / 2 := by rw [hrS_def]; exact min_le_right _ _
  have hrS_le_rN : ∀ R a : ℝ, 1 ≤ R → 2 * R ≤ a → rS ≤ rNbhd a h (2 * s) R δ := by
    intro R a hR1 ha2
    unfold rNbhd
    exact le_min (by linarith) (le_min (by linarith) (by linarith))
  have hb0s : 0 < h - 2 * (2 * s) := by linarith
  -- the Lipschitz constant of `D` on the neighbourhood (fixed scale), and the radius `ρ`
  have hDl0 : 0 ≤ DlipS κ L h s rS := DlipS_nonneg hs0 hrS0
  obtain ⟨ρ, hρ_def⟩ : ∃ ρ : ℝ, ρ = min (min s (1 / 4))
      (min ((h - η0) / 2) (min (δ / 8) (2 * d0 / (DlipS κ L h s rS + 1)))) := ⟨_, rfl⟩
  have hρ_s : ρ ≤ s := by rw [hρ_def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hρ_14 : ρ ≤ 1 / 4 := by rw [hρ_def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hρ_η : ρ ≤ (h - η0) / 2 := by
    rw [hρ_def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ_δ : ρ ≤ δ / 8 := by
    rw [hρ_def]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρ_D : ρ ≤ 2 * d0 / (DlipS κ L h s rS + 1) := by
    rw [hρ_def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hρ0 : 0 < ρ := by
    rw [hρ_def]
    refine lt_min (lt_min hs0 (by norm_num)) (lt_min (by linarith) (lt_min (by linarith) ?_))
    exact div_pos (by linarith) (by linarith)
  have hρδ : ρ < δ / 4 := by linarith
  have hηh' : η0 ≤ h - 2 * ρ := by linarith
  have hb0ρ : 0 < h - 2 * ρ := by linarith
  have hρs4 : ρ / 4 ≤ s := by linarith
  have hH : h + 4 * ρ < h + 5 := by linarith
  have hDlip : DlipS κ L h s rS * (ρ / 4) ≤ d0 / 2 := by
    have h1 : ρ * (DlipS κ L h s rS + 1) ≤ 2 * d0 := (le_div_iff₀ (by linarith)).mp hρ_D
    have h2 : DlipS κ L h s rS * ρ ≤ 2 * d0 := by linarith [h1, hρ0.le]
    linarith
  -- the uniform radius `R₀` (discharges `2H ≤ R`, `2(η₀+1+b) ≤ R`, `2ρ < R`, `1 ≤ R`)
  obtain ⟨R0, hR0_def⟩ : ∃ R0 : ℝ, R0 = max (max 1 (2 * (h + 5))) (2 * (η0 + 1 + (b : ℝ))) :=
    ⟨_, rfl⟩
  have hR01 : 1 ≤ R0 := by
    rw [hR0_def]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hR0H : 2 * (h + 5) ≤ R0 := by
    rw [hR0_def]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hR0m : 2 * (η0 + 1 + (b : ℝ)) ≤ R0 := by
    rw [hR0_def]; exact le_max_right _ _
  have hρ2 : 2 * ρ < R0 := by linarith
  -- the uniform radius `r ≤ rNbhd` for all `R ≥ R₀`, `a ≥ max(a₀, 2R)`
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = min (h - 2 * ρ) (min (δ - 2 * ρ) (R0 - 2 * ρ)) := ⟨_, rfl⟩
  have hr0 : 0 < r := by
    rw [hr_def]
    exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hr_le : ∀ R a : ℝ, R0 ≤ R → 2 * R ≤ a → r ≤ rNbhd a h ρ R δ := by
    intro R a hR ha2
    rw [hr_def]
    unfold rNbhd
    exact min_le_min le_rfl (min_le_min le_rfl (by linarith))
  refine ⟨ρ, hρ0, R0, hR01, r, hr0, fun R hR a ha2 => hr_le R a hR ha2, ?_⟩
  refine ⟨⌈2 * |κ| / r⌉₊ + 1, ?_⟩
  intro ε hε hε1 N hN Ω _ P _ q hq hTail hms R hR l hl a ha_eq ha2
  have hNpos : 0 < N := by omega
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hceil : 2 * |κ| / r ≤ (N : ℝ) := by
    have h1 : 2 * |κ| / r ≤ ((⌈2 * |κ| / r⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈2 * |κ| / r⌉₊ + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    push_cast at h2
    linarith
  have hNbig : |κ| / (N : ℝ) ≤ r / 2 := by
    rw [div_le_iff₀ hNposR]
    have h3 := (div_le_iff₀ hr0).mp hceil
    linarith
  have hRpos : 0 < R := by linarith
  have hapos : 0 < a := by linarith
  have hacut : 2 * R ≤ |a| := by rw [abs_of_pos hapos]; exact ha2
  have hcutA : (∀ᵐ (x : ℝ) ∂μ, δ ≤ |x - a| ∧ δ ≤ |x + a|) ∧
      (∀ w ∈ GammaN a h, d0 ≤ ‖Dsrc κ L μ w‖) := by
    rw [ha_eq]
    exact hcut l hl
  have hsupp : ∀ᵐ (x : ℝ) ∂μ, δ ≤ |x - a| := hcutA.1.mono fun x hx => hx.1
  have hsuppN : ∀ᵐ (x : ℝ) ∂μ, δ ≤ |x + a| := hcutA.1.mono fun x hx => hx.2
  have hD := hcutA.2
  have hR2ρ : 2 * ρ < R := by linarith
  refine ⟨?_, ?_, ?_⟩
  · intro p hp hRt
    exact prop017_bad P hNpos q hq μ b η0 h ρ a R ε (Cp p) (Dp p) (Rt p) Cms p hCms hη0 hρ0.le hηh'
      hapos.le hε hε1 hRpos hRt (hTail p hp) hms
  · intro ω hω
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨h1, -⟩ := hω
      exact h1
    · exact gneighbor_on_EN P hNpos q hq μ b pc b η0 δ ρ h (h + 5) R a ε Cms hη0 hρ0 hρδ hηh'
        hb0ρ hH hRpos (by linarith) (by linarith) (by linarith) hapos hacut hε.le (hmom pc)
        hsupp hsuppN hms (by omega) hbpc ω hω
    · exact derivative_jn_on_smaller_r P hNpos q hq μ b pc b η0 δ ρ h (h + 5) R a ε Cms κ L r hη0
        hρ0 hρδ hηh' hb0ρ hH hRpos (by linarith) (by linarith) (by linarith) hR2ρ hapos hacut
        hε.le (hmom pc) hsupp hsuppN hms (by omega) hbpc hr0 (hr_le R a hR ha2)
        hNbig ω hω
  · -- `|D|` is root-independent; the dummy root vector only feeds `nbhd_dist`'s root conjunct
    exact D_lower_scale (fun _ : Fin N => (0 : ℝ)) κ L d0 μ hs0 hrS0 (hrS_le_rN R a (by linarith) ha2) hapos
      hb0s hρ0 hρs4 hsupp hsuppN hd0 hD hDlip



open QuantumNLS.PROP018Probability
open Filter Topology

/-- `prop017Cb` is nonnegative for `ρ > 0`, `Cms ≥ 0` (its terms are sums of squares and nonnegative
multiples). -/
lemma prop017Cb_nonneg {η0 h ρ Cms : ℝ} {m : ℕ} (hρ : 0 < ρ) (hCms : 0 ≤ Cms) :
    0 ≤ prop017Cb η0 h ρ Cms m := by
  unfold prop017Cb prop017Kn
  have hK : 0 ≤ ∑ k : Fin (m + 1), Cms / (η0 + 1 + ((k : ℕ) : ℝ)) ^ 2 :=
    Finset.sum_nonneg fun k _ => div_nonneg hCms (sq_nonneg _)
  have hA : 0 ≤ (8 + 16 * ρ) / (h - 2 * ρ) ^ 2 + 2 := by
    have := div_nonneg (by linarith : (0 : ℝ) ≤ 8 + 16 * ρ) (sq_nonneg (h - 2 * ρ))
    linarith
  exact add_nonneg (mul_nonneg (by norm_num) hK)
    (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA) hCms) (sq_nonneg _))

/-- **Diagonal corollary of the uniform-`N₀` family.** Along `ε_N = N^{−γ}`, `R_N = N^θ`, `a_N = cutN L θ N`
(designated cut), with `3γ + θ < 1` and `1 < 2pθ`: the actual ε-indexed event `EN(ε_N)` has
`P_N(EN(ε_N)^c) → 0`, and on it the Gneighbor error `2K(ε_N + R_N^{−b})` is bounded by a sequence tending to `0`.
The event is the ε-indexed reading only (see the module header). -/
theorem prop017_diagonal {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (κ L h η0 δ d0 : ℝ) (hL : 0 < L) (l0 b pc : ℕ)
    (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc)
    (hmom : ∀ p : ℕ, Integrable (fun x : ℝ => x ^ (2 * p)) μ)
    (hη0 : 0 < η0) (hηh : η0 < h) (hδ : 0 < δ) (hd0 : 0 < d0)
    (hcut : ∀ l : ℕ, l0 ≤ l →
      (∀ᵐ (x : ℝ) ∂μ, δ ≤ |x - cutSeq L l| ∧ δ ≤ |x + cutSeq L l|) ∧
        (∀ w ∈ GammaN (cutSeq L l) h, d0 ≤ ‖Dsrc κ L μ w‖))
    (Cp Dp Rt : ℕ → ℝ) (Cms : ℝ) (hCms : 0 ≤ Cms)
    (θ γ : ℝ) (hθ : 0 < θ) (hγ : 0 < γ) (hsum : 3 * γ + θ < 1)
    (p : ℕ) (hp : 1 < 2 * (p : ℝ) * θ)
    (P : ∀ N : ℕ, Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]
    (q : ∀ N : ℕ, Ω N → Fin N → ℝ) (hq : ∀ N : ℕ, Measurable (q N))
    (hTail : ∀ N : ℕ, ∀ p' : ℕ, 1 ≤ p' → ∀ R' : ℝ, Rt p' ≤ R' → 0 < R' →
      ∫ ω, tailFraction (q N) R' ω ∂(P N) ≤ Cp p' * (1 / R' ^ (2 * p')) + Dp p' / ((N : ℝ) * R'))
    (hms : ∀ N : ℕ, ∀ x y : ℝ, η0 ≤ y → ∫ ω, ‖Gfull μ ((x : ℂ) + (y : ℂ) * Complex.I)
      - GN (q N ω) ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 ∂(P N) ≤ Cms / ((N : ℝ) * y ^ 2)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ R0 : ℝ, 1 ≤ R0 ∧ ∃ r : ℝ, 0 < r ∧
      (∀ R : ℝ, R0 ≤ R → ∀ a : ℝ, 2 * R ≤ a → r ≤ rNbhd a h ρ R δ) ∧
      Tendsto (fun N : ℕ => (P N).real (EN μ (q N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h η0
        ((N : ℝ) ^ (-γ)) b)ᶜ) atTop (𝓝 0) ∧
      (∀ᶠ N : ℕ in atTop, ∀ ω ∈ EN μ (q N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h η0 ((N : ℝ) ^ (-γ)) b,
        ∀ z ∈ NbhdN (cutN L θ N) h ρ, ‖Gfull μ z - GN (q N ω) z‖ ≤
          2 * KGN η0 δ ρ (h + 5) Cms b pc μ * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b)) ∧
      Tendsto (fun N : ℕ => 2 * KGN η0 δ ρ (h + 5) Cms b pc μ *
        ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b)) atTop (𝓝 0) := by
  obtain ⟨ρ, hρ0, R0, hR01, r, hr0, hrad, N0, hfam⟩ :=
    prop017_uniform μ κ L h η0 δ d0 hL l0 b pc hb hbpc hmom hη0 hηh hδ hd0 hcut Cp Dp Rt Cms hCms
  have hCb : 0 ≤ prop017Cb η0 h ρ Cms b := prop017Cb_nonneg hρ0 hCms
  have hp1 : 1 ≤ p := by
    by_contra hcon
    have h0 : p = 0 := by omega
    subst h0
    norm_num at hp
  have hb0 : b ≠ 0 := by omega
  have hmain : ∀ᶠ N : ℕ in atTop,
      (P N).real (EN μ (q N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h η0 ((N : ℝ) ^ (-γ)) b)ᶜ ≤
        propBound (Cp p) (Dp p) (prop017Cb η0 h ρ Cms b) p (N : ℝ) ((N : ℝ) ^ θ)
          (cutN L θ N) ((N : ℝ) ^ (-γ)) ∧
      (∀ ω ∈ EN μ (q N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h η0 ((N : ℝ) ^ (-γ)) b,
        ∀ z ∈ NbhdN (cutN L θ N) h ρ, ‖Gfull μ z - GN (q N ω) z‖ ≤
          2 * KGN η0 δ ρ (h + 5) Cms b pc μ * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b)) := by
    filter_upwards [regime_eventually hL hθ hγ (max R0 (Rt p)) l0, eventually_ge_atTop N0]
      with N hreg hN0
    have hle := hfam ((N : ℝ) ^ (-γ)) hreg.2.2.2.1 hreg.2.2.2.2 N hN0 (Ω N) (P N) (q N) (hq N)
      (hTail N) (hms N) ((N : ℝ) ^ θ) (le_trans (le_max_left _ _) hreg.1) (cutIdx L θ N) hreg.2.1
      (cutN L θ N) rfl hreg.2.2.1
    obtain ⟨hbd, hG, -⟩ := hle
    exact ⟨hbd p hp1 (le_trans (le_max_right _ _) hreg.1), fun ω hω => (hG ω hω).2.1⟩
  have hA : Tendsto (fun N : ℕ => (P N).real (EN μ (q N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h η0
      ((N : ℝ) ^ (-γ)) b)ᶜ) atTop (𝓝 0) :=
    tendsto_of_bound hL hθ hγ hsum p hp (Cp p) (Dp p) (prop017Cb η0 h ρ Cms b) hCb _
      (Eventually.of_forall fun N => measureReal_nonneg) (hmain.mono fun N h => h.1)
  have hε : Tendsto (fun N : ℕ => (N : ℝ) ^ (-γ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hγ).comp tendsto_natCast_atTop_atTop
  have hR' : Tendsto (fun N : ℕ => (N : ℝ) ^ θ) atTop atTop :=
    (tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop
  have hRb : Tendsto (fun N : ℕ => 1 / ((N : ℝ) ^ θ) ^ b) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop hb0).comp hR')
  have hC : Tendsto (fun N : ℕ => 2 * KGN η0 δ ρ (h + 5) Cms b pc μ *
      ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b)) atTop (𝓝 0) := by
    have h := (hε.add hRb).const_mul (2 * KGN η0 δ ρ (h + 5) Cms b pc μ)
    rw [add_zero, mul_zero] at h
    exact h
  refine ⟨ρ, hρ0, R0, hR01, r, hr0, hrad, hA, hmain.mono (fun N h => h.2), hC⟩

end QuantumNLS.PROP017UniformN
