import Mathlib
import QuantumNLS.RootEvent
import QuantumNLS.ResolventNeighborhood
import QuantumNLS.NonvanishingD

/-!
# PROP-017 with the source quantifiers

Owner: haiku_inventory (round 14). Repairs the quantifier structure of the PROP-017 statement
(`window_reconstruction.tex` lines 92–104: "there exist `ρ > 0`, independent of `N`, and events
`E_N` such that the following holds for `0 < ε ≤ 1` and all sufficiently large `N`").

Quantifier order of the conclusion:

  `∃ ρ > 0, ∃ R₀ ≥ 1, ∃ r > 0,`
  `  (∀ R ≥ R₀, ∀ a ≥ max(a₀, 2R), r ≤ rNbhd a h ρ R δ) ∧`
  `  ∀ 0 < ε ≤ 1, ∃ N₀, ∀ N ≥ N₀, ∀ (Ω, P, q) [model hypotheses at N], ∀ R ≥ R₀, ∀ a ≥ max(a₀,2R),`
  `    P(E_N^c) ≤ C_p N R^{-2b} + D_p/R + C_b(1+a)/(Nε³)  ∧`
  `    (on E_N: roots ≤ R, Gneighbor on NbhdN ρ, derivative on NbhdN (ρ/2)) ∧`
  `    (|D| ≥ d₀/2 on NbhdN (ρ/4))`.

The probability clause `Q7A:eq:bad` holds for **every** fixed `p ≥ 1` (source: "for every fixed
positive integer `p` in the quantum tail estimate"), with tail constants `C_p, D_p` and tail thresholds
`R_t(p)` (the source's `R ≥ R₀` for the tail, which may depend on `p`), fixed in `N`.
The constants `ρ, R₀, r, C_b, the Gneighbor and derivative constants` do not depend on `N`, `ε`, `R`,
`a`, or `p`. The regime inequalities (`ρ < δ/4`, `η₀ ≤ h−2ρ`, `h+4ρ < H`, `2H ≤ R`, `2(η₀+1+b) ≤ R`,
`2ρ < R`, `|κ|/N ≤ r/2`, and the `|D|` smallness `DlipS·(ρ/4) ≤ d₀/2`) are **discharged** inside the
proof from the chosen constants; none of them is a premise of the theorem.

**Cut family (designated cuts).** The source's model assumptions (support gap at the cuts, `|D| ≥ d₀`
on `Γ_ℓ`) are stated only at the designated cuts `a_ℓ = (2ℓ+1)π/L`, `ℓ ≥ ℓ₀` (source lines 22–31, 92–104).
The statement quantifies over `a = cutSeq L ℓ` only; no assumption is made at other real `a`.

**Event scope (documented, not resolved here).** The proof's event is `E_N = EN μ q R a ρ h η₀ ε b`,
which depends on `ε` (node and segment errors are `≤ ε`). The printed statement places "events `E_N`"
before "`0 < ε ≤ 1`". The statement below therefore records the proof-level reading: for each `ε`
there is an event `E_N(ε)` of this form. A single `ε`-free event satisfying all `ε`-clauses is not
provided by the printed bound (the term `C_b(1+a)/(Nε³)` diverges as `ε → 0`); this is the residual gap.

Hypotheses (source model inputs only): the moment bounds (`hmom`, source item 1), `η₀ > 0` with
`h > η₀` (source item 1), `δ > 0` and `d₀ > 0` with the cut conditions (source item 2) for all cuts
`a ≥ a₀` (the "sufficiently large cuts"), the uniform tail bound `Q7A:eq:tail` and the variance bound
`Q7A:eq:ms` for each `N` with constants `Cp, Dp, Cms` fixed in `N`.
-/

namespace QuantumNLS.PROP017CutFamily

open MeasureTheory Set Metric
open QuantumNLS.RootEvent QuantumNLS.Extrapolation QuantumNLS.ResolventNeighborhood
  QuantumNLS.NonvanishingD

/-- The designated cut sequence `a_ℓ = (2ℓ+1)π/L` (source line 30). -/
noncomputable def cutSeq (L : ℝ) (l : ℕ) : ℝ := (2 * (l : ℝ) + 1) * Real.pi / L

theorem prop017_source (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (κ L h η0 δ d0 : ℝ) (_hL : 0 < L) (l0 b pc : ℕ) (_hb : 1 ≤ b) (hbpc : b ≤ 2 * pc)
    (hmom : ∀ p : ℕ, Integrable (fun x : ℝ => x ^ (2 * p)) μ)
    (hη0 : 0 < η0) (hηh : η0 < h) (hδ : 0 < δ) (hd0 : 0 < d0)
    (hcut : ∀ l : ℕ, l0 ≤ l →
      (∀ᵐ (x : ℝ) ∂μ, δ ≤ |x - cutSeq L l| ∧ δ ≤ |x + cutSeq L l|) ∧
        (∀ w ∈ GammaN (cutSeq L l) h, d0 ≤ ‖Dsrc κ L μ w‖))
    (Cp Dp Rt : ℕ → ℝ) (Cms : ℝ) (hCms : 0 ≤ Cms) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ R0 : ℝ, 1 ≤ R0 ∧ ∃ r : ℝ, 0 < r ∧
      (∀ R : ℝ, R0 ≤ R → ∀ a : ℝ, 2 * R ≤ a → r ≤ rNbhd a h ρ R δ) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
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
  intro ε hε hε1
  refine ⟨⌈2 * |κ| / r⌉₊ + 1, ?_⟩
  intro N hN Ω _ P _ q hq hTail hms R hR l hl a ha_eq ha2
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

end QuantumNLS.PROP017CutFamily
