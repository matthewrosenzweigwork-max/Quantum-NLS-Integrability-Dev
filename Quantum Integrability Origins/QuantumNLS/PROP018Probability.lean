import Mathlib
import QuantumNLS.PROP017CutFamily

/-!
# PROP-018 probability step: diagonal parameter regime

Owner: haiku_inventory (round 17). Source `window_reconstruction.tex` lines 157–160 (PROP-018:
"Let `P_N` be the spectral projection onto `𝓔_N`. Suppose `ε+R^{-b}+N^{-1}→0`") and lines 280–286
(proof: `‖Φ_N − u^{⊗N}‖ ≤ 2√P(𝓔_N^c)`).

Probability and diagonal-parameter step only. No operator or spectral statement is proved, and no source
event is changed. The PROP-017 family (`PROP017CutFamily_80430db0`) enters only through the **shape** of its
probability bound, which is conditional on the ε-indexed reading of the event
(`haiku_event_quantifier_diagnosis_round17.md`) and on a uniform-`N₀` reading (see `tendsto_of_bound`).

Proved:

* `cut_bounds`: the designated cut `a_N = cutSeq L ℓ_N`, `ℓ_N = ⌈L N^θ/π⌉₊`, satisfies
  `2N^θ ≤ a_N ≤ 2N^θ + 3π/L` and `L N^θ/π ≤ ℓ_N`;
* `tendsto_regime_error`: `ε_N + R_N^{−b} + N^{−1} → 0` for `ε_N = N^{−γ}`, `R_N = N^θ` (PROP-018 regime);
* `tendsto_propBound`: the PROP-017 bound `N C_p R^{−2p} + D_p/R + C_b(1+a)/(N ε³)` along the diagonal
  `R_N = N^θ`, `ε_N = N^{−γ}`, `a_N` designated, tends to `0` when `3γ + θ < 1` and `1 < 2pθ`;
* `regime_eventually`: the diagonal satisfies the PROP-017 admissibility (`R_N ≥ R₀`, `ℓ_N ≥ ℓ₀`,
  `2R_N ≤ a_N`, `0 < ε_N ≤ 1`) eventually;
* `tendsto_of_bound`: any probability sequence eventually `0 ≤ P_N ≤ propBound` tends to `0`.

Not proved: the uniform-`N₀` reading of PROP-017 (the frozen statement gives `N₀` after `ε`), the operator
estimate `‖(…)P_N‖`, and the normalized-state estimate `‖Φ_N − u^{⊗N}‖`.
-/

namespace QuantumNLS.PROP018Probability

open Filter Topology
open QuantumNLS.PROP017CutFamily

/-- Designated cut index `ℓ_N = ⌈L N^θ/π⌉₊`. -/
noncomputable def cutIdx (L θ : ℝ) (N : ℕ) : ℕ := ⌈L * (N : ℝ) ^ θ / Real.pi⌉₊

/-- Designated cut `a_N = cutSeq L ℓ_N = (2ℓ_N+1)π/L`. -/
noncomputable def cutN (L θ : ℝ) (N : ℕ) : ℝ := cutSeq L (cutIdx L θ N)

/-- The PROP-017 probability bound at `(N, R, a, ε)`, same shape as `eq:bad`:
`N C_p R^{−2p} + D_p/R + C_b(1+a)/(N ε³)`. -/
noncomputable def propBound (Cp Dp Cb : ℝ) (p : ℕ) (N R a ε : ℝ) : ℝ :=
  N * (Cp * (1 / R ^ (2 * p))) + Dp / R + Cb * (1 + a) / (N * ε ^ 3)

lemma pow_rpow_nat {x : ℝ} (hx : 0 < x) (θ : ℝ) (k : ℕ) : (x ^ θ) ^ k = x ^ (θ * (k : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]

/-- Designated cut bounds: `2N^θ ≤ a_N ≤ 2N^θ + 3π/L` and `L N^θ/π ≤ ℓ_N`. -/
lemma cut_bounds {L θ : ℝ} (hL : 0 < L) (N : ℕ) :
    2 * (N : ℝ) ^ θ ≤ cutN L θ N ∧ cutN L θ N ≤ 2 * (N : ℝ) ^ θ + 3 * Real.pi / L ∧
      L * (N : ℝ) ^ θ / Real.pi ≤ (cutIdx L θ N : ℝ) := by
  have hLne : L ≠ 0 := hL.ne'
  have hNθ : 0 ≤ (N : ℝ) ^ θ := Real.rpow_nonneg (Nat.cast_nonneg N) θ
  have hx0 : 0 ≤ L * (N : ℝ) ^ θ / Real.pi := div_nonneg (mul_nonneg hL.le hNθ) Real.pi_pos.le
  have hceil1 : L * (N : ℝ) ^ θ / Real.pi ≤ (cutIdx L θ N : ℝ) := Nat.le_ceil _
  have hceil2 : (cutIdx L θ N : ℝ) < L * (N : ℝ) ^ θ / Real.pi + 1 := Nat.ceil_lt_add_one hx0
  have hc : 0 < Real.pi / L := div_pos Real.pi_pos hL
  have hxc : L * (N : ℝ) ^ θ / Real.pi * (Real.pi / L) = (N : ℝ) ^ θ := by
    rw [div_mul_div_comm, show L * (N : ℝ) ^ θ * Real.pi = (N : ℝ) ^ θ * (Real.pi * L) by ring]
    exact mul_div_cancel_right₀ _ (mul_ne_zero Real.pi_ne_zero hLne)
  have hcut : cutN L θ N = (2 * (cutIdx L θ N : ℝ) + 1) * (Real.pi / L) := by
    unfold cutN cutSeq
    ring
  rw [hcut]
  refine ⟨?_, ?_, hceil1⟩
  · nlinarith [mul_le_mul_of_nonneg_right hceil1 hc.le]
  · set x := L * (N : ℝ) ^ θ / Real.pi with hxdef
    have h1 : (2 * (cutIdx L θ N : ℝ) + 1) * (Real.pi / L) < (2 * (x + 1) + 1) * (Real.pi / L) :=
      mul_lt_mul_of_pos_right (by linarith) hc
    have e : (2 * (x + 1) + 1) * (Real.pi / L) = 2 * (N : ℝ) ^ θ + 3 * Real.pi / L := by
      rw [← hxc]
      ring
    linarith

/-- `1 + a_N ≤ (3 + 3π/L) N^θ` and `0 ≤ a_N`, for `N ≥ 1`, `θ ≥ 0`. -/
lemma one_add_cut_le {L θ : ℝ} (hL : 0 < L) (hθ : 0 ≤ θ) {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ cutN L θ N ∧ 1 + cutN L θ N ≤ (3 + 3 * Real.pi / L) * (N : ℝ) ^ θ := by
  obtain ⟨h1, h2, -⟩ := cut_bounds (θ := θ) hL N
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hge : (1 : ℝ) ≤ (N : ℝ) ^ θ := Real.one_le_rpow hN1 hθ
  have hNθ : 0 ≤ (N : ℝ) ^ θ := by linarith
  have hpi : 0 ≤ 3 * Real.pi / L := div_nonneg (by positivity) hL.le
  refine ⟨by linarith, ?_⟩
  nlinarith [mul_nonneg hpi (by linarith : (0 : ℝ) ≤ (N : ℝ) ^ θ - 1)]

/-- The PROP-018 regime error `ε_N + R_N^{−b} + N^{−1} → 0`, with `ε_N = N^{−γ}`, `R_N = N^θ`. -/
lemma tendsto_regime_error {θ γ b : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) (hb : 0 < b) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (-γ) + ((N : ℝ) ^ θ) ^ (-b) + 1 / (N : ℝ)) atTop
      (𝓝 0) := by
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-γ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hγ).comp hN
  have h2 : Tendsto (fun N : ℕ => ((N : ℝ) ^ θ) ^ (-b)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (mul_pos hθ hb)).comp hN
    refine Tendsto.congr' ?_ h
    filter_upwards [eventually_ge_atTop 1] with N hN1
    have hx : (0 : ℝ) < N := by exact_mod_cast hN1
    show (N : ℝ) ^ (-(θ * b)) = ((N : ℝ) ^ θ) ^ (-b)
    rw [← Real.rpow_mul hx.le]
    congr 1
    ring
  have h3 : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have h := (h1.add h2).add h3
  rw [add_zero, add_zero] at h
  exact h

lemma term1_eq {x : ℝ} (hx : 0 < x) (θ Cp : ℝ) (p : ℕ) :
    x * (Cp * (1 / (x ^ θ) ^ (2 * p))) = Cp * x ^ (-(2 * (p : ℝ) * θ - 1)) := by
  rw [pow_rpow_nat hx θ (2 * p), one_div, ← Real.rpow_neg hx.le]
  have e' : x * x ^ (-(θ * ((2 * p : ℕ) : ℝ))) = x ^ (-(2 * (p : ℝ) * θ - 1)) := by
    have h := Real.rpow_add hx 1 (-(θ * ((2 * p : ℕ) : ℝ)))
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    push_cast
    ring
  rw [show ∀ y : ℝ, x * (Cp * y) = Cp * (x * y) from fun y => by ring, e']

lemma term2_eq {x : ℝ} (hx : 0 < x) (θ Dp : ℝ) : Dp / x ^ θ = Dp * x ^ (-θ) := by
  rw [Real.rpow_neg hx.le, div_eq_mul_inv]

lemma term3_eq {x : ℝ} (hx : 0 < x) (γ C : ℝ) :
    C / (x * (x ^ (-γ)) ^ 3) = C * x ^ (-(1 - 3 * γ)) := by
  have hden : x * (x ^ (-γ)) ^ 3 = x ^ (1 - 3 * γ) := by
    rw [pow_rpow_nat hx (-γ) 3]
    rw [show (1 - 3 * γ) = 1 + (-γ * ((3 : ℕ) : ℝ)) by push_cast; ring, Real.rpow_add hx,
      Real.rpow_one]
  rw [hden, Real.rpow_neg hx.le, div_eq_mul_inv]

lemma propBound_eq {x : ℝ} (hx : 0 < x) (θ γ Cp Dp Cb a : ℝ) (p : ℕ) :
    propBound Cp Dp Cb p x (x ^ θ) a (x ^ (-γ)) =
      Cp * x ^ (-(2 * (p : ℝ) * θ - 1)) + Dp * x ^ (-θ) + Cb * (1 + a) * x ^ (-(1 - 3 * γ)) := by
  unfold propBound
  rw [term1_eq hx, term2_eq hx, term3_eq hx]

/-- **Diagonal PROP-017 bound tends to zero.** Along `R_N = N^θ`, `ε_N = N^{−γ}`, `a_N` designated,
with `3γ + θ < 1` and `1 < 2pθ`, the bound `propBound` tends to `0`. -/
theorem tendsto_propBound {L θ γ : ℝ} (hL : 0 < L) (hθ : 0 < θ) (hγ : 0 < γ)
    (hsum : 3 * γ + θ < 1) (p : ℕ) (hp : 1 < 2 * (p : ℝ) * θ) (Cp Dp Cb : ℝ) (hCb : 0 ≤ Cb) :
    Tendsto (fun N : ℕ => propBound Cp Dp Cb p (N : ℝ) ((N : ℝ) ^ θ) (cutN L θ N)
      ((N : ℝ) ^ (-γ))) atTop (𝓝 0) := by
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have f1 : Tendsto (fun N : ℕ => Cp * (N : ℝ) ^ (-(2 * (p : ℝ) * θ - 1))) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < 2 * (p : ℝ) * θ - 1)).comp hN).const_mul Cp
    rw [mul_zero] at h
    exact h
  have f2 : Tendsto (fun N : ℕ => Dp * (N : ℝ) ^ (-θ)) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop hθ).comp hN).const_mul Dp
    rw [mul_zero] at h
    exact h
  have f3 : Tendsto (fun N : ℕ => Cb * (1 + cutN L θ N) * (N : ℝ) ^ (-(1 - 3 * γ))) atTop
      (𝓝 0) := by
    have hK : 0 < 3 * γ + θ := by linarith
    have hy : 0 < 1 - 3 * γ - θ := by linarith
    have hg : Tendsto (fun N : ℕ => Cb * (3 + 3 * Real.pi / L) * (N : ℝ) ^ (-(1 - 3 * γ - θ)))
        atTop (𝓝 0) := by
      have h := (((tendsto_rpow_neg_atTop hy).comp hN).const_mul (Cb * (3 + 3 * Real.pi / L)))
      rw [mul_zero] at h
      exact h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
    · refine Eventually.of_forall fun N => ?_
      have h0 : 0 ≤ cutN L θ N := by
        have := (cut_bounds (θ := θ) hL N).1
        have hNθ : 0 ≤ (N : ℝ) ^ θ := Real.rpow_nonneg (Nat.cast_nonneg N) θ
        linarith
      exact mul_nonneg (mul_nonneg hCb (by linarith)) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    · filter_upwards [eventually_ge_atTop 1] with N hN1
      have hx : (0 : ℝ) < N := by exact_mod_cast hN1
      obtain ⟨h0, hK1⟩ := one_add_cut_le hL hθ.le hN1
      have hpow : 0 ≤ (N : ℝ) ^ (-(1 - 3 * γ)) := Real.rpow_nonneg hx.le _
      calc Cb * (1 + cutN L θ N) * (N : ℝ) ^ (-(1 - 3 * γ))
          ≤ Cb * ((3 + 3 * Real.pi / L) * (N : ℝ) ^ θ) * (N : ℝ) ^ (-(1 - 3 * γ)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK1 hCb) hpow
        _ = Cb * (3 + 3 * Real.pi / L) * (N : ℝ) ^ (-(1 - 3 * γ - θ)) := by
            rw [show -(1 - 3 * γ - θ) = θ + -(1 - 3 * γ) by ring, Real.rpow_add hx]
            ring
  have hs := (f1.add f2).add f3
  rw [add_zero, add_zero] at hs
  have heq : (fun N : ℕ => propBound Cp Dp Cb p (N : ℝ) ((N : ℝ) ^ θ) (cutN L θ N)
      ((N : ℝ) ^ (-γ))) =ᶠ[atTop] (fun N : ℕ => Cp * (N : ℝ) ^ (-(2 * (p : ℝ) * θ - 1))
        + Dp * (N : ℝ) ^ (-θ) + Cb * (1 + cutN L θ N) * (N : ℝ) ^ (-(1 - 3 * γ))) := by
    filter_upwards [eventually_ge_atTop 1] with N hN1
    have hx : (0 : ℝ) < N := by exact_mod_cast hN1
    exact propBound_eq hx θ γ Cp Dp Cb (cutN L θ N) p
  exact Tendsto.congr' heq.symm hs

/-- **Regime admissibility.** Eventually the diagonal satisfies the PROP-017 admissibility conditions. -/
lemma regime_eventually {L θ γ : ℝ} (hL : 0 < L) (hθ : 0 < θ) (hγ : 0 < γ) (R0 : ℝ) (ℓ0 : ℕ) :
    ∀ᶠ N : ℕ in atTop, R0 ≤ (N : ℝ) ^ θ ∧ ℓ0 ≤ cutIdx L θ N ∧
      2 * (N : ℝ) ^ θ ≤ cutN L θ N ∧ 0 < (N : ℝ) ^ (-γ) ∧ (N : ℝ) ^ (-γ) ≤ 1 := by
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hR : Tendsto (fun N : ℕ => (N : ℝ) ^ θ) atTop atTop :=
    (tendsto_rpow_atTop hθ).comp hN
  filter_upwards [hR.eventually_ge_atTop R0, hR.eventually_ge_atTop ((ℓ0 : ℝ) * Real.pi / L),
    eventually_ge_atTop 1] with N hR0 hℓ hN1
  have hx : (0 : ℝ) < N := by exact_mod_cast hN1
  have hcb := cut_bounds (θ := θ) hL N
  have hm : (ℓ0 : ℝ) ≤ L * (N : ℝ) ^ θ / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    have := (div_le_iff₀ hL).1 hℓ
    linarith
  have hℓ0 : ℓ0 ≤ cutIdx L θ N := by
    have : (ℓ0 : ℝ) ≤ (cutIdx L θ N : ℝ) := le_trans hm hcb.2.2
    exact_mod_cast this
  refine ⟨hR0, hℓ0, hcb.1, Real.rpow_pos_of_pos hx _, ?_⟩
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN1) (by linarith)

/-- **Conditional probability step.** Any probability sequence eventually bounded by the PROP-017
diagonal bound (with `ε_N = N^{−γ}`, `R_N = N^θ`, `a_N` designated) tends to `0`. The bound itself is
the frozen PROP-017 `eq:bad` shape, which is conditional on the ε-indexed event reading and on a
uniform-`N₀` reading of the family (not discharged here). -/
theorem tendsto_of_bound {L θ γ : ℝ} (hL : 0 < L) (hθ : 0 < θ) (hγ : 0 < γ)
    (hsum : 3 * γ + θ < 1) (p : ℕ) (hp : 1 < 2 * (p : ℝ) * θ) (Cp Dp Cb : ℝ) (hCb : 0 ≤ Cb)
    (Pbad : ℕ → ℝ) (hlow : ∀ᶠ N : ℕ in atTop, 0 ≤ Pbad N)
    (hup : ∀ᶠ N : ℕ in atTop, Pbad N ≤ propBound Cp Dp Cb p (N : ℝ) ((N : ℝ) ^ θ)
      (cutN L θ N) ((N : ℝ) ^ (-γ))) :
    Tendsto Pbad atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_propBound hL hθ hγ hsum p hp Cp Dp Cb hCb) hlow hup

end QuantumNLS.PROP018Probability
