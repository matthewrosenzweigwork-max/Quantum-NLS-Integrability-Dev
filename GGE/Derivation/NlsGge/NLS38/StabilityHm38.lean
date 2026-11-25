import NlsGge.NLS38.StabilityHm38a

/-! # GWP piece A6b: `h^m` Lipschitz dependence of cutoff solutions on the datum

Plan: `campaign/GWP_PLAN.md` §7, piece A6b (review note N2).

`cutSol_stability_hm`: for every `m ≥ 1`, two cutoff solutions with `h^m` data of size `≤ ρ` satisfy
`‖u(t) - w(t)‖_{h^m} ≤ e^{L|t|} ‖u(0) - w(0)‖_{h^m}`, with `L` depending only on `m`, `R`, `ρ`.

Proof (helpers in `StabilityHm38a`).  With interaction variables `vu`, `vw` and `F(s) = TK (vu - vw)`
(`TK = ` the truncated weight `wK m K`), `F' = TK (Gc vu - Gc vw)` and the truncated norm of the
difference of cutoff fields is bounded by
`M (R² ‖F‖ + R (‖u‖_K + ‖w‖_K) ‖d‖_{h¹})` (the splitting `χ_u (N u - N w) + (χ_u - χ_w) N w`,
note N2).  The inhomogeneous term is bounded on `|s| ≤ T` by A6a (`cutSol_wK_bound38`) and the `h¹`
Lipschitz bound of A5b (`cutSol_lipschitz`), then the two-sided Gronwall bound
(`norm_le_gronwallBound_of_norm_deriv_right_le`, applied on `[0, T]` and on its reflection) gives a
`K`-uniform bound, and `K → ∞` is `mem_and_hn_le_of_wK38`.

Cast convention (§6.0): all Sobolev indices are natural casts.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff Set
open scoped ComplexConjugate NNReal InnerProductSpace

theorem one_add_le_exp_mul38 {c L T : ℝ} (_hc : 0 ≤ c) (hL : 0 ≤ L) (hT : 0 ≤ T) :
    1 + c * T * Real.exp (L * T) ≤ Real.exp ((c + L) * T) := by
  have h1 : c * T + 1 ≤ Real.exp (c * T) := Real.add_one_le_exp _
  have h2 : 1 ≤ Real.exp (L * T) := Real.one_le_exp (by positivity)
  have h3 : Real.exp ((c + L) * T) = Real.exp (c * T) * Real.exp (L * T) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h3]
  have := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (L * T)).le
  nlinarith

/-- **`h^m` Lipschitz stability of cutoff solutions** (A6b), for every `m ≥ 1`. -/
theorem cutSol_stability_hm (m : ℕ) (hm : 1 ≤ m) (R ρ : ℝ) (hR : 0 < R) : ∃ L : ℝ, 0 ≤ L ∧ ∀ u w,
    IsCutSol R u → IsCutSol R w → u 0 ∈ seqSobolev38 m → w 0 ∈ seqSobolev38 m →
    hn m (u 0) ≤ ρ → hn m (w 0) ≤ ρ →
    ∀ t, hn m (fun n => u t n - w t n) ≤ Real.exp (L * |t|) * hn m (fun n => u 0 n - w 0 n) := by
  obtain ⟨M, hM, hMb⟩ := wl2_cutfield_sub38 m hm
  obtain ⟨C, hC, hCb⟩ := cutSol_wK_bound38 m hm
  obtain ⟨L1, hL1⟩ := cutSol_lipschitz R hR
  set ρ' : ℝ := max ρ 0 with hρ'
  have hρ0 : 0 ≤ ρ' := le_max_right _ _
  set K0 : ℝ := M * R ^ 2 with hK0
  set c : ℝ := 2 * M * R * ρ' with hc
  set L2 : ℝ := C * R ^ 2 + L1 with hL2
  have hK0pos : 0 < K0 := by positivity
  have hc0 : 0 ≤ c := by positivity
  have hL20 : 0 ≤ L2 := by positivity
  refine ⟨K0 + c + L2, by positivity, fun u w hu hw hu0 hw0 hρu hρw t => ?_⟩
  obtain ⟨vu, hcu, hdu⟩ := cutSol_interaction38 hu
  obtain ⟨vw, hcw, hdw⟩ := cutSol_interaction38 hw
  set H0 : ℝ := hn m (fun n => u 0 n - w 0 n) with hH0
  have hH00 : 0 ≤ H0 := hn_nonneg38 _ _
  have hd0 : (fun n => u 0 n - w 0 n) ∈ seqSobolev38 (m : ℝ) := sub_mem_nat38 m hu0 hw0
  have hd1 : ∀ s, (fun n => u s n - w s n) ∈ seqSobolev38 ((1 : ℕ) : ℝ) := fun s =>
    sub_mem_nat38 1 (hu.mem s) (hw.mem s)
  set T : ℝ := |t| with hT
  have hT0 : 0 ≤ T := abs_nonneg t
  -- truncated bound, uniformly in K
  have hK : ∀ K : ℕ, wl2 (wK m K) (fun n => u t n - w t n) ≤
      H0 * Real.exp ((K0 + c + L2) * T) := by
    intro K
    set F : ℝ → H0C38 := fun s => TK38 m K (vu s - vw s) with hF
    set F' : ℝ → H0C38 := fun s => TK38 m K (Gc 1 le_rfl R s (vu s) - Gc 1 le_rfl R s (vw s)) with hF'
    have hFd : ∀ s, HasDerivAt F (F' s) s := fun s =>
      hasDerivAt_TK38 m K ((hdu s).sub (hdw s))
    have hFn : ∀ s, ‖F s‖ = wl2 (wK m K) (fun n => u s n - w s n) := fun s =>
      norm_TK_sub_vs38 m K s (hcu s) (hcw s)
    have hph : ∀ s, phase s (carrierCoe38 ((1 : ℕ) : ℝ) (vu s)) = u s := fun s => by
      rw [hcu s, phase_phase_neg_apply]
    have hph' : ∀ s, phase s (carrierCoe38 ((1 : ℕ) : ℝ) (vw s)) = w s := fun s => by
      rw [hcw s, phase_phase_neg_apply]
    have hbd : ∀ s, |s| ≤ T → ‖F' s‖ ≤ K0 * ‖F s‖ + c * Real.exp (L2 * T) * H0 := by
      intro s hs
      have e1 : ‖F' s‖ = wl2 (wK m K) (fun n => ((cutoff R (hn 1 (u s)) : ℝ) : ℂ) * nonlin (u s) n -
          ((cutoff R (hn 1 (w s)) : ℝ) : ℂ) * nonlin (w s) n) := by
        simp only [hF']
        rw [norm_TK_Gc_sub38, hph, hph']
      have h2 := hMb R hR K (u s) (w s) (hu.mem s) (hw.mem s)
      rw [← e1] at h2
      -- bounds for the inhomogeneous factor
      have hus : wl2 (wK m K) (u s) ≤ ρ' * Real.exp (C * R ^ 2 * T) := by
        refine (hCb R hR u hu K s).trans ?_
        have : wl2 (wK m K) (u 0) ≤ ρ' := (wl2_wK_le_hn38 m K hm hu0).trans (hρu.trans (le_max_left _ _))
        exact mul_le_mul this (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs (by positivity)))
          (Real.exp_pos _).le hρ0
      have hws : wl2 (wK m K) (w s) ≤ ρ' * Real.exp (C * R ^ 2 * T) := by
        refine (hCb R hR w hw K s).trans ?_
        have : wl2 (wK m K) (w 0) ≤ ρ' := (wl2_wK_le_hn38 m K hm hw0).trans (hρw.trans (le_max_left _ _))
        exact mul_le_mul this (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs (by positivity)))
          (Real.exp_pos _).le hρ0
      have hlip := hL1 u w hu hw s
      have hh1 : hn 1 (fun n => u s n - w s n) ≤ Real.exp (L1 * T) * H0 := by
        refine hlip.trans ?_
        refine mul_le_mul (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs (by positivity)))
          ?_ (hn_nonneg38 _ _) (Real.exp_pos _).le
        exact hn_one_le_hn38 m hm _ hd0
      have hmain : R * (wl2 (wK m K) (u s) + wl2 (wK m K) (w s)) * hn 1 (fun n => u s n - w s n) ≤
          2 * R * ρ' * Real.exp (L2 * T) * H0 := by
        have hsum : wl2 (wK m K) (u s) + wl2 (wK m K) (w s) ≤ 2 * (ρ' * Real.exp (C * R ^ 2 * T)) := by
          linarith
        have hex : Real.exp (L2 * T) = Real.exp (C * R ^ 2 * T) * Real.exp (L1 * T) := by
          rw [← Real.exp_add, hL2]; congr 1; ring
        calc R * (wl2 (wK m K) (u s) + wl2 (wK m K) (w s)) * hn 1 (fun n => u s n - w s n)
            ≤ R * (2 * (ρ' * Real.exp (C * R ^ 2 * T))) * (Real.exp (L1 * T) * H0) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hsum hR.le) hh1 (hn_nonneg38 _ _) (by positivity)
          _ = 2 * R * ρ' * Real.exp (L2 * T) * H0 := by rw [hex]; ring
      rw [hFn s] at *
      calc ‖F' s‖ ≤ M * (R ^ 2 * wl2 (wK m K) (fun n => u s n - w s n) +
            R * (wl2 (wK m K) (u s) + wl2 (wK m K) (w s)) * hn 1 (fun n => u s n - w s n)) := h2
        _ ≤ M * (R ^ 2 * wl2 (wK m K) (fun n => u s n - w s n) +
            2 * R * ρ' * Real.exp (L2 * T) * H0) :=
            mul_le_mul_of_nonneg_left (add_le_add_right hmain _) hM.le
        _ = K0 * wl2 (wK m K) (fun n => u s n - w s n) + c * Real.exp (L2 * T) * H0 := by
            rw [hK0, hc]; ring
    have h0 : ‖F 0‖ ≤ H0 := by
      rw [hFn 0]
      exact (wl2_wK_le_hn38 m K hm hd0)
    have hG := gronwall_two_sided_vec38 hFd hK0pos (by positivity) hbd h0 t (le_of_eq hT.symm)
    rw [hFn t, ← hT] at hG
    refine hG.trans ?_
    have h1 := one_add_le_exp_mul38 hc0 hL20 hT0
    have h2 : Real.exp ((K0 + c + L2) * T) = Real.exp (K0 * T) * Real.exp ((c + L2) * T) := by
      rw [← Real.exp_add]; congr 1; ring
    calc H0 * Real.exp (K0 * T) + c * Real.exp (L2 * T) * H0 * T * Real.exp (K0 * T)
        = H0 * Real.exp (K0 * T) * (1 + c * T * Real.exp (L2 * T)) := by ring
      _ ≤ H0 * Real.exp (K0 * T) * Real.exp ((c + L2) * T) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = H0 * Real.exp ((K0 + c + L2) * T) := by rw [h2]; ring
  obtain ⟨-, hfin⟩ := mem_and_hn_le_of_wK38 m (hd1 t) hK
  rw [mul_comm]
  exact hfin

/-! ## Regression probes -/

/-- Probe `u = w`: the difference vanishes and the theorem returns the (trivial) bound `0 ≤ 0`. -/
theorem cutSol_stability_hm_self38 (m : ℕ) (hm : 1 ≤ m) (R ρ : ℝ) (hR : 0 < R) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u, IsCutSol R u → u 0 ∈ seqSobolev38 m → hn m (u 0) ≤ ρ → ∀ t,
      hn m (fun n => u t n - u t n) = 0 ∧
      hn m (fun n => u t n - u t n) ≤ Real.exp (L * |t|) * hn m (fun n => u 0 n - u 0 n) := by
  obtain ⟨L, hL, h⟩ := cutSol_stability_hm m hm R ρ hR
  refine ⟨L, hL, fun u hu hu0 hρ t => ⟨?_, h u u hu hu hu0 hu0 hρ hρ t⟩⟩
  simp [hn]

/-- Plane-wave probe, equal moduli: the difference of two plane waves with the same wave number and
`‖a‖ = ‖b‖` has constant `h^m` norm, consistent with the stability bound with `L = 0`. -/
theorem planeWave_diff_const38 (m : ℕ) (k : ℤ) (a b : ℂ) (hab : ‖a‖ = ‖b‖) (t : ℝ) :
    hn m (fun n => (Pi.single k (planeWaveAmp38 k a t) : ℤ → ℂ) n - (Pi.single k (planeWaveAmp38 k b t) : ℤ → ℂ) n) =
      hn m (fun n => (Pi.single k a : ℤ → ℂ) n - (Pi.single k b : ℤ → ℂ) n) := by
  have e : ∀ c : ℂ, (fun n => (Pi.single k (planeWaveAmp38 k a t) : ℤ → ℂ) n - (Pi.single k (planeWaveAmp38 k b t) : ℤ → ℂ) n) =
      Pi.single k (planeWaveAmp38 k a t - planeWaveAmp38 k b t) := fun c => by
    funext n; by_cases h : n = k
    · subst h; simp
    · simp [h]
  have e0 : (fun n => (Pi.single k a : ℤ → ℂ) n - (Pi.single k b : ℤ → ℂ) n) = Pi.single k (a - b) := by
    funext n; by_cases h : n = k
    · subst h; simp
    · simp [h]
  rw [e 0, e0, hn_single38, hn_single38]
  congr 1
  unfold planeWaveAmp38
  rw [← hab, ← mul_sub, norm_mul, norm_phaseFactor, one_mul]

/-- Plane-wave probe: two plane waves with the same wave number, as an instance of A6b. -/
theorem planeWave_stability_probe38 (m : ℕ) (hm : 1 ≤ m) (R : ℝ) (hR : 0 < R) (k : ℤ) (a b : ℂ)
    (ha : Real.sqrt ((1 + (k : ℝ) ^ 2) * ‖a‖ ^ 2) ≤ R) (hb : Real.sqrt ((1 + (k : ℝ) ^ 2) * ‖b‖ ^ 2) ≤ R) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t,
      hn m (fun n => (Pi.single k (planeWaveAmp38 k a t) : ℤ → ℂ) n - (Pi.single k (planeWaveAmp38 k b t) : ℤ → ℂ) n) ≤
        Real.exp (L * |t|) * hn m (fun n => (Pi.single k a : ℤ → ℂ) n - (Pi.single k b : ℤ → ℂ) n) := by
  obtain ⟨L, hL, h⟩ := cutSol_stability_hm m hm R (japaneseBracket k ^ m * max ‖a‖ ‖b‖) hR
  have h0 : ∀ c : ℂ, planeWaveAmp38 k c 0 = c := fun c => by simp [planeWaveAmp38]
  refine ⟨L, hL, fun t => ?_⟩
  have := h _ _ (isCutSol_planeWave R k a ha) (isCutSol_planeWave R k b hb)
    (single_mem_seqSobolev38 _ k _) (single_mem_seqSobolev38 _ k _)
    (by simp only [h0, hn_single38]
        exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by have := japaneseBracket_pos k; positivity))
    (by simp only [h0, hn_single38]
        exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by have := japaneseBracket_pos k; positivity)) t
  simpa only [h0] using this

end NlsGge.NLS38
