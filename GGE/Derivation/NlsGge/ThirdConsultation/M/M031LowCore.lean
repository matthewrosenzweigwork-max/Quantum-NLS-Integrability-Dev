import Mathlib
import NlsGge.ThirdConsultation.M.M030Label

/-!
# M-031 support (A, core): low-label real-part bound `|Re λ| ≤ (8Q² - 1/2)π` (proof development, AUTHOR; not self-reviewed)

Source: Molnar Thm 5 central box, via the landed labelling induction of M030Label (proof development).
`m031_split_two_sided`: the induction of `M030L.split_ray_up` (and its reflection, exactly as inside
`M030L.split_ray_down`, whose conclusion does not export the split) yields the splits at both thresholded edges
`Mπ - π/2` and `(1-M)π - π/2`.  `low_label_re_bound_core` takes `M = ⌈8Q² - 1⌉`; every low label has index in
`[2(1-M), 2M)`, so `(1-M)π - π/2 < Re λ < Mπ - π/2`, and `M < 8Q²`.
The set-level bridge enters as the explicit argument `hbridge` (same form as in
`periodic_labels_are_local_roots_of_bridge`); it is discharged by the landed `M030Bridge.perChar_zero_schurDet_zero`
in M031Low.  The strip/count facts `hstripm`, `hcardm` repeat the (non-exported) local steps of
`periodic_labels_are_local_roots_of_bridge` with the same landed lemmas.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M

open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation Metric Set

/-- Splits at both thresholded edges `M` and `1 - M`. -/
theorem m031_split_two_sided (r : ℤ → ℝ) (P : ℤ → ℤ → Prop) (hmono : Monotone r)
    (hPre : ∀ m k : ℤ, P m k → |r k - (m : ℝ) * Real.pi| < Real.pi / 4)
    (M : ℤ) (hM : 0 ≤ M)
    (hstrip : ∀ m : ℤ, M ≤ |m| → ∀ k : ℤ, |r k - (m : ℝ) * Real.pi| ≤ Real.pi / 2 → P m k)
    (hcard : ∀ m : ℤ, M ≤ |m| → ∀ S : Finset ℤ, (∀ k : ℤ, P m k ↔ k ∈ S) → S.card = 2)
    (Nc : ℤ) (hNc : 0 ≤ Nc)
    (hbase : ∀ m : ℤ, Nc + 1 ≤ m ∨ m ≤ -Nc → M030L.SplitAt r m) :
    M030L.SplitAt r M ∧ M030L.SplitAt r (1 - M) := by
  classical
  have habs1 : ∀ m : ℤ, M ≤ m → M ≤ |m| := fun m hm => hm.trans (le_abs_self m)
  have habs2 : ∀ m : ℤ, m ≤ -M → M ≤ |m| := fun m hm => by
    rw [← abs_neg m]; exact (show M ≤ -m by omega).trans (le_abs_self _)
  refine ⟨?_, ?_⟩
  · exact (M030L.split_ray_up r P hmono hPre M (fun m hm => hstrip m (habs1 m hm))
      (fun m hm => hcard m (habs1 m hm)) (-Nc) (by omega) (hbase (-Nc) (Or.inr le_rfl))
      (Nc + 1) (fun m hm => hbase m (Or.inl hm)) M le_rfl).1
  · set r' : ℤ → ℝ := fun k => -r (1 - k) with hr'
    set P' : ℤ → ℤ → Prop := fun m k => P (-m) (1 - k) with hP'
    have hmono' : Monotone r' := by
      intro k k' hkk'
      show -r (1 - k) ≤ -r (1 - k')
      have := hmono (show 1 - k' ≤ 1 - k by omega)
      linarith
    have hPre' : ∀ m k : ℤ, P' m k → |r' k - (m : ℝ) * Real.pi| < Real.pi / 4 := by
      intro m k hk
      have := hPre (-m) (1 - k) hk
      push_cast at this
      show |-r (1 - k) - (m : ℝ) * Real.pi| < Real.pi / 4
      rw [show -r (1 - k) - (m : ℝ) * Real.pi = -(r (1 - k) - -(m : ℝ) * Real.pi) by ring, abs_neg]
      exact this
    have hstrip' : ∀ m : ℤ, M ≤ m → ∀ k : ℤ, |r' k - (m : ℝ) * Real.pi| ≤ Real.pi / 2 → P' m k := by
      intro m hm k hk
      apply hstrip (-m) (habs2 (-m) (by omega)) (1 - k)
      push_cast
      have : r' k - (m : ℝ) * Real.pi = -(r (1 - k) - -(m : ℝ) * Real.pi) := by
        simp only [hr']; ring
      rw [this, abs_neg] at hk
      exact hk
    have hcard' : ∀ m : ℤ, M ≤ m → ∀ S : Finset ℤ, (∀ k : ℤ, P' m k ↔ k ∈ S) → S.card = 2 := by
      intro m hm S hS
      have hinj : Function.Injective (fun k : ℤ => 1 - k) := by
        intro x y hxy
        simp only at hxy
        omega
      have himg : ∀ j : ℤ, P (-m) j ↔ j ∈ S.image (fun k : ℤ => 1 - k) := by
        intro j
        rw [Finset.mem_image]
        constructor
        · intro hj
          refine ⟨1 - j, (hS (1 - j)).mp ?_, by ring⟩
          show P (-m) (1 - (1 - j))
          rw [show 1 - (1 - j) = j by ring]
          exact hj
        · rintro ⟨k, hk, rfl⟩
          exact (hS k).mpr hk
      have := hcard (-m) (habs2 (-m) (by omega)) _ himg
      rw [Finset.card_image_of_injective _ hinj] at this
      exact this
    have hDa' : M030L.SplitAt r' (1 - (Nc + 1)) :=
      M030L.split_reflect r (1 - (Nc + 1))
        (by rw [show 1 - (1 - (Nc + 1)) = Nc + 1 by ring]; exact hbase _ (Or.inl le_rfl))
    have hDM' : ∀ m : ℤ, 1 - (-Nc) ≤ m → M030L.SplitAt r' m := by
      intro m hm
      exact M030L.split_reflect r m (hbase (1 - m) (Or.inr (by omega)))
    have key := (M030L.split_ray_up r' P' hmono' hPre' M hstrip' hcard' (1 - (Nc + 1)) (by omega) hDa'
      (1 - (-Nc)) hDM' M le_rfl).1
    have hback := M030L.split_reflect r' (1 - M) (by rw [show 1 - (1 - M) = M by ring]; exact key)
    have hfun : (fun k => -r' (1 - k)) = r := by
      funext k
      simp only [hr']
      rw [show 1 - (1 - k) = k by ring]
      ring
    rw [hfun] at hback
    exact hback

/-- (A) core: the low labels lie in the printed real box, given the set-level bridge. -/
theorem low_label_re_bound_core
    (w : ℤ → ℝ) (hw : OneDerivativeWeight w) (φ : PotPair)
    (hφ : MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤)
    (hbridge : ∀ ψ : PotPair, MTwoMode.potentialCoefficientEnergy w ψ ≠ ⊤ → ∀ m : ℤ,
      8 * MTwoMode.potentialCoefficientNorm w ψ ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight m →
      ∀ z : ℂ, ∀ hz : z ∈ NlsGge.Atomic.KST004.spectralStrip m, perChar ψ z = 0 →
        MTwoMode.schurDet ψ m z hz = 0) :
    let Q : ℝ := MTwoMode.potentialCoefficientNorm w φ
    ∀ n : ℤ, NlsGge.Atomic.M.M054.indexWeight n < 8 * Q ^ 2 → ∀ plus : Bool,
      |(if plus then lamPlus φ n else lamMinus φ n).re| ≤ (8 * Q ^ 2 - 1 / 2) * Real.pi := by
  intro Q n hn plus
  have hpi := Real.pi_pos
  -- strip and count facts on the thresholded strips (as in `periodic_labels_are_local_roots_of_bridge`)
  have hloc : ∀ ψ : PotPair, MTwoMode.potentialCoefficientEnergy w ψ ≠ ⊤ → ∀ m : ℤ,
      8 * MTwoMode.potentialCoefficientNorm w ψ ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight m →
      ∀ z : ℂ, z ∈ NlsGge.Atomic.KST004.spectralStrip m → perChar ψ z = 0 →
        ‖z - countingCenter38 m‖ ≤ Real.pi / 5 := by
    intro ψ hψ m hm z hz h0
    have hd := M030L.schur_zero_mem_disc w hw ψ hψ m hm z hz (hbridge ψ hψ m hm z hz h0)
    have := (local_spectral_disc_in_strip w hw ψ hψ m hm).1 hd
    rw [mem_closedBall, dist_eq_norm] at this
    exact this
  have hstripm : ∀ m : ℤ, 8 * Q ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight m → ∀ k : ℤ,
      |(lamSeq φ k).re - (m : ℝ) * Real.pi| ≤ Real.pi / 2 →
        lamSeq φ k ∈ ball (countingCenter38 m) (Real.pi / 4) := by
    intro m hm k hk
    have hz : lamSeq φ k ∈ NlsGge.Atomic.KST004.spectralStrip m := hk
    have := hloc φ hφ m hm _ hz ((lamSeq_enumeration38 φ).1 k)
    rw [mem_ball, dist_eq_norm]
    linarith
  have hcardm : ∀ m : ℤ, 8 * Q ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight m →
      ∀ S : Finset ℤ, (∀ k : ℤ, lamSeq φ k ∈ ball (countingCenter38 m) (Real.pi / 4) ↔ k ∈ S) →
        S.card = 2 := by
    intro m hm S hS
    apply M030L.lamSeq_window_card φ m _ S hS
    apply M030L.card_two_of_homotopy φ m
    intro s hs0 hs1 z hz h0
    have hψ : MTwoMode.potentialCoefficientEnergy w (((s : ℝ) : ℂ) • φ) ≠ ⊤ :=
      ne_top_of_le_ne_top hφ (M030L.energy_smul_le w φ s hs0 hs1)
    have hN := M030L.norm_smul_le w φ hφ s hs0 hs1
    have hth : 8 * MTwoMode.potentialCoefficientNorm w (((s : ℝ) : ℂ) • φ) ^ 2 ≤
        NlsGge.Atomic.M.M054.indexWeight m := by
      have h0' : 0 ≤ MTwoMode.potentialCoefficientNorm w (((s : ℝ) : ℂ) • φ) := Real.sqrt_nonneg _
      have := pow_le_pow_left₀ h0' hN 2
      linarith
    rw [mem_sphere, dist_eq_norm] at hz
    have hzs : z ∈ NlsGge.Atomic.KST004.spectralStrip m := by
      show |z.re - (m : ℝ) * Real.pi| ≤ Real.pi / 2
      have := M030L.abs_re_sub_center_le z m
      linarith
    have := hloc _ hψ m hth z hzs h0
    linarith
  -- the first thresholded index
  have hn' : 1 + |(n : ℝ)| < 8 * Q ^ 2 := hn
  set M : ℤ := ⌈8 * Q ^ 2 - 1⌉ with hMdef
  have hMge : 8 * Q ^ 2 - 1 ≤ (M : ℝ) := Int.le_ceil _
  have hMlt : (M : ℝ) < 8 * Q ^ 2 - 1 + 1 := Int.ceil_lt_add_one _
  have hnM : |n| < M := by
    have h1 : ((|n| : ℤ) : ℝ) < (M : ℝ) := by
      rw [Int.cast_abs]
      have := abs_nonneg (n : ℝ)
      linarith
    exact_mod_cast h1
  have hM0 : 0 ≤ M := (abs_nonneg n).trans hnM.le
  have hthr : ∀ m : ℤ, M ≤ |m| → 8 * Q ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight m := by
    intro m hm
    unfold NlsGge.Atomic.M.M054.indexWeight
    have : ((M : ℤ) : ℝ) ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast hm
    rw [Int.cast_abs] at this
    linarith
  set Nc : ℤ := (canonicalCountingCutoff38 φ : ℤ) with hNc
  obtain ⟨hsU, hsD⟩ := m031_split_two_sided (fun k => (lamSeq φ k).re)
    (fun m k => lamSeq φ k ∈ ball (countingCenter38 m) (Real.pi / 4))
    (M030L.lamSeq_re_mono φ) (fun m k hk => M030L.re_sub_center_lt hk) M hM0
    (fun m hm => hstripm m (hthr m hm)) (fun m hm => hcardm m (hthr m hm))
    Nc (by omega) (fun m hm => M030L.lamSeq_split_base φ m hm)
  have hnb := abs_lt.mp hnM
  have hk : ∃ k : ℤ, (if plus then lamPlus φ n else lamMinus φ n) = lamSeq φ k ∧
      2 * (1 - M) ≤ k ∧ k < 2 * M := by
    cases plus
    · exact ⟨2 * n, rfl, by omega, by omega⟩
    · exact ⟨2 * n + 1, rfl, by omega, by omega⟩
  obtain ⟨k, hzk, hk1, hk2⟩ := hk
  rw [hzk]
  have hup : (lamSeq φ k).re < (M : ℝ) * Real.pi - Real.pi / 2 := hsU.2 k hk2
  have hlo : ((1 - M : ℤ) : ℝ) * Real.pi - Real.pi / 2 < (lamSeq φ k).re := hsD.1 k hk1
  push_cast at hlo
  rw [abs_le]
  constructor <;> nlinarith

end NlsGge.ThirdConsultation.M

end
