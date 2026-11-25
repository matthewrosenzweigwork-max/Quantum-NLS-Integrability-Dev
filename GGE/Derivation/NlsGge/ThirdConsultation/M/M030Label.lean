import Mathlib
import NlsGge.ThirdConsultation.M.M029Core
import NlsGge.ThirdConsultation.M.M029Disc
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.GK38.PeriodicLabellingWindows
import NlsGge.GK38.PeriodicLabellingFreeModel
import NlsGge.GK38.PairCompact
import NlsGge.GK38.Lib.Rouche

/-!
# M-030 / M-031 support: thresholded canonical labels are the two local Schur roots
(proof development, AUTHOR; not self-reviewed)

`periodic_labels_are_local_roots_of_bridge`: for every index `n` with `8 Q^2 <= <n>` the canonical labels
`lamMinus φ n = lamSeq φ (2n)`, `lamPlus φ n = lamSeq φ (2n+1)` lie in the strip, in `localSpectralDisc`, and are zeros
of `schurDet`.  The only input beyond landed/kit results is the explicit, separately proved set-level bridge
`hbridge` (a zero of `perChar ψ` in the strip of a thresholded `ψ` is a zero of `schurDet ψ`), proved in
`NlsGge.ThirdConsultation.M.M030Bridge` (`perChar_zero_schurDet_zero`).

Route (see M030Label_ROUTE.md):
* zeros of `perChar` in a thresholded strip lie in the closed disc of radius `π/5` (bridge + `schur_has_two_roots_core`
  + `local_spectral_disc_in_strip`);
* the small-disc zero count is `2` by the homotopy `s ↦ s • φ`, `s ∈ [0,1]` (landed `Lib.zeroCount_locallyConstant`,
  `discrim_L2_continuous`, `counting_free_small_card38`), since energy and threshold are monotone under the scaling;
* the canonical enumeration `lamSeq` has monotone real parts, and is split at every strip edge outside the canonical
  cutoff; a downward induction (and its reflection for negative indices) along the thresholded ray, with the window count
  `rootEnumeration_window_multiset38`, places `lamSeq (2n)`, `lamSeq (2n+1)` in the small disc of `n`.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M030L

open NlsGge.GK38 Metric Set

/-- The split of a real-part sequence at the strip edge `mπ - π/2`: indices from `2m` on lie strictly to the
right of the edge and earlier indices strictly to the left. -/
def SplitAt (r : ℤ → ℝ) (m : ℤ) : Prop :=
  (∀ k : ℤ, 2 * m ≤ k → (m : ℝ) * Real.pi - Real.pi / 2 < r k) ∧
  (∀ k : ℤ, k < 2 * m → r k < (m : ℝ) * Real.pi - Real.pi / 2)

/-- One downward step of the labelling induction. -/
theorem split_step (r : ℤ → ℝ) (P : ℤ → ℤ → Prop) (hmono : Monotone r)
    (hPre : ∀ m k : ℤ, P m k → |r k - (m : ℝ) * Real.pi| < Real.pi / 4)
    (m : ℤ)
    (hstrip : ∀ k : ℤ, |r k - (m : ℝ) * Real.pi| ≤ Real.pi / 2 → P m k)
    (hcard : ∀ S : Finset ℤ, (∀ k : ℤ, P m k ↔ k ∈ S) → S.card = 2)
    (lo : ℤ) (hlo : ∀ k : ℤ, k < lo → r k ≤ (m : ℝ) * Real.pi - Real.pi / 2)
    (hD1 : SplitAt r (m + 1)) :
    SplitAt r m ∧ P m (2 * m) ∧ P m (2 * m + 1) := by
  classical
  have hpi := Real.pi_pos
  obtain ⟨hD1a, hD1b⟩ := hD1
  have hD1a' : ∀ k : ℤ, 2 * m + 2 ≤ k → (m : ℝ) * Real.pi + Real.pi / 2 < r k := by
    intro k hk
    have := hD1a k (by omega)
    push_cast at this
    linarith
  have hD1b' : ∀ k : ℤ, k ≤ 2 * m + 1 → r k < (m : ℝ) * Real.pi + Real.pi / 2 := by
    intro k hk
    have := hD1b k (by omega)
    push_cast at this
    linarith
  set S : Finset ℤ := (Finset.Icc lo (2 * m + 1)).filter (fun k => P m k) with hSdef
  have hS : ∀ k : ℤ, P m k ↔ k ∈ S := by
    intro k
    rw [hSdef, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro hk
      have h1 := abs_lt.mp (hPre m k hk)
      refine ⟨⟨?_, ?_⟩, hk⟩
      · by_contra h
        push_neg at h
        have := hlo k h
        linarith
      · by_contra h
        push_neg at h
        have := hD1a' k (by omega)
        linarith
    · exact fun h => h.2
  have hc := hcard S hS
  have hup : ∀ k k' : ℤ, k ∈ S → k ≤ k' → k' ≤ 2 * m + 1 → k' ∈ S := by
    intro k k' hk hkk' hk'
    rw [← hS] at hk ⊢
    apply hstrip
    have h1 := abs_lt.mp (hPre m k hk)
    have h2 := hmono hkk'
    have h3 := hD1b' k' hk'
    rw [abs_le]
    constructor <;> linarith
  have hle : ∀ k : ℤ, k ∈ S → k ≤ 2 * m + 1 := by
    intro k hk
    rw [hSdef, Finset.mem_filter, Finset.mem_Icc] at hk
    exact hk.1.2
  obtain ⟨x, y, hxy, hSxy⟩ := Finset.card_eq_two.mp hc
  have hx : x ∈ S := by rw [hSxy]; simp
  have hy : y ∈ S := by rw [hSxy]; simp
  have hxle := hle x hx
  have hyle := hle y hy
  have h2m : 2 * m ∈ S := by
    rcases le_or_gt x (2 * m) with h | h
    · exact hup x (2 * m) hx h (by omega)
    · have hy2 : y ≤ 2 * m := by omega
      exact hup y (2 * m) hy hy2 (by omega)
  have h2m1 : 2 * m + 1 ∈ S := hup (2 * m) (2 * m + 1) h2m (by omega) le_rfl
  have hSeq : S = {2 * m, 2 * m + 1} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro k hk
      rw [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact h2m
      · exact h2m1
    · rw [hc, Finset.card_pair (by omega)]
  refine ⟨⟨?_, ?_⟩, (hS _).mpr h2m, (hS _).mpr h2m1⟩
  · intro k hk
    by_cases hk2 : 2 * m + 2 ≤ k
    · have := hD1a' k hk2
      linarith
    · have hkS : k ∈ S := by
        rw [hSeq, Finset.mem_insert, Finset.mem_singleton]
        omega
      have := abs_lt.mp (hPre m k ((hS k).mpr hkS))
      linarith [this.1]
  · intro k hk
    by_contra hcon
    push_neg at hcon
    have h3 := hD1b' k (by omega)
    have hP : P m k := hstrip k (by rw [abs_le]; constructor <;> linarith)
    have := (hS k).mp hP
    rw [hSeq, Finset.mem_insert, Finset.mem_singleton] at this
    omega

/-- Downward induction from a high split to every index of a ray `m ≥ m0`. -/
theorem split_ray_up (r : ℤ → ℝ) (P : ℤ → ℤ → Prop) (hmono : Monotone r)
    (hPre : ∀ m k : ℤ, P m k → |r k - (m : ℝ) * Real.pi| < Real.pi / 4)
    (m0 : ℤ)
    (hstrip : ∀ m : ℤ, m0 ≤ m → ∀ k : ℤ, |r k - (m : ℝ) * Real.pi| ≤ Real.pi / 2 → P m k)
    (hcard : ∀ m : ℤ, m0 ≤ m → ∀ S : Finset ℤ, (∀ k : ℤ, P m k ↔ k ∈ S) → S.card = 2)
    (a : ℤ) (ha : a ≤ m0) (hDa : SplitAt r a)
    (M : ℤ) (hDM : ∀ m : ℤ, M ≤ m → SplitAt r m) :
    ∀ m : ℤ, m0 ≤ m → SplitAt r m ∧ P m (2 * m) ∧ P m (2 * m + 1) := by
  have hpi := Real.pi_pos
  have hlo : ∀ m : ℤ, m0 ≤ m → ∀ k : ℤ, k < 2 * a → r k ≤ (m : ℝ) * Real.pi - Real.pi / 2 := by
    intro m hm k hk
    have h1 := hDa.2 k hk
    have ham : (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast ha.trans hm
    nlinarith
  have hsplit : ∀ d : ℕ, ∀ m : ℤ, m0 ≤ m → M - m ≤ (d : ℤ) → SplitAt r m := by
    intro d
    induction d with
    | zero =>
      intro m _ hd
      exact hDM m (by omega)
    | succ d ih =>
      intro m hm hd
      by_cases hMm : M ≤ m
      · exact hDM m hMm
      · have hD1 := ih (m + 1) (by omega) (by push_cast at hd; omega)
        exact (split_step r P hmono hPre m (hstrip m hm) (hcard m hm) (2 * a) (hlo m hm) hD1).1
  intro m hm
  have hD1 : SplitAt r (m + 1) := hsplit (M - (m + 1)).toNat (m + 1) (by omega) (by omega)
  exact split_step r P hmono hPre m (hstrip m hm) (hcard m hm) (2 * a) (hlo m hm) hD1

/-- Reflection of a real-part sequence: `r' k = - r (1 - k)`. -/
theorem split_reflect (r : ℤ → ℝ) (m : ℤ) (h : SplitAt r (1 - m)) :
    SplitAt (fun k => -r (1 - k)) m := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro k hk
    have := h2 (1 - k) (by omega)
    push_cast at this
    show (m : ℝ) * Real.pi - Real.pi / 2 < -r (1 - k)
    linarith
  · intro k hk
    have := h1 (1 - k) (by omega)
    push_cast at this
    show -r (1 - k) < (m : ℝ) * Real.pi - Real.pi / 2
    linarith

/-- The negative ray `m ≤ m1`, by reflection. -/
theorem split_ray_down (r : ℤ → ℝ) (P : ℤ → ℤ → Prop) (hmono : Monotone r)
    (hPre : ∀ m k : ℤ, P m k → |r k - (m : ℝ) * Real.pi| < Real.pi / 4)
    (m1 : ℤ)
    (hstrip : ∀ m : ℤ, m ≤ m1 → ∀ k : ℤ, |r k - (m : ℝ) * Real.pi| ≤ Real.pi / 2 → P m k)
    (hcard : ∀ m : ℤ, m ≤ m1 → ∀ S : Finset ℤ, (∀ k : ℤ, P m k ↔ k ∈ S) → S.card = 2)
    (b : ℤ) (hb : m1 + 1 ≤ b) (hDb : SplitAt r b)
    (A : ℤ) (hDA : ∀ m : ℤ, m ≤ A → SplitAt r m) :
    ∀ m : ℤ, m ≤ m1 → P m (2 * m) ∧ P m (2 * m + 1) := by
  classical
  set r' : ℤ → ℝ := fun k => -r (1 - k) with hr'
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
  have hstrip' : ∀ m : ℤ, -m1 ≤ m → ∀ k : ℤ, |r' k - (m : ℝ) * Real.pi| ≤ Real.pi / 2 → P' m k := by
    intro m hm k hk
    apply hstrip (-m) (by omega) (1 - k)
    push_cast
    have : r' k - (m : ℝ) * Real.pi = -(r (1 - k) - -(m : ℝ) * Real.pi) := by
      simp only [hr']; ring
    rw [this, abs_neg] at hk
    exact hk
  have hcard' : ∀ m : ℤ, -m1 ≤ m → ∀ S : Finset ℤ, (∀ k : ℤ, P' m k ↔ k ∈ S) → S.card = 2 := by
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
    have := hcard (-m) (by omega) _ himg
    rw [Finset.card_image_of_injective _ hinj] at this
    exact this
  have hDa' : SplitAt r' (1 - b) := by
    have := split_reflect r (1 - b) (by rw [show 1 - (1 - b) = b by ring]; exact hDb)
    exact this
  have hDM' : ∀ m : ℤ, 1 - A ≤ m → SplitAt r' m := by
    intro m hm
    exact split_reflect r m (hDA (1 - m) (by omega))
  have key := split_ray_up r' P' hmono' hPre' (-m1) hstrip' hcard' (1 - b) (by omega) hDa' (1 - A) hDM'
  intro m hm
  obtain ⟨_, h1, h2⟩ := key (-m) (by omega)
  refine ⟨?_, ?_⟩
  · have : P (-(-m)) (1 - (2 * (-m) + 1)) := h2
    rw [show -(-m) = m by ring, show 1 - (2 * (-m) + 1) = 2 * m by ring] at this
    exact this
  · have : P (-(-m)) (1 - 2 * (-m)) := h1
    rw [show -(-m) = m by ring, show 1 - 2 * (-m) = 2 * m + 1 by ring] at this
    exact this

theorem re_sub_center_lt {z : ℂ} {m : ℤ} (h : z ∈ ball (countingCenter38 m) (Real.pi / 4)) :
    |z.re - (m : ℝ) * Real.pi| < Real.pi / 4 := by
  rw [mem_ball, dist_eq_norm] at h
  have := Complex.abs_re_le_norm (z - countingCenter38 m)
  have hre : (z - countingCenter38 m).re = z.re - (m : ℝ) * Real.pi := by
    simp [countingCenter38]
  rw [hre] at this
  linarith

/-- The canonical labels have monotone real parts. -/
theorem lamSeq_re_mono (φ : PotPair) : Monotone fun k => (lamSeq φ k).re := by
  intro i j hij
  rcases (complexLexLE_iff38 _ _).mp (lamSeq_mono38 φ hij) with h | h
  · exact h.le
  · exact h.1.le

/-- Every canonical label lies either in the central counting disc or in its own small disc. -/
theorem lamSeq_regions (φ : PotPair) (k : ℤ) :
    (periodicCentralIndex38 (canonicalCountingCutoff38 φ) k ∧
      |(lamSeq φ k).re| < (canonicalCountingCutoff38 φ : ℝ) * Real.pi + Real.pi / 4) ∨
    (¬ periodicCentralIndex38 (canonicalCountingCutoff38 φ) k ∧
      |(lamSeq φ k).re - ((k / 2 : ℤ) : ℝ) * Real.pi| < Real.pi / 4) := by
  have h := (canonicalCountingCutoff_spec38 φ).1
  by_cases hk : periodicCentralIndex38 (canonicalCountingCutoff38 φ) k
  · left
    refine ⟨hk, ?_⟩
    have hm := periodicCandidate_central_mem38 h hk
    rw [mem_ball, dist_zero_right] at hm
    have := Complex.abs_re_le_norm (periodicCandidate38 (perChar φ) (canonicalCountingCutoff38 φ) k)
    unfold countingRadius38 at hm
    show |(periodicCandidate38 (perChar φ) (canonicalCountingCutoff38 φ) k).re| < _
    linarith
  · right
    exact ⟨hk, re_sub_center_lt (periodicCandidate_far_mem38 h hk)⟩

/-- Outside the canonical cutoff the canonical labels are split at every strip edge. -/
theorem lamSeq_split_base (φ : PotPair) (m : ℤ)
    (hm : (canonicalCountingCutoff38 φ : ℤ) + 1 ≤ m ∨ m ≤ -(canonicalCountingCutoff38 φ : ℤ)) :
    SplitAt (fun k => (lamSeq φ k).re) m := by
  have hpi := Real.pi_pos
  set N := canonicalCountingCutoff38 φ with hN
  have hmR : ((N : ℤ) : ℝ) + 1 ≤ (m : ℝ) ∨ (m : ℝ) ≤ -((N : ℤ) : ℝ) := by
    rcases hm with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  push_cast at hmR
  constructor
  · intro k hk
    show (m : ℝ) * Real.pi - Real.pi / 2 < (lamSeq φ k).re
    rcases lamSeq_regions φ k with ⟨hc, hre⟩ | ⟨_, hre⟩
    · unfold periodicCentralIndex38 at hc
      rcases hm with h | h
      · omega
      · rcases hmR with h' | h'
        · have : ((m : ℤ) : ℝ) ≤ -((N : ℤ) : ℝ) := by exact_mod_cast h
          push_cast at this
          have := (abs_lt.mp hre).1
          nlinarith
        · have := (abs_lt.mp hre).1
          nlinarith
    · have hq : m ≤ k / 2 := by omega
      have hqR : (m : ℝ) ≤ ((k / 2 : ℤ) : ℝ) := by exact_mod_cast hq
      have := (abs_lt.mp hre).1
      nlinarith
  · intro k hk
    show (lamSeq φ k).re < (m : ℝ) * Real.pi - Real.pi / 2
    rcases lamSeq_regions φ k with ⟨hc, hre⟩ | ⟨_, hre⟩
    · unfold periodicCentralIndex38 at hc
      rcases hm with h | h
      · have : ((N : ℤ) : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h
        push_cast at this
        have := (abs_lt.mp hre).2
        nlinarith
      · omega
    · have hq : k / 2 ≤ m - 1 := by omega
      have hqR : ((k / 2 : ℤ) : ℝ) ≤ (m : ℝ) - 1 := by
        have : ((k / 2 : ℤ) : ℝ) ≤ ((m - 1 : ℤ) : ℝ) := by exact_mod_cast hq
        push_cast at this
        exact this
      have := (abs_lt.mp hre).2
      nlinarith

/-- Window count: an index set characterizing a small disc has the disc's zero count. -/
theorem lamSeq_window_card (φ : PotPair) (m : ℤ)
    (hC : Multiset.card (Lib.zeroMultiset (perChar φ) (ball (countingCenter38 m) (Real.pi / 4))) = 2)
    (S : Finset ℤ) (hS : ∀ k : ℤ, lamSeq φ k ∈ ball (countingCenter38 m) (Real.pi / 4) ↔ k ∈ S) :
    S.card = 2 := by
  have h := rootEnumeration_window_multiset38 (canonicalCountingCutoff_spec38 φ).1
    (lamSeq_enumeration38 φ) S (countingCenter38 m) (Real.pi / 4) hS
  have := congrArg Multiset.card h
  rw [Multiset.card_map, Finset.card_val] at this
  rw [this, hC]

/-- The scaled family `s ↦ s • φ` has constant small-disc zero count when no member vanishes on the
circle; the free count is `2`. -/
theorem card_two_of_homotopy (φ : PotPair) (n : ℤ)
    (hne : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ z ∈ sphere (countingCenter38 n) (Real.pi / 4),
      perChar (((s : ℝ) : ℂ) • φ) z ≠ 0) :
    Multiset.card (Lib.zeroMultiset (perChar φ) (ball (countingCenter38 n) (Real.pi / 4))) = 2 := by
  let F : unitInterval → ℂ → ℂ := fun s z => perChar ((((s : ℝ)) : ℂ) • φ) z
  have hR : (0 : ℝ) < Real.pi / 4 := by positivity
  have hF : ∀ s : unitInterval, AnalyticOnNhd ℂ (F s) (closedBall (countingCenter38 n) (Real.pi / 4)) :=
    fun s => (analyticOnNhd_perChar_z _).mono (subset_univ _)
  have hcont : ContinuousOn (Function.uncurry F)
      (univ ×ˢ sphere (countingCenter38 n) (Real.pi / 4)) := by
    apply Continuous.continuousOn
    have hpath : Continuous fun p : unitInterval × ℂ => ((((p.1 : ℝ)) : ℂ) • φ, p.2) := by
      refine Continuous.prodMk ?_ continuous_snd
      exact (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).smul
        continuous_const
    have hd := discrim_L2_continuous.comp hpath
    have : Function.uncurry F = fun p : unitInterval × ℂ =>
        (discrim ((((p.1 : ℝ)) : ℂ) • φ) p.2) ^ 2 - 4 := by
      funext p
      rfl
    rw [this]
    exact (hd.pow 2).sub continuous_const
  have hne' : ∀ s : unitInterval, ∀ z ∈ sphere (countingCenter38 n) (Real.pi / 4), F s z ≠ 0 :=
    fun s z hz => hne s s.2.1 s.2.2 z hz
  have hlc := Lib.zeroCount_locallyConstant hR hF hcont hne'
  have heq := hlc.apply_eq_of_preconnectedSpace (0 : unitInterval) (1 : unitInterval)
  have h0 : F 0 = perChar 0 := by
    funext z
    show perChar ((((0 : ℝ)) : ℂ) • φ) z = perChar 0 z
    rw [Complex.ofReal_zero, zero_smul]
  have h1 : F 1 = perChar φ := by
    funext z
    show perChar ((((1 : ℝ)) : ℂ) • φ) z = perChar φ z
    rw [Complex.ofReal_one, one_smul]
  have heq' : Multiset.card (Lib.zeroMultiset (F 0) (ball (countingCenter38 n) (Real.pi / 4))) =
      Multiset.card (Lib.zeroMultiset (F 1) (ball (countingCenter38 n) (Real.pi / 4))) := heq
  rw [h0, h1, counting_free_small_card38 n] at heq'
  exact heq'.symm

/-! ### Scaling of the potential pair -/

theorem coeff_smul (c : ℂ) (φ : PotPair) (b : Bool) (k : ℤ) :
    MTwoMode.potentialCoefficientPair (c • φ) b k = c * MTwoMode.potentialCoefficientPair φ b k := by
  unfold MTwoMode.potentialCoefficientPair
  have h1 : (if b then (c • φ).1 else (c • φ).2) = c • (if b then φ.1 else φ.2) := by
    cases b <;> rfl
  rw [h1, map_smul,
    fourierCoeff_congr_ae (MeasureTheory.Lp.coeFn_smul c
      (NlsGge.Analysis.naturalPhysicalCoverL2 (if b then φ.1 else φ.2))),
    fourierCoeff.const_smul, smul_eq_mul]

theorem energy_smul_le (w : ℤ → ℝ) (φ : PotPair) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    MTwoMode.potentialCoefficientEnergy w (((s : ℝ) : ℂ) • φ) ≤
      MTwoMode.potentialCoefficientEnergy w φ := by
  unfold MTwoMode.potentialCoefficientEnergy
  refine ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal ?_
  rw [coeff_smul, coeff_smul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0]
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have ha := sq_nonneg ‖MTwoMode.potentialCoefficientPair φ true k‖
  have hb := sq_nonneg ‖MTwoMode.potentialCoefficientPair φ false k‖
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  rw [mul_pow, mul_pow]
  nlinarith

theorem norm_smul_le (w : ℤ → ℝ) (φ : PotPair)
    (hφ : MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    MTwoMode.potentialCoefficientNorm w (((s : ℝ) : ℂ) • φ) ≤
      MTwoMode.potentialCoefficientNorm w φ := by
  unfold MTwoMode.potentialCoefficientNorm
  exact Real.sqrt_le_sqrt (ENNReal.toReal_mono hφ (energy_smul_le w φ s hs0 hs1))

/-- The threshold propagates to larger absolute indices. -/
theorem threshold_mono (Q : ℝ) {n m : ℤ}
    (h : 8 * Q ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight n) (hnm : |n| ≤ |m|) :
    8 * Q ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight m := by
  unfold NlsGge.Atomic.M.M054.indexWeight at *
  have : |(n : ℝ)| ≤ |(m : ℝ)| := by
    rw [← Int.cast_abs, ← Int.cast_abs]
    exact_mod_cast hnm
  linarith

theorem abs_re_sub_center_le (z : ℂ) (m : ℤ) :
    |z.re - (m : ℝ) * Real.pi| ≤ ‖z - countingCenter38 m‖ := by
  have := Complex.abs_re_le_norm (z - countingCenter38 m)
  have hre : (z - countingCenter38 m).re = z.re - (m : ℝ) * Real.pi := by
    simp [countingCenter38]
  rw [hre] at this
  exact this

/-- A zero of `schurDet` in the strip of a thresholded pair lies in the local spectral disc (M-029 core). -/
theorem schur_zero_mem_disc (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (ψ : PotPair) (hψ : MTwoMode.potentialCoefficientEnergy w ψ ≠ ⊤) (m : ℤ)
    (hth : 8 * MTwoMode.potentialCoefficientNorm w ψ ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight m)
    (z : ℂ) (hz : z ∈ NlsGge.Atomic.KST004.spectralStrip m)
    (h0 : MTwoMode.schurDet ψ m z hz = 0) :
    z ∈ MTwoMode.localSpectralDisc w ψ m := by
  obtain ⟨_, _, xm, xp, _, _, hxm, hxp, _, hiff⟩ :=
    NlsGge.ThirdConsultation.M.schur_has_two_roots_core w hw ψ hψ m hth
  rcases (hiff z hz).1 h0 with h | h
  · rw [h]; exact hxm
  · rw [h]; exact hxp

end NlsGge.ThirdConsultation.M030L

namespace NlsGge.ThirdConsultation.M

open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation Metric Set

/-- Thresholded canonical labels are the two local Schur roots, given the set-level `perChar`/`schurDet`
bridge `hbridge` (proved as `perChar_zero_schurDet_zero` in `M030Bridge`). -/
theorem periodic_labels_are_local_roots_of_bridge
    (w : ℤ → ℝ) (hw : OneDerivativeWeight w) (φ : PotPair)
    (hφ : MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤) (n : ℤ)
    (hthreshold : 8 * MTwoMode.potentialCoefficientNorm w φ ^ 2 ≤
      NlsGge.Atomic.M.M054.indexWeight n)
    (hbridge : ∀ ψ : PotPair, MTwoMode.potentialCoefficientEnergy w ψ ≠ ⊤ → ∀ m : ℤ,
      8 * MTwoMode.potentialCoefficientNorm w ψ ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight m →
      ∀ z : ℂ, ∀ hz : z ∈ NlsGge.Atomic.KST004.spectralStrip m, perChar ψ z = 0 →
        MTwoMode.schurDet ψ m z hz = 0) :
    ∃ (h1 : lamMinus φ n ∈ NlsGge.Atomic.KST004.spectralStrip n)
      (h2 : lamPlus φ n ∈ NlsGge.Atomic.KST004.spectralStrip n),
      lamMinus φ n ∈ MTwoMode.localSpectralDisc w φ n ∧
      lamPlus φ n ∈ MTwoMode.localSpectralDisc w φ n ∧
      MTwoMode.schurDet φ n (lamMinus φ n) h1 = 0 ∧
      MTwoMode.schurDet φ n (lamPlus φ n) h2 = 0 := by
  have hpi := Real.pi_pos
  set Q := MTwoMode.potentialCoefficientNorm w φ with hQ
  -- zeros of `perChar ψ` in a thresholded strip lie within `π/5` of the center
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
  set Nc := canonicalCountingCutoff38 φ with hNc
  have hlab : lamSeq φ (2 * n) ∈ ball (countingCenter38 n) (Real.pi / 4) ∧
      lamSeq φ (2 * n + 1) ∈ ball (countingCenter38 n) (Real.pi / 4) := by
    rcases le_or_gt 0 n with hn | hn
    · have hray : ∀ m : ℤ, n ≤ m → 8 * Q ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight m :=
        fun m hm => M030L.threshold_mono Q hthreshold (abs_le_abs hm (by omega))
      have := M030L.split_ray_up (fun k => (lamSeq φ k).re)
        (fun m k => lamSeq φ k ∈ ball (countingCenter38 m) (Real.pi / 4))
        (M030L.lamSeq_re_mono φ) (fun m k hk => M030L.re_sub_center_lt hk) n
        (fun m hm => hstripm m (hray m hm)) (fun m hm => hcardm m (hray m hm))
        (-(Nc : ℤ)) (by omega) (M030L.lamSeq_split_base φ _ (Or.inr le_rfl))
        ((Nc : ℤ) + 1) (fun m hm => M030L.lamSeq_split_base φ m (Or.inl hm)) n le_rfl
      exact ⟨this.2.1, this.2.2⟩
    · have hray : ∀ m : ℤ, m ≤ n → 8 * Q ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight m := by
        intro m hm
        refine M030L.threshold_mono Q hthreshold ?_
        rw [← abs_neg m]
        exact abs_le_abs (by omega) (by omega)
      exact M030L.split_ray_down (fun k => (lamSeq φ k).re)
        (fun m k => lamSeq φ k ∈ ball (countingCenter38 m) (Real.pi / 4))
        (M030L.lamSeq_re_mono φ) (fun m k hk => M030L.re_sub_center_lt hk) n
        (fun m hm => hstripm m (hray m hm)) (fun m hm => hcardm m (hray m hm))
        ((Nc : ℤ) + 1) (by omega) (M030L.lamSeq_split_base φ _ (Or.inl le_rfl))
        (-(Nc : ℤ)) (fun m hm => M030L.lamSeq_split_base φ m (Or.inr hm)) n le_rfl
  obtain ⟨hm, hp⟩ := hlab
  have hs1 : lamMinus φ n ∈ NlsGge.Atomic.KST004.spectralStrip n := by
    show |(lamSeq φ (2 * n)).re - (n : ℝ) * Real.pi| ≤ Real.pi / 2
    have := abs_lt.mp (M030L.re_sub_center_lt hm)
    rw [abs_le]
    constructor <;> linarith
  have hs2 : lamPlus φ n ∈ NlsGge.Atomic.KST004.spectralStrip n := by
    show |(lamSeq φ (2 * n + 1)).re - (n : ℝ) * Real.pi| ≤ Real.pi / 2
    have := abs_lt.mp (M030L.re_sub_center_lt hp)
    rw [abs_le]
    constructor <;> linarith
  have hd1 : MTwoMode.schurDet φ n (lamMinus φ n) hs1 = 0 :=
    hbridge φ hφ n hthreshold _ hs1 ((lamSeq_enumeration38 φ).1 (2 * n))
  have hd2 : MTwoMode.schurDet φ n (lamPlus φ n) hs2 = 0 :=
    hbridge φ hφ n hthreshold _ hs2 ((lamSeq_enumeration38 φ).1 (2 * n + 1))
  exact ⟨hs1, hs2, M030L.schur_zero_mem_disc w hw φ hφ n hthreshold _ hs1 hd1,
    M030L.schur_zero_mem_disc w hw φ hφ n hthreshold _ hs2 hd2, hd1, hd2⟩

end NlsGge.ThirdConsultation.M

end
