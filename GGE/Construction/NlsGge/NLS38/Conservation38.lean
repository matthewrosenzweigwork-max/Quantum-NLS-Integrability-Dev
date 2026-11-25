import NlsGge.NLS38.Persistence38

/-! # GWP piece A7b: conservation of mass and energy inside the cutoff, and the no-exit lemma

Plan: `campaign/GWP_PLAN.md` §7 Part A, piece A7b.

* `conserved_inside`: for an `h¹` cutoff solution with `h³` data, mass and energy are constant on any
  time interval `[0, t]` (or `[t, 0]`) along which `‖u s‖_{h¹} < R`.  On such an interval the cutoff
  equals `1` at every point (`cutoff_eq_one`), `cutSol_C1_h1` (A6a) makes `u` a `C¹` curve of the
  `h¹` carrier, and the derivatives of `mass`, `kin`, `quart` (A7a) cancel:
  `d/dt mass = 2 Re ⟨u, -i(Λu + N)⟩ = 2 Im (kin + 2 quart) = 0` and
  `d/dt ham = 2 Re ⟨y, -i y⟩ = 0`, `y = Λu + N(u) ∈ ℓ²`.
* `no_exit`: a continuity (first exit time) argument for a real function.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff Set
open scoped ComplexConjugate NNReal

/-! ## Pairing identities on sequences -/

theorem summable_conj_mul38 {x y : ℤ → ℂ} (hx : Summable fun n => ‖x n‖ ^ 2)
    (hy : Summable fun n => ‖y n‖ ^ 2) : Summable fun n => conj (x n) * y n := by
  refine Summable.of_norm_bounded ((hx.add hy).mul_left (1 / 2)) fun n => ?_
  rw [norm_mul, Complex.norm_conj]
  nlinarith [sq_nonneg (‖x n‖ - ‖y n‖)]

theorem nonlin_summable_sq38 {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    Summable fun n => ‖nonlin x n‖ ^ 2 :=
  summable_sq_of_h1 (nonlin_mem38 1 le_rfl x hx)

theorem tsum_disp_pairing38 {x : ℤ → ℂ} :
    ∑' n, ((disp n : ℝ) : ℂ) * (conj (x n) * x n) = ((kin x : ℝ) : ℂ) := by
  unfold kin
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [Complex.conj_mul']
  push_cast
  ring

theorem tsum_nonlin_pairing38 {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    ∑' n, conj (x n) * nonlin x n = ((2 * quart x : ℝ) : ℂ) := by
  obtain ⟨him, hre⟩ := inner_nonlin_real hx
  apply Complex.ext
  · rw [hre, Complex.ofReal_re]
  · rw [him, Complex.ofReal_im]

/-- Mass: `Re ⟨x, -i(Λx + N(x))⟩ = 0`. -/
theorem re_mass_pairing38 {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    (∑' n, conj (x n) * (-Complex.I * (((disp n : ℝ) : ℂ) * x n + nonlin x n))).re = 0 := by
  have hs1 : Summable fun n => ((disp n : ℝ) : ℂ) * (conj (x n) * x n) :=
    summable_wconj disp_nonneg (summable_kin_of_h1 hx) (summable_kin_of_h1 hx)
  have hs2 : Summable fun n => conj (x n) * nonlin x n :=
    summable_conj_mul38 (summable_sq_of_h1 hx) (nonlin_summable_sq38 hx)
  have e : ∀ n, conj (x n) * (-Complex.I * (((disp n : ℝ) : ℂ) * x n + nonlin x n)) =
      -Complex.I * (((disp n : ℝ) : ℂ) * (conj (x n) * x n) + conj (x n) * nonlin x n) :=
    fun n => by ring
  simp only [e]
  rw [tsum_mul_left, hs1.tsum_add hs2, tsum_disp_pairing38, tsum_nonlin_pairing38 hx]
  simp

/-- Energy: with `y = Λx + N(x)`, `D = -i y ∈ ℓ²`, `Re Σ (2πn)² x̄ D + Re Σ conj N D = Re(-i ‖y‖²) = 0`. -/
theorem re_ham_pairing38 {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ))
    (hD : (fun n => -Complex.I * (((disp n : ℝ) : ℂ) * x n + nonlin x n)) ∈
      seqSobolev38 ((1 : ℕ) : ℝ)) :
    (∑' n, ((disp n : ℝ) : ℂ) * (conj (x n) * (-Complex.I * (((disp n : ℝ) : ℂ) * x n +
        nonlin x n)))).re +
      (∑' n, conj (nonlin x n) * (-Complex.I * (((disp n : ℝ) : ℂ) * x n + nonlin x n))).re = 0 := by
  set D : ℤ → ℂ := fun n => -Complex.I * (((disp n : ℝ) : ℂ) * x n + nonlin x n) with hDdef
  have hDs : Summable fun n => ‖D n‖ ^ 2 := summable_sq_of_h1 hD
  have hbs := nonlin_summable_sq38 hx
  have has : Summable fun n => ‖((disp n : ℝ) : ℂ) * x n‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
      ((hDs.mul_left 2).add (hbs.mul_left 2))
    have h1 : ((disp n : ℝ) : ℂ) * x n = Complex.I * D n - nonlin x n := by
      simp only [hDdef]
      ring_nf
      simp [Complex.I_sq]
    have h2 : ‖((disp n : ℝ) : ℂ) * x n‖ ≤ ‖D n‖ + ‖nonlin x n‖ := by
      rw [h1]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, one_mul]
    nlinarith [norm_nonneg (((disp n : ℝ) : ℂ) * x n), norm_nonneg (D n), norm_nonneg (nonlin x n),
      sq_nonneg (‖D n‖ - ‖nonlin x n‖)]
  have hf : Summable fun n => ((disp n : ℝ) : ℂ) * (conj (x n) * D n) := by
    refine (summable_conj_mul38 has hDs).congr fun n => ?_
    simp only [map_mul, Complex.conj_ofReal]
    ring
  have hg : Summable fun n => conj (nonlin x n) * D n := summable_conj_mul38 hbs hDs
  rw [← Complex.add_re, ← hf.tsum_add hg, Complex.re_tsum (hf.add hg)]
  have hz : ∀ n, (((disp n : ℝ) : ℂ) * (conj (x n) * D n) + conj (nonlin x n) * D n).re = 0 := by
    intro n
    have h : ((disp n : ℝ) : ℂ) * (conj (x n) * D n) + conj (nonlin x n) * D n =
        -Complex.I * (conj (((disp n : ℝ) : ℂ) * x n + nonlin x n) *
          (((disp n : ℝ) : ℂ) * x n + nonlin x n)) := by
      simp only [hDdef, map_add, map_mul, Complex.conj_ofReal]
      ring
    have hy : conj (((disp n : ℝ) : ℂ) * x n + nonlin x n) *
        (((disp n : ℝ) : ℂ) * x n + nonlin x n) =
        ((‖((disp n : ℝ) : ℂ) * x n + nonlin x n‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.conj_mul']; push_cast; rfl
    rw [h, hy, neg_mul, Complex.neg_re, Complex.I_mul_re, Complex.ofReal_im]
    simp
  simp only [hz, tsum_zero]

/-! ## Constancy from a vanishing derivative on `uIcc 0 t` -/

theorem const_on_uIcc38 {f : ℝ → ℝ} (t : ℝ) (h : ∀ s ∈ uIcc 0 t, HasDerivAt f 0 s) : f t = f 0 := by
  rcases le_total 0 t with ht | ht
  · rw [uIcc_of_le ht] at h
    exact constant_of_has_deriv_right_zero (a := 0) (b := t)
      (fun s hs => (h s hs).continuousAt.continuousWithinAt)
      (fun s hs => (h s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt) t ⟨ht, le_rfl⟩
  · rw [uIcc_of_ge ht] at h
    exact (constant_of_has_deriv_right_zero (a := t) (b := 0)
      (fun s hs => (h s hs).continuousAt.continuousWithinAt)
      (fun s hs => (h s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt) 0 ⟨ht, le_rfl⟩).symm

/-! ## Conservation inside the cutoff -/

/-- **Mass and energy are conserved while the solution stays inside the cutoff ball** (A7b). -/
theorem conserved_inside (R : ℝ) (hR : 0 < R) {u : ℝ → ℤ → ℂ} (hu : IsCutSol R u)
    (h3 : u 0 ∈ seqSobolev38 ((3 : ℕ) : ℝ)) (t : ℝ)
    (hin : ∀ s ∈ Set.uIcc 0 t, hn 1 (u s) < R) :
    mass (u t) = mass (u 0) ∧ ham (u t) = ham (u 0) := by
  obtain ⟨γ, hγ0, hγ⟩ := cutSol_C1_h1_aux hR hu h3
  have key : ∀ s ∈ uIcc 0 t, HasDerivAt (fun r => mass (u r)) 0 s ∧
      HasDerivAt (fun r => ham (u r)) 0 s := by
    intro s hs
    obtain ⟨D, hD, hDc⟩ := hγ s
    have hχ : cutoff R (hn 1 (u s)) = 1 := cutoff_eq_one hR (hin s hs).le
    simp only [hχ, Complex.ofReal_one, one_mul] at hDc
    have hxs : u s ∈ seqSobolev38 ((1 : ℕ) : ℝ) := hu.mem s
    have hDm : (fun n => -Complex.I * (((disp n : ℝ) : ℂ) * u s n + nonlin (u s) n)) ∈
        seqSobolev38 ((1 : ℕ) : ℝ) := by
      rw [← hDc]; exact carrierCoe38_mem _ D
    constructor
    · have h := hasDerivAt_mass hD
      simp only [hγ0, hDc] at h
      rw [re_mass_pairing38 hxs, mul_zero] at h
      exact h
    · have h := (hasDerivAt_kin hD).add (hasDerivAt_quart hD)
      simp only [hγ0, hDc] at h
      have e := re_ham_pairing38 hxs hDm
      have : 2 * (∑' n, ((disp n : ℝ) : ℂ) * (conj (u s n) * (-Complex.I * (((disp n : ℝ) : ℂ) *
          u s n + nonlin (u s) n)))).re + 2 * (∑' n, conj (nonlin (u s) n) * (-Complex.I *
          (((disp n : ℝ) : ℂ) * u s n + nonlin (u s) n))).re = 0 := by linarith
      rw [this] at h
      exact h
  exact ⟨const_on_uIcc38 t fun s hs => (key s hs).1, const_on_uIcc38 t fun s hs => (key s hs).2⟩

/-! ## No exit -/

theorem no_exit_nonneg38 {φ : ℝ → ℝ} (hφ : Continuous φ) {R2 B2 : ℝ} (hB : B2 < R2) (h0 : φ 0 ≤ B2)
    (hstep : ∀ t, 0 ≤ t → (∀ s ∈ Icc 0 t, φ s < R2) → φ t ≤ B2) :
    ∀ t, 0 ≤ t → φ t ≤ B2 := by
  intro t ht
  have hall : ∀ s ∈ Icc 0 t, φ s < R2 := by
    by_contra hcon
    push Not at hcon
    set S : Set ℝ := {s ∈ Icc 0 t | R2 ≤ φ s} with hS
    have hSc : IsCompact S := by
      have : IsClosed S := isClosed_Icc.inter (isClosed_le continuous_const hφ)
      exact isCompact_Icc.of_isClosed_subset this (fun s hs => hs.1)
    have hSne : S.Nonempty := by
      obtain ⟨s, hs, hs2⟩ := hcon
      exact ⟨s, hs, hs2⟩
    obtain ⟨s1, hs1, hmin⟩ := hSc.exists_isLeast hSne
    have hs1pos : 0 < s1 := by
      rcases hs1.1.1.eq_or_lt with h | h
      · exfalso
        have := hs1.2
        rw [← h] at this
        linarith
      · exact h
    have hlt : ∀ s ∈ Ico 0 s1, φ s ≤ B2 := by
      intro s hs
      apply hstep s hs.1
      intro r hr
      by_contra hrr
      push Not at hrr
      have : s1 ≤ r := hmin ⟨⟨hr.1, hr.2.trans (hs.2.le.trans hs1.1.2)⟩, hrr⟩
      linarith [hs.2, hr.2]
    have hcl : IsClosed {x | φ x ≤ B2} := isClosed_le hφ continuous_const
    have : s1 ∈ closure (Ico 0 s1) := by
      rw [closure_Ico hs1pos.ne]
      exact ⟨hs1pos.le, le_rfl⟩
    have h2 : φ s1 ≤ B2 := hcl.closure_subset_iff.2 hlt this
    linarith [hs1.2]
  exact hstep t ht hall

/-- **No exit** (A7b): a continuous function that starts `≤ B2 < R2` and cannot exceed `B2` as long as it
stays `< R2` on the whole segment from `0` never exceeds `B2`. -/
theorem no_exit {φ : ℝ → ℝ} (hφ : Continuous φ) {R2 B2 : ℝ} (hB : B2 < R2) (h0 : φ 0 ≤ B2)
    (hstep : ∀ t, (∀ s ∈ Set.uIcc 0 t, φ s < R2) → φ t ≤ B2) : ∀ t, φ t ≤ B2 := by
  intro t
  rcases le_total 0 t with ht | ht
  · exact no_exit_nonneg38 hφ hB h0
      (fun r hr h => hstep r (by rw [uIcc_of_le hr]; exact h)) t ht
  · have hψ : Continuous fun s => φ (-s) := hφ.comp continuous_neg
    have := no_exit_nonneg38 (φ := fun s => φ (-s)) hψ hB (by simpa using h0)
      (fun r hr h => by
        refine hstep (-r) fun s hs => ?_
        rw [uIcc_of_ge (by linarith)] at hs
        have := h (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
        simpa using this) (-t) (by linarith)
    simpa using this

/-! ## Regression probes -/

section Probes

/-- Probe 1: conservation for the plane-wave cutoff solution, via `conserved_inside`, and the explicit
values `mass = ‖a‖²`, `ham = (2πk)²‖a‖² + ‖a‖⁴` (the plane wave of `isCutSol_planeWave`). -/
theorem planeWave_conserved38 (R : ℝ) (hR : 0 < R) (k : ℤ) (a : ℂ)
    (hRa : Real.sqrt ((1 + (k : ℝ) ^ 2) * ‖a‖ ^ 2) < R) (t : ℝ) :
    mass (Pi.single k (planeWaveAmp38 k a t)) = mass (Pi.single k (planeWaveAmp38 k a 0)) ∧
      ham (Pi.single k (planeWaveAmp38 k a t)) = ham (Pi.single k (planeWaveAmp38 k a 0)) ∧
      mass (Pi.single k (planeWaveAmp38 k a t)) = ‖a‖ ^ 2 ∧
      ham (Pi.single k (planeWaveAmp38 k a t)) = disp k * ‖a‖ ^ 2 + ‖a‖ ^ 4 := by
  have hnorm : ∀ s, ‖planeWaveAmp38 k a s‖ = ‖a‖ := fun s => by
    unfold planeWaveAmp38
    rw [norm_mul, norm_phaseFactor, one_mul]
  have hcut := isCutSol_planeWave R k a hRa.le
  have h3 : (Pi.single k (planeWaveAmp38 k a 0) : ℤ → ℂ) ∈ seqSobolev38 ((3 : ℕ) : ℝ) :=
    single_mem_seqSobolev38 _ k _
  have hin : ∀ s ∈ Set.uIcc 0 t, hn 1 (Pi.single k (planeWaveAmp38 k a s)) < R := fun s _ => by
    have h := hn_one_sq_single k (planeWaveAmp38 k a s)
    rw [hnorm] at h
    have hn0 : 0 ≤ hn 1 (Pi.single k (planeWaveAmp38 k a s)) := Real.sqrt_nonneg _
    have : hn 1 (Pi.single k (planeWaveAmp38 k a s)) =
        Real.sqrt ((1 + (k : ℝ) ^ 2) * ‖a‖ ^ 2) := by
      rw [← Real.sqrt_sq hn0, h]
    rw [this]; exact hRa
  obtain ⟨h1, h2⟩ := conserved_inside R hR hcut h3 t hin
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [mass_single, hnorm]
  · rw [ham_def, kin_single, quart_single, hnorm]

/-- Probe 2: `no_exit` on a constant function. -/
theorem no_exit_const38 (c R2 B2 : ℝ) (hB : B2 < R2) (hc : c ≤ B2) (t : ℝ) : c ≤ B2 :=
  no_exit (φ := fun _ => c) continuous_const hB hc (fun _ _ => hc) t

/-- Probe 3: `no_exit` with a function that touches the barrier `B2` but never `R2`: `φ t = B2 * cos t`
for `0 ≤ B2 < R2`... here the step hypothesis is verified by the pointwise bound. -/
theorem no_exit_cos38 (B2 R2 : ℝ) (hB : B2 < R2) (hB0 : 0 ≤ B2) (t : ℝ) :
    B2 * Real.cos t ≤ B2 :=
  no_exit (φ := fun s => B2 * Real.cos s) (by fun_prop) hB (by simp)
    (fun s _ => mul_le_of_le_one_right hB0 (Real.cos_le_one s)) t

end Probes

end NlsGge.NLS38
