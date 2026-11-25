import NlsGge.NLS38.FlowMaps38
import NlsGge.Birkhoff.S04Moments38
import NlsGge.Analysis.H1Fourier

/-! # GWP piece A10: the physical flow `nlsFlowL2` and the package `NLSGWP`

Plan: `campaign/GWP_PLAN.md` §6.1, §6.2 and §7 (A10); review notes N3, N8.

* `nlsFlowL2 t u` : `H^1` data evolve through `nlsFlowSeq` on the physical Fourier coefficients
  `physicalFourier`, the other fields are fixed (junk branch, `μ_W`-null).
* physical identities: `physicalFourier_nlsFlowL2`, `fourierSeq38_nlsFlowL2` (reflection symmetry),
  `nlsFlowL2_mem`, `nlsFlowL2_zero`, `nlsFlowL2_add`, `physH38_nlsFlowL2`, `nlsFlowL2_of_not_H1`,
  `nlsFlowL2_norm`.
* `IsPhysicalNLSSolution`, `nlsFlowL2_isPhysicalNLSSolution`, `isPhysicalNLSSolution_iff`.
* `NLSGWP m`, `nls_gwp (m) (hm : 1 ≤ m)`, `nlsGWP_one_cast`.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff Set Filter Topology
open scoped ComplexConjugate NNReal ENNReal

/-! ## Definition of `nlsFlowL2` (review note N8: the `h^0` membership and the `0` cast) -/

theorem physicalFourier_mem_one38 {u : PhysicalL2} (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    physicalFourier u ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
  (mem_seqSobolev38_iff _ _).2 (by rw [Nat.cast_one]; exact hu)

theorem physicalFourier_mem_one_iff38 (u : PhysicalL2) :
    physicalFourier u ∈ seqSobolev38 ((1 : ℕ) : ℝ) ↔ SobolevSquareSummable 1 (physicalFourier u) :=
  ⟨fun h => by have := (mem_seqSobolev38_iff _ _).1 h; rwa [Nat.cast_one] at this,
    physicalFourier_mem_one38⟩

/-- `nlsFlowSeq t` of the coefficients of an `H¹` field lies in `h^0` (from the `m = 1` case and
`seqSobolev38_natCast_mono`; the `((0:ℕ):ℝ)` transport is done inside `seqSobolev38_natCast_mono`). -/
theorem nlsFlowSeq_mem_zero38 (t : ℝ) {u : PhysicalL2}
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    nlsFlowSeq t (physicalFourier u) ∈ seqSobolev38 0 :=
  seqSobolev38_natCast_mono (m := 1)
    (nlsFlowSeq_mem 1 le_rfl t _ (physicalFourier_mem_one38 hu))

open scoped Classical in
/-- The actual NLS solution map on `PhysicalL2`; `H¹` data evolve, other fields are fixed
(junk, `μ_W`-null). -/
def nlsFlowL2 (t : ℝ) (u : PhysicalL2) : PhysicalL2 :=
  if h : SobolevSquareSummable 1 (physicalFourier u) then
    physicalFourierL2.symm (seqToLp38 (nlsFlowSeq t (physicalFourier u)) (nlsFlowSeq_mem_zero38 t h))
  else u

theorem physicalFourier_injective38 {u w : PhysicalL2} (h : physicalFourier u = physicalFourier w) :
    u = w := by
  apply physicalFourierL2.injective
  apply lp.ext
  funext n
  rw [physicalFourierL2_apply, physicalFourierL2_apply, h]

theorem physicalFourier_nlsFlowL2 {u : PhysicalL2} (hu : SobolevSquareSummable 1 (physicalFourier u))
    (t : ℝ) : physicalFourier (nlsFlowL2 t u) = nlsFlowSeq t (physicalFourier u) := by
  unfold nlsFlowL2
  simp only [hu, ↓reduceDIte]
  funext n
  rw [← physicalFourierL2_apply, LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem fourierSeq38_eq_refl38 (u : PhysicalL2) : fourierSeq38 u = refl (physicalFourier u) := by
  funext n
  rw [fourierSeq38_apply]
  rfl

theorem fourierSeq38_nlsFlowL2 {u : PhysicalL2} (hu : SobolevSquareSummable 1 (physicalFourier u))
    (t : ℝ) : fourierSeq38 (nlsFlowL2 t u) = nlsFlowSeq t (fourierSeq38 u) := by
  rw [fourierSeq38_eq_refl38, fourierSeq38_eq_refl38, physicalFourier_nlsFlowL2 hu,
    nlsFlowSeq_refl]

theorem nlsFlowL2_mem (m : ℕ) (hm : 1 ≤ m) {u : PhysicalL2}
    (hu : SobolevSquareSummable (m : ℝ) (physicalFourier u)) (t : ℝ) :
    SobolevSquareSummable (m : ℝ) (physicalFourier (nlsFlowL2 t u)) := by
  have hu1 : SobolevSquareSummable 1 (physicalFourier u) := by
    have := (mem_seqSobolev38_iff ((m : ℕ) : ℝ) _).2 hu
    have h1 := seqSobolev38_mono (by exact_mod_cast hm : (1 : ℝ) ≤ m) this
    exact (mem_seqSobolev38_iff _ _).1 h1
  rw [physicalFourier_nlsFlowL2 hu1]
  exact (mem_seqSobolev38_iff _ _).1
    (nlsFlowSeq_mem m hm t _ ((mem_seqSobolev38_iff _ _).2 hu))

theorem nlsFlowL2_of_not_H1 {u : PhysicalL2} (hu : ¬ SobolevSquareSummable 1 (physicalFourier u))
    (t : ℝ) : nlsFlowL2 t u = u := by
  unfold nlsFlowL2
  simp only [hu, ↓reduceDIte]

theorem nlsFlowL2_zero (u : PhysicalL2) : nlsFlowL2 0 u = u := by
  by_cases hu : SobolevSquareSummable 1 (physicalFourier u)
  · apply physicalFourier_injective38
    rw [physicalFourier_nlsFlowL2 hu, nlsFlowSeq_zero]
  · exact nlsFlowL2_of_not_H1 hu 0

theorem nlsFlowL2_add {u : PhysicalL2} (hu : SobolevSquareSummable 1 (physicalFourier u))
    (s t : ℝ) : nlsFlowL2 (s + t) u = nlsFlowL2 s (nlsFlowL2 t u) := by
  have hv : SobolevSquareSummable 1 (physicalFourier (nlsFlowL2 t u)) := by
    have := nlsFlowL2_mem 1 le_rfl (u := u) (by simpa using hu) t
    simpa using this
  apply physicalFourier_injective38
  rw [physicalFourier_nlsFlowL2 hu, physicalFourier_nlsFlowL2 hv, physicalFourier_nlsFlowL2 hu,
    nlsFlowSeq_add]

theorem physH38_nlsFlowL2 (m : ℕ) (hm : 1 ≤ m) {u : PhysicalL2}
    (hu : fourierSeq38 u ∈ seqSobolev38 (m : ℝ)) (t : ℝ) :
    physH38 m (nlsFlowL2 t u) = nlsFlowC m hm t (physH38 m u) := by
  have hu' : SobolevSquareSummable (m : ℝ) (physicalFourier u) := (fourierSeq38_mem_iff _ u).1 hu
  have hu1 : SobolevSquareSummable 1 (physicalFourier u) := by
    have := seqSobolev38_mono (by exact_mod_cast hm : (1 : ℝ) ≤ m) hu
    simpa using (fourierSeq38_mem_iff 1 u).1 this
  have hv : fourierSeq38 (nlsFlowL2 t u) ∈ seqSobolev38 (m : ℝ) :=
    (fourierSeq38_mem_iff _ _).2 (nlsFlowL2_mem m hm hu' t)
  rw [physH38_of_mem m _ hv, physH38_of_mem m _ hu]
  apply carrierExt38
  show fourierSeq38 (nlsFlowL2 t u) = nlsFlowSeq t (fourierSeq38 u)
  exact fourierSeq38_nlsFlowL2 hu1 t

theorem nlsFlowL2_norm {u : PhysicalL2} (hu : SobolevSquareSummable 1 (physicalFourier u))
    (t : ℝ) : ‖nlsFlowL2 t u‖ = ‖u‖ := by
  have hx := physicalFourier_mem_one38 hu
  obtain ⟨hs, h0⟩ := nlsFlowSeq_spec _ hx
  have hm : mass (nlsFlowSeq t (physicalFourier u)) = mass (physicalFourier u) := by
    have := (nls_conserved hs t).1
    rwa [h0] at this
  have e1 := (hasSum_physicalFourier_sq (nlsFlowL2 t u)).tsum_eq
  have e2 := (hasSum_physicalFourier_sq u).tsum_eq
  have : ‖nlsFlowL2 t u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [← e1, ← e2, physicalFourier_nlsFlowL2 hu]
    exact hm
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

/-! ## Physical-coefficient form of `IsNLSSol` (review note N3) -/

/-- physical-coefficient form of `IsNLSSol` (audit-facing). -/
structure IsPhysicalNLSSolution (U : ℝ → PhysicalL2) : Prop where
  mem   : ∀ t, SobolevSquareSummable 1 (physicalFourier (U t))
  cont  : Continuous fun t => physH38 1 (U t)
  deriv : ∀ t n, HasDerivAt (fun s => physicalFourier (U s) n)
            (-Complex.I * (((disp n : ℝ) : ℂ) * physicalFourier (U t) n +
              nonlin (physicalFourier (U t)) n)) t

theorem physH38_eq_refl_carrier38 (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    physH38 1 u = reflCarrier38 ((1 : ℕ) : ℝ)
      (carrierMk38 ((1 : ℕ) : ℝ) (physicalFourier u) (physicalFourier_mem_one38 hu)) := by
  rw [physH38_of_mem 1 u ((fourierSeq38_mem_iff _ u).2 (by rw [Nat.cast_one]; exact hu))]
  apply carrierExt38
  show fourierSeq38 u = refl (physicalFourier u)
  exact fourierSeq38_eq_refl38 u

theorem reflCarrier38_involutive (r : ℝ) (x : SobolevCarrier38 r) :
    reflCarrier38 r (reflCarrier38 r x) = x := by
  apply carrierExt38
  show refl (refl (carrierCoe38 r x)) = carrierCoe38 r x
  exact refl_refl38 _

theorem isPhysicalNLSSolution_iff (U : ℝ → PhysicalL2) :
    IsPhysicalNLSSolution U ↔
      (∀ t, SobolevSquareSummable 1 (physicalFourier (U t))) ∧
        IsNLSSol (fun t => physicalFourier (U t)) := by
  constructor
  · intro h
    refine ⟨h.mem, ⟨fun t => physicalFourier_mem_one38 (h.mem t), ?_, h.deriv⟩⟩
    have hc : (fun t => carrierMk38 ((1 : ℕ) : ℝ) (physicalFourier (U t))
        (physicalFourier_mem_one38 (h.mem t))) =
        fun t => reflCarrier38 ((1 : ℕ) : ℝ) (physH38 1 (U t)) := by
      funext t
      rw [physH38_eq_refl_carrier38 _ (h.mem t), reflCarrier38_involutive]
    rw [hc]
    exact (reflCarrier38 ((1 : ℕ) : ℝ)).continuous.comp h.cont
  · rintro ⟨hm, hs⟩
    refine ⟨hm, ?_, hs.deriv⟩
    have hc : (fun t => physH38 1 (U t)) = fun t => reflCarrier38 ((1 : ℕ) : ℝ)
        (carrierMk38 ((1 : ℕ) : ℝ) (physicalFourier (U t)) (hs.mem t)) := by
      funext t
      exact physH38_eq_refl_carrier38 _ (hm t)
    rw [hc]
    exact (reflCarrier38 ((1 : ℕ) : ℝ)).continuous.comp hs.cont

theorem nlsFlowL2_isPhysicalNLSSolution {u : PhysicalL2}
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    IsPhysicalNLSSolution (fun t => nlsFlowL2 t u) := by
  rw [isPhysicalNLSSolution_iff]
  have hx := physicalFourier_mem_one38 hu
  have e : (fun t => physicalFourier (nlsFlowL2 t u)) = fun t => nlsFlowSeq t (physicalFourier u) :=
    funext fun t => physicalFourier_nlsFlowL2 hu t
  have hmem : ∀ t, SobolevSquareSummable 1 (physicalFourier (nlsFlowL2 t u)) := fun t => by
    have := nlsFlowL2_mem 1 le_rfl (u := u) (by simpa using hu) t
    simpa using this
  refine ⟨hmem, ?_⟩
  rw [e]
  exact (nlsFlowSeq_spec _ hx).1


/-! ## The GWP package -/

/-- GWP of `i uₜ = -uₓₓ + 2|u|²u` on `ℝ/ℤ` in `H^m`, `m ≥ 1`. -/
structure NLSGWP (m : ℕ) : Prop where
  exists_unique : ∀ x ∈ seqSobolev38 (m : ℝ), ∃! u : ℝ → ℤ → ℂ, IsNLSSolM m u ∧ u 0 = x
  uniq_h1 : ∀ x ∈ seqSobolev38 ((1 : ℕ) : ℝ), ∀ u w, IsNLSSol u → IsNLSSol w → u 0 = x → w 0 = x →
    u = w
  group : ∀ x ∈ seqSobolev38 ((1 : ℕ) : ℝ),
    nlsFlowSeq 0 x = x ∧ ∀ s t, nlsFlowSeq (s + t) x = nlsFlowSeq s (nlsFlowSeq t x)
  mapsTo : ∀ t, ∀ x ∈ seqSobolev38 (m : ℝ), nlsFlowSeq t x ∈ seqSobolev38 (m : ℝ)
  continuous : Continuous fun p : ℝ × SobolevCarrier38 (m : ℝ) =>
    carrierMap38 _ _ (nlsFlowSeq p.1) (mapsTo p.1) p.2
  lipschitz : ∀ ρ T : ℝ, ∃ L : ℝ≥0, ∀ t, |t| ≤ T →
    LipschitzOnWith L (carrierMap38 _ _ (nlsFlowSeq t) (mapsTo t)) (Metric.closedBall 0 ρ)
  conservation : ∀ x ∈ seqSobolev38 ((1 : ℕ) : ℝ), ∀ t,
    mass (nlsFlowSeq t x) = mass x ∧ ham (nlsFlowSeq t x) = ham x
  h1_bound : ∀ x ∈ seqSobolev38 ((1 : ℕ) : ℝ), ∀ t,
    hn 1 (nlsFlowSeq t x) ^ 2 ≤ mass x + ham x / (4 * Real.pi ^ 2)

/-- A cutoff solution bounded by `R` in `h¹` is a true `h^m` solution. -/
theorem isNLSSolM_of_cutSolM38 (m : ℕ) {R : ℝ} {u : ℝ → ℤ → ℂ} (hu : IsCutSolM m R u)
    (hb : ∀ t, hn 1 (u t) ≤ R) : IsNLSSolM m u := by
  have hc : ∀ t, cutoff R (hn 1 (u t)) = 1 := fun t =>
    cutoff_eq_one_of_nonneg (by unfold hn; exact Real.sqrt_nonneg _) (hb t)
  exact ⟨hu.mem, hu.cont, fun t n => by simpa [hc t] using hu.deriv t n⟩

/-- An `h^m` solution (`m ≥ 1`) is an `h¹` solution. -/
theorem isNLSSol_of_isNLSSolM38 (m : ℕ) (hm : 1 ≤ m) {u : ℝ → ℤ → ℂ} (hu : IsNLSSolM m u) :
    IsNLSSol u := by
  have hle : ((1 : ℕ) : ℝ) ≤ (m : ℝ) := Nat.cast_le.2 hm
  have hmem : ∀ t, u t ∈ seqSobolev38 ((1 : ℕ) : ℝ) := fun t => seqSobolev38_mono hle (hu.mem t)
  refine ⟨hmem, ?_, hu.deriv⟩
  have hc : (fun t => carrierMk38 ((1 : ℕ) : ℝ) (u t) (hmem t)) =
      fun t => carrierIncl38 hle (carrierMk38 (m : ℝ) (u t) (hu.mem t)) := by
    funext t
    apply carrierExt38
    simp only [carrierCoe38_mk, carrierCoe38_incl38]
  rw [hc]
  exact (carrierIncl38 hle).continuous.comp hu.cont

theorem flow_isNLSSolM38 (m : ℕ) (hm : 1 ≤ m) {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 (m : ℝ)) :
    IsNLSSolM m (fun t => nlsFlowSeq t x) := by
  have hx1 : x ∈ seqSobolev38 ((1 : ℕ) : ℝ) := seqSobolev38_mono (by exact_mod_cast hm) hx
  obtain ⟨hs, h0⟩ := nlsFlowSeq_spec x hx1
  refine isNLSSolM_of_cutSolM38 m (flow_isCutSolM38 m hm hx (le_refl (Bx x + 2)))
    (R := Bx x + 2) (fun t => ?_)
  have h1 := hn_le_Bx38 (hs.mem t)
  have h2 : Bx (nlsFlowSeq t x) = Bx x := by
    unfold Bx
    rw [(nls_conserved hs t).1, (nls_conserved hs t).2, h0]
  linarith

theorem nls_gwp (m : ℕ) (hm : 1 ≤ m) : NLSGWP m where
  exists_unique x hx := by
    refine ⟨fun t => nlsFlowSeq t x, ⟨flow_isNLSSolM38 m hm hx, nlsFlowSeq_zero x⟩, ?_⟩
    rintro u ⟨hu, h0⟩
    funext t
    have := nlsFlowSeq_eq_of_sol (isNLSSol_of_isNLSSolM38 m hm hu) t
    rw [h0] at this
    exact this.symm
  uniq_h1 _ _ u w hu hw h0u h0w := nls_unique hu hw (h0u.trans h0w.symm)
  group x _ := ⟨nlsFlowSeq_zero x, fun s t => nlsFlowSeq_add s t x⟩
  mapsTo t := nlsFlowSeq_mem m hm t
  continuous := continuous_nlsFlowC_uncurry m hm
  lipschitz ρ T := nlsFlowC_lipschitzOn m hm ρ T
  conservation x hx t := by
    obtain ⟨hs, h0⟩ := nlsFlowSeq_spec x hx
    have := nls_conserved hs t
    rwa [h0] at this
  h1_bound x hx t := by
    obtain ⟨hs, h0⟩ := nlsFlowSeq_spec x hx
    have h1 := hn_sq_le_Bx_sq38 (hs.mem t)
    have hc := nls_conserved hs t
    rw [h0] at hc
    rw [Bx_sq38, hc.1, hc.2] at h1
    exact h1

/-- `nls_gwp 1` with a literal `1 : ℝ` (review note N4): the `((1:ℕ):ℝ)` of the package is
transported along `Nat.cast_one`. -/
theorem nlsGWP_cast38 (r : ℝ) (hr : r = ((1 : ℕ) : ℝ)) :
    (∀ x ∈ seqSobolev38 r, ∃! u : ℝ → ℤ → ℂ, IsNLSSol u ∧ u 0 = x) ∧
    ∃ hmaps : ∀ t, ∀ x ∈ seqSobolev38 r, nlsFlowSeq t x ∈ seqSobolev38 r,
      (Continuous fun p : ℝ × SobolevCarrier38 r => carrierMap38 _ _ (nlsFlowSeq p.1) (hmaps p.1) p.2) ∧
      ∀ ρ T : ℝ, ∃ L : ℝ≥0, ∀ t, |t| ≤ T →
        LipschitzOnWith L (carrierMap38 _ _ (nlsFlowSeq t) (hmaps t)) (Metric.closedBall 0 ρ) := by
  subst hr
  have h := nls_gwp 1 le_rfl
  exact ⟨h.exists_unique, h.mapsTo, h.continuous, h.lipschitz⟩

theorem nlsGWP_one_cast :
    (∀ x ∈ seqSobolev38 1, ∃! u : ℝ → ℤ → ℂ, IsNLSSol u ∧ u 0 = x) ∧
    ∃ hmaps : ∀ t, ∀ x ∈ seqSobolev38 1, nlsFlowSeq t x ∈ seqSobolev38 1,
      (Continuous fun p : ℝ × SobolevCarrier38 1 => carrierMap38 _ _ (nlsFlowSeq p.1) (hmaps p.1) p.2) ∧
      ∀ ρ T : ℝ, ∃ L : ℝ≥0, ∀ t, |t| ≤ T →
        LipschitzOnWith L (carrierMap38 _ _ (nlsFlowSeq t) (hmaps t)) (Metric.closedBall 0 ρ) :=
  nlsGWP_cast38 1 Nat.cast_one.symm

/-! ## Regression probe: the plane wave on `PhysicalL2` -/

/-- The physical field with a single Fourier mode, `physicalFourier = Pi.single k a`. -/
def planeWaveL2_38 (k : ℤ) (a : ℂ) : PhysicalL2 :=
  physicalFourierL2.symm (lp.single 2 k a)

theorem physicalFourier_planeWaveL2_38 (k : ℤ) (a : ℂ) :
    physicalFourier (planeWaveL2_38 k a) = Pi.single k a := by
  funext n
  rw [← physicalFourierL2_apply]
  unfold planeWaveL2_38
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem planeWaveL2_H1_38 (k : ℤ) (a : ℂ) :
    SobolevSquareSummable 1 (physicalFourier (planeWaveL2_38 k a)) := by
  rw [← physicalFourier_mem_one_iff38, physicalFourier_planeWaveL2_38]
  refine finiteSupport_mem_seqSobolev38 _ _ ((Set.finite_singleton k).subset fun n hn => ?_)
  by_contra h
  have h' : n ≠ k := fun e => h (by simp [e])
  exact hn (by simp [h'])

/-- Probe: `S_t` of a single mode is the explicit phase rotation (the NLS flow acts on
`physicalFourier`, by `nlsFlowSeq_planeWave`), and the `L²` norm is `‖a‖`. -/
theorem nlsFlowL2_planeWave_probe38 (t : ℝ) (k : ℤ) (a : ℂ) :
    physicalFourier (nlsFlowL2 t (planeWaveL2_38 k a)) =
      Pi.single k (Complex.exp (-(Complex.I * t * ((2 * Real.pi * k) ^ 2 + 2 * (‖a‖ : ℂ) ^ 2))) * a)
    ∧ ‖nlsFlowL2 t (planeWaveL2_38 k a)‖ = ‖a‖ := by
  refine ⟨?_, ?_⟩
  · rw [physicalFourier_nlsFlowL2 (planeWaveL2_H1_38 k a), physicalFourier_planeWaveL2_38,
      nlsFlowSeq_planeWave]
  · rw [nlsFlowL2_norm (planeWaveL2_H1_38 k a)]
    unfold planeWaveL2_38
    rw [LinearIsometryEquiv.norm_map, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

/-! ## Regression probe: the junk branch (review note N8) -/

/-- An `L²` field whose coefficients are not in `H¹`: `physicalFourier = ⟨n⟩⁻¹` (`⟨n⟩² |c_n|² = 1`). -/
def junkL2_38 : PhysicalL2 := physicalFourierL2.symm NlsGge.Analysis.reciprocalBracketL2

theorem not_H1_junkL2_38 : ¬ SobolevSquareSummable 1 (physicalFourier junkL2_38) := by
  intro h
  have hc : ∀ n : ℤ, physicalFourier junkL2_38 n = NlsGge.Analysis.reciprocalBracketL2 n := fun n => by
    rw [← physicalFourierL2_apply]
    unfold junkL2_38
    rw [LinearIsometryEquiv.apply_symm_apply]
  have h1 : (fun n : ℤ => Real.rpow (japaneseBracket n) (2 * 1) * ‖physicalFourier junkL2_38 n‖ ^ 2) =
      fun _ => (1 : ℝ) := by
    funext n
    rw [hc]
    have e : ‖(NlsGge.Analysis.reciprocalBracketL2 : ℤ → ℂ) n‖ ^ 2 = 1 / (1 + (n : ℝ) ^ 2) := by
      show ‖(Real.sqrt (1 / (1 + (n : ℝ) ^ 2)) : ℂ) * 1‖ ^ 2 = _
      rw [mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity)]
    have hb : Real.rpow (japaneseBracket n) (2 * 1) = 1 + (n : ℝ) ^ 2 := by
      rw [mul_one]
      show (japaneseBracket n) ^ (2 : ℝ) = _
      rw [Real.rpow_two]
      unfold japaneseBracket
      exact Real.sq_sqrt (by positivity)
    rw [e, hb]
    field_simp
  unfold SobolevSquareSummable at h
  rw [h1] at h
  exact one_ne_zero ((summable_const_iff (1 : ℝ)).1 h)

/-- Probe: off `H¹` the map is the identity, so the junk field is fixed. -/
theorem nlsFlowL2_junk_probe38 (t : ℝ) : nlsFlowL2 t junkL2_38 = junkL2_38 :=
  nlsFlowL2_of_not_H1 not_H1_junkL2_38 t

end NlsGge.NLS38
