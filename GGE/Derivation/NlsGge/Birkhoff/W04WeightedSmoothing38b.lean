import NlsGge.Birkhoff.W04WeightedSmoothing38

/-! # W04 (`D:thm:weighted`), part 2: the translation orbit as a Banach-valued Fourier series

Source: `paper/v2.tex` l.1489-1494 ("Use the translation orbit `θ ↦ S_θ x` ... The weighted `h¹` norm
of the input orbit is exactly `‖x‖_{E_s}`").  Birkhoff-free.

* `HC38 r` is `h^r` as a *complex* Hilbert (hence Banach) space of sequences, the `X`, `Y` of W03;
* `hSingle38 r n u` is the `n`-th mode `u e_n ∈ h^r` (the Fourier coefficient of the orbit);
* `orbitModel38` is the weighted coefficient vector `(w_n · x_n e_n)_n ∈ ℓ²(ℤ; h^ρ)` of the orbit
  `θ ↦ S_θ x`; `synth_orbitModel38` identifies its synthesis with the orbit (W04.02);
* `ι` (`orbitCLM38 : E_σ →L[ℝ] Model (h^ρ)`) is a real-linear isometry (first norm identity of
  W04.05) and `π` (`modeCLM38 : Model (h^ρ') →L[ℝ] E_τ`) extracts the diagonal `n`-th mode of the
  `n`-th coefficient.

Complex scalars: the spaces here are complex sequence spaces with their underlying real structure,
exactly the setting of W03 (`NormedSpace ℂ X`, real analyticity); the "paired frequencies" of the
real subspace never occur, so the norm identity holds with factor exactly one.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Composition MeasureTheory AddCircle
open scoped Real

/-! ## `h^r` as a complex Hilbert space of sequences -/

/-- `h^r` as a complex Hilbert space (weight `⟨n⟩^{2r}`). -/
abbrev HC38 (r : ℝ) : Type := WeightedHilbert (sobolevModeWeight r)

/-- A sequence of `h^r` as an element of `HC38 r`. -/
def hMk38 (r : ℝ) (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 r) : HC38 r :=
  (⟨x, hx⟩ : weightedSubmodule (sobolevModeWeight r))

@[simp] theorem hMk38_apply (r : ℝ) (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 r) (n : ℤ) :
    (hMk38 r x hx : HC38 r) n = x n := rfl

theorem hCoe38_mem (r : ℝ) (y : HC38 r) : (y : ℤ → ℂ) ∈ seqSobolev38 r := y.2

theorem hExt38 (r : ℝ) {y z : HC38 r} (h : ∀ n, y n = z n) : y = z :=
  Subtype.ext (funext h)

theorem hMk38_coe (r : ℝ) (y : HC38 r) :
    hMk38 r (y : ℤ → ℂ) (hCoe38_mem r y) = y := hExt38 r fun _ => rfl

theorem norm_sq_hC38 (r : ℝ) (y : HC38 r) :
    ‖y‖ ^ 2 = ∑' n : ℤ, sobolevModeWeight r n * ‖(y : ℤ → ℂ) n‖ ^ 2 :=
  weightedHilbert_norm_sq (sobolevModeWeight r) y

theorem hasSum_norm_sq_hC38 (r : ℝ) (y : HC38 r) :
    HasSum (fun n : ℤ => sobolevModeWeight r n * ‖(y : ℤ → ℂ) n‖ ^ 2) (‖y‖ ^ 2) :=
  weightedHilbert_hasSum (sobolevModeWeight r) y

theorem finiteSupport_single_W04 (m : ℤ) (u : ℂ) :
    {n : ℤ | (Pi.single m u : ℤ → ℂ) n ≠ 0}.Finite :=
  (Set.finite_singleton m).subset (fun n hn => by
    by_contra h
    exact hn (by simp [show n ≠ m from h]))

/-- The `n`-th mode `u e_n ∈ h^r`. -/
def hSingle38 (r : ℝ) (n : ℤ) (u : ℂ) : HC38 r :=
  hMk38 r (Pi.single n u) (finiteSupport_mem_seqSobolev38 r _ (finiteSupport_single_W04 n u))

theorem hSingle38_apply (r : ℝ) (n : ℤ) (u : ℂ) (m : ℤ) :
    (hSingle38 r n u : HC38 r) m = if m = n then u else 0 := by
  classical
  change (Pi.single n u : ℤ → ℂ) m = _
  rw [Pi.single_apply]

theorem norm_sq_hSingle38 (r : ℝ) (n : ℤ) (u : ℂ) :
    ‖hSingle38 r n u‖ ^ 2 = sobolevModeWeight r n * ‖u‖ ^ 2 := by
  rw [norm_sq_hC38, tsum_eq_single n]
  · simp [hSingle38_apply]
  · intro m hm
    simp [hSingle38_apply, hm]

/-- The `m`-th coordinate as a continuous complex-linear functional on `h^r`. -/
def hCoord38 (r : ℝ) (m : ℤ) : HC38 r →L[ℂ] ℂ where
  toFun y := (y : ℤ → ℂ) m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_carrierCoe_apply38 r m

@[simp] theorem hCoord38_apply (r : ℝ) (m : ℤ) (y : HC38 r) :
    hCoord38 r m y = (y : ℤ → ℂ) m := rfl

theorem sobolevModeWeight_mul_norm_sq_le (r : ℝ) (y : HC38 r) (n : ℤ) :
    sobolevModeWeight r n * ‖(y : ℤ → ℂ) n‖ ^ 2 ≤ ‖y‖ ^ 2 :=
  le_hasSum (hasSum_norm_sq_hC38 r y) n
    (fun j _ => mul_nonneg (sobolevModeWeight_pos r j).le (sq_nonneg _))

/-! ## The orbit as a function on the circle -/

theorem fourier_coe_eq_rotPhase38 (n : ℤ) (t : ℝ) :
    fourier n ((t : ℝ) : AddCircle (1 : ℝ)) = rotPhase38 (2 * π * t) n := by
  rw [fourier_coe_apply]
  unfold rotPhase38
  congr 1
  push_cast
  ring

theorem exists_coe_eq (θ : AddCircle (1 : ℝ)) : ∃ t : ℝ, ((t : ℝ) : AddCircle (1 : ℝ)) = θ :=
  QuotientAddGroup.mk_surjective θ

/-- Coordinates commute with Fourier coefficients of continuous Banach-valued functions. -/
theorem coord_fourierCoeff38 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X] (ℓ : X →L[ℂ] ℂ) {f : AddCircle (1 : ℝ) → X} (hf : Continuous f) (n : ℤ) :
    ℓ (fourierCoeff f n) = fourierCoeff (fun θ => ℓ (f θ)) n := by
  unfold fourierCoeff
  rw [← ℓ.integral_comp_comm ((integrable_of_continuous hf).fourier_smul _)]
  simp

/-- Fourier coefficients of a scalar mode. -/
theorem fourierCoeff_mode38 (m n : ℤ) (v : ℂ) :
    fourierCoeff (fun θ : AddCircle (1 : ℝ) => fourier m θ * v) n = if m = n then v else 0 := by
  have := fourierCoeff_fourier_smul (X := ℂ) m n v
  simpa only [smul_eq_mul] using this


/-! ## The weighted orbit vector, the isometry `ι` and the extraction `π` -/

section Orbit

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper)

theorem hSmul_apply38 (r : ℝ) (a : ℝ) (v : HC38 r) (m : ℤ) :
    ((a • v : HC38 r) : ℤ → ℂ) m = (a : ℂ) * (v : ℤ → ℂ) m := rfl

theorem hAdd_apply38 (r : ℝ) (v v' : HC38 r) (m : ℤ) :
    ((v + v' : HC38 r) : ℤ → ℂ) m = (v : ℤ → ℂ) m + (v' : ℤ → ℂ) m := rfl

theorem eSmul_apply38 (σ : ℝ) (a : ℝ) (y : ECarrier38 c σ) (m : ℤ) :
    eCoe38 c σ (a • y) m = (a : ℂ) * eCoe38 c σ y m := rfl

theorem eAdd_apply38 (σ : ℝ) (y z : ECarrier38 c σ) (m : ℤ) :
    eCoe38 c σ (y + z) m = eCoe38 c σ y m + eCoe38 c σ z m := rfl

/-- `w_n² ⟨n⟩^{2r} = a_n ⟨n⟩^{-2σ}` whenever `s + 1 - r = σ`. -/
theorem orbitWeight38_sq_mul' (s r σ : ℝ) (hσ : s + 1 - r = σ) (n : ℤ) :
    orbitWeight38 c s n ^ 2 * sobolevModeWeight r n = fullModeWeight c σ n := by
  rw [← hσ]; exact orbitWeight38_sq_mul c s r n

theorem norm_orbit_term38 (s r σ : ℝ) (hσ : s + 1 - r = σ) (n : ℤ) (u : ℂ) :
    ‖orbitWeight38 c s n • hSingle38 r n u‖ ^ 2 = fullModeWeight c σ n * ‖u‖ ^ 2 := by
  rw [norm_smul, mul_pow, norm_sq_hSingle38, Real.norm_eq_abs, sq_abs, ← mul_assoc,
    orbitWeight38_sq_mul' c s r σ hσ]

/-- The weighted coefficient vector `(w_n · x_n e_n)_n` of the orbit `θ ↦ S_θ x`. -/
def orbitMk38 (s ρ σ : ℝ) (hσ : s + 1 - ρ = σ) (x : ℤ → ℂ) (hx : x ∈ seqE38 c σ) :
    Model (HC38 ρ) :=
  Model.mk (fun n => orbitWeight38 c s n • hSingle38 ρ n (x n)) (by
    have := (mem_seqE38_iff c σ x).1 hx
    exact this.congr fun n => (norm_orbit_term38 c s ρ σ hσ n (x n)).symm)

@[simp] theorem orbitMk38_apply (s ρ σ : ℝ) (hσ : s + 1 - ρ = σ) (x : ℤ → ℂ)
    (hx : x ∈ seqE38 c σ) (n : ℤ) :
    (orbitMk38 c s ρ σ hσ x hx) n = orbitWeight38 c s n • hSingle38 ρ n (x n) := rfl

/-- **First norm identity of W04.05.** The weighted `h^ρ` norm of the orbit vector is exactly
the `E_σ` norm of `x`. -/
theorem norm_orbitMk38 (s ρ σ : ℝ) (hσ : s + 1 - ρ = σ) (y : ECarrier38 c σ) :
    ‖orbitMk38 c s ρ σ hσ (eCoe38 c σ y) (eCoe38_mem c σ y)‖ = ‖y‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [Model.norm_sq_eq, norm_sq_eCarrier38]
  refine tsum_congr fun n => ?_
  rw [orbitMk38_apply, norm_orbit_term38 c s ρ σ hσ]

/-- `ι`: `y ↦` the weighted orbit vector of `y`, a real-linear isometry `E_σ → ℓ²(ℤ; h^ρ)`. -/
def orbitCLM38 (s ρ σ : ℝ) (hσ : s + 1 - ρ = σ) : ECarrier38 c σ →L[ℝ] Model (HC38 ρ) :=
  LinearMap.mkContinuous
    { toFun := fun y => orbitMk38 c s ρ σ hσ (eCoe38 c σ y) (eCoe38_mem c σ y)
      map_add' := fun y z => Model.ext fun n => hExt38 ρ fun m => by
        simp only [orbitMk38_apply, Model.add_apply]
        rw [hAdd_apply38, hSmul_apply38, hSmul_apply38, hSmul_apply38, hSingle38_apply,
          hSingle38_apply, hSingle38_apply, eAdd_apply38]
        split_ifs <;> ring
      map_smul' := fun a y => Model.ext fun n => hExt38 ρ fun m => by
        simp only [orbitMk38_apply, Model.smul_apply, RingHom.id_apply]
        rw [hSmul_apply38, hSmul_apply38, hSmul_apply38, hSingle38_apply, hSingle38_apply,
          eSmul_apply38]
        split_ifs <;> ring }
    1 (fun y => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      exact (norm_orbitMk38 c s ρ σ hσ y).le)

@[simp] theorem orbitCLM38_apply (s ρ σ : ℝ) (hσ : s + 1 - ρ = σ) (y : ECarrier38 c σ) :
    orbitCLM38 c s ρ σ hσ y = orbitMk38 c s ρ σ hσ (eCoe38 c σ y) (eCoe38_mem c σ y) := rfl

/-! ### The extraction `π` -/

/-- `(w_n)⁻¹ ·` (the `n`-th mode of the `n`-th coefficient). -/
def modeSeq38 (s ρ' : ℝ) (g : Model (HC38 ρ')) : ℤ → ℂ :=
  fun n => ((orbitWeight38 c s n)⁻¹ : ℝ) * ((g n : HC38 ρ') : ℤ → ℂ) n

theorem fullModeWeight_mul_norm_modeSeq38 (s ρ' τ : ℝ) (hτ : s + 1 - ρ' = τ)
    (g : Model (HC38 ρ')) (n : ℤ) :
    fullModeWeight c τ n * ‖modeSeq38 c s ρ' g n‖ ^ 2 =
      sobolevModeWeight ρ' n * ‖((g n : HC38 ρ') : ℤ → ℂ) n‖ ^ 2 := by
  have hw := orbitWeight38_pos c s n
  unfold modeSeq38
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, ← orbitWeight38_sq_mul' c s ρ' τ hτ]
  field_simp

theorem mem_modeSeq38 (s ρ' τ : ℝ) (hτ : s + 1 - ρ' = τ) (g : Model (HC38 ρ')) :
    modeSeq38 c s ρ' g ∈ seqE38 c τ := by
  rw [mem_seqE38_iff]
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (fullModeWeight_pos c τ n).le
    (sq_nonneg _)) (fun n => ?_) g.summable_sq
  rw [fullModeWeight_mul_norm_modeSeq38 c s ρ' τ hτ]
  exact sobolevModeWeight_mul_norm_sq_le ρ' (g n) n

theorem norm_modeSeq38_le (s ρ' τ : ℝ) (hτ : s + 1 - ρ' = τ) (g : Model (HC38 ρ')) :
    ‖eMk38 c τ (modeSeq38 c s ρ' g) (mem_modeSeq38 c s ρ' τ hτ g)‖ ≤ ‖g‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [Model.norm_sq_eq, norm_sq_eCarrier38]
  refine Summable.tsum_le_tsum (fun n => ?_) ?_ g.summable_sq
  · rw [eCoe38_mk, fullModeWeight_mul_norm_modeSeq38 c s ρ' τ hτ]
    exact sobolevModeWeight_mul_norm_sq_le ρ' (g n) n
  · have := (mem_seqE38_iff c τ _).1 (mem_modeSeq38 c s ρ' τ hτ g)
    exact this

/-- `π`: extract the diagonal modes, `Model (h^ρ') →L[ℝ] E_τ`. -/
def modeCLM38 (s ρ' τ : ℝ) (hτ : s + 1 - ρ' = τ) : Model (HC38 ρ') →L[ℝ] ECarrier38 c τ :=
  LinearMap.mkContinuous
    { toFun := fun g => eMk38 c τ (modeSeq38 c s ρ' g) (mem_modeSeq38 c s ρ' τ hτ g)
      map_add' := fun g h => eExt38 c τ (funext fun n => by
        simp only [eCoe38_mk, modeSeq38, Model.add_apply]
        rw [eAdd_apply38]
        simp only [eCoe38_mk, modeSeq38]
        rw [hAdd_apply38]; ring)
      map_smul' := fun a g => eExt38 c τ (funext fun n => by
        simp only [eCoe38_mk, modeSeq38, Model.smul_apply, RingHom.id_apply]
        rw [eSmul_apply38]
        simp only [eCoe38_mk, modeSeq38]
        rw [hSmul_apply38]; ring) }
    1 (fun g => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      exact norm_modeSeq38_le c s ρ' τ hτ g)

theorem eCoe38_modeCLM38 (s ρ' τ : ℝ) (hτ : s + 1 - ρ' = τ) (g : Model (HC38 ρ')) :
    eCoe38 c τ (modeCLM38 c s ρ' τ hτ g) = modeSeq38 c s ρ' g := rfl

/-! ### Identification of the orbit (W04.02) and of the image orbit (W04.04, W04.05) -/

theorem coeff_orbitMk38 (s ρ σ : ℝ) (hσ : s + 1 - ρ = σ) (x : ℤ → ℂ) (hx : x ∈ seqE38 c σ)
    (n : ℤ) : coeff (orbitWeight38 c s) (orbitMk38 c s ρ σ hσ x hx) n = hSingle38 ρ n (x n) := by
  unfold coeff
  rw [orbitMk38_apply]
  exact inv_smul_smul₀ (orbitWeight38_pos c s n).ne' _

/-- **W04.02.** The synthesis of the weighted coefficient vector is the translation orbit:
`synth_w (ι x) (t mod 1) = S_{2πt} x` as an element of `h^ρ`, i.e.
`(synth_w (ι x) (t))_m = e^{2πi m t} x_m`. -/
theorem synth_orbitMk38 (s ρ σ : ℝ) (hσ : s + 1 - ρ = σ) (x : ℤ → ℂ) (hx : x ∈ seqE38 c σ)
    (t : ℝ) :
    synth (orbitWeight38 c s) (orbitMk38 c s ρ σ hσ x hx) ((t : ℝ) : AddCircle (1 : ℝ)) =
      hMk38 ρ (rotSeq38 (2 * π * t) x)
        (rotSeq38_mem ρ _ (seqE38_subset_seqSobolev38 c σ ρ hx)) := by
  have hw := orbitWeight38_admissible c s
  refine hExt38 ρ fun m => ?_
  set g := orbitMk38 c s ρ σ hσ x hx with hg
  set θ : AddCircle (1 : ℝ) := ((t : ℝ) : AddCircle (1 : ℝ)) with hθ
  have hs := summable_expSum_terms (summable_norm_coeff hw g).1 θ
  have h1 : (hCoord38 ρ m) (synth (orbitWeight38 c s) g θ) =
      ∑' n, (hCoord38 ρ m) (fourier n θ • coeff (orbitWeight38 c s) g n) := by
    unfold synth expSum
    exact (hCoord38 ρ m).map_tsum hs
  have h2 : ∀ n : ℤ, (hCoord38 ρ m) (fourier n θ • coeff (orbitWeight38 c s) g n) =
      if n = m then fourier m θ * x m else 0 := by
    intro n
    rw [map_smul, hg, coeff_orbitMk38, hCoord38_apply, hSingle38_apply, smul_eq_mul]
    by_cases h : n = m
    · subst h; simp
    · simp [h, Ne.symm h]
  simp_rw [h2] at h1
  rw [tsum_ite_eq] at h1
  change (hCoord38 ρ m) _ = _
  rw [h1, hθ, fourier_coe_eq_rotPhase38]
  rfl

theorem continuous_synth_orbit38 (s ρ : ℝ) (G : Model (HC38 ρ)) :
    Continuous (synth (orbitWeight38 c s) G) :=
  continuous_synth (orbitWeight38_admissible c s) G

/-- **W04.04 (image orbit).** If the synthesis of `G ∈ ℓ²(ℤ; h^ρ')` is the orbit `S_{2πt} z` of a
sequence `z ∈ h^ρ'`, then the `m`-th mode of the `n`-th coefficient of `G` is `w_n z_n δ_{mn}`. -/
theorem coord_of_orbit_synth38 (s ρ' : ℝ) (G : Model (HC38 ρ')) (z : ℤ → ℂ)
    (hz : z ∈ seqSobolev38 ρ')
    (hG : ∀ t : ℝ, synth (orbitWeight38 c s) G ((t : ℝ) : AddCircle (1 : ℝ)) =
      hMk38 ρ' (rotSeq38 (2 * π * t) z) (rotSeq38_mem ρ' _ hz)) (n m : ℤ) :
    ((G n : HC38 ρ') : ℤ → ℂ) m = if m = n then (orbitWeight38 c s n : ℂ) * z n else 0 := by
  have hw := orbitWeight38_admissible c s
  have h1 := coord_fourierCoeff38 (hCoord38 ρ' m) (continuous_synth hw G) n
  rw [fourierCoeff_synth hw G n] at h1
  have h2 : (fun θ : AddCircle (1 : ℝ) => (hCoord38 ρ' m) (synth (orbitWeight38 c s) G θ)) =
      fun θ => fourier m θ * z m := by
    funext θ
    obtain ⟨t, rfl⟩ := exists_coe_eq θ
    rw [hG t, fourier_coe_eq_rotPhase38]
    rfl
  rw [h2, fourierCoeff_mode38] at h1
  have h3 : (hCoord38 ρ' m) (coeff (orbitWeight38 c s) G n) =
      ((orbitWeight38 c s n)⁻¹ : ℝ) * ((G n : HC38 ρ') : ℤ → ℂ) m := by
    unfold coeff
    rw [hCoord38_apply, hSmul_apply38]
  rw [h3] at h1
  have hw0 : ((orbitWeight38 c s n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (orbitWeight38_pos c s n).ne'
  have h4 : ((G n : HC38 ρ') : ℤ → ℂ) m =
      (orbitWeight38 c s n : ℂ) * (((orbitWeight38 c s n)⁻¹ : ℝ) *
        ((G n : HC38 ρ') : ℤ → ℂ) m) := by
    push_cast
    field_simp
  rw [h4, h1]
  by_cases h : m = n
  · subst h; simp
  · simp [h]

/-- The extraction recovers `z` from the image orbit. -/
theorem eCoe_modeCLM_of_orbit_synth38 (s ρ' τ : ℝ) (hτ : s + 1 - ρ' = τ) (G : Model (HC38 ρ'))
    (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 ρ')
    (hG : ∀ t : ℝ, synth (orbitWeight38 c s) G ((t : ℝ) : AddCircle (1 : ℝ)) =
      hMk38 ρ' (rotSeq38 (2 * π * t) z) (rotSeq38_mem ρ' _ hz)) :
    eCoe38 c τ (modeCLM38 c s ρ' τ hτ G) = z := by
  rw [eCoe38_modeCLM38]
  funext n
  unfold modeSeq38
  rw [coord_of_orbit_synth38 c s ρ' G z hz hG n n]
  simp only [↓reduceIte]
  have hw0 : ((orbitWeight38 c s n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (orbitWeight38_pos c s n).ne'
  push_cast
  field_simp

/-- **Second norm identity of W04.05.** The weighted norm of the image orbit is the `E_τ` norm of
`z`. -/
theorem norm_eq_of_orbit_synth38 (s ρ' τ : ℝ) (hτ : s + 1 - ρ' = τ) (G : Model (HC38 ρ'))
    (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 ρ')
    (hG : ∀ t : ℝ, synth (orbitWeight38 c s) G ((t : ℝ) : AddCircle (1 : ℝ)) =
      hMk38 ρ' (rotSeq38 (2 * π * t) z) (rotSeq38_mem ρ' _ hz)) :
    ‖G‖ = ‖modeCLM38 c s ρ' τ hτ G‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [Model.norm_sq_eq, norm_sq_eCarrier38]
  refine tsum_congr fun n => ?_
  have hz' := eCoe_modeCLM_of_orbit_synth38 c s ρ' τ hτ G z hz hG
  have hG' : G n = orbitWeight38 c s n • hSingle38 ρ' n (z n) := by
    refine hExt38 ρ' fun m => ?_
    rw [coord_of_orbit_synth38 c s ρ' G z hz hG n m, hSmul_apply38, hSingle38_apply]
    split_ifs <;> simp
  have e : ‖G n‖ ^ 2 = fullModeWeight c τ n * ‖z n‖ ^ 2 := by
    rw [hG', norm_orbit_term38 c s ρ' τ hτ]
  rw [hz']
  exact e

end Orbit

end NlsGge.Birkhoff
