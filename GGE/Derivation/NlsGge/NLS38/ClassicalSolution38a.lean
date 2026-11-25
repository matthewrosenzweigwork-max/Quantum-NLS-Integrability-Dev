import NlsGge.NLS38.WeightedTrilinear38

/-! # GWP piece A11 (part a): the evaluation series `serU` on `ℓ¹`

Plan: `campaign/GWP_PLAN.md` §7 Part A, piece A11.  The entry point is
`NlsGge.NLS38.ClassicalSolution38`.

`serU x θ = ∑ₙ xₙ e^{2πinθ}` (period one, the project's Fourier convention
`u(θ) = ∑ uₙ e^{2πinθ}`).  Everything here is `ℓ¹` calculus: summability is proved before every
`tsum` identity (AGENTS.md).

* linearity, the bound `‖serU f θ‖ ≤ l1 f`, periodicity, continuity in `θ` and joint continuity along
  a curve that is continuous in `ℓ¹`;
* Cauchy product `serU_mul` (`ℤ × ℤ` reindexing with `pairEquiv`) and `serU_conj`;
* termwise differentiation `hasDerivAt_serU` with `dx f n = 2πi n fₙ`;
* `dx` on the scale `h^m`: `hn m (dx f) ≤ 2π hn (m+1) f`.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff Filter Topology
open scoped ComplexConjugate

/-- Evaluation of a Fourier coefficient sequence at `θ ∈ ℝ` (period one):
`serU x θ = ∑ₙ xₙ e^{2πinθ}`. -/
def serU (x : ℤ → ℂ) (θ : ℝ) : ℂ := ∑' n : ℤ, x n * Complex.exp (2 * Real.pi * Complex.I * n * θ)

/-- The exponential `e^{2πinθ}`. -/
def eT (n : ℤ) (θ : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * n * θ)

theorem serU_def (x : ℤ → ℂ) (θ : ℝ) : serU x θ = ∑' n : ℤ, x n * eT n θ := rfl

theorem norm_eT (n : ℤ) (θ : ℝ) : ‖eT n θ‖ = 1 := by
  unfold eT
  have : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (θ : ℂ)) =
      ((2 * Real.pi * n * θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this]
  exact Complex.norm_exp_ofReal_mul_I _

theorem eT_add (a b : ℤ) (θ : ℝ) : eT (a + b) θ = eT a θ * eT b θ := by
  unfold eT
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem eT_neg (n : ℤ) (θ : ℝ) : conj (eT n θ) = eT (-n) θ := by
  unfold eT
  rw [← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]

theorem eT_periodic (n : ℤ) (θ : ℝ) : eT n (θ + 1) = eT n θ := by
  unfold eT
  have : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((θ + 1 : ℝ) : ℂ)) =
      (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (θ : ℂ)) + (n : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem serU_periodic (f : ℤ → ℂ) (θ : ℝ) : serU f (θ + 1) = serU f θ := by
  simp only [serU_def, eT_periodic]

/-! ## `ℓ¹` calculus -/

theorem summable_serU_term {f : ℤ → ℂ} (hf : IsL1 f) (θ : ℝ) :
    Summable fun n => f n * eT n θ :=
  Summable.of_norm (hf.congr fun n => by rw [norm_mul, norm_eT, mul_one])

theorem norm_serU_le {f : ℤ → ℂ} (hf : IsL1 f) (θ : ℝ) : ‖serU f θ‖ ≤ l1 f := by
  rw [serU_def]
  refine (norm_tsum_le_tsum_norm (summable_serU_term hf θ).norm).trans (le_of_eq ?_)
  unfold l1
  exact tsum_congr fun n => by rw [norm_mul, norm_eT, mul_one]

theorem l1_nonneg (f : ℤ → ℂ) : 0 ≤ l1 f := tsum_nonneg fun _ => norm_nonneg _

theorem serU_add {f g : ℤ → ℂ} (hf : IsL1 f) (hg : IsL1 g) (θ : ℝ) :
    serU (f + g) θ = serU f θ + serU g θ := by
  simp only [serU_def, Pi.add_apply, add_mul]
  exact (summable_serU_term hf θ).tsum_add (summable_serU_term hg θ)

theorem serU_sub {f g : ℤ → ℂ} (hf : IsL1 f) (hg : IsL1 g) (θ : ℝ) :
    serU (f - g) θ = serU f θ - serU g θ := by
  simp only [serU_def, Pi.sub_apply, sub_mul]
  exact (summable_serU_term hf θ).tsum_sub (summable_serU_term hg θ)

theorem serU_smul (c : ℂ) (f : ℤ → ℂ) (θ : ℝ) : serU (c • f) θ = c * serU f θ := by
  simp only [serU_def, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact tsum_mul_left

theorem serU_fun_mul_const (c : ℂ) (f : ℤ → ℂ) (θ : ℝ) :
    serU (fun n => c * f n) θ = c * serU f θ := serU_smul c f θ

theorem serU_neg (f : ℤ → ℂ) (θ : ℝ) : serU (fun n => - f n) θ = - serU f θ := by
  have := serU_smul (-1) f θ
  rw [neg_one_smul] at this
  show serU (-f) θ = _
  rw [this]; ring

theorem isL1_neg {f : ℤ → ℂ} (hf : IsL1 f) : IsL1 (fun n => - f n) :=
  hf.congr fun n => by simp

theorem isL1_const_mul (c : ℂ) {f : ℤ → ℂ} (hf : IsL1 f) : IsL1 (fun n => c * f n) :=
  isL1_smul c hf

theorem continuous_serU {f : ℤ → ℂ} (hf : IsL1 f) : Continuous (serU f) := by
  unfold serU
  refine continuous_tsum (u := fun n => ‖f n‖) (fun n => ?_) hf fun n θ => ?_
  · fun_prop
  · rw [norm_mul, show Complex.exp (2 * Real.pi * Complex.I * n * θ) = eT n θ from rfl, norm_eT,
      mul_one]

/-- Joint continuity along an `ℓ¹`-continuous curve. -/
theorem continuous_serU_curve {y : ℝ → ℤ → ℂ} (hy : ∀ t, IsL1 (y t))
    (hc : ∀ t0, Tendsto (fun t => l1 (y t - y t0)) (𝓝 t0) (𝓝 0)) :
    Continuous (Function.uncurry fun t θ => serU (y t) θ) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t0, θ0⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun p : ℝ × ℝ => l1 (y p.1 - y t0)) (𝓝 (t0, θ0)) (𝓝 0) :=
    (hc t0).comp (continuousAt_fst (p := (t0, θ0)))
  have h2 : Tendsto (fun p : ℝ × ℝ => ‖serU (y t0) p.2 - serU (y t0) θ0‖) (𝓝 (t0, θ0)) (𝓝 0) := by
    have hcont := continuous_serU (hy t0)
    have : Tendsto (fun θ : ℝ => ‖serU (y t0) θ - serU (y t0) θ0‖) (𝓝 θ0) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 (hcont.tendsto θ0)
    exact this.comp (continuousAt_snd (p := (t0, θ0)))
  refine squeeze_zero (fun p => norm_nonneg _) (fun p => ?_) (by simpa using h1.add h2)
  show ‖serU (y p.1) p.2 - serU (y t0) θ0‖ ≤ _
  have e : serU (y p.1) p.2 - serU (y t0) θ0 =
      serU (y p.1 - y t0) p.2 + (serU (y t0) p.2 - serU (y t0) θ0) := by
    rw [serU_sub (hy _) (hy _)]; ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  exact norm_serU_le (isL1_sub (hy _) (hy _)) _

/-! ## Cauchy product and conjugation -/

theorem eT_split (a b : ℤ) (θ : ℝ) : eT a θ = eT b θ * eT (a - b) θ := by
  rw [← eT_add]; congr 1; ring

theorem serU_mul {f g : ℤ → ℂ} (hf : IsL1 f) (hg : IsL1 g) (θ : ℝ) :
    serU f θ * serU g θ = serU (conv f g) θ := by
  have hfs := summable_serU_term hf θ
  have hgs := summable_serU_term hg θ
  set F : ℤ × ℤ → ℂ := fun p => (f p.1 * eT p.1 θ) * (g p.2 * eT p.2 θ) with hFdef
  set H : ℤ × ℤ → ℂ := fun p => f p.2 * g (p.1 - p.2) * eT p.1 θ with hHdef
  have hF : Summable F := summable_mul_of_summable_norm
    (f := fun a => f a * eT a θ) (g := fun b => g b * eT b θ) hfs.norm hgs.norm
  have hFH : ∀ p, F (pairEquiv p) = H p := by
    intro p
    simp only [hFdef, hHdef, pairEquiv, Equiv.coe_fn_mk]
    rw [eT_split p.1 p.2 θ]; ring
  have hH : Summable H := by
    have := (pairEquiv.summable_iff (f := F)).2 hF
    exact this.congr hFH
  have h1 : ∑' z : ℤ × ℤ, F z = ∑' p : ℤ × ℤ, H p := by
    rw [← pairEquiv.tsum_eq F]
    exact tsum_congr hFH
  have e1 : serU f θ * serU g θ = ∑' z : ℤ × ℤ, F z := by
    rw [serU_def, serU_def]
    exact tsum_mul_tsum_of_summable_norm (f := fun a => f a * eT a θ)
      (g := fun b => g b * eT b θ) hfs.norm hgs.norm
  rw [e1, h1, hH.tsum_prod, serU_def]
  refine tsum_congr fun n => ?_
  simp only [hHdef, conv]
  rw [tsum_mul_right]

theorem serU_conj (f : ℤ → ℂ) (θ : ℝ) : conj (serU f θ) = serU (cstar f) θ := by
  rw [serU_def, serU_def, Complex.conj_tsum]
  simp only [map_mul, eT_neg, cstar]
  rw [← (Equiv.neg ℤ).tsum_eq (fun n => conj (f (-n)) * eT n θ)]
  exact tsum_congr fun n => by simp

/-! ## Termwise differentiation -/

/-- `dx f n = 2πi n fₙ`: the symbol of `∂ₓ`. -/
def dx (f : ℤ → ℂ) (n : ℤ) : ℂ := (2 * Real.pi * Complex.I * n) * f n

theorem hasDerivAt_eT (n : ℤ) (θ : ℝ) :
    HasDerivAt (fun y : ℝ => eT n y) (eT n θ * (2 * Real.pi * Complex.I * n)) θ := by
  unfold eT
  have h := ((Complex.ofRealCLM.hasDerivAt (x := θ)).const_mul
    (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))).cexp
  simpa [mul_comm] using h

theorem norm_dx_term (f : ℤ → ℂ) (n : ℤ) (θ : ℝ) :
    ‖f n * (eT n θ * (2 * Real.pi * Complex.I * n))‖ = ‖dx f n‖ := by
  have e : f n * (eT n θ * (2 * Real.pi * Complex.I * n)) = dx f n * eT n θ := by
    simp only [dx]; ring
  rw [e, norm_mul, norm_eT, mul_one]

theorem hasDerivAt_serU {f : ℤ → ℂ} (hf : IsL1 f) (hf' : IsL1 (dx f)) (θ : ℝ) :
    HasDerivAt (serU f) (serU (dx f) θ) θ := by
  have h := hasDerivAt_tsum (u := fun n => ‖dx f n‖) (g := fun (n : ℤ) (y : ℝ) => f n * eT n y)
    (g' := fun (n : ℤ) (y : ℝ) => f n * (eT n y * (2 * Real.pi * Complex.I * n))) (y₀ := θ)
    hf' (fun n y => (hasDerivAt_eT n y).const_mul (f n))
    (fun n y => (norm_dx_term f n y).le) (summable_serU_term hf θ) θ
  have e : ∀ y : ℝ, serU f y = ∑' n, f n * eT n y := fun y => rfl
  have e' : serU (dx f) θ = ∑' n, f n * (eT n θ * (2 * Real.pi * Complex.I * n)) := by
    rw [serU_def]
    exact tsum_congr fun n => by simp only [dx]; ring
  rw [e']
  exact h

/-! ## `dx` on the scale `h^m` -/

theorem jb_sq38 (n : ℤ) : japaneseBracket n ^ 2 = 1 + (n : ℝ) ^ 2 := by
  unfold japaneseBracket
  exact Real.sq_sqrt (by positivity)

theorem norm_dx (f : ℤ → ℂ) (n : ℤ) : ‖dx f n‖ = 2 * Real.pi * |(n : ℝ)| * ‖f n‖ := by
  have h1 : ‖(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))‖ = 2 * Real.pi * |(n : ℝ)| := by
    simp [abs_of_pos Real.pi_pos]
  rw [dx, norm_mul, h1]

theorem dx_sub (f g : ℤ → ℂ) : dx (f - g) = dx f - dx g := by
  funext n; simp [dx, mul_sub]

theorem dx_term_le (m : ℕ) (f : ℤ → ℂ) (n : ℤ) :
    japaneseBracket n ^ (2 * m) * ‖dx f n‖ ^ 2 ≤
      (2 * Real.pi) ^ 2 * (japaneseBracket n ^ (2 * (m + 1)) * ‖f n‖ ^ 2) := by
  rw [norm_dx]
  have hsq : (|(n : ℝ)|) ^ 2 ≤ japaneseBracket n ^ 2 := by
    rw [jb_sq38, sq_abs]; linarith
  have e : japaneseBracket n ^ (2 * (m + 1)) = japaneseBracket n ^ (2 * m) * japaneseBracket n ^ 2 := by
    rw [← pow_add]; ring_nf
  rw [e]
  have h0 : 0 ≤ japaneseBracket n ^ (2 * m) := pow_nonneg (japaneseBracket_pos n).le _
  have : (2 * Real.pi * |(n : ℝ)| * ‖f n‖) ^ 2 = (2 * Real.pi) ^ 2 * (|(n : ℝ)| ^ 2 * ‖f n‖ ^ 2) := by
    ring
  rw [this]
  have h2 : 0 ≤ ‖f n‖ ^ 2 := sq_nonneg _
  have h3 : |(n : ℝ)| ^ 2 * ‖f n‖ ^ 2 ≤ japaneseBracket n ^ 2 * ‖f n‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hsq h2
  have h4 := mul_le_mul_of_nonneg_left h3 h0
  have h5 := mul_le_mul_of_nonneg_left h4 (sq_nonneg (2 * Real.pi))
  calc japaneseBracket n ^ (2 * m) * ((2 * Real.pi) ^ 2 * (|(n : ℝ)| ^ 2 * ‖f n‖ ^ 2))
      = (2 * Real.pi) ^ 2 * (japaneseBracket n ^ (2 * m) * (|(n : ℝ)| ^ 2 * ‖f n‖ ^ 2)) := by ring
    _ ≤ (2 * Real.pi) ^ 2 * (japaneseBracket n ^ (2 * m) * (japaneseBracket n ^ 2 * ‖f n‖ ^ 2)) := h5
    _ = _ := by ring

theorem summable_dx_hn (m : ℕ) {f : ℤ → ℂ} (hf : f ∈ seqSobolev38 ((m + 1 : ℕ) : ℝ)) :
    Summable fun n => japaneseBracket n ^ (2 * m) * ‖dx f n‖ ^ 2 := by
  have hs := (summable_hn_of_mem (m + 1) f hf).mul_left ((2 * Real.pi) ^ 2)
  exact Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg (japaneseBracket_pos n).le _)
    (sq_nonneg _)) (fun n => dx_term_le m f n) hs

theorem dx_mem (m : ℕ) {f : ℤ → ℂ} (hf : f ∈ seqSobolev38 ((m + 1 : ℕ) : ℝ)) :
    dx f ∈ seqSobolev38 (m : ℝ) := by
  have := summable_dx_hn m hf
  have h : Summable fun n : ℤ => sobolevModeWeight (m : ℝ) n * ‖dx f n‖ ^ 2 := by
    simpa only [sobolevModeWeight_natCast_eq] using this
  exact (mem_seqSobolev38_iff _ _).2 h

theorem hn_dx_le (m : ℕ) {f : ℤ → ℂ} (hf : f ∈ seqSobolev38 ((m + 1 : ℕ) : ℝ)) :
    hn m (dx f) ≤ 2 * Real.pi * hn (m + 1) f := by
  have hle : hn m (dx f) ^ 2 ≤ (2 * Real.pi * hn (m + 1) f) ^ 2 := by
    rw [hn_sq, mul_pow, hn_sq]
    exact (summable_dx_hn m hf).tsum_le_tsum (fun n => dx_term_le m f n)
      ((summable_hn_of_mem (m + 1) f hf).mul_left _) |>.trans_eq (by rw [tsum_mul_left])
  exact le_of_sq_le_sq hle (by have := hn_nonneg38 (m + 1) f; positivity) |> fun h => h

theorem hn_mono38 {a b : ℕ} (hab : a ≤ b) {d : ℤ → ℂ} (hd : d ∈ seqSobolev38 (b : ℝ)) :
    hn a d ≤ hn b d := by
  unfold hn
  apply Real.sqrt_le_sqrt
  have ha : d ∈ seqSobolev38 (a : ℝ) := seqSobolev38_mono (by exact_mod_cast hab) hd
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_hn_of_mem a d ha) (summable_hn_of_mem b d hd)
  have hb : 1 ≤ japaneseBracket n := by
    unfold japaneseBracket
    exact Real.one_le_sqrt.2 (by nlinarith [sq_nonneg (n : ℝ)])
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hb (by omega)) (sq_nonneg _)

/-- `ℓ¹` control by `h^1`, the constant `C₁`, for the `ℓ¹` norm of a difference. -/
theorem l1_le_hn_one {f : ℤ → ℂ} (hf : f ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    IsL1 f ∧ l1 f ≤ C1 * hn 1 f := isL1_of_hn_one f hf

end NlsGge.NLS38
