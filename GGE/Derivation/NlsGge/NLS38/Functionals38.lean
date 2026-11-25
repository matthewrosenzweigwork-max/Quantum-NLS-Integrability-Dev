import NlsGge.NLS38.Functionals38a

/-! # GWP piece A7a (part b): the bounded bilinear map, continuity and derivatives on the carrier

Plan: `campaign/GWP_PLAN.md` §7 Part A, piece A7a (risk R5).  Public entry point
`NlsGge.NLS38.Functionals38` for the A7a API; part a is `NlsGge.NLS38.Functionals38a`
(definitions `mass kin quart ham`, summability on `h¹`, `hn_one_sq`, `quart_le`, `inner_nonlin_real`).

* `convC38 : h¹ →L h¹ →L h⁰`, `(x, y) ↦ x * y`, bounded real bilinear (Young `ℓ¹ * ℓ²` and
  `ℓ¹ ≤ C₁ h¹`);
* `mass kin quart` of a carrier element are `‖ι x‖²`, `4π²(‖x‖² - ‖ι x‖²)`, `‖convC38 x x‖²`
  (`ι = carrierIncl38 : h¹ → h⁰`); continuity on `SobolevCarrier38 1`;
* derivatives along `C¹` curves of the carrier (`HasDerivAt γ γ' t`):
  `D mass (u) y = 2 Re ⟨u, y⟩`, `D kin (u) y = 2 Re Σ (2πn)² ū_n y_n`,
  `D quart (u) y = 2 Re ⟨N(u), y⟩` with `⟨a, b⟩ = Σ ā_n b_n` (adjointness `inner_conv_cstar`).
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open scoped ComplexConjugate InnerProductSpace

/-- `SobolevCarrier38 1` (index a natural cast, §6.0). -/
abbrev H1C38 : Type := SobolevCarrier38 ((1 : ℕ) : ℝ)
/-- `SobolevCarrier38 0` (index a natural cast, §6.0). -/
abbrev H0C38 : Type := SobolevCarrier38 ((0 : ℕ) : ℝ)

/-- The inclusion `h¹ → h⁰`. -/
def incl01 : H1C38 →L[ℝ] H0C38 :=
  carrierIncl38 (show ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num)

theorem coe_incl01 (x : H1C38) :
    carrierCoe38 ((0 : ℕ) : ℝ) (incl01 x) = carrierCoe38 ((1 : ℕ) : ℝ) x :=
  carrierCoe38_incl38 _ x

theorem mem0_of_summable {x : ℤ → ℂ} (h : Summable fun n : ℤ => ‖x n‖ ^ 2) :
    x ∈ seqSobolev38 ((0 : ℕ) : ℝ) := by
  rw [mem_seqSobolev38_iff]
  unfold SobolevSquareSummable
  simpa [Nat.cast_zero] using h

theorem hn_one_coe (x : H1C38) : hn 1 (carrierCoe38 _ x) = ‖x‖ := by
  have h := carrier_hasSum_norm_sq38 ((1 : ℕ) : ℝ) x
  have h2 : ∑' n : ℤ, sobolevModeWeight ((1 : ℕ) : ℝ) n * ‖carrierCoe38 _ x n‖ ^ 2 = ‖x‖ ^ 2 :=
    h.tsum_eq
  rw [← Real.sqrt_sq (norm_nonneg x), ← h2]
  unfold hn
  simp only [sobolevModeWeight_natCast_eq]

theorem isL1_coe (x : H1C38) : IsL1 (carrierCoe38 _ x) ∧ l1 (carrierCoe38 _ x) ≤ C1 * ‖x‖ := by
  obtain ⟨h1, h2⟩ := isL1_of_hn_one _ (carrierCoe38_mem ((1 : ℕ) : ℝ) x)
  exact ⟨h1, by rwa [hn_one_coe] at h2⟩

theorem summable_sq_coe (x : H1C38) : Summable fun n => ‖carrierCoe38 _ x n‖ ^ 2 :=
  summable_sq_of_h1 (carrierCoe38_mem ((1 : ℕ) : ℝ) x)

theorem mass_coe_le (x : H1C38) : mass (carrierCoe38 _ x) ≤ ‖x‖ ^ 2 := by
  have := mass_le_hn_sq (carrierCoe38_mem ((1 : ℕ) : ℝ) x)
  rwa [hn_one_coe] at this

/-! ## The bilinear map `convC38` -/

section Bilinear

theorem summable_sq_conv_coe (x y : H1C38) :
    Summable fun n => ‖conv (carrierCoe38 _ x) (carrierCoe38 _ y) n‖ ^ 2 :=
  (summable_sq_conv (isL1_coe x).1 (summable_sq_coe y)).1

/-- `x * y ∈ h⁰`, as an element of the carrier. -/
def convMk (x y : H1C38) : H0C38 :=
  carrierMk38 ((0 : ℕ) : ℝ) (conv (carrierCoe38 _ x) (carrierCoe38 _ y))
    (mem0_of_summable (summable_sq_conv_coe x y))

@[simp] theorem coe_convMk (x y : H1C38) :
    carrierCoe38 ((0 : ℕ) : ℝ) (convMk x y) = conv (carrierCoe38 _ x) (carrierCoe38 _ y) := rfl

theorem coe_add (r : ℝ) (x y : SobolevCarrier38 r) :
    carrierCoe38 r (x + y) = carrierCoe38 r x + carrierCoe38 r y := rfl

theorem coe_smul (r : ℝ) (c : ℝ) (x : SobolevCarrier38 r) :
    carrierCoe38 r (c • x) = (c : ℂ) • carrierCoe38 r x := by
  funext n
  exact (Complex.real_smul (x := c) (z := carrierCoe38 r x n))

theorem norm_sq_convMk (x y : H1C38) :
    ‖convMk x y‖ ^ 2 = ∑' n, ‖conv (carrierCoe38 _ x) (carrierCoe38 _ y) n‖ ^ 2 := by
  have h := carrier_hasSum_norm_sq_zero38 (convMk x y)
  exact h.tsum_eq.symm

theorem norm_convMk_le (x y : H1C38) : ‖convMk x y‖ ≤ C1 * ‖x‖ * ‖y‖ := by
  obtain ⟨hL, hl⟩ := isL1_coe x
  have hl0 : 0 ≤ l1 (carrierCoe38 _ x) := tsum_nonneg fun _ => norm_nonneg _
  have h1 := (summable_sq_conv hL (summable_sq_coe y)).2
  have h2 := mass_coe_le y
  have h3 : l1 (carrierCoe38 _ x) ^ 2 ≤ (C1 * ‖x‖) ^ 2 := pow_le_pow_left₀ hl0 hl 2
  have hsq : ‖convMk x y‖ ^ 2 ≤ (C1 * ‖x‖ * ‖y‖) ^ 2 := by
    rw [norm_sq_convMk]
    calc _ ≤ l1 (carrierCoe38 _ x) ^ 2 * ∑' n, ‖carrierCoe38 _ y n‖ ^ 2 := h1
      _ ≤ (C1 * ‖x‖) ^ 2 * ‖y‖ ^ 2 := mul_le_mul h3 h2 (mass_nonneg _) (sq_nonneg _)
      _ = _ := by ring
  have hC : 0 ≤ C1 := norm_nonneg _
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hsq

theorem convMk_add_left (x x' y : H1C38) : convMk (x + x') y = convMk x y + convMk x' y := by
  apply carrierExt38
  rw [coe_add, coe_convMk, coe_convMk, coe_convMk, coe_add]
  exact conv_add_left (isL1_coe x).1 (isL1_coe x').1 (isL1_coe y).1

theorem convMk_add_right (x y y' : H1C38) : convMk x (y + y') = convMk x y + convMk x y' := by
  apply carrierExt38
  rw [coe_add, coe_convMk, coe_convMk, coe_convMk, coe_add]
  exact conv_add_right (isL1_coe x).1 (isL1_coe y).1 (isL1_coe y').1

theorem convMk_smul_left (c : ℝ) (x y : H1C38) : convMk (c • x) y = c • convMk x y := by
  apply carrierExt38
  rw [coe_smul, coe_convMk, coe_smul, coe_convMk]
  exact conv_smul_left _ _ _

theorem convMk_smul_right (c : ℝ) (x y : H1C38) : convMk x (c • y) = c • convMk x y := by
  apply carrierExt38
  rw [coe_smul, coe_convMk, coe_smul, coe_convMk]
  exact conv_smul_right _ _ _

/-- The bounded real bilinear map `(x, y) ↦ x * y`, `h¹ × h¹ → h⁰`. -/
def convC38 : H1C38 →L[ℝ] H1C38 →L[ℝ] H0C38 :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ convMk convMk_add_left convMk_smul_left convMk_add_right convMk_smul_right)
    C1 (fun x y => by simpa [LinearMap.mk₂_apply] using norm_convMk_le x y)

@[simp] theorem convC38_apply (x y : H1C38) : convC38 x y = convMk x y := rfl

theorem coe_convC38 (x y : H1C38) :
    carrierCoe38 ((0 : ℕ) : ℝ) (convC38 x y) = conv (carrierCoe38 _ x) (carrierCoe38 _ y) := rfl

theorem convC38_comm (x y : H1C38) : convC38 x y = convC38 y x := by
  apply carrierExt38
  rw [coe_convC38, coe_convC38]
  exact conv_comm _ _

end Bilinear

/-! ## The functionals on the carrier -/

section Carrier

theorem mass_coe_eq (x : H1C38) : mass (carrierCoe38 _ x) = ‖incl01 x‖ ^ 2 := by
  have h := carrier_hasSum_norm_sq_zero38 (incl01 x)
  rw [coe_incl01] at h
  exact h.tsum_eq

theorem quart_coe_eq (x : H1C38) : quart (carrierCoe38 _ x) = ‖convC38 x x‖ ^ 2 := by
  rw [convC38_apply, norm_sq_convMk]; rfl

theorem kin_coe_eq (x : H1C38) :
    kin (carrierCoe38 _ x) = 4 * Real.pi ^ 2 * (‖x‖ ^ 2 - ‖incl01 x‖ ^ 2) := by
  have h := hn_one_sq (carrierCoe38_mem ((1 : ℕ) : ℝ) x)
  rw [hn_one_coe, mass_coe_eq] at h
  have hpi : (4 * Real.pi ^ 2) ≠ 0 := by positivity
  rw [h]; field_simp; ring

theorem continuous_mass_coe : Continuous fun x : H1C38 => mass (carrierCoe38 _ x) := by
  simp only [mass_coe_eq]
  exact (incl01.continuous.norm).pow 2

theorem continuous_quart_coe : Continuous fun x : H1C38 => quart (carrierCoe38 _ x) := by
  simp only [quart_coe_eq]
  exact ((convC38.continuous₂.comp (continuous_id.prodMk continuous_id)).norm).pow 2

theorem continuous_kin_coe : Continuous fun x : H1C38 => kin (carrierCoe38 _ x) := by
  simp only [kin_coe_eq]
  exact continuous_const.mul ((continuous_norm.pow 2).sub ((incl01.continuous.norm).pow 2))

theorem continuous_ham_coe : Continuous fun x : H1C38 => ham (carrierCoe38 _ x) :=
  continuous_kin_coe.add continuous_quart_coe

/-- `mass` and `ham` are continuous on `SobolevCarrier38 1` (so is `Bx` of A8). -/
theorem continuous_mass_ham :
    Continuous (fun x : H1C38 => mass (carrierCoe38 _ x)) ∧
      Continuous (fun x : H1C38 => ham (carrierCoe38 _ x)) :=
  ⟨continuous_mass_coe, continuous_ham_coe⟩

end Carrier

/-! ## Inner products in coordinates -/

section Inner

theorem summable_wconj {w : ℤ → ℝ} (hw : ∀ n, 0 ≤ w n) {x y : ℤ → ℂ}
    (hx : Summable fun n => w n * ‖x n‖ ^ 2) (hy : Summable fun n => w n * ‖y n‖ ^ 2) :
    Summable fun n => ((w n : ℝ) : ℂ) * (conj (x n) * y n) := by
  refine Summable.of_norm_bounded ((hx.add hy).mul_left (1 / 2)) fun n => ?_
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (hw n)]
  nlinarith [mul_nonneg (hw n) (sq_nonneg (‖x n‖ - ‖y n‖))]

/-- Real inner product of the carrier as the real part of the complex pairing. -/
theorem inner_eq_re_tsum (r : ℝ) (a b : SobolevCarrier38 r) :
    inner ℝ a b = (∑' n, ((sobolevModeWeight r n : ℝ) : ℂ) *
      (conj (carrierCoe38 r a n) * carrierCoe38 r b n)).re := by
  have hs := summable_wconj (fun n => (sobolevModeWeight_pos r n).le)
    (carrier_hasSum_norm_sq38 r a).summable (carrier_hasSum_norm_sq38 r b).summable
  rw [Complex.re_tsum hs]
  refine ((carrier_inner_hasSum38 r a b).tsum_eq).symm.trans (tsum_congr fun n => ?_)
  rw [Complex.re_ofReal_mul]

theorem inner_eq_re_tsum_zero (a b : H0C38) :
    inner ℝ a b = (∑' n, conj (carrierCoe38 _ a n) * carrierCoe38 _ b n).re := by
  rw [inner_eq_re_tsum]
  simp only [sobolevModeWeight_natCast_zero, Complex.ofReal_one, one_mul]

theorem inner_incl01 (a b : H1C38) :
    inner ℝ (incl01 a) (incl01 b) =
      (∑' n, conj (carrierCoe38 _ a n) * carrierCoe38 _ b n).re := by
  rw [inner_eq_re_tsum_zero]
  simp only [coe_incl01]

/-- `4π² (⟨x,y⟩_{h¹} - ⟨ιx, ιy⟩_{h⁰}) = Σ (2πn)² Re(x̄_n y_n)`. -/
theorem hasSum_disp_inner (a b : H1C38) :
    HasSum (fun n : ℤ => disp n * (conj (carrierCoe38 _ a n) * carrierCoe38 _ b n).re)
      (4 * Real.pi ^ 2 * (inner ℝ a b - inner ℝ (incl01 a) (incl01 b))) := by
  have h1 := carrier_inner_hasSum38 ((1 : ℕ) : ℝ) a b
  have h0 := carrier_inner_hasSum38 ((0 : ℕ) : ℝ) (incl01 a) (incl01 b)
  simp only [coe_incl01, sobolevModeWeight_natCast_zero, one_mul] at h0
  have h := (h1.sub h0).mul_left (4 * Real.pi ^ 2)
  refine h.congr_fun fun n => ?_
  simp only [sobolevModeWeight_cast_one, disp_eq]
  ring

theorem re_tsum_disp (a b : H1C38) :
    (∑' n, ((disp n : ℝ) : ℂ) * (conj (carrierCoe38 _ a n) * carrierCoe38 _ b n)).re =
      4 * Real.pi ^ 2 * (inner ℝ a b - inner ℝ (incl01 a) (incl01 b)) := by
  have hs := summable_wconj disp_nonneg
    (summable_kin_of_h1 (carrierCoe38_mem ((1 : ℕ) : ℝ) a))
    (summable_kin_of_h1 (carrierCoe38_mem ((1 : ℕ) : ℝ) b))
  rw [Complex.re_tsum hs]
  refine Eq.trans (tsum_congr fun n => ?_) (hasSum_disp_inner a b).tsum_eq
  rw [Complex.re_ofReal_mul]

end Inner

/-! ## Derivatives along `C¹` curves of the carrier -/

section Deriv

variable {γ : ℝ → H1C38} {γ' : H1C38} {t : ℝ}

theorem hasDerivAt_incl01 (h : HasDerivAt γ γ' t) :
    HasDerivAt (fun s => incl01 (γ s)) (incl01 γ') t :=
  incl01.hasFDerivAt.comp_hasDerivAt t h

/-- `d/dt Q₀(u) = 2 Re ⟨u, u'⟩`. -/
theorem hasDerivAt_mass (h : HasDerivAt γ γ' t) :
    HasDerivAt (fun s => mass (carrierCoe38 ((1 : ℕ) : ℝ) (γ s)))
      (2 * (∑' n, conj (carrierCoe38 ((1 : ℕ) : ℝ) (γ t) n) *
        carrierCoe38 ((1 : ℕ) : ℝ) γ' n).re) t := by
  have h1 := (hasDerivAt_incl01 h).norm_sq
  rw [inner_incl01] at h1
  simpa only [mass_coe_eq] using h1

/-- `d/dt Σ (2πn)² |u_n|² = 2 Re Σ (2πn)² ū_n u'_n`. -/
theorem hasDerivAt_kin (h : HasDerivAt γ γ' t) :
    HasDerivAt (fun s => kin (carrierCoe38 ((1 : ℕ) : ℝ) (γ s)))
      (2 * (∑' n, ((disp n : ℝ) : ℂ) * (conj (carrierCoe38 ((1 : ℕ) : ℝ) (γ t) n) *
        carrierCoe38 ((1 : ℕ) : ℝ) γ' n)).re) t := by
  have h1 := ((h.norm_sq).sub (hasDerivAt_incl01 h).norm_sq).const_mul (4 * Real.pi ^ 2)
  rw [re_tsum_disp]
  simp only [kin_coe_eq]
  convert h1 using 1
  ring

/-- `d/dt ∫|u|⁴ = 2 Re ⟨N(u), u'⟩`  (`D Q(u) y = 4 Re ⟨u*u, u*y⟩ = 2 Re ⟨N(u), y⟩`). -/
theorem hasDerivAt_quart (h : HasDerivAt γ γ' t) :
    HasDerivAt (fun s => quart (carrierCoe38 ((1 : ℕ) : ℝ) (γ s)))
      (2 * (∑' n, conj (nonlin (carrierCoe38 ((1 : ℕ) : ℝ) (γ t)) n) *
        carrierCoe38 ((1 : ℕ) : ℝ) γ' n).re) t := by
  have hc : HasDerivAt (fun s => convC38 (γ s)) (convC38 γ') t :=
    convC38.hasFDerivAt.comp_hasDerivAt t h
  have hb := hc.clm_apply h
  have h1 := hb.norm_sq
  simp only [quart_coe_eq]
  convert h1 using 1
  rw [inner_eq_re_tsum_zero]
  congr 2
  -- the pairing identity
  set u := carrierCoe38 ((1 : ℕ) : ℝ) (γ t) with hu
  set v := carrierCoe38 ((1 : ℕ) : ℝ) γ' with hv
  have hL : IsL1 u := (isL1_coe (γ t)).1
  have hw : Summable fun n => ‖conv u u n‖ ^ 2 := summable_sq_conv_coe (γ t) (γ t)
  have hadj := inner_conv_cstar (f := conv u u) (g := u) (y := v) hw hL (summable_sq_coe γ')
  have e1 : ∀ n, conj (carrierCoe38 ((0 : ℕ) : ℝ) (convC38 (γ t) (γ t)) n) *
      carrierCoe38 ((0 : ℕ) : ℝ) (convC38 γ' (γ t) + convC38 (γ t) γ') n =
      2 * (conj (conv u u n) * conv u v n) := fun n => by
    rw [coe_convC38, coe_add, Pi.add_apply, coe_convC38, coe_convC38, conv_comm v u]
    ring
  simp only [e1]
  rw [tsum_mul_left, ← hadj]
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  simp only [nonlin, map_mul, map_ofNat]
  ring

end Deriv

/-! ## Regression probes: the derivative formulas along the ray `s ↦ s x` -/

section Probes

variable (x : H1C38)

theorem quart_coe_smul (s : ℝ) :
    quart (carrierCoe38 ((1 : ℕ) : ℝ) (s • x)) = s ^ 4 * quart (carrierCoe38 _ x) := by
  rw [quart_coe_eq, quart_coe_eq]
  simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]
  ring

theorem mass_coe_smul (s : ℝ) :
    mass (carrierCoe38 ((1 : ℕ) : ℝ) (s • x)) = s ^ 2 * mass (carrierCoe38 _ x) := by
  rw [mass_coe_eq, mass_coe_eq, map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- Euler identity for the quartic charge at `s = 1`: `2 Re ⟨N(x), x⟩ = 4 Q(x)`
(compare `inner_nonlin_real`). -/
theorem probe_deriv_quart_ray :
    2 * (∑' n, conj (nonlin (carrierCoe38 ((1 : ℕ) : ℝ) x) n) * carrierCoe38 _ x n).re =
      4 * quart (carrierCoe38 _ x) := by
  have hγ : HasDerivAt (fun s : ℝ => s • x) x 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
  have h := hasDerivAt_quart hγ
  have h2 : HasDerivAt (fun s : ℝ => quart (carrierCoe38 ((1 : ℕ) : ℝ) (s • x)))
      (4 * quart (carrierCoe38 _ x)) 1 := by
    simp only [quart_coe_smul]
    simpa using (hasDerivAt_pow 4 (1 : ℝ)).mul_const (quart (carrierCoe38 ((1 : ℕ) : ℝ) x))
  have := h.unique h2
  simpa using this

/-- Euler identity for the mass: `2 Re ⟨x, x⟩ = 2 Q₀(x)`. -/
theorem probe_deriv_mass_ray :
    2 * (∑' n, conj (carrierCoe38 ((1 : ℕ) : ℝ) x n) * carrierCoe38 _ x n).re =
      2 * mass (carrierCoe38 _ x) := by
  have hγ : HasDerivAt (fun s : ℝ => s • x) x 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
  have h := hasDerivAt_mass hγ
  have h2 : HasDerivAt (fun s : ℝ => mass (carrierCoe38 ((1 : ℕ) : ℝ) (s • x)))
      (2 * mass (carrierCoe38 _ x)) 1 := by
    simp only [mass_coe_smul]
    simpa using (hasDerivAt_pow 2 (1 : ℝ)).mul_const (mass (carrierCoe38 ((1 : ℕ) : ℝ) x))
  have := h.unique h2
  simpa using this

/-- Euler identity for the kinetic energy: `2 Re Σ (2πn)² x̄_n x_n = 2 kin x`. -/
theorem probe_deriv_kin_ray :
    2 * (∑' n, ((disp n : ℝ) : ℂ) * (conj (carrierCoe38 ((1 : ℕ) : ℝ) x n) *
      carrierCoe38 _ x n)).re = 2 * kin (carrierCoe38 _ x) := by
  have hγ : HasDerivAt (fun s : ℝ => s • x) x 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
  have h := hasDerivAt_kin hγ
  have hk : ∀ s : ℝ, kin (carrierCoe38 ((1 : ℕ) : ℝ) (s • x)) =
      s ^ 2 * kin (carrierCoe38 _ x) := fun s => by
    rw [kin_coe_eq, kin_coe_eq, map_smul, norm_smul, norm_smul, mul_pow, mul_pow,
      Real.norm_eq_abs, sq_abs]
    ring
  have h2 : HasDerivAt (fun s : ℝ => kin (carrierCoe38 ((1 : ℕ) : ℝ) (s • x)))
      (2 * kin (carrierCoe38 _ x)) 1 := by
    simp only [hk]
    simpa using (hasDerivAt_pow 2 (1 : ℝ)).mul_const (kin (carrierCoe38 ((1 : ℕ) : ℝ) x))
  have := h.unique h2
  simpa using this

end Probes

end NlsGge.NLS38
