import Mathlib
import QuantumNLS.LocalSpectralReduced
import QuantumNLS.Local020Abs
import QuantumNLS.Local020Core
import QuantumNLS.Local020Mul1
import QuantumNLS.Local020Entry

/-! LOCAL-020 stages S2 (common phase) and S3 (boost), together.

`W = mulU` with `α x = e^{-i(a + b x)}`, `β x = e^{+i(a + b x)}`, `b = p_k/2`.  Then
`𝓛_{u'} W = W 𝓛_u + p_k W` for `u'(x) = e^{2i(a + b x)} u(x)` (`inter_phaseBoost`; the parity changes by `(-1)^k`),
`W χ_{n,j} = e^{∓ia} χ_{n+k,j}` (`doublet_rel`), and consequently (via `Local020Core.reduced_transport`)
`B'_{n+k}(u') = p_k + M B_n(u) M⁻¹` with `M = diag(e^{-ia}, e^{ia})`; the lower-left entry satisfies
`b_{n+k}(u') = e^{2ia} b_n(u)`.  `k = 0` is the common phase `e^{2ia}`, `a = 0` the boost `B_k`. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Filter Topology QuantumNLS.LocalSpectral QuantumNLS.Local020Abs QuantumNLS.Local020Mul1
open scoped ENNReal

namespace QuantumNLS.Local020Mul2

variable {L κ : ℝ}

/-- `α(x) = e^{-i(a+bx)}`. -/
def af (a b : ℝ) (x : ℝ) : ℂ := Complex.exp (((-(a + b * x) : ℝ) : ℂ) * Complex.I)
/-- `β(x) = e^{i(a+bx)}`. -/
def bf (a b : ℝ) (x : ℝ) : ℂ := Complex.exp (((a + b * x : ℝ) : ℂ) * Complex.I)

theorem unitDiag_ab (a b : ℝ) : UnitDiag (af a b) (bf a b) :=
  ⟨by unfold af; fun_prop, by unfold bf; fun_prop,
    fun x => by unfold af; exact Complex.norm_exp_ofReal_mul_I _,
    fun x => by unfold bf; exact Complex.norm_exp_ofReal_mul_I _⟩

theorem af_mul_bf (a b x : ℝ) : af a b x * bf a b x = 1 := by
  unfold af bf
  rw [← Complex.exp_add]
  have : ((-(a + b * x) : ℝ) : ℂ) * Complex.I + ((a + b * x : ℝ) : ℂ) * Complex.I = 0 := by
    push_cast; ring
  rw [this, Complex.exp_zero]

theorem conj_bf (a b x : ℝ) : starRingEnd ℂ (bf a b x) = af a b x := by
  unfold af bf
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal]
  ring

theorem hasDerivAt_af (a b x : ℝ) :
    HasDerivAt (af a b) (-(Complex.I * (b : ℂ)) * af a b x) x := by
  have h0 : HasDerivAt (fun y : ℝ => -(a + b * y)) (-b) x := by
    have := (((hasDerivAt_id' x).const_mul b).const_add a).neg
    rw [mul_one] at this
    exact this
  have h1 := (h0.ofReal_comp.mul_const Complex.I).cexp
  refine h1.congr_deriv ?_
  unfold af; push_cast; ring

theorem hasDerivAt_bf (a b x : ℝ) :
    HasDerivAt (bf a b) ((Complex.I * (b : ℂ)) * bf a b x) x := by
  have h0 : HasDerivAt (fun y : ℝ => a + b * y) b x := by
    have := (((hasDerivAt_id' x).const_mul b).const_add a)
    rw [mul_one] at this
    exact this
  have h1 := (h0.ofReal_comp.mul_const Complex.I).cexp
  refine h1.congr_deriv ?_
  unfold bf; ring

theorem continuous_af_deriv (a b : ℝ) : Continuous (fun x => -(Complex.I * (b : ℂ)) * af a b x) := by
  unfold af; fun_prop

theorem continuous_bf_deriv (a b : ℝ) : Continuous (fun x => (Complex.I * (b : ℂ)) * bf a b x) := by
  unfold bf; fun_prop

/-- The pointwise intertwining identity. -/
theorem lopPt_dmat (a b : ℝ) (x : ℝ) (w : ℂ) (d g : E2) :
    lopPt κ (bf a b x ^ 2 * w)
      (dmat (af a b) (bf a b) x d +
        dmat (fun y => -(Complex.I * (b : ℂ)) * af a b y) (fun y => (Complex.I * (b : ℂ)) * bf a b y) x g)
      (dmat (af a b) (bf a b) x g) =
    dmat (af a b) (bf a b) x (lopPt κ w d g) + ((2 * b : ℝ) : ℂ) • dmat (af a b) (bf a b) x g := by
  have h1 := af_mul_bf a b x
  have h2 := conj_bf a b x
  unfold lopPt Jm
  ext i
  fin_cases i
  · simp only [dmat_eq, vec2, map_pow, map_mul, h2, Fin.zero_eta]
    simp
    linear_combination (-(2 * Complex.I) * (Real.sqrt κ : ℂ) * starRingEnd ℂ w * g 1 * af a b x) * h1
      + (-(2 * af a b x * (b : ℂ) * g 0)) * Complex.I_sq
  · simp only [dmat_eq, vec2, map_pow, map_mul, h2, Fin.mk_one]
    simp
    linear_combination ((2 * Complex.I) * (Real.sqrt κ : ℂ) * w * g 0 * bf a b x) * h1
      + (-(2 * (b : ℂ) * bf a b x * g 1)) * Complex.I_sq

theorem af_neg (a b x : ℝ) : af (-a) (-b) x = bf a b x := by
  unfold af bf; congr 1; push_cast; ring

theorem bf_neg (a b x : ℝ) : bf (-a) (-b) x = af a b x := by
  unfold af bf; congr 1; push_cast; ring

theorem mulU_mulU_neg (a b : ℝ) (f : H2 L) :
    mulU (unitDiag_ab (-a) (-b)) (mulU (unitDiag_ab a b) f) = f := by
  apply Lp.ext
  filter_upwards [mulU_ae (unitDiag_ab (-a) (-b)) (mulU (unitDiag_ab a b) f),
    mulU_ae (unitDiag_ab a b) f] with x h1 h2
  rw [h1, h2, dmat_dmat (by rw [af_neg, mul_comm, af_mul_bf]) (by rw [bf_neg, af_mul_bf])]

/-- The conjugated potential `e^{2i(a+bx)} u`. -/
def upb (a b : ℝ) (u : ℝ → ℂ) : ℝ → ℂ := fun x => bf a b x ^ 2 * u x

theorem upb_neg (a b : ℝ) (u : ℝ → ℂ) : upb (-a) (-b) (upb a b u) = u := by
  funext x
  unfold upb
  rw [bf_neg, ← mul_assoc, ← mul_pow, mul_comm, af_mul_bf]
  simp

theorem af_L (a b : ℝ) (τ : ℤˣ) (hτ : Complex.exp (((b * L : ℝ) : ℂ) * Complex.I) = ((τ : ℤ) : ℂ)) :
    af a b L = ((τ : ℤ) : ℂ) * af a b 0 := by
  have e : af a b L = Complex.exp (((-a : ℝ) : ℂ) * Complex.I) * (Complex.exp (((b * L : ℝ) : ℂ) * Complex.I))⁻¹ := by
    unfold af
    rw [← Complex.exp_neg, ← Complex.exp_add]
    congr 1; push_cast; ring
  rcases Int.units_eq_one_or τ with rfl | rfl <;> (rw [e, hτ]; simp [af])

theorem bf_L (a b : ℝ) (τ : ℤˣ) (hτ : Complex.exp (((b * L : ℝ) : ℂ) * Complex.I) = ((τ : ℤ) : ℂ)) :
    bf a b L = ((τ : ℤ) : ℂ) * bf a b 0 := by
  have e : bf a b L = Complex.exp (((a : ℝ) : ℂ) * Complex.I) * (Complex.exp (((b * L : ℝ) : ℂ) * Complex.I)) := by
    unfold bf
    rw [← Complex.exp_add]
    congr 1; push_cast; ring
  rw [e, hτ, mul_comm]
  simp [bf]

theorem dmat_L (a b : ℝ) (τ : ℤˣ)
    (hτ : Complex.exp (((b * L : ℝ) : ℂ) * Complex.I) = ((τ : ℤ) : ℂ)) (v : E2) :
    dmat (af a b) (bf a b) L v = ((τ : ℤ) : ℂ) • dmat (af a b) (bf a b) 0 v := by
  unfold dmat
  rw [af_L a b τ hτ, bf_L a b τ hτ, smul_add, smul_smul, smul_smul]

/-- Forward direction of the intertwining. -/
theorem fwd (hL : 0 < L) (a b : ℝ) (τ : ℤˣ)
    (hτ : Complex.exp (((b * L : ℝ) : ℂ) * Complex.I) = ((τ : ℤ) : ℂ)) (u : ℝ → ℂ) (σ : ℤˣ)
    {f φ : H2 L} (hfφ : (f, φ) ∈ LuGraph L κ u σ) :
    (mulU (unitDiag_ab a b) f, (1 : ℂ) • mulU (unitDiag_ab a b) φ +
        ((2 * b : ℝ) : ℂ) • mulU (unitDiag_ab a b) f) ∈ LuGraph L κ (upb a b u) (σ * τ) := by
  obtain ⟨g, h, hrep, hbc, hφ⟩ := hfφ
  refine ⟨fun x => dmat (af a b) (bf a b) x (g x),
    fun x => dmat (af a b) (bf a b) x (h x) +
      dmat (fun y => -(Complex.I * (b : ℂ)) * af a b y) (fun y => (Complex.I * (b : ℂ)) * bf a b y) x (g x),
    ?_, ?_, ?_⟩
  · exact isH1Rep_mul hL hrep (unitDiag_ab a b) (hasDerivAt_af a b) (hasDerivAt_bf a b)
      (continuous_af_deriv a b) (continuous_bf_deriv a b)
  · simp only
    rw [hbc, dmat_smul, dmat_L a b τ hτ, smul_smul, Units.val_mul, Int.cast_mul, mul_comm]
  · simp only
    filter_upwards [Lp.coeFn_add ((1 : ℂ) • mulU (unitDiag_ab a b) φ) (((2 * b : ℝ) : ℂ) • mulU (unitDiag_ab a b) f),
      Lp.coeFn_smul (1 : ℂ) (mulU (unitDiag_ab a b) φ),
      Lp.coeFn_smul (((2 * b : ℝ) : ℂ)) (mulU (unitDiag_ab a b) f),
      mulU_ae (unitDiag_ab a b) φ, mulU_ae (unitDiag_ab a b) f, hφ, hrep.1] with x h1 h2 h3 h4 h5 h6 h7
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, h4, h5, h6, h7]
    unfold upb
    rw [lopPt_dmat a b x (u x) (h x) (g x)]
    simp

theorem hτ_neg (b : ℝ) (τ : ℤˣ)
    (hτ : Complex.exp (((b * L : ℝ) : ℂ) * Complex.I) = ((τ : ℤ) : ℂ)) :
    Complex.exp ((((-b) * L : ℝ) : ℂ) * Complex.I) = ((τ : ℤ) : ℂ) := by
  have e : Complex.exp ((((-b) * L : ℝ) : ℂ) * Complex.I) =
      (Complex.exp (((b * L : ℝ) : ℂ) * Complex.I))⁻¹ := by
    rw [← Complex.exp_neg]; congr 1; push_cast; ring
  rw [e, hτ]
  rcases Int.units_eq_one_or τ with rfl | rfl <;> simp

/-- **Intertwining of the graphs** for the unit diagonal multiplier `e^{∓i(a+bx)}`. -/
theorem inter_ab (hL : 0 < L) (a b : ℝ) (τ : ℤˣ)
    (hτ : Complex.exp (((b * L : ℝ) : ℂ) * Complex.I) = ((τ : ℤ) : ℂ)) (u : ℝ → ℂ) (σ : ℤˣ) :
    Inter (LuGraph L κ u σ) (LuGraph L κ (upb a b u) (σ * τ)) (mulU (unitDiag_ab a b)) 1
      ((2 * b : ℝ) : ℂ) := by
  refine ⟨one_mul 1, fun f φ => ⟨fwd hL a b τ hτ u σ, fun h' => ?_⟩, fun f φ h => by simpa using h⟩
  have h2 := fwd hL (-a) (-b) τ (hτ_neg b τ hτ) (upb a b u) (σ * τ) h'
  rw [mulU_mulU_neg, map_add, map_smul, map_smul, mulU_mulU_neg, mulU_mulU_neg, upb_neg,
    mul_assoc, Int.units_mul_self, mul_one] at h2
  convert h2 using 2
  rw [one_smul, one_smul]
  have : ((2 * (-b) : ℝ) : ℂ) = -((2 * b : ℝ) : ℂ) := by push_cast; ring
  rw [this, neg_smul]
  abel

/-- Constant unit diagonal matrix as a linear isometric equivalence of `ℂ²`. -/
def diagLI (α β : ℝ → ℂ) (h : UnitDiag α β) (x : ℝ) : E2 ≃ₗᵢ[ℂ] E2 :=
  LinearIsometryEquiv.ofSurjective
    { toFun := dmat α β x
      map_add' := dmat_add α β x
      map_smul' := dmat_smul α β x
      norm_map' := norm_dmat (h.na x) (h.nb x) }
    (fun w => ⟨dmat (fun y => starRingEnd ℂ (α y)) (fun y => starRingEnd ℂ (β y)) x w,
      dmat_dmat (α := fun y => starRingEnd ℂ (α y)) (β := fun y => starRingEnd ℂ (β y)) (α₂ := α)
        (β₂ := β) (x := x) (by rw [mul_comm]; exact UnitDiag.conj_mul (h.na x))
        (by rw [mul_comm]; exact UnitDiag.conj_mul (h.nb x)) w⟩)

theorem diagLI_apply (α β : ℝ → ℂ) (h : UnitDiag α β) (x : ℝ) (v : E2) :
    diagLI α β h x v = dmat α β x v := rfl

theorem pm_add (L : ℝ) (n k : ℤ) : pm L (n + k) = pm L n + pm L k := by
  unfold pm; push_cast; ring

theorem pm_cast_add (L : ℝ) (n k : ℤ) : (pm L (n + k) : ℂ) = (pm L n : ℂ) + (pm L k : ℂ) := by
  rw [pm_add]; push_cast; ring

theorem exp_id0 (a : ℝ) (k n : ℤ) (x : ℝ) :
    af a (pm L k / 2) x * Complex.exp (rate L n 0 * (x : ℂ)) =
      af a 0 0 * Complex.exp (rate L (n + k) 0 * (x : ℂ)) := by
  unfold af rate sgn
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [if_true]
  push_cast
  rw [pm_cast_add]
  ring

theorem exp_id1 (a : ℝ) (k n : ℤ) (x : ℝ) :
    bf a (pm L k / 2) x * Complex.exp (rate L n 1 * (x : ℂ)) =
      bf a 0 0 * Complex.exp (rate L (n + k) 1 * (x : ℂ)) := by
  unfold bf rate sgn
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [one_ne_zero, if_false]
  push_cast
  rw [pm_cast_add]
  ring

/-- `W χ_{n,j} = e^{∓ia} χ_{n+k,j}`. -/
theorem mulU_chi (a : ℝ) (k n : ℤ) (j : Fin 2) :
    mulU (unitDiag_ab a (pm L k / 2)) (chi L n j) =
      (if j = 0 then af a 0 0 else bf a 0 0) • chi L (n + k) j := by
  apply Lp.ext
  filter_upwards [mulU_ae (unitDiag_ab a (pm L k / 2)) (chi L n j), (memLp_chiFun L n j).coeFn_toLp,
    Lp.coeFn_smul (if j = 0 then af a 0 0 else bf a 0 0) (chi L (n + k) j),
    (memLp_chiFun L (n + k) j).coeFn_toLp] with x h1 h2 h3 h4
  rw [h1, h3, Pi.smul_apply]
  have e2 : (chi L n j : ℝ → E2) x = chiFun L n j x := h2
  have e4 : (chi L (n + k) j : ℝ → E2) x = chiFun L (n + k) j x := h4
  rw [e2, e4]
  fin_cases j
  · ext i
    fin_cases i
    · simp [dmat_eq, chiFun, vec2, EuclideanSpace.single_apply]
      rw [mul_left_comm, exp_id0, mul_left_comm]
    · simp [dmat_eq, chiFun, vec2, EuclideanSpace.single_apply]
  · ext i
    fin_cases i
    · simp [dmat_eq, chiFun, vec2, EuclideanSpace.single_apply]
    · simp [dmat_eq, chiFun, vec2, EuclideanSpace.single_apply]
      rw [mul_left_comm, exp_id1, mul_left_comm]

/-- The diagonal unit matrix `M = diag(e^{-ia}, e^{ia})`. -/
def Mdiag (a : ℝ) : E2 ≃ₗᵢ[ℂ] E2 := diagLI (af a 0) (bf a 0) (unitDiag_ab a 0) 0

theorem Mdiag_apply (a : ℝ) (v : E2) : Mdiag a v = vec2 (af a 0 0 * v 0) (bf a 0 0 * v 1) :=
  dmat_eq _ _ 0 v

theorem doublet_rel (a : ℝ) (k n : ℤ) :
    QuantumNLS.Local020Core.DoubletRel (L := L) (mulU (unitDiag_ab a (pm L k / 2))) (Mdiag a) n (n + k) := by
  unfold QuantumNLS.Local020Core.DoubletRel
  ext v : 1
  simp only [ContinuousLinearMap.comp_apply, ic_apply]
  rw [embed_apply, embed_apply, map_add, map_smul, map_smul, mulU_chi, mulU_chi, Mdiag_apply]
  simp only [vec2_zero, vec2_one, if_true, one_ne_zero, if_false, smul_smul]
  rw [mul_comm (v 0), mul_comm (v 1)]

theorem parity_add (n k : ℤ) : parity (n + k) = parity n * parity k := by
  unfold parity
  by_cases hn : Even n <;> by_cases hk : Even k <;> simp [hn, hk, Int.even_add]

/-- **S2/S3.**  `SmallCompression` is invariant and the lower-left entry of the polar-normalized reduced matrix at
`n + k` for the potential `e^{2i(a + p_k x/2)} u` is `e^{2ia}` times the entry at `n` for `u`. -/
theorem phaseBoost_reduced (hL : 0 < L) (a : ℝ) (k n : ℤ) (r : ℝ) (u : ℝ → ℂ) :
    (SmallCompression L κ (upb a (pm L k / 2) u) (n + k) r ↔ SmallCompression L κ u n r) ∧
    ∀ (h' : SmallCompression L κ (upb a (pm L k / 2) u) (n + k) r) (hh : SmallCompression L κ u n r),
      QuantumNLS.Local020Entry.bentry (reducedMatrix2 L κ (upb a (pm L k / 2) u) (n + k) r h') =
        Complex.exp (((2 * a : ℝ) : ℂ) * Complex.I) *
          QuantumNLS.Local020Entry.bentry (reducedMatrix2 L κ u n r hh) := by
  have hτ : Complex.exp ((((pm L k / 2) * L : ℝ) : ℂ) * Complex.I) = (((parity k : ℤˣ) : ℤ) : ℂ) := by
    have : (((pm L k / 2) * L : ℝ) : ℂ) * Complex.I = (k : ℂ) * (Real.pi * Complex.I) := by
      unfold pm
      have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      push_cast
      field_simp
    rw [this]; exact cexp_int_pi k
  have h := inter_ab (κ := κ) hL a (pm L k / 2) (parity k) hτ u (parity n)
  rw [← parity_add] at h
  have hn : center L (n + k) = ((2 * (pm L k / 2) : ℝ) : ℂ) + 1 * center L n := by
    unfold QuantumNLS.LocalSpectral.center; rw [pm_cast_add]; push_cast; ring
  obtain ⟨hs, hr⟩ := QuantumNLS.Local020Core.reduced_transport (κ := κ) r h (Or.inl rfl) hn
    (doublet_rel a k n)
  refine ⟨hs, fun h' hh => ?_⟩
  have hB := hr h' hh
  have hc := QuantumNLS.Local020Entry.bentry_transport (Mdiag a) (af a 0 0) (bf a 0 0) (Mdiag_apply a)
    (UnitDiag.conj_mul ((unitDiag_ab a 0).na 0)) 1 _ _ hB
  rw [hc, one_mul]
  congr 1
  have h1 : starRingEnd ℂ (af a 0 0) = bf a 0 0 := by
    rw [← conj_bf a 0 0, Complex.conj_conj]
  rw [h1]
  unfold bf
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end QuantumNLS.Local020Mul2

#print axioms QuantumNLS.Local020Mul2.phaseBoost_reduced
#print axioms QuantumNLS.Local020Mul2.inter_ab
