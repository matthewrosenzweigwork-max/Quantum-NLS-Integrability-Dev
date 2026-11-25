import Mathlib
import QuantumNLS.SpatialTransfer
import QuantumNLS.PhysicalTensor

/-!
# DEF-049: local two-component spectral operator and parity domain

Source: `DEFINITIONS_LEDGER.md:1201` (DEF-049); canonical occurrence `chapters/local/spectral_reduction.tex`,
`sec:local-spectral`.  Ledger text: on `L²(0,L;ℂ²)` use `D_σ = {f ∈ H¹ : f(L) = σ f(0)}`, `σ = ±1`, and
`𝓛_u = 2i diag(1,−1) ∂_x + [[0, −2i√κ ū],[2i√κ u, 0]]`; at the free value `2πn/L` the parity is `(−1)^n`;
Riesz projections and their normalized rank-two compressions are defined by the contours and inverse square root of
the section; their common radius and analyticity are theorem conclusions (not claimed here).

## Encoding
* `H2 L = Lp (EuclideanSpace ℂ (Fin 2)) 2 (volume.restrict (Ioc 0 L))` (`L²(0,L;ℂ²)`).
* **`H¹` on an interval** is encoded as absolutely continuous functions with `L²` derivative
  (`IsH1Rep`: `f = g` a.e., `h ∈ L²`, `g(x) = g(0) + ∫₀ˣ h` on `[0,L]`), i.e. `W^{1,2}(0,L)`; `domain L σ` imposes
  `g(L) = σ g(0)`.
* The operator `𝓛_u` on `D_σ` is given by its **graph** `LuGraph L κ u σ ⊆ H × H`: `(f, φ)` with `f ∈ D_σ` and
  `φ = 2iJ h + V_u g` a.e. (`lopPt`), `u : ℝ → ℂ` an `L²(0,L)` representative (the DEF-001 profile enters as
  `circleRep u`, `x ↦ u(x mod L)`).  This avoids constructing `V_u f ∈ L²` as an element before it is needed.
* Resolvents are bounded operators `R` with `R φ ∈ D_σ`, `(z − 𝓛_u) R φ = φ` and `R(z − 𝓛_u) f = f` (`IsResolvent`,
  unique by `IsResolvent.unique`); `resolvent` picks it, junk value `0` outside the resolvent set.

## Proved (all `u = 0` and algebraic facts; no analytic conclusion is claimed)
* **Binding to DEF-013**: `coef_mulVec` records the entries of `SpatialTransfer.balCoef` and `lopPt_of_spatial`:
  if `g' = A g` with `A = [[−iz/2, √κ ū],[√κ u, iz/2]]` then `2iJ g' + V g = z g`.
* **Free eigenfunctions and parity**: `chi L m j = L^{-1/2} e^{±ip_m x/2} e_j`, `p_m = 2πm/L`.
  `chi_mem_domain`: `χ_{m,j} ∈ D_{(−1)^m}` (`parity m = (−1)^m`); `parity_unique`: on `χ_{m,j}` the boundary condition
  `g(L) = σ' g(0)`, `σ' = ±1`, holds only for `σ' = (−1)^m`; `free_eigen`: `𝓛_0 χ_{m,j} = p_m χ_{m,j}` on `D_{(−1)^m}`.
* Not proved: that the `χ_{m,j}` (`m ≡ parity`) form an orthonormal basis of `H_σ` (stated in the source section).

## Defined, exactly as the section gives them (no claim about well-posedness)
`rieszProj` (`P_n(u) = (2πi)⁻¹ ∮_{|z−p_n|=r} (z − 𝓛_u)⁻¹ dz`), `freeProj`, `perturbedProj`, `invSqrt` (power series
`∑ binom(−1/2,k)(T−1)^k`, `invSqrtCoeff`), `embed` (ordered basis `(χ_{n,1},χ_{n,2})`), `compression`
(`P P_n(u) P`), `normalizedIsometry` (`U_n = P_n(u) P [P P_n(u) P]^{-1/2}`), `dressedIntegral`, `reducedMatrix`
(`B_n = p_n 1 + U_n^*((2πi)⁻¹∮(z−p_n)(z−𝓛_u)⁻¹dz)U_n`).  The contour radius `ContourRadius L r` (`0 < r < 2π/L = d/2`)
and the potential ball `PotentialBall L` (radius `ρ`, `‖u‖ < ρ` in `PotentialBall.Contains`) are explicit parameters.
Summability of the series, the rank-two property, self-adjointness, the common radius and analyticity are theorem
conclusions of the source and are **not** claimed.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set ComplexConjugate
open scoped ENNReal InnerProductSpace

set_option autoImplicit false
noncomputable section

namespace QuantumNLS.LocalSpectral

/-- `ℂ²` with its Hilbert structure. -/
abbrev E2 := EuclideanSpace ℂ (Fin 2)

/-- The interval measure on `(0, L]`. -/
def μI (L : ℝ) : Measure ℝ := volume.restrict (Ioc 0 L)

instance (L : ℝ) : IsFiniteMeasure (μI L) := by unfold μI; infer_instance

/-- **`H_σ = L²(0, L; ℂ²)`.** -/
abbrev H2 (L : ℝ) := Lp E2 2 (μI L)

/-- The vector `(a, b) ∈ ℂ²`. -/
def vec2 (a b : ℂ) : E2 := WithLp.toLp 2 ![a, b]

@[simp] lemma vec2_zero (a b : ℂ) : (vec2 a b) 0 = a := rfl
@[simp] lemma vec2_one (a b : ℂ) : (vec2 a b) 1 = b := rfl

/-- `J = diag(1, −1)`. -/
def Jm (v : E2) : E2 := vec2 (v 0) (-v 1)

/-- Pointwise action of `𝓛_u = 2iJ∂_x + V_u`: `lopPt κ w d g = 2iJ d + V g`, with
`V = [[0, −2i√κ w̄],[2i√κ w, 0]]`, `d = ∂_x g`, `w = u(x)`. -/
def lopPt (κ : ℝ) (w : ℂ) (d g : E2) : E2 :=
  (2 * Complex.I) • Jm d +
    vec2 (-(2 * Complex.I) * (Real.sqrt κ : ℂ) * conj w * g 1) ((2 * Complex.I) * (Real.sqrt κ : ℂ) * w * g 0)

/-- `f` has the `H¹` representative `g` with derivative `h`: `f = g` a.e., `h ∈ L²`, and `g(x) = g(0) + ∫₀ˣ h`
on `[0, L]` (absolutely continuous with `L²` derivative = `W^{1,2}(0,L)`). -/
def IsH1Rep (L : ℝ) (f : H2 L) (g h : ℝ → E2) : Prop :=
  (f : ℝ → E2) =ᵐ[μI L] g ∧ MemLp h 2 (μI L) ∧ ∀ x ∈ Icc 0 L, g x = g 0 + ∫ s in (0 : ℝ)..x, h s

/-- **`D_σ = {f ∈ H¹ : f(L) = σ f(0)}`** (`σ = ±1`, as a unit of `ℤ`). -/
def domain (L : ℝ) (σ : ℤˣ) : Set (H2 L) :=
  {f | ∃ g h, IsH1Rep L f g h ∧ g L = (((σ : ℤ) : ℂ)) • g 0}

/-- **The operator `𝓛_u` on `D_σ`, as its graph**: `(f, φ)` with `f ∈ D_σ` and `φ = 2iJ f' + V_u f` a.e.
(`u` an `L²(0,L)` representative of the potential). -/
def LuGraph (L κ : ℝ) (u : ℝ → ℂ) (σ : ℤˣ) : Set (H2 L × H2 L) :=
  {p | ∃ g h, IsH1Rep L p.1 g h ∧ g L = (((σ : ℤ) : ℂ)) • g 0 ∧
    (p.2 : ℝ → E2) =ᵐ[μI L] fun x => lopPt κ (u x) (h x) (g x)}

/-- **Binding to DEF-013.**  If `g' = A g` with `A` the balanced spatial coefficient matrix
`[[−iz/2, √κ ū],[√κ u, iz/2]]` of `SpatialTransfer.balCoef` (entries recorded by `coef_mulVec`), then
`𝓛_u g = z g`: "direct multiplication of the spatial equation by `2iJ`". -/
theorem lopPt_of_spatial (κ : ℝ) (z w f0 f1 d0 d1 : ℂ)
    (h0 : d0 = -(Complex.I * z) / 2 * f0 + (Real.sqrt κ : ℂ) * conj w * f1)
    (h1 : d1 = (Real.sqrt κ : ℂ) * w * f0 + Complex.I * z / 2 * f1) :
    lopPt κ w (vec2 d0 d1) (vec2 f0 f1) = z • vec2 f0 f1 := by
  unfold lopPt Jm
  ext i
  fin_cases i
  · simp [h0]; linear_combination (-(z * f0)) * Complex.I_sq
  · simp [h1]; linear_combination (-(z * f1)) * Complex.I_sq

/-- The spatial matrix of DEF-013 applied to `(f0, f1)` has exactly the entries used above. -/
theorem coef_mulVec (κ : ℝ) (u : ℝ → ℂ) (z f0 f1 : ℂ) (x : ℝ) :
    (QuantumNLS.SpatialTransfer.balCoef κ u z x).mulVec ![f0, f1] =
      ![-(Complex.I * z) / 2 * f0 + (Real.sqrt κ : ℂ) * conj (u x) * f1,
        (Real.sqrt κ : ℂ) * u x * f0 + Complex.I * z / 2 * f1] := by
  ext i
  fin_cases i <;>
    simp [QuantumNLS.SpatialTransfer.balCoef, QuantumNLS.SpatialTransfer.coef, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]


/-! ### Free eigenfunctions and parity -/

section Free

/-- `p_m = 2π m / L`. -/
def pm (L : ℝ) (m : ℤ) : ℝ := 2 * Real.pi * m / L

/-- The parity `σ = (−1)^m ∈ ℤˣ`. -/
def parity (m : ℤ) : ℤˣ := if Even m then 1 else -1

/-- The sign in the exponent: `χ_{m,1}` carries `e^{−ip_m x/2}`, `χ_{m,2}` carries `e^{+ip_m x/2}`. -/
def sgn (j : Fin 2) : ℝ := if j = 0 then -1 else 1

/-- The exponent rate `b = sgn(j) · i p_m / 2`. -/
def rate (L : ℝ) (m : ℤ) (j : Fin 2) : ℂ := (sgn j : ℂ) * Complex.I * (pm L m : ℂ) / 2

/-- The free eigenfunction representative `χ_{m,j}(x) = L^{-1/2} e^{sgn(j) i p_m x / 2} e_j`. -/
def chiFun (L : ℝ) (m : ℤ) (j : Fin 2) (x : ℝ) : E2 :=
  (((Real.sqrt L)⁻¹ : ℝ) * Complex.exp (rate L m j * (x : ℂ))) • EuclideanSpace.single j (1 : ℂ)

/-- Its derivative `∂_x χ_{m,j} = b χ_{m,j}`. -/
def dchiFun (L : ℝ) (m : ℤ) (j : Fin 2) (x : ℝ) : E2 := rate L m j • chiFun L m j x

theorem continuous_chiFun (L : ℝ) (m : ℤ) (j : Fin 2) : Continuous (chiFun L m j) := by
  unfold chiFun; fun_prop

theorem norm_chiFun (L : ℝ) (m : ℤ) (j : Fin 2) (x : ℝ) :
    ‖chiFun L m j x‖ = (Real.sqrt L)⁻¹ := by
  unfold chiFun rate
  rw [norm_smul, PiLp.norm_single, norm_one, mul_one, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  have : ‖Complex.exp ((sgn j : ℂ) * Complex.I * (pm L m : ℂ) / 2 * (x : ℂ))‖ = 1 := by
    have h : (sgn j : ℂ) * Complex.I * (pm L m : ℂ) / 2 * (x : ℂ) =
        (((sgn j * pm L m / 2 * x : ℝ)) : ℂ) * Complex.I := by push_cast; ring
    rw [h]; exact Complex.norm_exp_ofReal_mul_I _
  rw [this, mul_one]

theorem memLp_chiFun (L : ℝ) (m : ℤ) (j : Fin 2) : MemLp (chiFun L m j) 2 (μI L) :=
  MemLp.of_bound (continuous_chiFun L m j).aestronglyMeasurable _
    (Filter.Eventually.of_forall fun x => (norm_chiFun L m j x).le)

theorem continuous_dchiFun (L : ℝ) (m : ℤ) (j : Fin 2) : Continuous (dchiFun L m j) := by
  unfold dchiFun; have := continuous_chiFun L m j; fun_prop

theorem memLp_dchiFun (L : ℝ) (m : ℤ) (j : Fin 2) : MemLp (dchiFun L m j) 2 (μI L) :=
  MemLp.of_bound (continuous_dchiFun L m j).aestronglyMeasurable (‖rate L m j‖ * (Real.sqrt L)⁻¹)
    (Filter.Eventually.of_forall fun x => by
      unfold dchiFun; rw [norm_smul, norm_chiFun])

/-- The free eigenfunction `χ_{m,j} ∈ H_σ`. -/
def chi (L : ℝ) (m : ℤ) (j : Fin 2) : H2 L := (memLp_chiFun L m j).toLp (chiFun L m j)

theorem hasDerivAt_chiFun (L : ℝ) (m : ℤ) (j : Fin 2) (x : ℝ) :
    HasDerivAt (chiFun L m j) (dchiFun L m j x) x := by
  have h1 : HasDerivAt (fun y : ℝ => (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Complex.exp (rate L m j * (y : ℂ)))
      ((((Real.sqrt L)⁻¹ : ℝ) : ℂ) * (Complex.exp (rate L m j * (x : ℂ)) * (rate L m j * 1))) x :=
    ((((hasDerivAt_id x).ofReal_comp).const_mul (rate L m j)).cexp).const_mul _
  have h2 := h1.smul_const (EuclideanSpace.single j (1 : ℂ))
  refine h2.congr_deriv ?_
  unfold dchiFun chiFun
  rw [smul_smul]; congr 1; ring


theorem cexp_int_pi (m : ℤ) : Complex.exp ((m : ℂ) * (Real.pi * Complex.I)) = (((parity m : ℤˣ) : ℤ) : ℂ) := by
  rcases Int.even_or_odd' m with ⟨k, rfl | rfl⟩
  · have h : (((2 * k : ℤ) : ℂ)) * (Real.pi * Complex.I) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
    simp [parity]
  · have h : (((2 * k + 1 : ℤ) : ℂ)) * (Real.pi * Complex.I) =
        (k : ℂ) * (2 * Real.pi * Complex.I) + Real.pi * Complex.I := by
      push_cast; ring
    rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I]
    have : ¬ Even (2 * k + 1) := Int.not_even_two_mul_add_one k
    simp [parity, this]

theorem cexp_rate_L {L : ℝ} (hL : L ≠ 0) (m : ℤ) (j : Fin 2) :
    Complex.exp (rate L m j * (L : ℂ)) = (((parity m : ℤˣ) : ℤ) : ℂ) := by
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  have h : rate L m j * (L : ℂ) = ((sgn j : ℝ) : ℂ) * ((m : ℂ) * (Real.pi * Complex.I)) := by
    unfold rate pm; push_cast; field_simp
  rw [h]
  unfold sgn
  split_ifs
  · have := cexp_int_pi (-m)
    rw [show (((-1 : ℝ)) : ℂ) * ((m : ℂ) * (Real.pi * Complex.I)) = ((-m : ℤ) : ℂ) * (Real.pi * Complex.I) by
      push_cast; ring, this]
    simp [parity]
  · rw [show (((1 : ℝ)) : ℂ) * ((m : ℂ) * (Real.pi * Complex.I)) = (m : ℂ) * (Real.pi * Complex.I) by
      push_cast; ring, cexp_int_pi]

theorem chiFun_at_L {L : ℝ} (hL : L ≠ 0) (m : ℤ) (j : Fin 2) :
    chiFun L m j L = (((parity m : ℤˣ) : ℤ) : ℂ) • chiFun L m j 0 := by
  unfold chiFun
  rw [cexp_rate_L hL, smul_smul]
  simp
  ring_nf

/-- **The free eigenfunction `χ_{m,j}` lies in `D_{(−1)^m}`** (the parity of the free value `p_m = 2πm/L`). -/
theorem chi_mem_domain {L : ℝ} (hL : 0 < L) (m : ℤ) (j : Fin 2) : chi L m j ∈ domain L (parity m) := by
  refine ⟨chiFun L m j, dchiFun L m j, ⟨?_, memLp_dchiFun L m j, fun x _ => ?_⟩, chiFun_at_L hL.ne' m j⟩
  · exact (memLp_chiFun L m j).coeFn_toLp
  · have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := x)
      (fun y _ => hasDerivAt_chiFun L m j y) ((continuous_dchiFun L m j).intervalIntegrable _ _)
    rw [this]; abel

/-- **Parity is exactly `(−1)^m`**: on the free eigenfunction, the boundary condition `g(L) = σ' g(0)` with
`σ' = ±1` holds only for `σ' = (−1)^m`. -/
theorem parity_unique {L : ℝ} (hL : 0 < L) (m : ℤ) (j : Fin 2) (σ' : ℤˣ)
    (h : chiFun L m j L = (((σ' : ℤˣ) : ℤ) : ℂ) • chiFun L m j 0) : σ' = parity m := by
  rw [chiFun_at_L hL.ne'] at h
  have h0 : chiFun L m j 0 ≠ 0 := by
    intro h0
    have := norm_chiFun L m j 0
    rw [h0, norm_zero] at this
    have hpos : 0 < (Real.sqrt L)⁻¹ := by positivity
    linarith
  have h2 : ((((parity m : ℤˣ) : ℤ) : ℂ) - (((σ' : ℤˣ) : ℤ) : ℂ)) • chiFun L m j 0 = 0 := by
    rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · have : (((parity m : ℤˣ) : ℤ) : ℂ) = (((σ' : ℤˣ) : ℤ) : ℂ) := sub_eq_zero.mp h3
    exact (Units.ext (Int.cast_injective this)).symm
  · exact absurd h3 h0

theorem lopPt_free (L κ : ℝ) (m : ℤ) (j : Fin 2) (x : ℝ) :
    lopPt κ 0 (dchiFun L m j x) (chiFun L m j x) = (pm L m : ℂ) • chiFun L m j x := by
  unfold lopPt Jm dchiFun chiFun rate sgn
  fin_cases j <;> ext i <;> fin_cases i <;>
    simp [vec2, EuclideanSpace.single_apply] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

/-- **Free eigenfunctions and eigenvalues on `D_σ`**: with `σ = (−1)^m`, `(χ_{m,j}, p_m χ_{m,j})` lies in the
graph of `𝓛_0` on `D_σ`, i.e. `𝓛_0 χ_{m,j} = p_m χ_{m,j}`. -/
theorem free_eigen {L : ℝ} (hL : 0 < L) (κ : ℝ) (m : ℤ) (j : Fin 2) :
    (chi L m j, (pm L m : ℂ) • chi L m j) ∈ LuGraph L κ (fun _ => 0) (parity m) := by
  refine ⟨chiFun L m j, dchiFun L m j, ⟨(memLp_chiFun L m j).coeFn_toLp, memLp_dchiFun L m j,
    fun x _ => ?_⟩, chiFun_at_L hL.ne' m j, ?_⟩
  · have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := x)
      (fun y _ => hasDerivAt_chiFun L m j y) ((continuous_dchiFun L m j).intervalIntegrable _ _)
    rw [this]; abel
  · filter_upwards [Lp.coeFn_smul (pm L m : ℂ) (chi L m j), (memLp_chiFun L m j).coeFn_toLp] with x h1 h2
    show ((pm L m : ℂ) • chi L m j : H2 L) x = _
    rw [h1, Pi.smul_apply, show (chi L m j : ℝ → E2) x = chiFun L m j x from h2, lopPt_free]

end Free


/-! ### Resolvent, Riesz projections and the normalized rank-two compression -/

section Riesz

variable (L κ : ℝ)

/-- `R` is the resolvent `(z − 𝓛_u)⁻¹` of `𝓛_u` on `D_σ`: `R φ ∈ D_σ` solves `(z − 𝓛_u) R φ = φ`, and
`R (z − 𝓛_u) f = f` on `D_σ`. -/
def IsResolvent (u : ℝ → ℂ) (σ : ℤˣ) (z : ℂ) (R : H2 L →L[ℂ] H2 L) : Prop :=
  (∀ φ, (R φ, z • R φ - φ) ∈ LuGraph L κ u σ) ∧
    ∀ p ∈ LuGraph L κ u σ, R (z • p.1 - p.2) = p.1

variable {L κ}

/-- The resolvent, when it exists, is unique. -/
theorem IsResolvent.unique {u : ℝ → ℂ} {σ : ℤˣ} {z : ℂ} {R R' : H2 L →L[ℂ] H2 L}
    (h : IsResolvent L κ u σ z R) (h' : IsResolvent L κ u σ z R') : R = R' := by
  ext φ : 1
  have := h.2 (R' φ, z • R' φ - φ) (h'.1 φ)
  simpa using this

variable (L κ)

open Classical in
/-- `(z − 𝓛_u)⁻¹` on `H_σ` (junk value `0` where `z` is not in the resolvent set). -/
def resolvent (u : ℝ → ℂ) (σ : ℤˣ) (z : ℂ) : H2 L →L[ℂ] H2 L :=
  if h : ∃ R, IsResolvent L κ u σ z R then h.choose else 0

/-- The free value `p_n = 2πn/L` as a complex number (the centre of the contour `Γ_n`). -/
def center (n : ℤ) : ℂ := (pm L n : ℂ)

/-- **Riesz projection** `P_n(u) = (2πi)⁻¹ ∮_{|z−p_n|=r} (z − 𝓛_u)⁻¹ dz` on `D_σ`. -/
def rieszProj (u : ℝ → ℂ) (σ : ℤˣ) (n : ℤ) (r : ℝ) : H2 L →L[ℂ] H2 L :=
  ((2 * Real.pi * Complex.I)⁻¹ : ℂ) • circleIntegral (fun z => resolvent L κ u σ z) (center L n) r

/-- The free projection `P = P_n(0)` in parity `(−1)^n`. -/
def freeProj (n : ℤ) (r : ℝ) : H2 L →L[ℂ] H2 L := rieszProj L κ (fun _ => 0) (parity n) n r

/-- The perturbed projection `P_n(u)` in parity `(−1)^n`. -/
def perturbedProj (u : ℝ → ℂ) (n : ℤ) (r : ℝ) : H2 L →L[ℂ] H2 L := rieszProj L κ u (parity n) n r

/-- Coefficients of the power series of `(1 + x)^{-1/2}`: `binom(−1/2, k)`. -/
def invSqrtCoeff (k : ℕ) : ℝ := (∏ i ∈ Finset.range k, (-(1 / 2 : ℝ) - i)) / (Nat.factorial k : ℝ)

/-- The inverse square root `T^{-1/2} = ∑_k binom(−1/2,k) (T − 1)^k`, defined by its power series about the
identity (as in the source; summability is a theorem of the source, not assumed here). -/
def invSqrt (T : H2 L →L[ℂ] H2 L) : H2 L →L[ℂ] H2 L :=
  ∑' k : ℕ, (invSqrtCoeff k : ℂ) • (T - 1) ^ k

/-- The ordered basis `(χ_{n,1}, χ_{n,2})` of `P H_{(−1)^n}`, as the embedding `ℂ² → H_σ`. -/
def embed (n : ℤ) : E2 →L[ℂ] H2 L :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => v 0 • chi L n 0 + v 1 • chi L n 1
      map_add' := fun v w => by simp [add_smul]; abel
      map_smul' := fun c v => by simp [smul_add, smul_smul] }

/-- The compression `P P_n(u) P`. -/
def compression (u : ℝ → ℂ) (n : ℤ) (r : ℝ) : H2 L →L[ℂ] H2 L :=
  freeProj L κ n r * perturbedProj L κ u n r * freeProj L κ n r

/-- **The normalized isometry** `U_n = P_n(u) P [P P_n(u) P]^{-1/2} : ℂ² → H_σ` (basis-identified). -/
def normalizedIsometry (u : ℝ → ℂ) (n : ℤ) (r : ℝ) : E2 →L[ℂ] H2 L :=
  (perturbedProj L κ u n r * freeProj L κ n r * invSqrt L (compression L κ u n r)).comp (embed L n)

/-- `(2πi)⁻¹ ∮ (z − p_n)(z − 𝓛_u)⁻¹ dz`. -/
def dressedIntegral (u : ℝ → ℂ) (n : ℤ) (r : ℝ) : H2 L →L[ℂ] H2 L :=
  ((2 * Real.pi * Complex.I)⁻¹ : ℂ) •
    circleIntegral (fun z => (z - center L n) • resolvent L κ u (parity n) z) (center L n) r

/-- **The reduced matrix** `B_n = p_n 1 + U_n^* ((2πi)⁻¹ ∮ (z − p_n)(z − 𝓛_u)⁻¹ dz) U_n : ℂ² → ℂ²`. -/
def reducedMatrix (u : ℝ → ℂ) (n : ℤ) (r : ℝ) : E2 →L[ℂ] E2 :=
  (pm L n : ℂ) • ContinuousLinearMap.id ℂ E2 +
    (ContinuousLinearMap.adjoint (normalizedIsometry L κ u n r)) ∘L (dressedIntegral L κ u n r) ∘L
      (normalizedIsometry L κ u n r)

end Riesz

/-! ### Potential ball and contour radius (explicit parameters) -/

/-- The contour radius `0 < r < d/2 = 2π/L` of `Γ_n` (`d = 4π/L` is the spacing of the free eigenvalues). -/
structure ContourRadius (L r : ℝ) : Prop where
  pos : 0 < r
  lt : r < 2 * Real.pi / L

/-- The potential ball `‖u‖₂ < ρ`: its radius `ρ` is an explicit parameter (the source's common radius is a
theorem conclusion, not asserted here). -/
structure PotentialBall (L : ℝ) where
  ρ : ℝ
  pos : 0 < ρ

open QuantumNLS.PhysicalTensor in
/-- `u ∈ L²(𝕋_L)` lies in the potential ball. -/
def PotentialBall.Contains {L : ℝ} [Fact (0 < L)] (B : PotentialBall L) (u : L2T L) : Prop := ‖u‖ < B.ρ

open QuantumNLS.PhysicalTensor in
/-- The interval representative `x ↦ u(x mod L)` of a physical profile `u ∈ L²(𝕋_L)` (DEF-001). -/
def circleRep {L : ℝ} [Fact (0 < L)] (u : L2T L) : ℝ → ℂ := fun x => (u : AddCircle L → ℂ) (x : AddCircle L)

end QuantumNLS.LocalSpectral

#print axioms QuantumNLS.LocalSpectral.lopPt_of_spatial
#print axioms QuantumNLS.LocalSpectral.coef_mulVec
#print axioms QuantumNLS.LocalSpectral.chi_mem_domain
#print axioms QuantumNLS.LocalSpectral.parity_unique
#print axioms QuantumNLS.LocalSpectral.free_eigen
#print axioms QuantumNLS.LocalSpectral.IsResolvent.unique
