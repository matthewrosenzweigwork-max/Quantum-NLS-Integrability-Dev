import NlsGge.Birkhoff.F01Determinant38
import NlsGge.Analysis.ReciprocalBracket

/-! # F01 (wave A3), file c: row/column Hilbert-Schmidt lemma and F01.01-F01.03

Plan and status: `NlsGge/Birkhoff/F01_PLAN.md`.

Part 1 (B-free): a weighted Cauchy-Schwarz estimate of the Hilbert-Schmidt energy in terms of
two `h¹ → h²` bounds (one for `A`, one for `A^*`); its concrete instance on `h⁰`.
Part 2 (conditional on `B : BirkhoffInput38`, `O : OneSmoothingInput38 B`): F01.01 (symplectic adjoint
identity and `B(x)^*`), F01.02 (`B(x)`, `B(x)^*` map `h¹ → h²` continuously in the `h¹` base point),
F01.03 (Hilbert-Schmidt continuity `x ↦ B(x) ∈ HS(h⁰)` on `h¹`).
-/

set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Analysis.RegularizedDeterminant
open scoped InnerProductSpace ENNReal

namespace NlsGge.Birkhoff

section RowCol

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {I : Type*}

theorem hasSum_inner_sq38 (b : HilbertBasis I ℝ E) (y : E) :
    HasSum (fun q => (inner ℝ (b q) y) ^ 2) (‖y‖ ^ 2) := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (b.repr y)
  simpa [HilbertBasis.repr_apply_apply, ENNReal.toReal_ofNat, Real.rpow_two] using h

theorem ofReal_norm_sq_eq_tsum38 (b : HilbertBasis I ℝ E) (y : E) :
    ENNReal.ofReal (‖y‖ ^ 2) = ∑' q, ENNReal.ofReal ((inner ℝ (b q) y) ^ 2) := by
  rw [← (hasSum_inner_sq38 b y).tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg (fun q => sq_nonneg _) (hasSum_inner_sq38 b y).summable]

variable [CompleteSpace E]

/-- Pointwise: `t² ≤ (ρ_p/ρ_q)^{-2} … ` split of a matrix entry along the row/column weights. -/
theorem entry_le38 {ρp ρq t : ℝ} (hp : 0 < ρp) (hq : 0 < ρq) :
    ENNReal.ofReal (t ^ 2) ≤
      ENNReal.ofReal (ρp⁻¹ ^ 2) * ENNReal.ofReal (ρq ^ 2 * t ^ 2) +
        ENNReal.ofReal (ρq⁻¹ ^ 2) * ENNReal.ofReal (ρp ^ 2 * t ^ 2) := by
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rcases le_total ρp ρq with h | h
  · have h1 : 1 ≤ ρp⁻¹ * ρq := by
      rw [le_inv_mul_iff₀ hp]; linarith
    have h2 : 1 ≤ (ρp⁻¹ * ρq) ^ 2 := one_le_pow₀ h1
    nlinarith [sq_nonneg t, mul_nonneg (sq_nonneg ρq⁻¹) (mul_nonneg (sq_nonneg ρp) (sq_nonneg t)),
      mul_pow ρp⁻¹ ρq 2]
  · have h1 : 1 ≤ ρq⁻¹ * ρp := by
      rw [le_inv_mul_iff₀ hq]; linarith
    have h2 : 1 ≤ (ρq⁻¹ * ρp) ^ 2 := one_le_pow₀ h1
    nlinarith [sq_nonneg t, mul_nonneg (sq_nonneg ρp⁻¹) (mul_nonneg (sq_nonneg ρq) (sq_nonneg t)),
      mul_pow ρq⁻¹ ρp 2]

/-- **Row/column bound for the Hilbert-Schmidt energy** (weighted Cauchy-Schwarz):
if the `ρ²`-weighted energy of the columns `A b_p` is at most `M1² ρ_p` and that of the columns of
`A^*` is at most `M2² ρ_p`, then `energy A ≤ (M1² + M2²) Σ ρ_p^{-1}`. -/
theorem energy_le_rowcol38 (b : HilbertBasis I ℝ E) (ρ : I → ℝ) (hρ : ∀ p, 0 < ρ p)
    (A : E →L[ℝ] E) (M1 M2 : ℝ)
    (h1 : ∀ p, ∑' q, ENNReal.ofReal (ρ q ^ 2 * (inner ℝ (b q) (A (b p))) ^ 2) ≤
      ENNReal.ofReal (M1 ^ 2 * ρ p))
    (h2 : ∀ q, ∑' p, ENNReal.ofReal (ρ p ^ 2 *
        (inner ℝ (b p) (ContinuousLinearMap.adjoint A (b q))) ^ 2) ≤
      ENNReal.ofReal (M2 ^ 2 * ρ q)) :
    energy A ≤ ENNReal.ofReal (M1 ^ 2 + M2 ^ 2) * ∑' p, ENNReal.ofReal (ρ p)⁻¹ := by
  classical
  rw [energy_eq_basis A b]
  have hnorm : ∀ p, ENNReal.ofReal (‖A (b p)‖ ^ 2) =
      ∑' q, ENNReal.ofReal ((inner ℝ (b q) (A (b p))) ^ 2) :=
    fun p => ofReal_norm_sq_eq_tsum38 b _
  simp_rw [hnorm]
  have hent : ∀ p q, ENNReal.ofReal ((inner ℝ (b q) (A (b p))) ^ 2) ≤
      ENNReal.ofReal ((ρ p)⁻¹ ^ 2) * ENNReal.ofReal (ρ q ^ 2 * (inner ℝ (b q) (A (b p))) ^ 2) +
        ENNReal.ofReal ((ρ q)⁻¹ ^ 2) * ENNReal.ofReal (ρ p ^ 2 *
          (inner ℝ (b p) (ContinuousLinearMap.adjoint A (b q))) ^ 2) := by
    intro p q
    have e : inner ℝ (b p) (ContinuousLinearMap.adjoint A (b q)) = inner ℝ (b q) (A (b p)) := by
      rw [ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
    rw [e]
    exact entry_le38 (hρ p) (hρ q)
  calc ∑' p, ∑' q, ENNReal.ofReal ((inner ℝ (b q) (A (b p))) ^ 2)
      ≤ ∑' p, ∑' q, (ENNReal.ofReal ((ρ p)⁻¹ ^ 2) *
          ENNReal.ofReal (ρ q ^ 2 * (inner ℝ (b q) (A (b p))) ^ 2) +
        ENNReal.ofReal ((ρ q)⁻¹ ^ 2) * ENNReal.ofReal (ρ p ^ 2 *
          (inner ℝ (b p) (ContinuousLinearMap.adjoint A (b q))) ^ 2)) :=
        ENNReal.tsum_le_tsum fun p => ENNReal.tsum_le_tsum fun q => hent p q
    _ = ∑' p, ∑' q, ENNReal.ofReal ((ρ p)⁻¹ ^ 2) *
          ENNReal.ofReal (ρ q ^ 2 * (inner ℝ (b q) (A (b p))) ^ 2) +
        ∑' p, ∑' q, ENNReal.ofReal ((ρ q)⁻¹ ^ 2) * ENNReal.ofReal (ρ p ^ 2 *
          (inner ℝ (b p) (ContinuousLinearMap.adjoint A (b q))) ^ 2) := by
        simp_rw [ENNReal.tsum_add]
    _ ≤ ENNReal.ofReal (M1 ^ 2) * ∑' p, ENNReal.ofReal (ρ p)⁻¹ +
        ENNReal.ofReal (M2 ^ 2) * ∑' p, ENNReal.ofReal (ρ p)⁻¹ := by
        gcongr ?_ + ?_
        · rw [← ENNReal.tsum_mul_left]
          refine ENNReal.tsum_le_tsum fun p => ?_
          rw [ENNReal.tsum_mul_left]
          calc ENNReal.ofReal ((ρ p)⁻¹ ^ 2) * ∑' q, ENNReal.ofReal (ρ q ^ 2 *
                (inner ℝ (b q) (A (b p))) ^ 2)
              ≤ ENNReal.ofReal ((ρ p)⁻¹ ^ 2) * ENNReal.ofReal (M1 ^ 2 * ρ p) :=
                mul_le_mul' le_rfl (h1 p)
            _ = ENNReal.ofReal (M1 ^ 2) * ENNReal.ofReal (ρ p)⁻¹ := by
                rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
                congr 1
                have := (hρ p).ne'
                field_simp
        · rw [← ENNReal.tsum_mul_left, ENNReal.tsum_comm]
          refine ENNReal.tsum_le_tsum fun q => ?_
          rw [ENNReal.tsum_mul_left]
          calc ENNReal.ofReal ((ρ q)⁻¹ ^ 2) * ∑' p, ENNReal.ofReal (ρ p ^ 2 *
                (inner ℝ (b p) (ContinuousLinearMap.adjoint A (b q))) ^ 2)
              ≤ ENNReal.ofReal ((ρ q)⁻¹ ^ 2) * ENNReal.ofReal (M2 ^ 2 * ρ q) :=
                mul_le_mul' le_rfl (h2 q)
            _ = ENNReal.ofReal (M2 ^ 2) * ENNReal.ofReal (ρ q)⁻¹ := by
                rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
                congr 1
                have := (hρ q).ne'
                field_simp
    _ = ENNReal.ofReal (M1 ^ 2 + M2 ^ 2) * ∑' p, ENNReal.ofReal (ρ p)⁻¹ := by
        rw [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), add_mul]

end RowCol

abbrev H0_38 : Type := SobolevCarrier38 ((0 : ℕ) : ℝ)

/-- The standard real Hilbert basis `e_{(n,j)}` of `h⁰`. -/
def bas0_38 : HilbertBasis (ℤ × Fin 2) ℝ H0_38 :=
  weightedRealHilbertBasis (sobolevModeWeight ((0 : ℕ) : ℝ))

theorem bas0_38_coe (p : ℤ × Fin 2) (n : ℤ) :
    carrierCoe38 ((0 : ℕ) : ℝ) (bas0_38 p) n =
      if n = p.1 then Complex.orthonormalBasisOneI p.2 else 0 := by
  have h := weightedRealBasisVector_apply (sobolevModeWeight ((0 : ℕ) : ℝ)) p n
  rw [sobolevModeWeight_natCast_zero] at h
  simp only [Real.sqrt_one, Complex.ofReal_one, div_one] at h
  have e : bas0_38 p = weightedRealBasisVector (sobolevModeWeight ((0 : ℕ) : ℝ)) p :=
    weightedRealHilbertBasis_apply _ p
  rw [e]
  exact h

theorem bas0_38_inner (p : ℤ × Fin 2) (y : H0_38) :
    inner ℝ (bas0_38 p) y = inner ℝ (Complex.orthonormalBasisOneI p.2) (carrierCoe38 ((0 : ℕ) : ℝ) y p.1) := by
  have h := weightedRealBasisVector_inner (sobolevModeWeight ((0 : ℕ) : ℝ)) p y
  have e : bas0_38 p = weightedRealBasisVector (sobolevModeWeight ((0 : ℕ) : ℝ)) p :=
    weightedRealHilbertBasis_apply _ p
  rw [e]
  refine h.trans ?_
  congr 1
  show (Real.sqrt (sobolevModeWeight ((0 : ℕ) : ℝ) p.1) : ℂ) * _ = _
  rw [sobolevModeWeight_natCast_zero]; simp; rfl


abbrev H1_38 : Type := SobolevCarrier38 ((1 : ℕ) : ℝ)
abbrev H2_38 : Type := SobolevCarrier38 (((1 + 1 : ℕ)) : ℝ)

/-- The inclusion `h¹ ↪ h⁰`. -/
def i10_38 : H1_38 →L[ℝ] H0_38 :=
  carrierIncl38 (by norm_num : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ))

/-- The inclusion `h² ↪ h⁰`. -/
def i20_38 : H2_38 →L[ℝ] H0_38 :=
  carrierIncl38 (by norm_num : ((0 : ℕ) : ℝ) ≤ (((1 + 1 : ℕ)) : ℝ))

/-- The inclusion `h² ↪ h¹`. -/
def i21_38 : H2_38 →L[ℝ] H1_38 :=
  carrierIncl38 (by norm_num : ((1 : ℕ) : ℝ) ≤ (((1 + 1 : ℕ)) : ℝ))

@[simp] theorem carrierCoe38_i10 (x : H1_38) (n : ℤ) :
    carrierCoe38 ((0 : ℕ) : ℝ) (i10_38 x) n = carrierCoe38 ((1 : ℕ) : ℝ) x n :=
  congrFun (carrierCoe38_incl38 _ x) n

@[simp] theorem carrierCoe38_i20 (x : H2_38) (n : ℤ) :
    carrierCoe38 ((0 : ℕ) : ℝ) (i20_38 x) n = carrierCoe38 (((1 + 1 : ℕ)) : ℝ) x n :=
  congrFun (carrierCoe38_incl38 _ x) n

@[simp] theorem carrierCoe38_i21 (x : H2_38) (n : ℤ) :
    carrierCoe38 ((1 : ℕ) : ℝ) (i21_38 x) n = carrierCoe38 (((1 + 1 : ℕ)) : ℝ) x n :=
  congrFun (carrierCoe38_incl38 _ x) n

theorem coe_i10_38' (x : H1_38) :
    carrierCoe38 ((0 : ℕ) : ℝ) (i10_38 x) = carrierCoe38 ((1 : ℕ) : ℝ) x :=
  carrierCoe38_incl38 _ x

theorem i10_38_i21_38 (x : H2_38) : i10_38 (i21_38 x) = i20_38 x := by
  apply carrierExt38; funext n; simp

theorem sobolevModeWeight_natCast_F01_38 (k : ℕ) (n : ℤ) :
    sobolevModeWeight (k : ℝ) n = (1 + (n : ℝ) ^ 2) ^ k := by
  unfold sobolevModeWeight japaneseBracket
  rw [Real.rpow_eq_pow, show (2 * (k : ℝ)) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, pow_mul,
    Real.sq_sqrt (by positivity)]

/-- The weights `ρ_{(n,j)} = ⟨n⟩²`. -/
def rho38 (p : ℤ × Fin 2) : ℝ := 1 + ((p.1 : ℤ) : ℝ) ^ 2

theorem rho38_pos (p : ℤ × Fin 2) : 0 < rho38 p := by unfold rho38; positivity

/-- `Σ_p ρ_p^{-1} = 2 Σ_n (1+n²)^{-1}`: the Hilbert-Schmidt norm of `h¹ ↪ h⁰` squared. -/
def hsConst38 : ℝ := 2 * ∑' n : ℤ, 1 / (1 + (n : ℝ) ^ 2)

theorem tsum_ofReal_rho38_inv :
    ∑' p : ℤ × Fin 2, ENNReal.ofReal (rho38 p)⁻¹ = ENNReal.ofReal hsConst38 := by
  have hs := NlsGge.Analysis.summable_reciprocal_bracket_square
  rw [ENNReal.tsum_prod']
  have : ∀ m : ℤ, ∑' k : Fin 2, ENNReal.ofReal (rho38 (m, k))⁻¹ =
      2 * ENNReal.ofReal (1 / (1 + (m : ℝ) ^ 2)) := by
    intro m
    rw [tsum_fintype]
    simp [rho38]
  simp_rw [this]
  rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs,
    hsConst38, ENNReal.ofReal_mul (by norm_num)]
  simp

/-- `ρ²`-weighted energy of the coordinates of an element of `h²` is its squared norm. -/
theorem tsum_weighted_inner38 (z : H2_38) :
    ∑' q : ℤ × Fin 2, ENNReal.ofReal (rho38 q ^ 2 * (inner ℝ (bas0_38 q) (i20_38 z)) ^ 2) =
      ENNReal.ofReal (‖z‖ ^ 2) := by
  have hz := carrier_hasSum_norm_sq38 (((1 + 1 : ℕ)) : ℝ) z
  rw [ENNReal.tsum_prod']
  have : ∀ m : ℤ, ∑' k : Fin 2, ENNReal.ofReal (rho38 (m, k) ^ 2 *
      (inner ℝ (bas0_38 (m, k)) (i20_38 z)) ^ 2) =
      ENNReal.ofReal (sobolevModeWeight (((1 + 1 : ℕ)) : ℝ) m *
        ‖carrierCoe38 (((1 + 1 : ℕ)) : ℝ) z m‖ ^ 2) := by
    intro m
    rw [tsum_fintype, sobolevModeWeight_natCast_F01_38]
    have h := Complex.orthonormalBasisOneI.sum_sq_norm_inner_right
      (carrierCoe38 (((1 + 1 : ℕ)) : ℝ) z m)
    simp only [bas0_38_inner, carrierCoe38_i20, rho38]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity), ← Finset.mul_sum]
    congr 1
    rw [← h]
    simp only [Real.norm_eq_abs, sq_abs]
  simp_rw [this]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg (sobolevModeWeight_pos _ _).le (sq_nonneg _))
    hz.summable, hz.tsum_eq]


/-- The standard real Hilbert basis of `h¹` (coordinates `e_{(n,j)} / ⟨n⟩`). -/
def bas1_38 : HilbertBasis (ℤ × Fin 2) ℝ H1_38 :=
  weightedRealHilbertBasis (sobolevModeWeight ((1 : ℕ) : ℝ))

theorem bas1_38_coe (p : ℤ × Fin 2) (n : ℤ) :
    carrierCoe38 ((1 : ℕ) : ℝ) (bas1_38 p) n =
      (if n = p.1 then Complex.orthonormalBasisOneI p.2 else 0) /
        (Real.sqrt (sobolevModeWeight ((1 : ℕ) : ℝ) n) : ℂ) := by
  have h := weightedRealBasisVector_apply (sobolevModeWeight ((1 : ℕ) : ℝ)) p n
  have e : bas1_38 p = weightedRealBasisVector (sobolevModeWeight ((1 : ℕ) : ℝ)) p :=
    weightedRealHilbertBasis_apply _ p
  rw [e]
  exact h

theorem norm_i10_bas1_sq (p : ℤ × Fin 2) : ‖i10_38 (bas1_38 p)‖ ^ 2 = (rho38 p)⁻¹ := by
  have h := carrier_hasSum_norm_sq_zero38 (i10_38 (bas1_38 p))
  have h2 : HasSum (fun n : ℤ => ‖carrierCoe38 ((0 : ℕ) : ℝ) (i10_38 (bas1_38 p)) n‖ ^ 2)
      (rho38 p)⁻¹ := by
    have := hasSum_single (f := fun n : ℤ => ‖carrierCoe38 ((0 : ℕ) : ℝ) (i10_38 (bas1_38 p)) n‖ ^ 2)
      p.1 (fun n hn => by
        simp [bas1_38_coe, hn])
    convert this using 1
    have hv : carrierCoe38 ((0 : ℕ) : ℝ) (i10_38 (bas1_38 p)) p.1 =
        Complex.orthonormalBasisOneI p.2 /
          (Real.sqrt (sobolevModeWeight ((1 : ℕ) : ℝ) p.1) : ℂ) := by
      simp only [coe_i10_38', bas1_38_coe, ite_true]
    rw [hv, norm_div, Complex.orthonormalBasisOneI.orthonormal.1 p.2, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt (sobolevModeWeight_pos _ _).le,
      sobolevModeWeight_natCast_F01_38]
    simp [rho38]
  exact h.unique h2

/-- **v2:** "The inclusion `h¹ ↪ h⁰` is Hilbert-Schmidt", with `‖ι‖²_HS = Σ_p ρ_p^{-1}`. -/
theorem energy_i10_38 : energy i10_38 = ENNReal.ofReal hsConst38 := by
  rw [energy_eq_basis i10_38 bas1_38, ← tsum_ofReal_rho38_inv]
  refine tsum_congr (fun p => ?_)
  rw [norm_i10_bas1_sq]

theorem isHilbertSchmidt_i10_38 : IsHilbertSchmidt i10_38 := by
  unfold IsHilbertSchmidt
  rw [energy_i10_38]
  exact ENNReal.ofReal_ne_top

/-- The basis vector `e_p` seen as an element of `h¹`. -/
def xi38 (p : ℤ × Fin 2) : H1_38 :=
  carrierMk38 ((1 : ℕ) : ℝ) (carrierCoe38 ((0 : ℕ) : ℝ) (bas0_38 p))
    (finiteSupport_mem_seqSobolev38 _ _ ((Set.finite_singleton p.1).subset (fun n hn => by
      by_contra h
      apply hn
      have h' : n ≠ p.1 := by simpa using h
      simp [bas0_38_coe, h'])))

@[simp] theorem carrierCoe38_xi38 (p : ℤ × Fin 2) (n : ℤ) :
    carrierCoe38 ((1 : ℕ) : ℝ) (xi38 p) n = carrierCoe38 ((0 : ℕ) : ℝ) (bas0_38 p) n := by
  rw [xi38, carrierCoe38_mk]

theorem i10_xi38 (p : ℤ × Fin 2) : i10_38 (xi38 p) = bas0_38 p := by
  apply carrierExt38; funext n; simp

theorem norm_xi38_sq (p : ℤ × Fin 2) : ‖xi38 p‖ ^ 2 = rho38 p := by
  have h := carrier_hasSum_norm_sq38 ((1 : ℕ) : ℝ) (xi38 p)
  have h2 : HasSum (fun n : ℤ => sobolevModeWeight ((1 : ℕ) : ℝ) n *
      ‖carrierCoe38 ((1 : ℕ) : ℝ) (xi38 p) n‖ ^ 2) (rho38 p) := by
    have := hasSum_single (f := fun n : ℤ => sobolevModeWeight ((1 : ℕ) : ℝ) n *
      ‖carrierCoe38 ((1 : ℕ) : ℝ) (xi38 p) n‖ ^ 2) p.1 (fun n hn => by
        simp [carrierCoe38_xi38, bas0_38_coe, hn])
    convert this using 1
    have hv : carrierCoe38 ((1 : ℕ) : ℝ) (xi38 p) p.1 = Complex.orthonormalBasisOneI p.2 := by
      rw [carrierCoe38_xi38, bas0_38_coe]; simp
    rw [hv, Complex.orthonormalBasisOneI.orthonormal.1 p.2, sobolevModeWeight_natCast_F01_38]
    simp [rho38]
  exact h.unique h2

/-- **Row/column estimate on `h⁰`** (replacing v2's duality + interpolation + `h¹ ↪ h⁰` HS):
if `A` and `A^*` map `h¹` into `h²` (through `D`, `D'`), then `energy A ≤ (‖D‖²+‖D'‖²)·Σ ρ_p^{-1}`. -/
theorem energy_le_h1h2_38 (A : H0_38 →L[ℝ] H0_38) (D D' : H1_38 →L[ℝ] H2_38)
    (hD : ∀ ξ, A (i10_38 ξ) = i20_38 (D ξ))
    (hD' : ∀ ξ, ContinuousLinearMap.adjoint A (i10_38 ξ) = i20_38 (D' ξ)) :
    energy A ≤ ENNReal.ofReal ((‖D‖ ^ 2 + ‖D'‖ ^ 2) * hsConst38) := by
  have key : ∀ (T : H1_38 →L[ℝ] H2_38) (p : ℤ × Fin 2),
      ∑' q, ENNReal.ofReal (rho38 q ^ 2 * (inner ℝ (bas0_38 q) (i20_38 (T (xi38 p)))) ^ 2) ≤
        ENNReal.ofReal (‖T‖ ^ 2 * rho38 p) := by
    intro T p
    rw [tsum_weighted_inner38]
    apply ENNReal.ofReal_le_ofReal
    rw [← norm_xi38_sq p]
    calc ‖T (xi38 p)‖ ^ 2 ≤ (‖T‖ * ‖xi38 p‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm _) 2
      _ = ‖T‖ ^ 2 * ‖xi38 p‖ ^ 2 := by ring
  have h := energy_le_rowcol38 bas0_38 rho38 rho38_pos A ‖D‖ ‖D'‖
    (fun p => by rw [← i10_xi38 p, hD]; exact key D p)
    (fun q => by rw [← i10_xi38 q, hD']; exact key D' q)
  rw [tsum_ofReal_rho38_inv, ← ENNReal.ofReal_mul (by positivity)] at h
  exact h

theorem isHilbertSchmidt_of_h1h2_38 (A : H0_38 →L[ℝ] H0_38) (D D' : H1_38 →L[ℝ] H2_38)
    (hD : ∀ ξ, A (i10_38 ξ) = i20_38 (D ξ))
    (hD' : ∀ ξ, ContinuousLinearMap.adjoint A (i10_38 ξ) = i20_38 (D' ξ)) :
    IsHilbertSchmidt A :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (energy_le_h1h2_38 A D D' hD hD')

/-- The Hilbert-Schmidt norm bound `‖A‖²_HS ≤ (‖D‖²+‖D'‖²)·Σ_p ρ_p^{-1}`. -/
theorem norm_sq_ofCLM_le_h1h2_38 (A : H0_38 →L[ℝ] H0_38) (D D' : H1_38 →L[ℝ] H2_38)
    (hD : ∀ ξ, A (i10_38 ξ) = i20_38 (D ξ))
    (hD' : ∀ ξ, ContinuousLinearMap.adjoint A (i10_38 ξ) = i20_38 (D' ξ)) :
    ‖HilbertSchmidt.ofCLM A (isHilbertSchmidt_of_h1h2_38 A D D' hD hD')‖ ^ 2 ≤
      (‖D‖ ^ 2 + ‖D'‖ ^ 2) * hsConst38 := by
  have h := energy_le_h1h2_38 A D D' hD hD'
  have e := HilbertSchmidt.energy_eq_norm_sq
    (HilbertSchmidt.ofCLM A (isHilbertSchmidt_of_h1h2_38 A D D' hD hD'))
  rw [HilbertSchmidt.toCLM_ofCLM] at e
  rw [e] at h
  have hc : 0 ≤ hsConst38 := by
    unfold hsConst38
    exact mul_nonneg (by norm_num) (tsum_nonneg (fun n => by positivity))
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h


/-! ## Part 2: F01.01-F01.03 conditional on `B` and `O` -/

namespace BirkhoffInput38

variable (B : BirkhoffInput38)

/-- `L(x) = DT(x)` on `h⁰` (v2 `lem:determinants`). -/
def Lop (x : H0_38) : H0_38 →L[ℝ] H0_38 := fderiv ℝ (B.TC 0) x

/-- `B(x) = L(x) − Id`. -/
def Bop (x : H0_38) : H0_38 →L[ℝ] H0_38 := B.Lop x - 1

/-- `L(x)^{-1} = D T⁻¹ (T x)` (the identification is `Lop_comp_Linv`, `Linv_comp_Lop`). -/
def Linv (x : H0_38) : H0_38 →L[ℝ] H0_38 := fderiv ℝ (B.TinvC 0) (B.TC 0 x)

theorem differentiableAt_TC0 (x : H0_38) : DifferentiableAt ℝ (B.TC 0) x :=
  (B.analyticOnNhd_TC 0 x trivial).differentiableAt

theorem differentiableAt_TinvC0 (x : H0_38) : DifferentiableAt ℝ (B.TinvC 0) x :=
  (B.analyticOnNhd_TinvC 0 x trivial).differentiableAt

/-- The canonicity field in the form `⟪J L ξ, L η⟫ = ⟪J ξ, η⟫`. -/
theorem Lop_form (x ξ η : H0_38) :
    inner ℝ (J38 _ (B.Lop x ξ)) (B.Lop x η) = inner ℝ (J38 _ ξ) η := by
  rw [← stdSymplectic38_eq_inner, ← stdSymplectic38_eq_inner]
  exact B.canonical x ξ η

/-- **F01.01** `L(x)^* 𝕁 L(x) = 𝕁` on `h⁰` (v2 eq. symplecticcommon, first half). -/
theorem Lop_adjoint_mul (x : H0_38) :
    ContinuousLinearMap.adjoint (B.Lop x) * J38 _ * B.Lop x = J38 _ := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_right ℝ
  intro η
  show inner ℝ (ContinuousLinearMap.adjoint (B.Lop x) (J38 _ (B.Lop x ξ))) η = _
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact B.Lop_form x ξ η

theorem Linv_comp_Lop (x : H0_38) : B.Linv x * B.Lop x = 1 := by
  have h1 : HasFDerivAt (B.TC 0) (B.Lop x) x := (B.differentiableAt_TC0 x).hasFDerivAt
  have h2 : HasFDerivAt (B.TinvC 0) (B.Linv x) (B.TC 0 x) :=
    (B.differentiableAt_TinvC0 _).hasFDerivAt
  have h3 := h2.comp x h1
  have h4 : (B.TinvC 0) ∘ (B.TC 0) = id := funext (B.TinvC_TC 0)
  rw [h4] at h3
  exact (h3.unique (hasFDerivAt_id x))

theorem Lop_comp_Linv (x : H0_38) : B.Lop x * B.Linv x = 1 := by
  have h1 : HasFDerivAt (B.TC 0) (B.Lop (B.TinvC 0 (B.TC 0 x))) (B.TinvC 0 (B.TC 0 x)) :=
    (B.differentiableAt_TC0 _).hasFDerivAt
  have h2 : HasFDerivAt (B.TinvC 0) (B.Linv x) (B.TC 0 x) :=
    (B.differentiableAt_TinvC0 _).hasFDerivAt
  have h3 := h1.comp (B.TC 0 x) h2
  have h4 : (B.TC 0) ∘ (B.TinvC 0) = id := funext (B.TC_TinvC 0)
  rw [h4] at h3
  rw [B.TinvC_TC 0 x] at h3
  exact h3.unique (hasFDerivAt_id _)

/-- **F01.01** `B(x)^* = −𝕁 (L(x)^{-1} − Id) 𝕁` (v2 eq. symplecticcommon, second half). -/
theorem Bop_adjoint (x : H0_38) :
    ContinuousLinearMap.adjoint (B.Bop x) = -(J38 _ * (B.Linv x - 1) * J38 _) := by
  have hJJ := J38_mul_J38 ((0 : ℕ) : ℝ)
  have h1 : ContinuousLinearMap.adjoint (B.Lop x) * J38 _ = J38 _ * B.Linv x := by
    calc ContinuousLinearMap.adjoint (B.Lop x) * J38 _
        = ContinuousLinearMap.adjoint (B.Lop x) * J38 _ * (B.Lop x * B.Linv x) := by
          rw [B.Lop_comp_Linv, mul_one]
      _ = (ContinuousLinearMap.adjoint (B.Lop x) * J38 _ * B.Lop x) * B.Linv x := by
          rw [← mul_assoc]
      _ = J38 _ * B.Linv x := by rw [B.Lop_adjoint_mul]
  have h2 : ContinuousLinearMap.adjoint (B.Lop x) = -(J38 _ * B.Linv x * J38 _) := by
    calc ContinuousLinearMap.adjoint (B.Lop x)
        = ContinuousLinearMap.adjoint (B.Lop x) * (J38 _ * (-J38 _)) := by
          rw [mul_neg, hJJ, neg_neg, mul_one]
      _ = (ContinuousLinearMap.adjoint (B.Lop x) * J38 _) * (-J38 _) := by rw [mul_assoc]
      _ = -(J38 _ * B.Linv x * J38 _) := by rw [h1, mul_neg]
  have h3 : ContinuousLinearMap.adjoint (1 : H0_38 →L[ℝ] H0_38) = 1 := ContinuousLinearMap.adjoint_id
  rw [Bop, map_sub, h2, h3, mul_sub, sub_mul, mul_one, hJJ]
  abel

/-! ### F01.02: the one-smoothing pieces (fields `smooth_*`, `analytic_smooth_*` at `r = 1`) -/

variable (O : OneSmoothingInput38 B)

/-- `K = T − Id : h¹ → h²` (field `smooth_T 1`). -/
def Kfwd1 : H1_38 → H2_38 :=
  carrierMap38 ((1 : ℕ) : ℝ) (((1 + 1 : ℕ)) : ℝ) (fun x => B.T x - x) (O.smooth_T 1 le_rfl)

/-- `T⁻¹ − Id : h¹ → h²` (field `smooth_Tinv 1`). -/
def Kinv1 : H1_38 → H2_38 :=
  carrierMap38 ((1 : ℕ) : ℝ) (((1 + 1 : ℕ)) : ℝ) (fun z => B.Tinv z - z) (O.smooth_Tinv 1 le_rfl)

theorem analytic_Kfwd1 : AnalyticOnNhd ℝ (B.Kfwd1 O) Set.univ := O.analytic_smooth_T 1 le_rfl

theorem analytic_Kinv1 : AnalyticOnNhd ℝ (B.Kinv1 O) Set.univ := O.analytic_smooth_Tinv 1 le_rfl

/-- `D K (x₁) : h¹ → h²`. -/
def Dfwd (x1 : H1_38) : H1_38 →L[ℝ] H2_38 := fderiv ℝ (B.Kfwd1 O) x1

/-- `D (T⁻¹ − Id) (y₁) : h¹ → h²`. -/
def Dinv (y1 : H1_38) : H1_38 →L[ℝ] H2_38 := fderiv ℝ (B.Kinv1 O) y1

theorem TC1_eq : B.TC 1 = fun x => x + i21_38 (B.Kfwd1 O x) := by
  funext x
  apply carrierExt38
  funext n
  show B.T (carrierCoe38 ((1 : ℕ) : ℝ) x) n =
    carrierCoe38 ((1 : ℕ) : ℝ) x n + carrierCoe38 ((1 : ℕ) : ℝ) (i21_38 (B.Kfwd1 O x)) n
  rw [carrierCoe38_i21]
  show _ = _ + (B.T (carrierCoe38 ((1 : ℕ) : ℝ) x) - carrierCoe38 ((1 : ℕ) : ℝ) x) n
  simp

theorem TinvC1_eq : B.TinvC 1 = fun x => x + i21_38 (B.Kinv1 O x) := by
  funext x
  apply carrierExt38
  funext n
  show B.Tinv (carrierCoe38 ((1 : ℕ) : ℝ) x) n =
    carrierCoe38 ((1 : ℕ) : ℝ) x n + carrierCoe38 ((1 : ℕ) : ℝ) (i21_38 (B.Kinv1 O x)) n
  rw [carrierCoe38_i21]
  show _ = _ + (B.Tinv (carrierCoe38 ((1 : ℕ) : ℝ) x) - carrierCoe38 ((1 : ℕ) : ℝ) x) n
  simp

theorem differentiableAt_Kfwd1 (x : H1_38) : DifferentiableAt ℝ (B.Kfwd1 O) x :=
  (B.analytic_Kfwd1 O x trivial).differentiableAt

theorem differentiableAt_Kinv1 (x : H1_38) : DifferentiableAt ℝ (B.Kinv1 O) x :=
  (B.analytic_Kinv1 O x trivial).differentiableAt

theorem fderiv_TC1 (x1 : H1_38) :
    fderiv ℝ (B.TC 1) x1 = ContinuousLinearMap.id ℝ H1_38 + i21_38.comp (B.Dfwd O x1) := by
  rw [B.TC1_eq O]
  exact ((hasFDerivAt_id x1).add
    (i21_38.hasFDerivAt.comp x1 (B.differentiableAt_Kfwd1 O x1).hasFDerivAt)).fderiv

theorem fderiv_TinvC1 (y1 : H1_38) :
    fderiv ℝ (B.TinvC 1) y1 = ContinuousLinearMap.id ℝ H1_38 + i21_38.comp (B.Dinv O y1) := by
  rw [B.TinvC1_eq O]
  exact ((hasFDerivAt_id y1).add
    (i21_38.hasFDerivAt.comp y1 (B.differentiableAt_Kinv1 O y1).hasFDerivAt)).fderiv

theorem coe_i10_38 (x : H1_38) :
    carrierCoe38 ((0 : ℕ) : ℝ) (i10_38 x) = carrierCoe38 ((1 : ℕ) : ℝ) x :=
  carrierCoe38_incl38 _ x

theorem TC0_i10 (x1 : H1_38) : B.TC 0 (i10_38 x1) = i10_38 (B.TC 1 x1) := by
  apply carrierExt38
  rw [B.TC_coe, coe_i10_38, coe_i10_38, B.TC_coe]

/-- `L(ι x₁) ι ξ₁ = ι ξ₁ + ι₂₀ (D K (x₁) ξ₁)`. -/
theorem Lop_incl (x1 ξ1 : H1_38) :
    B.Lop (i10_38 x1) (i10_38 ξ1) = i10_38 ξ1 + i20_38 (B.Dfwd O x1 ξ1) := by
  have h := B.fderiv_TC_compat 0 1 (by norm_num) x1 ξ1
  rw [B.fderiv_TC1 O] at h
  have h' : B.Lop (i10_38 x1) (i10_38 ξ1) =
      i10_38 ((ContinuousLinearMap.id ℝ H1_38 + i21_38.comp (B.Dfwd O x1)) ξ1) := h.symm
  rw [h']
  simp only [add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, map_add, i10_38_i21_38]

/-- **F01.02 (forward).** `B(ι x₁) ι ξ₁ = ι₂₀ (D K (x₁) ξ₁)`: `B(x)` maps `h¹ → h²`. -/
theorem Bop_incl (x1 ξ1 : H1_38) :
    B.Bop (i10_38 x1) (i10_38 ξ1) = i20_38 (B.Dfwd O x1 ξ1) := by
  rw [Bop, sub_apply, B.Lop_incl O, one_apply_eq_self]
  abel

/-- `L(ι x₁)^{-1} ι ξ₁ = ι ξ₁ + ι₂₀ (D (T⁻¹ − Id) (T x₁) ξ₁)`. -/
theorem Linv_incl (x1 ξ1 : H1_38) :
    B.Linv (i10_38 x1) (i10_38 ξ1) = i10_38 ξ1 + i20_38 (B.Dinv O (B.TC 1 x1) ξ1) := by
  have h := B.fderiv_TinvC_compat 0 1 (by norm_num) (B.TC 1 x1) ξ1
  rw [B.fderiv_TinvC1 O] at h
  have h' : B.Linv (i10_38 x1) (i10_38 ξ1) =
      i10_38 ((ContinuousLinearMap.id ℝ H1_38 + i21_38.comp (B.Dinv O (B.TC 1 x1))) ξ1) := by
    rw [Linv, B.TC0_i10]
    exact h.symm
  rw [h']
  simp only [add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, map_add, i10_38_i21_38]

/-- The `h¹ → h²` operator representing `B(ι x₁)^*`: `−𝕁 D(T⁻¹ − Id)(T x₁) 𝕁`. -/
def Dadj (x1 : H1_38) : H1_38 →L[ℝ] H2_38 :=
  -((J38 (((1 + 1 : ℕ)) : ℝ)).comp ((B.Dinv O (B.TC 1 x1)).comp (J38 ((1 : ℕ) : ℝ))))

theorem J38_i10 (ξ : H1_38) : J38 ((0 : ℕ) : ℝ) (i10_38 ξ) = i10_38 (J38 ((1 : ℕ) : ℝ) ξ) :=
  J38_incl _ ξ

theorem J38_i20 (ξ : H2_38) : J38 ((0 : ℕ) : ℝ) (i20_38 ξ) = i20_38 (J38 (((1 + 1 : ℕ)) : ℝ) ξ) :=
  J38_incl _ ξ

/-- **F01.02 (adjoint).** `B(ι x₁)^* ι ξ₁ = ι₂₀ (Dadj x₁ ξ₁)`: `B(x)^*` maps `h¹ → h²`. -/
theorem Bop_adjoint_incl (x1 ξ1 : H1_38) :
    ContinuousLinearMap.adjoint (B.Bop (i10_38 x1)) (i10_38 ξ1) = i20_38 (B.Dadj O x1 ξ1) := by
  rw [B.Bop_adjoint]
  simp only [neg_apply, mul_apply_eq_comp, sub_apply,
    one_apply_eq_self]
  rw [J38_i10, B.Linv_incl O, add_sub_cancel_left, J38_i20]
  simp [Dadj]

theorem continuous_Dfwd : Continuous (B.Dfwd O) := by
  have : ContDiff ℝ 1 (B.Kfwd1 O) :=
    contDiff_iff_contDiffAt.2 (fun x => (B.analytic_Kfwd1 O x trivial).contDiffAt)
  exact this.continuous_fderiv one_ne_zero

theorem continuous_Dinv : Continuous (B.Dinv O) := by
  have : ContDiff ℝ 1 (B.Kinv1 O) :=
    contDiff_iff_contDiffAt.2 (fun x => (B.analytic_Kinv1 O x trivial).contDiffAt)
  exact this.continuous_fderiv one_ne_zero

theorem continuous_Dadj : Continuous (B.Dadj O) := by
  unfold Dadj
  refine Continuous.neg ?_
  have h1 : Continuous (fun x1 : H1_38 => B.Dinv O (B.TC 1 x1)) :=
    (B.continuous_Dinv O).comp (B.continuous_TC 1)
  exact ((ContinuousLinearMap.compL ℝ H1_38 H1_38 H2_38).flip (J38 ((1 : ℕ) : ℝ)) |>.continuous).comp h1
    |> fun h => (((ContinuousLinearMap.compL ℝ H1_38 H2_38 H2_38 (J38 (((1 + 1 : ℕ)) : ℝ)))).continuous.comp h)

/-! ### F01.03: Hilbert-Schmidt continuity -/

include O in
theorem Bop_isHS (x1 : H1_38) : IsHilbertSchmidt (B.Bop (i10_38 x1)) :=
  isHilbertSchmidt_of_h1h2_38 _ (B.Dfwd O x1) (B.Dadj O x1) (B.Bop_incl O x1)
    (B.Bop_adjoint_incl O x1)

/-- `x₁ ↦ B(x₁) ∈ HS(h⁰)` for `x₁ ∈ h¹` (v2 `lem:determinants`, first assertion). -/
def BHS (x1 : H1_38) : HilbertSchmidt H0_38 H0_38 :=
  HilbertSchmidt.ofCLM (B.Bop (i10_38 x1)) (B.Bop_isHS O x1)

@[simp] theorem toCLM_BHS (x1 : H1_38) :
    HilbertSchmidt.toCLM (B.BHS O x1) = B.Bop (i10_38 x1) := rfl

/-- The difference estimate: apply the row/column bound to `B(x) − B(y)` (v2: "apply the same
interpolation bound to differences"). -/
theorem norm_sq_BHS_sub_le (x y : H1_38) :
    ‖B.BHS O x - B.BHS O y‖ ^ 2 ≤
      (‖B.Dfwd O x - B.Dfwd O y‖ ^ 2 + ‖B.Dadj O x - B.Dadj O y‖ ^ 2) * hsConst38 := by
  have hD : ∀ ξ : H1_38, (B.Bop (i10_38 x) - B.Bop (i10_38 y)) (i10_38 ξ) =
      i20_38 ((B.Dfwd O x - B.Dfwd O y) ξ) := by
    intro ξ
    rw [sub_apply, B.Bop_incl O, B.Bop_incl O, sub_apply,
      map_sub]
  have hD' : ∀ ξ : H1_38, ContinuousLinearMap.adjoint (B.Bop (i10_38 x) - B.Bop (i10_38 y))
      (i10_38 ξ) = i20_38 ((B.Dadj O x - B.Dadj O y) ξ) := by
    intro ξ
    rw [map_sub, sub_apply, B.Bop_adjoint_incl O, B.Bop_adjoint_incl O,
      sub_apply, map_sub]
  have h := norm_sq_ofCLM_le_h1h2_38 _ _ _ hD hD'
  have e : B.BHS O x - B.BHS O y = HilbertSchmidt.ofCLM (B.Bop (i10_38 x) - B.Bop (i10_38 y))
      (isHilbertSchmidt_of_h1h2_38 _ _ _ hD hD') := by
    apply HilbertSchmidt.ext
    intro v
    rfl
  rw [e]
  exact h

/-- **F01.03.** `x₁ ↦ B(x₁)` is continuous from `h¹` to `HS(h⁰)`. -/
theorem continuous_BHS : Continuous (B.BHS O) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hK : Filter.Tendsto (fun y => ‖B.Dfwd O y - B.Dfwd O x‖) (nhds x) (nhds 0) := by
    have := ((B.continuous_Dfwd O).tendsto x).sub_const (B.Dfwd O x)
    simpa using this.norm
  have hA : Filter.Tendsto (fun y => ‖B.Dadj O y - B.Dadj O x‖) (nhds x) (nhds 0) := by
    have := ((B.continuous_Dadj O).tendsto x).sub_const (B.Dadj O x)
    simpa using this.norm
  have hb : Filter.Tendsto (fun y => Real.sqrt ((‖B.Dfwd O y - B.Dfwd O x‖ ^ 2 +
      ‖B.Dadj O y - B.Dadj O x‖ ^ 2) * hsConst38)) (nhds x) (nhds 0) := by
    have h1 := ((hK.pow 2).add (hA.pow 2)).mul_const hsConst38
    have h2 := (Real.continuous_sqrt.tendsto _).comp h1
    have h3 : (0 ^ 2 + 0 ^ 2 : ℝ) * hsConst38 = 0 := by norm_num
    rw [h3, Real.sqrt_zero] at h2
    exact h2
  refine squeeze_zero (fun y => norm_nonneg _) (fun y => ?_) hb
  have h := B.norm_sq_BHS_sub_le O y x
  exact Real.le_sqrt_of_sq_le h

end BirkhoffInput38

end NlsGge.Birkhoff
