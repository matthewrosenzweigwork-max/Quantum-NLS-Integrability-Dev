import NlsGge.GK38.MolnarLocalization
import NlsGge.Schur.ActualSourceSchurEigenBridge38V1
import NlsGge.Schur.ActualSchurRealTypeSymmetry38V1
import NlsGge.Schur.ActualSchurOwnModeVariation38V1
import NlsGge.Schur.ActualPotentialTransposeEntryPrerequisites24

/-!
# Mo2 part C: the Fourier-side bridge for Molnár's localization

Piece Mo2 of the E01 plan (`campaign/E01_PLAN.md` §6.12), Molnár arXiv:1403.1369, Theorem 5.
This file proves `MolnarBridge38` (stated in `MolnarLocalization.lean`) and assembles the
unconditional theorems `molnar_localization38` (Molnár's norm) and `molnar_localization_H1_38`
(repository `H¹` norm).

**Route.**  A real zero `x` of `Δh(v)² - 1` has `Δh(v)(x) = spectralSign p` for `p ∈ {0, 1}`.
By `actualSourceEigenvalue_iff_halfTrace_E02_38` (with `z = -x`, so `-z = x`) and
`actualSourcePerturbedDirac_eigenvalue_iff_coordinate_kernel38V1`, there is a nonzero `x` in the
free weighted domain of `ℓ²(Bool × Sector p)` with `(z - mπ) x_(b,m) = (Ṽ x)_(b,m)`.  The entries
of `Ṽ` are `û((m+l)/2)` (upper output, lower input) and `conj û((m+l)/2)` (lower output, upper
input) (`actualPotentialTranspose_pair_entry_formula24`, `physicalFourier_star38`), and
`HilbertBasis.hasSum_repr` turns the matrix entries into the series of `Mo2.Setup`.
The `Setup` data is `c₁(k) = û(k/2)`, `c₂(k) = conj û(k/2)` (even `k`, else `0`), `λ = z = -x`,
index `-n`, `f₁ = x_(true,·)`, `f₂ = x_(false,·)` extended by zero off the sector.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set
open scoped Topology ENNReal

namespace NlsGge.GK38

open NlsGge.SpectralFoundations NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

noncomputable section

/-! ### The conjugate potential is `H¹` -/

theorem sobolevSquareSummable_star38 (v : PhysicalL2)
    (hv : SobolevSquareSummable 1 (physicalFourier v)) :
    SobolevSquareSummable 1 (physicalFourier (star v : PhysicalL2)) := by
  unfold SobolevSquareSummable at hv ⊢
  have h := (Equiv.neg ℤ).summable_iff.mpr hv
  refine h.congr (fun j => ?_)
  simp only [Function.comp, Equiv.neg_apply, physicalFourier_star38, norm_star]
  have : Real.rpow (japaneseBracket (-j)) (2 * 1) = Real.rpow (japaneseBracket j) (2 * 1) := by
    rw [japaneseBracket_h1_weight, japaneseBracket_h1_weight]; simp
  rw [this]

/-! ### Matrix entries as series -/

/-- Matrix-entry series of a bounded operator on the parity pair in the Fourier basis. -/
theorem pair_hasSum_inner (n : ℤ) (T : ParityPair n →L[ℂ] ParityPair n) (x : ParityPair n)
    (i : Bool × Sector n) :
    HasSum (fun j : Bool × Sector n =>
        parityPairRepr n x j * inner ℂ (parityPairVector n i) (T (parityPairVector n j)))
      (inner ℂ (parityPairVector n i) (T x)) := by
  have hb : ∀ j, parityPairFourierBasis n j = parityPairVector n j := by
    intro j
    simp [parityPairFourierBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]
  have h0 := (parityPairFourierBasis n).hasSum_repr x
  have h1 := (innerSL ℂ (parityPairVector n i)).hasSum (T.hasSum h0)
  simpa [innerSL_apply_apply, hb, inner_smul_right, parityPairRepr] using h1


/-- The potential `Ṽ = repr ∘ V ∘ repr.symm` of the pair `(v, star v)` in coordinates. -/
abbrev coordPot38 (p : ℤ) (v : PhysicalL2) (hv : SobolevSquareSummable 1 (physicalFourier v)) :
    SectorSquare p →L[ℂ] SectorSquare p :=
  actualSchurEndomorphismToSquareV5_30 p
    (coveredH1ParityPairPotential v (star v) hv (sobolevSquareSummable_star38 v hv) p)

theorem coordPot38_apply (p : ℤ) (v : PhysicalL2) (hv : SobolevSquareSummable 1 (physicalFourier v))
    (y : SectorSquare p) (i : Bool × Sector p) :
    coordPot38 p v hv y i =
      inner ℂ (parityPairVector p i)
        (coveredH1ParityPairPotential v (star v) hv (sobolevSquareSummable_star38 v hv) p
          ((parityPairRepr p).symm y)) := by
  unfold coordPot38 actualSchurEndomorphismToSquareV5_30
  simp only [ContinuousLinearMap.comp_apply]
  exact parityPairRepr_eq_inner38 p _ i

/-- Upper row of the coordinate potential: `(Ṽ y)_(true,m) = Σ_l û((m+l)/2) y_(false,l)`. -/
theorem coordPot38_upper_hasSum (p : ℤ) (v : PhysicalL2)
    (hv : SobolevSquareSummable 1 (physicalFourier v)) (y : SectorSquare p) (m : Sector p) :
    HasSum (fun l : Sector p => physicalFourier v ((m.val + l.val) / 2) * y.val (false, l))
      (coordPot38 p v hv y (true, m)) := by
  rw [coordPot38_apply]
  have h := pair_hasSum_inner p
    (coveredH1ParityPairPotential v (star v) hv (sobolevSquareSummable_star38 v hv) p)
    ((parityPairRepr p).symm y) (true, m)
  simp only [LinearIsometryEquiv.apply_symm_apply] at h
  have hinj : Function.Injective (fun l : Sector p => ((false, l) : Bool × Sector p)) :=
    fun a b hab => by simpa using hab
  rw [← hinj.hasSum_iff] at h
  · convert h using 1
    funext l
    simp only [Function.comp, actualPotentialTranspose_pair_entry_formula24]
    simp [mul_comm]
  · rintro ⟨c, l⟩ hc
    have : c = true := by
      by_contra hne
      exact hc ⟨l, by simp at hne; simp [hne]⟩
    subst this
    simp [actualPotentialTranspose_pair_entry_formula24]

/-- Lower row of the coordinate potential:
`(Ṽ y)_(false,m) = Σ_l conj û((m+l)/2) y_(true,l)`. -/
theorem coordPot38_lower_hasSum (p : ℤ) (v : PhysicalL2)
    (hv : SobolevSquareSummable 1 (physicalFourier v)) (y : SectorSquare p) (m : Sector p) :
    HasSum (fun l : Sector p =>
        star (physicalFourier v ((m.val + l.val) / 2)) * y.val (true, l))
      (coordPot38 p v hv y (false, m)) := by
  rw [coordPot38_apply]
  have h := pair_hasSum_inner p
    (coveredH1ParityPairPotential v (star v) hv (sobolevSquareSummable_star38 v hv) p)
    ((parityPairRepr p).symm y) (false, m)
  simp only [LinearIsometryEquiv.apply_symm_apply] at h
  have hinj : Function.Injective (fun l : Sector p => ((true, l) : Bool × Sector p)) :=
    fun a b hab => by simpa using hab
  rw [← hinj.hasSum_iff] at h
  · convert h using 1
    funext l
    have hm := m.property
    have hl := l.property
    have e : -((-(m.val + l.val)) / 2) = (m.val + l.val) / 2 := by omega
    simp only [Function.comp, actualPotentialTranspose_pair_entry_formula24, physicalFourier_star38,
      e]
    simp [mul_comm]
  · rintro ⟨c, l⟩ hc
    have : c = false := by
      by_contra hne
      exact hc ⟨l, by simp at hne; simp [hne]⟩
    subst this
    simp [actualPotentialTranspose_pair_entry_formula24]


/-! ### The sequences `c₁`, `c₂` and their weighted norms -/

/-- `c₁(k) = û(k/2)` for even `k`, `0` for odd `k`. -/
def cA38 (v : PhysicalL2) (k : ℤ) : ℂ := if k % 2 = 0 then physicalFourier v (k / 2) else 0

/-- `c₂(k) = conj û(k/2)` for even `k`, `0` for odd `k`. -/
def cB38 (v : PhysicalL2) (k : ℤ) : ℂ :=
  if k % 2 = 0 then star (physicalFourier v (k / 2)) else 0

theorem molnarTerm_summable38 (v : PhysicalL2) (hv : SobolevSquareSummable 1 (physicalFourier v)) :
    Summable fun j : ℤ => molnarBracket38 (2 * j) ^ 2 * ‖physicalFourier v j‖ ^ 2 := by
  have hs : Summable fun j : ℤ => Real.rpow (japaneseBracket j) (2 * 1) * ‖physicalFourier v j‖ ^ 2 :=
    hv
  have hle : ∀ j : ℤ, molnarBracket38 (2 * j) ^ 2 * ‖physicalFourier v j‖ ^ 2 ≤
      8 * (Real.rpow (japaneseBracket j) (2 * 1) * ‖physicalFourier v j‖ ^ 2) := by
    intro j
    rw [japaneseBracket_h1_weight j]
    have : molnarBracket38 (2 * j) ^ 2 ≤ 8 * (1 + (j : ℝ) ^ 2) := by
      unfold molnarBracket38
      push_cast
      rw [abs_mul]
      have h2 : |(2 : ℝ)| = 2 := by norm_num
      rw [h2]
      nlinarith [sq_abs (j : ℝ), abs_nonneg (j : ℝ), sq_nonneg (|(j : ℝ)| - 1 / 2)]
    calc molnarBracket38 (2 * j) ^ 2 * ‖physicalFourier v j‖ ^ 2
        ≤ 8 * (1 + (j : ℝ) ^ 2) * ‖physicalFourier v j‖ ^ 2 := by gcongr
      _ = _ := by ring
  exact Summable.of_nonneg_of_le (fun j => by positivity) hle (hs.mul_left 8)

theorem SW_cAB_term38 (v : PhysicalL2) (f : ℂ → ℂ) (hf : ∀ z, ‖f z‖ = ‖z‖)
    (c : ℤ → ℂ) (hc : ∀ k, c k = if k % 2 = 0 then f (physicalFourier v (k / 2)) else 0) :
    Mo2.SW c = ∑' j : ℤ, ENNReal.ofReal (molnarBracket38 (2 * j) ^ 2 * ‖physicalFourier v j‖ ^ 2) := by
  unfold Mo2.SW
  have hinj : Function.Injective (fun j : ℤ => 2 * j) := fun a b h => by simpa using h
  rw [← hinj.tsum_eq]
  · refine tsum_congr fun j => ?_
    have h2 : (2 * j) % 2 = 0 := by omega
    have h3 : (2 * j) / 2 = j := by omega
    simp only [hc, h2, h3, ite_true, Mo2.eW]
    rw [← ofReal_norm, hf, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_pow (by positivity)]
    congr 1
    unfold molnarBracket38
    push_cast
    ring
  · intro k hk
    by_contra hnr
    apply hk
    have : k % 2 ≠ 0 := by
      intro h0; apply hnr; exact ⟨k / 2, by show 2 * (k / 2) = k; omega⟩
    simp [hc, this]

theorem SW_cA_add_cB38 (v : PhysicalL2) (hv : SobolevSquareSummable 1 (physicalFourier v)) :
    Mo2.SW (cA38 v) + Mo2.SW (cB38 v) = ENNReal.ofReal (molnarNormSq v) := by
  rw [SW_cAB_term38 v id (fun _ => rfl) (cA38 v) (fun k => rfl),
    SW_cAB_term38 v star (fun z => norm_star z) (cB38 v) (fun k => rfl)]
  unfold molnarNormSq
  have hs := molnarTerm_summable38 v hv
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hs,
    ← two_mul]
  norm_num


/-! ### Extension by zero from the parity sector to `ℤ` -/

/-- The `b`-component of `y ∈ ℓ²(Bool × Sector p)`, extended by zero off the sector. -/
def extC38 (p : ℤ) (y : SectorSquare p) (b : Bool) (m : ℤ) : ℂ :=
  if h : m % 2 = p % 2 then y.val (b, ⟨m, h⟩) else 0

theorem extC38_sector (p : ℤ) (y : SectorSquare p) (b : Bool) (m : Sector p) :
    extC38 p y b m.val = y.val (b, m) := by
  simp [extC38, m.property]

theorem extC38_off (p : ℤ) (y : SectorSquare p) (b : Bool) (m : ℤ) (h : m % 2 ≠ p % 2) :
    extC38 p y b m = 0 := by
  simp [extC38, h]

theorem extC38_summable (p : ℤ) (y : freeWeightedDomainPointwise p) (b : Bool) :
    Summable (fun k : ℤ => ‖extC38 p y.val b k‖ ^ 2) ∧
    Summable (fun k : ℤ => ((k : ℝ) * Real.pi) ^ 2 * ‖extC38 p y.val b k‖ ^ 2) := by
  have hinj : Function.Injective (fun l : Sector p => ((b, l) : Bool × Sector p)) :=
    fun a c hab => by simpa using hab
  have hval : Function.Injective (fun l : Sector p => (l.val : ℤ)) := Subtype.val_injective
  have h0 : Summable fun i : Bool × Sector p => ‖y.val.val i‖ ^ 2 := by
    have := (lp.memℓp y.val).summable (by norm_num)
    simpa [Real.rpow_two] using this
  have h1 : Summable fun i : Bool × Sector p => ‖freeWeightedCoordinates p y.val i‖ ^ 2 := by
    have := y.property.summable (p := 2) (by norm_num)
    simpa [Real.rpow_two] using this
  constructor
  · rw [← hval.summable_iff (fun k hk => by
      have : k % 2 ≠ p % 2 := fun h => hk ⟨⟨k, h⟩, rfl⟩
      simp [extC38_off p _ b k this])]
    refine (h0.comp_injective hinj).congr fun l => ?_
    simp [Function.comp, extC38_sector]
  · rw [← hval.summable_iff (fun k hk => by
      have : k % 2 ≠ p % 2 := fun h => hk ⟨⟨k, h⟩, rfl⟩
      simp [extC38_off p _ b k this])]
    refine (h1.comp_injective hinj).congr fun l => ?_
    simp [Function.comp, extC38_sector, freeWeightedCoordinates, spectralCenter,
      mul_pow]

theorem SW_ne_top_of_summable38 (f : ℤ → ℂ) (h1 : Summable fun k : ℤ => ‖f k‖ ^ 2)
    (h2 : Summable fun k : ℤ => ((k : ℝ) * Real.pi) ^ 2 * ‖f k‖ ^ 2) : Mo2.SW f ≠ ⊤ := by
  have hs : Summable fun k : ℤ => 2 * ‖f k‖ ^ 2 + 2 * (((k : ℝ) * Real.pi) ^ 2 * ‖f k‖ ^ 2) :=
    (h1.mul_left 2).add (h2.mul_left 2)
  have hle : ∀ k : ℤ, (Mo2.eW k * ‖f k‖ₑ) ^ 2 ≤
      ENNReal.ofReal (2 * ‖f k‖ ^ 2 + 2 * (((k : ℝ) * Real.pi) ^ 2 * ‖f k‖ ^ 2)) := by
    intro k
    unfold Mo2.eW
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hpi := Real.pi_gt_three
    have hk : (1 + |(k : ℝ)|) ^ 2 ≤ 2 + 2 * ((k : ℝ) * Real.pi) ^ 2 := by
      have : (1 + |(k : ℝ)|) ^ 2 ≤ 2 + 2 * (k : ℝ) ^ 2 := by
        nlinarith [sq_abs (k : ℝ), sq_nonneg (|(k : ℝ)| - 1)]
      have h9 : (k : ℝ) ^ 2 ≤ ((k : ℝ) * Real.pi) ^ 2 := by
        have h1 : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
        rw [mul_pow]
        calc (k : ℝ) ^ 2 = (k : ℝ) ^ 2 * 1 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      linarith
    calc ((1 + |(k : ℝ)|) * ‖f k‖) ^ 2 = (1 + |(k : ℝ)|) ^ 2 * ‖f k‖ ^ 2 := by ring
      _ ≤ (2 + 2 * ((k : ℝ) * Real.pi) ^ 2) * ‖f k‖ ^ 2 := by gcongr
      _ = _ := by ring
  unfold Mo2.SW
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hs]
  exact ENNReal.ofReal_ne_top


theorem extC38_hasSum (p : ℤ) (y : SectorSquare p) (c : ℤ → ℂ)
    (hc : ∀ k : ℤ, k % 2 ≠ 0 → c k = 0) (g : Bool) (m : ℤ) (a : ℂ)
    (hsec : m % 2 = p % 2 → HasSum (fun l : Sector p => c (m + l.val) * y.val (g, l)) a)
    (hoff : m % 2 ≠ p % 2 → a = 0) :
    HasSum (fun l : ℤ => c (m + l) * extC38 p y g l) a := by
  by_cases h : m % 2 = p % 2
  · rw [← Subtype.val_injective.hasSum_iff (f := fun l : ℤ => c (m + l) * extC38 p y g l)]
    · convert hsec h using 1
      funext l
      simp [Function.comp, extC38_sector]
    · intro l hl
      have : l % 2 ≠ p % 2 := fun h' => hl ⟨⟨l, h'⟩, rfl⟩
      simp [extC38_off p y g l this]
  · have h0 := hoff h
    subst h0
    convert hasSum_zero using 1
    funext l
    by_cases hl : l % 2 = p % 2
    · have : (m + l) % 2 ≠ 0 := by omega
      simp [hc _ this]
    · simp [extC38_off p y g l hl]

theorem cA38_odd (v : PhysicalL2) (k : ℤ) (h : k % 2 ≠ 0) : cA38 v k = 0 := by simp [cA38, h]
theorem cB38_odd (v : PhysicalL2) (k : ℤ) (h : k % 2 ≠ 0) : cB38 v k = 0 := by simp [cB38, h]

/-- The kernel equation read coordinatewise: `(λ - mπ) y_(b,m) = (Ṽ y)_(b,m)`. -/
theorem kernel_coord38 (p : ℤ) (v : PhysicalL2) (hv : SobolevSquareSummable 1 (physicalFourier v))
    (lam : ℝ) (y : freeWeightedDomainPointwise p)
    (hk : (lam : ℂ) • y.val - freeCoordinateDirac p y - coordPot38 p v hv y.val = 0)
    (i : Bool × Sector p) :
    ((lam - i.2.val * Real.pi : ℝ) : ℂ) * y.val.val i = coordPot38 p v hv y.val i := by
  have h := congrArg (fun w : SectorSquare p => (w : Bool × Sector p → ℂ) i) hk
  simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    freeCoordinateDirac_apply, spectralCenter, lp.coeFn_zero, Pi.zero_apply] at h
  push_cast
  linear_combination h

/-- **The Fourier system.**  A nonzero solution of the coordinate kernel equation yields the data
of `Mo2.Setup` with `c₁ = û(·/2)`, `c₂ = conj û(·/2)`, `λ = lam`. -/
theorem setup_of_kernel38 (v : PhysicalL2) (hv : SobolevSquareSummable 1 (physicalFourier v))
    (R2 : ℝ) (hR : molnarNormSq v ≤ R2) (p n : ℤ) (lam : ℝ)
    (hlam : |lam - n * Real.pi| ≤ Real.pi / 2) (h8 : 8 * R2 ≤ 1 + |(n : ℝ)|)
    (y : freeWeightedDomainPointwise p) (hy0 : y.val ≠ 0)
    (hk : (lam : ℂ) • y.val - freeCoordinateDirac p y - coordPot38 p v hv y.val = 0) :
    Mo2.Setup n lam (cA38 v) (cB38 v) (extC38 p y.val true) (extC38 p y.val false) R2 ∧
      ((∃ m, extC38 p y.val true m ≠ 0) ∨ (∃ m, extC38 p y.val false m ≠ 0)) := by
  refine ⟨⟨hlam, (molnarNormSq_nonneg v).trans hR, ?_, h8, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [SW_cA_add_cB38 v hv]; exact ENNReal.ofReal_le_ofReal hR
  · exact SW_ne_top_of_summable38 _ (extC38_summable p y true).1 (extC38_summable p y true).2
  · exact SW_ne_top_of_summable38 _ (extC38_summable p y false).1 (extC38_summable p y false).2
  · intro m
    refine extC38_hasSum p y.val (cA38 v) (cA38_odd v) false m _ (fun hm => ?_)
      (fun hm => by simp [Mo2.hF, extC38_off p _ true m hm])
    have h1 := coordPot38_upper_hasSum p v hv y.val ⟨m, hm⟩
    have h2 := kernel_coord38 p v hv lam y hk (true, ⟨m, hm⟩)
    have h3 : ((lam - m * Real.pi : ℝ) : ℂ) * extC38 p y.val true m =
        coordPot38 p v hv y.val (true, ⟨m, hm⟩) := by
      rw [show extC38 p y.val true m = y.val.val (true, ⟨m, hm⟩) from extC38_sector p y.val true ⟨m, hm⟩]
      exact h2
    simp only [Mo2.hF]
    rw [h3]
    convert h1 using 1
    funext l
    have : (m + l.val) % 2 = 0 := by have := l.property; omega
    simp [cA38, this]
  · intro m
    refine extC38_hasSum p y.val (cB38 v) (cB38_odd v) true m _ (fun hm => ?_)
      (fun hm => by simp [Mo2.hF, extC38_off p _ false m hm])
    have h1 := coordPot38_lower_hasSum p v hv y.val ⟨m, hm⟩
    have h2 := kernel_coord38 p v hv lam y hk (false, ⟨m, hm⟩)
    have h3 : ((lam - m * Real.pi : ℝ) : ℂ) * extC38 p y.val false m =
        coordPot38 p v hv y.val (false, ⟨m, hm⟩) := by
      rw [show extC38 p y.val false m = y.val.val (false, ⟨m, hm⟩) from extC38_sector p y.val false ⟨m, hm⟩]
      exact h2
    simp only [Mo2.hF]
    rw [h3]
    convert h1 using 1
    funext l
    have : (m + l.val) % 2 = 0 := by have := l.property; omega
    simp [cB38, this]
  · by_contra hne
    push Not at hne
    apply hy0
    apply lp.ext
    funext ⟨b, m⟩
    cases b
    · have := hne.2 m.val
      rwa [extC38_sector] at this
    · have := hne.1 m.val
      rwa [extC38_sector] at this


/-! ### The bridge -/

theorem halfTrace_sq_one_sign38 (v : PhysicalL2) (z : ℂ)
    (h : actualPhysicalUnitHalfTrace32 v z ^ 2 = 1) :
    ∃ p : ℤ, actualPhysicalUnitHalfTrace32 v z = spectralSign p := by
  have h2 : (actualPhysicalUnitHalfTrace32 v z - 1) * (actualPhysicalUnitHalfTrace32 v z + 1) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact ⟨0, by simp [spectralSign]; linear_combination h3⟩
  · exact ⟨1, by simp [spectralSign]; linear_combination h3⟩

/-- **The Fourier-side bridge** (Molnár Theorem 5, reduction to the Lyapunov-Schmidt system). -/
theorem molnarBridge38_holds : ∀ (v : PhysicalL2) (R2 : ℝ),
    SobolevSquareSummable 1 (physicalFourier v) → molnarNormSq v ≤ R2 → MolnarBridge38 v R2 := by
  intro v R2 hv hR n x hn hx hz
  obtain ⟨p, hp⟩ := halfTrace_sq_one_sign38 v (x : ℂ) hz
  have hv₂ := sobolevSquareSummable_star38 v hv
  have hsrc := (actualSourceEigenvalue_iff_halfTrace_E02_38 p v (-(x : ℂ))).mpr
    (by rw [neg_neg]; exact hp)
  obtain ⟨y, hy0, hk⟩ :=
    (actualSourcePerturbedDirac_eigenvalue_iff_coordinate_kernel38V1 p v (star v) hv hv₂
      (-(x : ℂ))).mp hsrc
  have hcast : (((-x : ℝ)) : ℂ) = -(x : ℂ) := by push_cast; ring
  rw [← hcast] at hk
  have hlam : |(-x) - ((-n : ℤ) : ℝ) * Real.pi| ≤ Real.pi / 2 := by
    rw [show (-x) - ((-n : ℤ) : ℝ) * Real.pi = -(x - n * Real.pi) by push_cast; ring, abs_neg]
    exact hx
  have h8 : 8 * R2 ≤ 1 + |(((-n : ℤ)) : ℝ)| := by
    have e2 : (1 + |(((-n : ℤ)) : ℝ)|) = molnarBracket38 n := by
      unfold molnarBracket38; push_cast; rw [abs_neg]
    rw [e2]; exact hn
  obtain ⟨S, hne⟩ := setup_of_kernel38 v hv R2 hR p (-n) (-x) hlam h8 y hy0 hk
  exact ⟨_, _, _, _, S, hne⟩

end

end NlsGge.GK38
