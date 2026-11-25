import Mathlib
import QuantumNLS.RootNlsInvTime
import QuantumNLS.RootNlsInvLax
import QuantumNLS.RootEnergyVectorField
import QuantumNLS.Def024CubicSmoothEvaluation
import QuantumNLS.DiscParamContinuity

/-!
# R-BFCC01E8, stage 3: conservation of the discriminant for regular solutions

Source: `ROOT_nls_invariance.tex`, proof of `thm:root-nls-invariance`, paragraphs 1-3.
For `u ∈ C¹([-T,T]; H¹)` with `u(t) ∈ H³`, solving `i u_t = −u_xx + 2κ|u|²u` (as an identity of
`L²(𝕋_L)` vectors, in the vocabulary of the accepted R-63A99F0E: `physical`, `lap` = `−∂ₓ²`,
`Fh` = `|u|²u`), the discriminant `L2SpatialTransfer.discriminant κ u(t) z` (the actual DEF-013
transfer trace of the `L²` class) has zero time derivative and is constant on `[-T,T]`, for every
complex `z`.

Route: the continuous representative `q(t,x) = Σ uₙ(t) eₙ(x)` (`S1`) is `C²` in `x`
(`Def024CubicSmoothEmbedding.profileJet`), its time derivative is uniform in `x` (`S1` is a bounded
map `H¹ → C(𝕋_L)`), the pointwise equation follows from continuity of both sides, and stages
`RootNlsInvLax` / `RootNlsInvTime` give `∂ₜΔ = tr W(L) = tr(B(0)M(L) − M(L)B(0)) = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set ComplexConjugate Asymptotics
open scoped Matrix Interval
open QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
  QuantumNLS.LocalWellPosedness QuantumNLS.F04Regularity QuantumNLS.RootEnergyVariation
  QuantumNLS.Def024CubicSmoothEmbedding QuantumNLS.Def024CubicSmoothEvaluation

namespace QuantumNLS.RootNlsInvDisc
open QuantumNLS.SpatialTransfer QuantumNLS.L1SpatialTransfer QuantumNLS.RootNlsInvLax

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

local instance : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))

local instance : ENormedAddMonoid Mat2 :=
  NormedAddGroup.toENormedAddMonoid

variable {L : ℝ} [Fact (0 < L)]

/-- `H³ ↪ H²`. -/
abbrev m32 : h04 L 3 →L[ℂ] h04 L 2 := h04_mono L (by norm_num)

lemma one_le_jet : (1 : ℝ) ≤ 3 - ((2 : ℕ) : ℝ) := by norm_num

/-- The second spatial derivative as an `H¹` vector: coefficients `(ip_n)² bₙ`. -/
def jet2 (b : h04 L 3) : h04 L 1 := h04_mono L one_le_jet (jetMap 3 2 b)

/-- The representative of `u ∈ H³` is the zeroth profile jet. -/
lemma S1_m31 (b : h04 L 3) (x : ℝ) : S1 (m31 b) (x : AddCircle L) = profileJet b 0 x := by
  rw [profileJet_zero]; rfl

lemma S1_jet2 (b : h04 L 3) (x : ℝ) : S1 (jet2 b) (x : AddCircle L) = profileJet b 2 x := rfl

/-- `−∂ₓ²` of the H² image equals minus the second jet, in `h⁰`. -/
lemma lap_m32 (b : h04 L 3) : lap (m32 b) = m10 (-jet2 b) := by
  apply WSeq.ext
  funext n
  change ((freq L n ^ 2 : ℝ) : ℂ) * b.val n = -((Complex.I * (freq L n : ℂ)) ^ 2 * b.val n)
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

lemma hasDerivAt_jet0 (b : h04 L 3) (x : ℝ) : HasDerivAt (profileJet b 0) (profileJet b 1 x) x :=
  hasDerivAt_profileJet 0 (by norm_num) b x

lemma hasDerivAt_jet1 (b : h04 L 3) (x : ℝ) : HasDerivAt (profileJet b 1) (profileJet b 2 x) x :=
  hasDerivAt_profileJet 1 (by norm_num) b x

lemma jet_period (b : h04 L 3) (j : ℕ) : profileJet b j L = profileJet b j 0 := by
  unfold profileJet
  rw [AddCircle.coe_period, QuotientAddGroup.mk_zero]

lemma continuous_coe_circle : Continuous (fun x : ℝ => (x : AddCircle L)) := continuous_quotient_mk'

/-- `‖q‖² = q q̄` as complex numbers. -/
lemma normsq_cast (q : ℂ) : ((‖q‖ ^ 2 : ℝ) : ℂ) = q * conj q := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma sq_mul_sq {κ : ℝ} (hκ : 0 ≤ κ) : RootNlsInvLax.sq κ * RootNlsInvLax.sq κ = (κ : ℂ) := by
  show ((Real.sqrt κ : ℝ) : ℂ) * ((Real.sqrt κ : ℝ) : ℂ) = (κ : ℂ)
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hκ]

/-- **Pointwise form of the equation** for the continuous representatives. -/
theorem pointwise_eq {κ : ℝ} (hκ : 0 ≤ κ) (b : h04 L 3) (w : h04 L 1)
    (he : Complex.I • physical (m10 w) =
      physical (lap (m32 b)) + ((2 * κ : ℝ) : ℂ) • physical (m10 (Fh (le_refl (1 : ℝ)) (m31 b))))
    (x : ℝ) :
    S1 w (x : AddCircle L) = -Complex.I * (-profileJet b 2 x +
      2 * (RootNlsInvLax.sq κ * RootNlsInvLax.sq κ) * (profileJet b 0 x * conj (profileJet b 0 x)) * profileJet b 0 x) := by
  set c : ℂ := ((2 * κ : ℝ) : ℂ) with hc
  set F1 : AddCircle L → ℂ := fun y => Complex.I * S1 w y with hF1
  set F2 : AddCircle L → ℂ := fun y => -(S1 (jet2 b) y) +
    c * (((‖S1 (m31 b) y‖ ^ 2 : ℝ) : ℂ) * S1 (m31 b) y) with hF2
  have hF1c : Continuous F1 := continuous_const.mul (S1 w).continuous
  have hF2c : Continuous F2 :=
    ((S1 (jet2 b)).continuous.neg).add (continuous_const.mul
      ((Complex.continuous_ofReal.comp ((S1 (m31 b)).continuous.norm.pow 2)).mul (S1 (m31 b)).continuous))
  have hae : F1 =ᵐ[volume] F2 := by
    have hfun : (⇑(Complex.I • physical (m10 w)) : AddCircle L → ℂ) =
        ⇑(physical (m10 (-jet2 b)) + c • physical (m10 (Fh (le_refl (1 : ℝ)) (m31 b)))) := by
      rw [he, lap_m32]
    filter_upwards [Lp.coeFn_smul Complex.I (physical (m10 w)),
      Lp.coeFn_add (physical (m10 (-jet2 b)))
        (c • physical (m10 (Fh (le_refl (1 : ℝ)) (m31 b)))),
      Lp.coeFn_smul c (physical (m10 (Fh (le_refl (1 : ℝ)) (m31 b)))),
      physical_rep w, physical_rep (-jet2 b), RootEnergyVectorField.cubic (m31 b),
      physical_rep (m31 b)] with y h1 h2 h3 h4 h5 h6 h7
    have hy := congrFun hfun y
    rw [h1, h2] at hy
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at hy
    rw [h3] at hy
    simp only [Pi.smul_apply, smul_eq_mul] at hy
    rw [h4, h5, h6, h7] at hy
    simp only [hF1, hF2]
    rw [hy, map_neg, ContinuousMap.neg_apply]
  have hEq : F1 = F2 := (Continuous.ae_eq_iff_eq volume hF1c hF2c).mp hae
  have hx := congrFun hEq (x : AddCircle L)
  simp only [hF1, hF2, S1_m31, S1_jet2, normsq_cast] at hx
  have hk : c = 2 * (RootNlsInvLax.sq κ * RootNlsInvLax.sq κ) := by rw [hc, sq_mul_sq hκ]; push_cast; ring
  rw [hk] at hx
  linear_combination (-Complex.I) * hx + (S1 w (x : AddCircle L)) * Complex.I_sq

/-- Matrix form of the uniform time-difference quotient. -/
lemma balCoef_lin (κ : ℝ) (f g p : ℝ → ℂ) (z : ℂ) (r x : ℝ) :
    balCoef κ f z x - balCoef κ g z x - r • balCoef κ p 0 x =
      balCoef κ (fun y => f y - g y - (r : ℂ) * p y) 0 x - balCoef κ (fun _ => 0) 0 x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [balCoef, coef, Matrix.smul_apply, Complex.real_smul, map_sub, map_mul] <;> ring

lemma norm_balCoef_lin (κ : ℝ) (f g p : ℝ → ℂ) (z : ℂ) (r x : ℝ) :
    ‖balCoef κ f z x - balCoef κ g z x - r • balCoef κ p 0 x‖ ≤
      Real.sqrt κ * ‖f x - g x - (r : ℂ) * p x‖ := by
  rw [balCoef_lin]
  refine (DiscParamContinuity.norm_balCoef_sub_le κ κ _ _ 0 x).trans (le_of_eq ?_)
  simp only [mul_zero, sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg κ)]

/-- Continuous trace on `Mat2`. -/
def trCLM : Mat2 →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℝ ℂ)

lemma trCLM_apply (M : Mat2) : trCLM M = Matrix.trace M := by
  simp [trCLM, Matrix.traceLinearMap_apply]

/-- The `L²` discriminant of the time slice is the transfer trace of its continuous representative. -/
lemma disc_eq_trace (κ : ℝ) (b : h04 L 3) (z : ℂ) :
    L2SpatialTransfer.discriminant κ (physical (m10 (m31 b))) z =
      Matrix.trace (transfer (balCoef κ (profileJet b 0) z) L) := by
  rw [← L2SpatialTransfer.discriminant_eq_of_representative κ (physical (m10 (m31 b)))
    (v := ⇑(S1 (m31 b))) (physical_rep (m31 b)).symm z]
  congr 3
  funext s
  exact S1_m31 b s

/-- **Zero time derivative of the discriminant.** -/
theorem hasDerivWithinAt_disc {κ : ℝ} (hκ : 0 ≤ κ) {J : Set ℝ} {u : ℝ → h04 L 3} {v : ℝ → h04 L 1}
    {t₀ : ℝ}
    (hd : HasDerivWithinAt (fun s => m31 (u s)) (v t₀) J t₀)
    (he : Complex.I • physical (m10 (v t₀)) =
      physical (lap (m32 (u t₀))) + ((2 * κ : ℝ) : ℂ) •
        physical (m10 (Fh (le_refl (1 : ℝ)) (m31 (u t₀)))))
    (z : ℂ) :
    HasDerivWithinAt (fun t => L2SpatialTransfer.discriminant κ (physical (m10 (m31 (u t)))) z)
      0 J t₀ := by
  have hL : 0 < L := Fact.out
  set P : ℝ → ℂ := fun x => S1 (v t₀) (x : AddCircle L) with hPdef
  have hPc : Continuous P := (S1 (v t₀)).continuous.comp continuous_coe_circle
  set A : ℝ → ℝ → Mat2 := fun t => balCoef κ (profileJet (u t) 0) z with hA
  set Ad : ℝ → Mat2 := balCoef κ P 0 with hAd
  set b := u t₀ with hb
  have hP : ∀ x, P x = -Complex.I * (-profileJet b 2 x +
      2 * (RootNlsInvLax.sq κ * RootNlsInvLax.sq κ) * (profileJet b 0 x * conj (profileJet b 0 x)) * profileJet b 0 x) :=
    fun x => pointwise_eq hκ b (v t₀) he x
  obtain ⟨hWc, hWe⟩ := W_integral (L := L) κ z (hasDerivAt_jet0 b) (hasDerivAt_jet1 b) hPc hP
  set W : ℝ → Mat2 := fun x => laxB κ z (profileJet b 0 x) (profileJet b 1 x) *
      transfer (balCoef κ (profileJet b 0) z) x -
    transfer (balCoef κ (profileJet b 0) z) x * laxB κ z (profileJet b 0 0) (profileJet b 1 0)
    with hW
  -- uniform time derivative of the representative
  have hQ : HasDerivWithinAt (fun s => S1 (m31 (u s))) (S1 (v t₀)) J t₀ :=
    ((S1 (L := L)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t₀ hd
  rw [hasDerivWithinAt_iff_isLittleO, isLittleO_iff] at hQ
  have hlin : ∀ ε > 0, ∀ᶠ t in 𝓝[J] t₀, ∀ x ∈ Icc 0 L,
      ‖A t x - A t₀ x - (t - t₀) • Ad x‖ ≤ ε * |t - t₀| := by
    intro ε hε
    have hε' : 0 < ε / (Real.sqrt κ + 1) := div_pos hε (by positivity)
    filter_upwards [hQ hε'] with t ht x _
    have hpt := (ContinuousMap.norm_coe_le_norm
      (S1 (m31 (u t)) - S1 (m31 (u t₀)) - (t - t₀) • S1 (v t₀)) (x : AddCircle L)).trans ht
    simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, S1_m31, Complex.real_smul,
      Real.norm_eq_abs] at hpt
    calc ‖A t x - A t₀ x - (t - t₀) • Ad x‖
        ≤ Real.sqrt κ * ‖profileJet (u t) 0 x - profileJet b 0 x - ((t - t₀ : ℝ) : ℂ) * P x‖ :=
          norm_balCoef_lin κ _ _ _ z (t - t₀) x
      _ ≤ Real.sqrt κ * (ε / (Real.sqrt κ + 1) * |t - t₀|) :=
          mul_le_mul_of_nonneg_left hpt (Real.sqrt_nonneg κ)
      _ ≤ ε * |t - t₀| := by
          rw [← mul_assoc, ← mul_div_assoc]
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          rw [div_le_iff₀ (by positivity)]
          nlinarith [Real.sqrt_nonneg κ]
  have hAc : ∀ t, ContinuousOn (A t) (Icc 0 L) := fun t =>
    (continuous_coef _ _ (continuous_profileJet 0 (by norm_num) (u t)) z).continuousOn
  have hAdc : ContinuousOn Ad (Icc 0 L) := (continuous_coef _ _ hPc 0).continuousOn
  have hT := RootNlsInvTime.hasDerivWithinAt_transfer (A := A) (Ad := Ad) (W := W) (J := J)
    hL.le hAc hAdc hWc hlin hWe
  have htr := trCLM.hasFDerivAt.comp_hasDerivWithinAt t₀ hT
  have h0 : trCLM (W L) = 0 := by
    rw [trCLM_apply]
    exact trace_W_period κ z _ (jet_period b 0) (jet_period b 1)
  replace htr := htr.congr_deriv h0
  have hfun : (fun t => L2SpatialTransfer.discriminant κ (physical (m10 (m31 (u t)))) z) =
      fun t => trCLM (transfer (A t) L) := by
    funext t
    rw [trCLM_apply]
    exact disc_eq_trace κ (u t) z
  rw [hfun]
  exact htr

/-- **The discriminant of a regular solution is independent of time** (every complex `z`). -/
theorem disc_const {κ T : ℝ} (hκ : 0 ≤ κ) {u : ℝ → h04 L 3} {v : ℝ → h04 L 1}
    (hd : ∀ t ∈ Icc (-T) T, HasDerivWithinAt (fun s => m31 (u s)) (v t) (Icc (-T) T) t)
    (he : ∀ t ∈ Icc (-T) T, Complex.I • physical (m10 (v t)) =
      physical (lap (m32 (u t))) + ((2 * κ : ℝ) : ℂ) •
        physical (m10 (Fh (le_refl (1 : ℝ)) (m31 (u t)))))
    (z : ℂ) : ∀ t ∈ Icc (-T) T, ∀ s ∈ Icc (-T) T,
      L2SpatialTransfer.discriminant κ (physical (m10 (m31 (u t)))) z =
        L2SpatialTransfer.discriminant κ (physical (m10 (m31 (u s)))) z := by
  have key := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun t => L2SpatialTransfer.discriminant κ (physical (m10 (m31 (u t)))) z)
    (f' := fun _ => (0 : ℂ)) (C := 0)
    (fun t ht => hasDerivWithinAt_disc hκ (hd t ht) (he t ht) z) (fun _ _ => by simp)
  have hc : ∀ t ∈ Icc (-T) T, L2SpatialTransfer.discriminant κ (physical (m10 (m31 (u t)))) z =
      L2SpatialTransfer.discriminant κ (physical (m10 (m31 (u (-T))))) z := by
    intro t ht
    have h1 := key t ht
    rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at h1
    exact h1
  intro t ht s hs
  rw [hc t ht, hc s hs]

end QuantumNLS.RootNlsInvDisc

#print axioms QuantumNLS.RootNlsInvDisc.pointwise_eq
#print axioms QuantumNLS.RootNlsInvDisc.hasDerivWithinAt_disc
#print axioms QuantumNLS.RootNlsInvDisc.disc_const
