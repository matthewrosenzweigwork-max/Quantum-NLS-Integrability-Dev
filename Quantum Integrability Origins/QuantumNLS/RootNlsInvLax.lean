import Mathlib
import QuantumNLS.L2SpatialTransfer

/-!
# R-BFCC01E8, stage 2: the derived time matrix and the zero-curvature identity

Source: `ROOT_nls_invariance.tex`, proof of `thm:root-nls-invariance`, first and second paragraphs.
With `S = diag(1,-1)`, `Q = √κ [[0, ū],[u, 0]]`, `A = -izS/2 + Q` (the frozen balanced coefficient
`SpatialTransfer.balCoef`), the time coefficient computed in the source is
`B = i(z²/2 + κ|u|²) S − zQ − i S Q_x`.
This module proves, for a fixed time and a `C²` profile `q` obeying the pointwise equation
`i P = −q_xx + 2κ|q|² q` (`P` = time derivative of `q`):

* `lax_compat`: the pointwise identity `B_x = A_t + [A, B]`, i.e. `A_t − B_x + [A,B] = 0`
  (`eq:root-derived-compatibility`), with `A_t = √κ [[0, P̄],[P, 0]]`;
* `W_integral`: `W(x) = B(x)M(x) − M(x)B(0)` is continuous and solves the differentiated integral
  equation `W(x) = ∫₀ˣ (A W + A_t M)`, `M = transfer A`;
* `trace_W_period`: if `q, q_x` are `L`-periodic then `tr W(L) = tr(B(0)M(L) − M(L)B(0)) = 0`.
`κ|q|²` is written `s²·q·q̄` with `s = √κ` (equal to `κ|q|²` for `κ ≥ 0`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set ComplexConjugate
open scoped Matrix Interval

namespace QuantumNLS.RootNlsInvLax
open QuantumNLS.SpatialTransfer QuantumNLS.L1SpatialTransfer

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

local instance : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))

local instance : ENormedAddMonoid Mat2 :=
  NormedAddGroup.toENormedAddMonoid

/-- `√κ` as a complex number. -/
abbrev sq (κ : ℝ) : ℂ := ((Real.sqrt κ : ℝ) : ℂ)

/-- The derived time coefficient `B = i(z²/2+κ|q|²)S − zQ − iSQ_x` at one point. -/
def laxB (κ : ℝ) (z q q1 : ℂ) : Mat2 :=
  !![Complex.I * (z ^ 2 / 2 + sq κ * sq κ * (q * conj q)),
      -(sq κ * (z * conj q + Complex.I * conj q1));
    sq κ * (-(z * q) + Complex.I * q1),
      -(Complex.I * (z ^ 2 / 2 + sq κ * sq κ * (q * conj q)))]

/-- Its `x`-derivative, given `q' = q1`, `q1' = q2`. -/
def laxBd (κ : ℝ) (z q q1 q2 : ℂ) : Mat2 :=
  !![Complex.I * (sq κ * sq κ * (q1 * conj q + q * conj q1)),
      -(sq κ * (z * conj q1 + Complex.I * conj q2));
    sq κ * (-(z * q1) + Complex.I * q2),
      -(Complex.I * (sq κ * sq κ * (q1 * conj q + q * conj q1)))]

/-- The frozen balanced coefficient at a point. -/
lemma balCoef_apply (κ : ℝ) (u : ℝ → ℂ) (z : ℂ) (x : ℝ) :
    balCoef κ u z x = !![-(Complex.I * z) / 2, sq κ * conj (u x); sq κ * u x, Complex.I * z / 2] :=
  rfl

/-- **Zero curvature** `B_x = A_t + AB − BA`, pointwise, from the equation `iP = −q₂ + 2κ|q|²q`. -/
theorem lax_compat (κ : ℝ) (z q q1 q2 P : ℂ)
    (hP : P = -Complex.I * (-q2 + 2 * (sq κ * sq κ) * (q * conj q) * q)) :
    laxBd κ z q q1 q2 =
      !![-(Complex.I * 0) / 2, sq κ * conj P; sq κ * P, Complex.I * 0 / 2] +
      !![-(Complex.I * z) / 2, sq κ * conj q; sq κ * q, Complex.I * z / 2] * laxB κ z q q1 -
      laxB κ z q q1 * !![-(Complex.I * z) / 2, sq κ * conj q; sq κ * q, Complex.I * z / 2] := by
  have hc : conj P = Complex.I * (-conj q2 + 2 * (sq κ * sq κ) * (conj q * q) * conj q) := by
    rw [hP]
    simp only [map_mul, map_neg, map_add, map_ofNat, Complex.conj_I, Complex.conj_ofReal,
      RingHomCompTriple.comp_apply, RingHom.id_apply, Complex.conj_conj]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [laxB, laxBd, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const,
      Fin.zero_eta, Fin.mk_one, Fin.isValue]
  all_goals (try rw [hc])
  all_goals (try rw [hP])
  all_goals ring_nf
  all_goals (try simp only [Complex.I_sq])
  all_goals (try ring_nf)

/-- Entrywise derivative of a `2 × 2` matrix function. -/
theorem hasDerivAt_mat2 {f11 f12 f21 f22 : ℝ → ℂ} {d11 d12 d21 d22 : ℂ} {x : ℝ}
    (h11 : HasDerivAt f11 d11 x) (h12 : HasDerivAt f12 d12 x)
    (h21 : HasDerivAt f21 d21 x) (h22 : HasDerivAt f22 d22 x) :
    HasDerivAt (fun y => (!![f11 y, f12 y; f21 y, f22 y] : Mat2)) !![d11, d12; d21, d22] x := by
  have e : (fun y => (!![f11 y, f12 y; f21 y, f22 y] : Mat2)) = fun y =>
      f11 y • (!![1, 0; 0, 0] : Mat2) + f12 y • (!![0, 1; 0, 0] : Mat2) +
        f21 y • (!![0, 0; 1, 0] : Mat2) + f22 y • (!![0, 0; 0, 1] : Mat2) := by
    funext y
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have e' : (!![d11, d12; d21, d22] : Mat2) =
      d11 • (!![1, 0; 0, 0] : Mat2) + d12 • (!![0, 1; 0, 0] : Mat2) +
        d21 • (!![0, 0; 1, 0] : Mat2) + d22 • (!![0, 0; 0, 1] : Mat2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [e, e']
  exact (((h11.smul_const _).add (h12.smul_const _)).add (h21.smul_const _)).add (h22.smul_const _)

/-- `x`-derivative of `B(q(x), q₁(x))`. -/
theorem hasDerivAt_laxB (κ : ℝ) (z : ℂ) {q q1 : ℝ → ℂ} {x : ℝ} {d1 d2 : ℂ}
    (hq : HasDerivAt q d1 x) (hq1 : HasDerivAt q1 d2 x) :
    HasDerivAt (fun y => laxB κ z (q y) (q1 y)) (laxBd κ z (q x) d1 d2) x := by
  have hc : HasDerivAt (fun y => conj (q y)) (conj d1) x := by
    simpa only [Complex.star_def] using hq.star
  have hc1 : HasDerivAt (fun y => conj (q1 y)) (conj d2) x := by
    simpa only [Complex.star_def] using hq1.star
  have hqq : HasDerivAt (fun y => q y * conj (q y)) (d1 * conj (q x) + q x * conj d1) x :=
    hq.mul hc
  have h11 : HasDerivAt (fun y => Complex.I * (z ^ 2 / 2 + sq κ * sq κ * (q y * conj (q y))))
      (Complex.I * (sq κ * sq κ * (d1 * conj (q x) + q x * conj d1))) x := by
    have := ((hqq.const_mul (sq κ * sq κ)).const_add (z ^ 2 / 2)).const_mul Complex.I
    simpa using this
  have h12 : HasDerivAt (fun y => -(sq κ * (z * conj (q y) + Complex.I * conj (q1 y))))
      (-(sq κ * (z * conj d1 + Complex.I * conj d2))) x :=
    (((hc.const_mul z).add (hc1.const_mul Complex.I)).const_mul (sq κ)).neg
  have h21 : HasDerivAt (fun y => sq κ * (-(z * q y) + Complex.I * q1 y))
      (sq κ * (-(z * d1) + Complex.I * d2)) x :=
    (((hq.const_mul z).neg).add (hq1.const_mul Complex.I)).const_mul (sq κ)
  have h22 := h11.neg
  exact hasDerivAt_mat2 h11 h12 h21 h22

variable {L : ℝ} [Fact (0 < L)]

/-- **The differentiated integral equation** for `W = BM − MB(0)`. -/
theorem W_integral (κ : ℝ) (z : ℂ) {q q1 q2 P : ℝ → ℂ}
    (hq : ∀ x, HasDerivAt q (q1 x) x) (hq1 : ∀ x, HasDerivAt q1 (q2 x) x)
    (hPc : Continuous P)
    (hP : ∀ x, P x = -Complex.I * (-q2 x + 2 * (sq κ * sq κ) * (q x * conj (q x)) * q x)) :
    ContinuousOn (fun x => laxB κ z (q x) (q1 x) * transfer (balCoef κ q z) x -
        transfer (balCoef κ q z) x * laxB κ z (q 0) (q1 0)) (Icc 0 L) ∧
    ∀ x ∈ Icc 0 L,
      laxB κ z (q x) (q1 x) * transfer (balCoef κ q z) x -
          transfer (balCoef κ q z) x * laxB κ z (q 0) (q1 0) =
        ∫ s in (0 : ℝ)..x,
          (balCoef κ q z s * (laxB κ z (q s) (q1 s) * transfer (balCoef κ q z) s -
              transfer (balCoef κ q z) s * laxB κ z (q 0) (q1 0)) +
            balCoef κ P 0 s * transfer (balCoef κ q z) s) := by
  have hL : 0 < L := Fact.out
  have hqc : Continuous q := continuous_iff_continuousAt.mpr fun x => (hq x).continuousAt
  have hq1c : Continuous q1 := continuous_iff_continuousAt.mpr fun x => (hq1 x).continuousAt
  set A := balCoef κ q z with hA
  set Ad := balCoef κ P 0 with hAd
  have hAc : Continuous A := continuous_coef _ _ hqc z
  have hAdc : Continuous Ad := continuous_coef _ _ hPc 0
  set B : ℝ → Mat2 := fun x => laxB κ z (q x) (q1 x) with hB
  have hBd : ∀ x, HasDerivAt B (laxBd κ z (q x) (q1 x) (q2 x)) x := fun x =>
    hasDerivAt_laxB κ z (hq x) (hq1 x)
  have hBc : Continuous B := continuous_iff_continuousAt.mpr fun x => (hBd x).continuousAt
  -- classical fundamental solution
  set Mc := SpatialTransfer.spatialTransfer κ q z with hMc
  have hF : IsFundamental A Mc := LinearFundamental.spatialTransfer_spec' κ hqc z
  have hMcc : Continuous Mc := continuous_iff_continuousAt.mpr fun x => (hF.2 x).continuousAt
  have hEq : EqOn (transfer A) Mc (Icc 0 L) := L2SpatialTransfer.transfer_eq_frozen κ hqc z
  set Wc : ℝ → Mat2 := fun x => B x * Mc x - Mc x * B 0 with hWc
  have hWcc : Continuous Wc := (hBc.mul hMcc).sub (hMcc.mul continuous_const)
  have hWd : ∀ x, HasDerivAt Wc (A x * Wc x + Ad x * Mc x) x := by
    intro x
    have h1 := (hBd x).mul (hF.2 x)
    have h2 := (hF.2 x).mul_const (B 0)
    have h3 := h1.sub h2
    refine h3.congr_deriv ?_
    have hk := lax_compat κ z (q x) (q1 x) (q2 x) (P x) (hP x)
    have hAx : A x = !![-(Complex.I * z) / 2, sq κ * conj (q x); sq κ * q x, Complex.I * z / 2] :=
      rfl
    have hAdx : Ad x = !![-(Complex.I * 0) / 2, sq κ * conj (P x); sq κ * P x, Complex.I * 0 / 2] :=
      rfl
    rw [← hAx, ← hAdx] at hk
    have hk' : laxBd κ z (q x) (q1 x) (q2 x) = Ad x + A x * B x - B x * A x := hk
    rw [hk']
    show _ = A x * (B x * Mc x - Mc x * B 0) + Ad x * Mc x
    noncomm_ring
  refine ⟨?_, ?_⟩
  · apply ContinuousOn.congr hWcc.continuousOn
    intro x hx
    dsimp only
    rw [hEq hx]
  · intro x hx
    have hsub : uIcc (0 : ℝ) x ⊆ Icc 0 L := by
      rw [uIcc_of_le hx.1]; exact Icc_subset_Icc_right hx.2
    have hcont : Continuous (fun s => A s * Wc s + Ad s * Mc s) :=
      (hAc.mul hWcc).add (hAdc.mul hMcc)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hWd y)
      (hcont.intervalIntegrable 0 x)
    have hW0 : Wc 0 = 0 := by simp [hWc, hF.1]
    rw [hW0, sub_zero] at hftc
    have hlhs : B x * transfer A x - transfer A x * B 0 = Wc x := by
      simp only [hWc, hEq hx]
    rw [hlhs, ← hftc]
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' := hsub hs
    simp only [hWc, hB, hEq hs']

/-- **Trace of `W` at the period**: zero when `q, q_x` are periodic. -/
theorem trace_W_period (κ : ℝ) (z : ℂ) {q q1 : ℝ → ℂ} (M : Mat2)
    (hq : q L = q 0) (hq1 : q1 L = q1 0) :
    Matrix.trace (laxB κ z (q L) (q1 L) * M - M * laxB κ z (q 0) (q1 0)) = 0 := by
  rw [hq, hq1, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

end QuantumNLS.RootNlsInvLax

#print axioms QuantumNLS.RootNlsInvLax.lax_compat
#print axioms QuantumNLS.RootNlsInvLax.hasDerivAt_laxB
#print axioms QuantumNLS.RootNlsInvLax.W_integral
#print axioms QuantumNLS.RootNlsInvLax.trace_W_period
