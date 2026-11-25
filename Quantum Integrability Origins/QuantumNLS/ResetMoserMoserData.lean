import QuantumNLS.ResetMoserYGen
import QuantumNLS.ResetMoserDt
import QuantumNLS.ResetMoserRestrict
import QuantumNLS.ResetMoserClamp

/-!
# `thm:reset-moser` (LOCAL-017), item 4: the Moser field `Y_t = Ycov(D_t, β⁰)` and its bounds

Source: `symplectic_correction.tex`, "The deformation and its invariant ball": "For `0 ≤ t ≤ 1`, put `Ω^t = ω + t(Ω − ω)` and define `Y_t` uniquely by
`ι_{Y_t}Ω^t = −β⁰` (eq:reset-moser-field).  The inverse of the associated real operator exists by the Neumann series, uniformly in `t` and `z`.
Consequently `Y_t` is analytic in `z`, continuous in `t`, and `‖Y_t(z)‖ ≤ C‖z‖³`, `‖DY_t(z)‖ ≤ C‖z‖²` (eq:reset-Y-bounds)."  And: "`dq_n(z)Y_t(z) = 0`".

Convention: `iota_Ycov` gives `ω(Y,h) + D(Y,h) = −b(h)` for `Y = Ycov D b`; hence `ι_{Y_t}Ω^t = −β⁰` is `Y_t = Ycov (D_t) β⁰` (with `b = β⁰`).

* `MoserData S`: the analytic data the Moser deformation consumes, all on a ball `B_{R0}`: the local bounds of `Ω` (`Loc`), `M R0² ≤ 1/4`, and the covector
  field `β⁰` with analyticity, annihilation of the angular space (`hann`), `‖β⁰‖ ≤ B‖z‖³`, `‖Dβ⁰‖ ≤ B‖z‖²`, and `d β⁰ = Ω − ω` (antisymmetrised `Dβ⁰`).
  It is instantiated for `β⁰ = β − df` from the Haar stage in `ResetMoserBetaData`.
* `Yf t z = Ycov (D_t z) (β⁰ z)`; `norm_Yf_le` (`‖Y_t(z)‖ ≤ B‖z‖³`), `dq_Yf_zero` (`dq_n(z) Y_t(z) = 0`, for `|t| ≤ 2`).
* `Ghat (z,s) = Yf (sig s) z`, the field on `K × ℝ` with clamped time: `Ghat_deriv` (explicit uniform bound on its Fréchet derivative on `B_{R0} × ℝ`).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.ResetMoserClamp

theorem contDiffAt_YcovX' {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {D : X → Form} {b : X → Cov}
    {z : X} {n : WithTop ℕ∞} (hD : ContDiffAt ℝ n D z) (hb : ContDiffAt ℝ n b z) (hsm : ‖D z‖ < 1) :
    ContDiffAt ℝ n (fun w => Ycov (D w) (b w)) z := by
  have hN0 : ‖Nop (D z)‖ < 1 := by have := norm_Nop_le (D z); linarith
  have hu : IsUnit (1 + Nop (D z)) := isUnit_one_add hN0
  let NopCLM : Form →L[ℝ] (K →L[ℝ] K) := (ContinuousLinearMap.compL ℝ K Cov K) (Jw.symm : Cov →L[ℝ] K)
  have h1 : ContDiffAt ℝ n (fun w => 1 + Nop (D w)) z :=
    contDiffAt_const.add (NopCLM.contDiff.contDiffAt.comp z hD)
  have hinv : ContDiffAt ℝ n (Ring.inverse : (K →L[ℝ] K) → (K →L[ℝ] K)) (1 + Nop (D z)) := by
    have := (analyticAt_inverse (𝕜 := ℝ) hu.unit).contDiffAt (n := n)
    rwa [hu.unit_spec] at this
  have h2 : ContDiffAt ℝ n (Ring.inverse ∘ fun w => 1 + Nop (D w)) z :=
    ContDiffAt.comp z hinv h1
  have h3 : ContDiffAt ℝ n (fun w => Jw.symm (b w)) z :=
    (Jw.symm : Cov →L[ℝ] K).contDiff.contDiffAt.comp z hb
  exact (h2.clm_apply h3).neg

/-- The analytic data of the Moser deformation, on one ball `B_{R0}`. -/
structure MoserData (S : Hyp) where
  R0 : ℝ
  M : ℝ
  B : ℝ
  β0 : K → Cov
  hL : Loc S R0 M
  hMR : M * R0 ^ 2 ≤ 1 / 4
  B_nonneg : 0 ≤ B
  β0_an : ∀ z ∈ ball (0 : K) R0, AnalyticAt ℝ β0 z
  β0_ann : ∀ z ∈ ball (0 : K) R0, ∀ h ∈ Tz z, β0 z h = 0
  β0_b3 : ∀ z ∈ ball (0 : K) R0, ‖β0 z‖ ≤ B * ‖z‖ ^ 3
  β0_b2 : ∀ z ∈ ball (0 : K) R0, ‖fderiv ℝ β0 z‖ ≤ B * ‖z‖ ^ 2
  β0_d : ∀ z ∈ ball (0 : K) R0, ∀ a b : K,
    fderiv ℝ β0 z a b - fderiv ℝ β0 z b a = (S.Ω z - omegaF) a b

namespace MoserData

variable {S : Hyp} (MD : MoserData S)

theorem R0_pos : 0 < MD.R0 := MD.hL.ρpos

theorem ball_sub : ball (0 : K) MD.R0 ⊆ ball (0 : K) S.R := ball_subset_ball MD.hL.ρR

theorem M_nonneg : 0 ≤ MD.M := MD.hL.M0

theorem β0_cont : ContinuousOn MD.β0 (ball (0 : K) MD.R0) :=
  fun z hz => (MD.β0_an z hz).continuousAt.continuousWithinAt

/-- The Moser field `Y_t(z) = Ycov (D_t z) (β⁰ z)`, `ι_{Y_t} Ω^t = −β⁰`. -/
def Yf (t : ℝ) (z : K) : K := Ycov (Dt S t z) (MD.β0 z)

theorem norm_Dl_le {z : K} (hz : z ∈ ball (0 : K) MD.R0) : ‖S.Ω z - omegaF‖ ≤ MD.M * ‖z‖ ^ 2 :=
  MD.hL.b2 z hz

theorem M_sq_le {z : K} (hz : z ∈ ball (0 : K) MD.R0) : MD.M * ‖z‖ ^ 2 ≤ 1 / 4 := by
  have h1 : ‖z‖ ^ 2 ≤ MD.R0 ^ 2 := by
    have := mem_ball_zero_iff.1 hz
    nlinarith [norm_nonneg z]
  calc MD.M * ‖z‖ ^ 2 ≤ MD.M * MD.R0 ^ 2 := mul_le_mul_of_nonneg_left h1 MD.M_nonneg
    _ ≤ 1 / 4 := MD.hMR

theorem norm_Dt_le {t : ℝ} (ht : |t| ≤ 2) {z : K} (hz : z ∈ ball (0 : K) MD.R0) :
    ‖Dt S t z‖ ≤ 1 / 2 := by
  unfold Dt
  rw [norm_smul, Real.norm_eq_abs]
  have h1 := MD.norm_Dl_le hz
  have h2 := MD.M_sq_le hz
  calc |t| * ‖S.Ω z - omegaF‖ ≤ 2 * (MD.M * ‖z‖ ^ 2) :=
        mul_le_mul ht h1 (norm_nonneg _) (by norm_num)
    _ ≤ 1 / 2 := by linarith

theorem norm_Dt_lt {t : ℝ} (ht : |t| ≤ 2) {z : K} (hz : z ∈ ball (0 : K) MD.R0) :
    ‖Dt S t z‖ < 1 := lt_of_le_of_lt (MD.norm_Dt_le ht hz) (by norm_num)

theorem norm_Yf_le {t : ℝ} (ht : |t| ≤ 2) {z : K} (hz : z ∈ ball (0 : K) MD.R0) :
    ‖MD.Yf t z‖ ≤ MD.B * ‖z‖ ^ 3 :=
  (norm_Ycov_le (MD.norm_Dt_lt ht hz) _).trans (MD.β0_b3 z hz)

/-- `dq_n(z) Y_t(z) = 0` on `B_{R0}`, for `|t| ≤ 2`. -/
theorem dq_Yf_zero {t : ℝ} (ht : |t| ≤ 2) {z : K} (hz : z ∈ ball (0 : K) MD.R0) (n : ℤ) :
    fderiv ℝ (q n) z (MD.Yf t z) = 0 :=
  (dq_Ycov_zero (Dfam := Dt S t) (β0 := MD.β0) (R := MD.R0)
    ((continuousOn_Dt S t).mono MD.ball_sub) MD.β0_cont (fun z hz => MD.norm_Dt_lt ht hz)
    (fun z hz _ => Dt_Tz S t (MD.ball_sub hz)) MD.β0_ann).1 z hz n

/-- The field on `K × ℝ` with clamped time. -/
def Ghat (p : K × ℝ) : K := Ycov (Dt S (sig p.2) p.1) (MD.β0 p.1)

theorem Ghat_apply (z : K) (s : ℝ) : MD.Ghat (z, s) = MD.Yf (sig s) z := rfl

theorem norm_Ghat_le {p : K × ℝ} (hp : p.1 ∈ ball (0 : K) MD.R0) :
    ‖MD.Ghat p‖ ≤ MD.B * ‖p.1‖ ^ 3 :=
  MD.norm_Yf_le (by simpa using abs_sig_le p.2 |>.trans (by norm_num : (3 / 2 : ℝ) ≤ 2)) hp

theorem Ghat_contDiffAt {p : K × ℝ} (hp : p.1 ∈ ball (0 : K) MD.R0) :
    ContDiffAt ℝ 1 MD.Ghat p := by
  have hΩ : ContDiffAt ℝ 1 S.Ω p.1 := (S.Ω_contDiffAt (MD.ball_sub hp)).of_le (by norm_num)
  have hΩ' : ContDiffAt ℝ 1 (fun q : K × ℝ => S.Ω q.1) p :=
    ContDiffAt.comp p hΩ contDiffAt_fst
  have hs : ContDiffAt ℝ 1 (fun q : K × ℝ => sig q.2) p :=
    ContDiffAt.comp p (sig_contDiff_one.contDiffAt) contDiffAt_snd
  have hD : ContDiffAt ℝ 1 (fun q : K × ℝ => Dt S (sig q.2) q.1) p :=
    hs.smul (hΩ'.sub contDiffAt_const)
  have hb : ContDiffAt ℝ 1 (fun q : K × ℝ => MD.β0 q.1) p :=
    ContDiffAt.comp p ((MD.β0_an p.1 hp).contDiffAt) contDiffAt_fst
  exact contDiffAt_YcovX' hD hb (MD.norm_Dt_lt (by
    have := abs_sig_le p.2; linarith) hp)

/-- Uniform Fréchet derivative bound for `Ghat` on `B_{R0} × ℝ`. -/
theorem Ghat_deriv {cσ : ℝ} (hc : ∀ s, ‖deriv sig s‖ ≤ cσ) {p : K × ℝ} (hp : p.1 ∈ ball (0 : K) MD.R0) :
    ∃ L : K × ℝ →L[ℝ] K, HasFDerivAt MD.Ghat L p ∧
      ‖L‖ ≤ (3 / 2 * (MD.M * ‖p.1‖) + cσ * (MD.M * ‖p.1‖ ^ 2)) * (MD.B * ‖p.1‖ ^ 3) + MD.B * ‖p.1‖ ^ 2 := by
  obtain ⟨z, s⟩ := p
  simp only at hp ⊢
  have hzS := MD.ball_sub hp
  have hΩd : HasFDerivAt S.Ω (fderiv ℝ S.Ω z) z :=
    (((S.Ω_contDiffAt hzS).differentiableAt (by norm_num)).hasFDerivAt)
  have hsd : HasFDerivAt (fun q : K × ℝ => sig q.2) ((deriv sig s) • ContinuousLinearMap.snd ℝ K ℝ) (z, s) := by
    have h1 : HasDerivAt sig (deriv sig s) (((z, s) : K × ℝ).2) :=
      (sig_contDiff_one.differentiable one_ne_zero s).hasDerivAt
    exact h1.comp_hasFDerivAt (z, s) (hasFDerivAt_snd (𝕜 := ℝ) (E := K) (F := ℝ) (p := (z, s)))
  have hOd : HasFDerivAt (fun q : K × ℝ => S.Ω q.1 - omegaF)
      ((fderiv ℝ S.Ω z).comp (ContinuousLinearMap.fst ℝ K ℝ)) (z, s) :=
    ((hΩd.comp (z, s) hasFDerivAt_fst).sub_const omegaF)
  have hDd := hsd.smul hOd
  have hβd : HasFDerivAt (fun q : K × ℝ => MD.β0 q.1)
      ((fderiv ℝ MD.β0 z).comp (ContinuousLinearMap.fst ℝ K ℝ)) (z, s) :=
    (((MD.β0_an z hp).differentiableAt.hasFDerivAt).comp (z, s) hasFDerivAt_fst)
  have hsm : ‖Dt S (sig s) z‖ < 1 := MD.norm_Dt_lt (by have := abs_sig_le s; linarith) hp
  obtain ⟨L, hL, hLf⟩ := hasFDerivAt_YcovX (D := fun q : K × ℝ => Dt S (sig q.2) q.1)
    (b := fun q : K × ℝ => MD.β0 q.1) hDd hβd hsm
  refine ⟨L, hL, ?_⟩
  have hD'n : ‖(sig s) • ((fderiv ℝ S.Ω z).comp (ContinuousLinearMap.fst ℝ K ℝ)) +
      ((deriv sig s) • ContinuousLinearMap.snd ℝ K ℝ).smulRight (S.Ω z - omegaF)‖ ≤
      3 / 2 * (MD.M * ‖z‖) + cσ * (MD.M * ‖z‖ ^ 2) := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      have h1 : ‖(fderiv ℝ S.Ω z).comp (ContinuousLinearMap.fst ℝ K ℝ)‖ ≤ MD.M * ‖z‖ :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
          calc ‖fderiv ℝ S.Ω z‖ * ‖ContinuousLinearMap.fst ℝ K ℝ‖ ≤ (MD.M * ‖z‖) * 1 :=
                mul_le_mul (MD.hL.b1 z hp) (ContinuousLinearMap.norm_fst_le ℝ K ℝ) (norm_nonneg _)
                  (by have := MD.M_nonneg; positivity)
            _ = MD.M * ‖z‖ := mul_one _)
      exact mul_le_mul (abs_sig_le s) h1 (norm_nonneg _) (by norm_num)
    · have hsn : ‖(deriv sig s) • ContinuousLinearMap.snd ℝ K ℝ‖ ≤ cσ := by
        rw [norm_smul]
        have h3 := ContinuousLinearMap.norm_snd_le (𝕜 := ℝ) (E := K) (F := ℝ)
        have h4 := hc s
        nlinarith [norm_nonneg (deriv sig s), norm_nonneg (ContinuousLinearMap.snd ℝ K ℝ)]
      rw [ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul hsn (MD.norm_Dl_le hp) (norm_nonneg _) ((norm_nonneg _).trans hsn)
  have hb'n : ‖(fderiv ℝ MD.β0 z).comp (ContinuousLinearMap.fst ℝ K ℝ)‖ ≤ MD.B * ‖z‖ ^ 2 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
      calc ‖fderiv ℝ MD.β0 z‖ * ‖ContinuousLinearMap.fst ℝ K ℝ‖ ≤ (MD.B * ‖z‖ ^ 2) * 1 :=
            mul_le_mul (MD.β0_b2 z hp) (ContinuousLinearMap.norm_fst_le ℝ K ℝ) (norm_nonneg _)
              (by have := MD.B_nonneg; positivity)
        _ = MD.B * ‖z‖ ^ 2 := mul_one _)
  refine ContinuousLinearMap.opNorm_le_bound _ (by
    have := MD.B_nonneg; have := MD.M_nonneg
    have h0 : 0 ≤ cσ := (norm_nonneg _).trans (hc 0)
    positivity) (fun h => ?_)
  rw [hLf h]
  refine (norm_Ycov_derivX_le (D := fun q : K × ℝ => Dt S (sig q.2) q.1)
    (b := fun q : K × ℝ => MD.β0 q.1) (z := (z, s)) hsm h).trans ?_
  have hbz : ‖MD.β0 z‖ ≤ MD.B * ‖z‖ ^ 3 := MD.β0_b3 z hp
  have : (‖(sig s) • ((fderiv ℝ S.Ω z).comp (ContinuousLinearMap.fst ℝ K ℝ)) +
      ((deriv sig s) • ContinuousLinearMap.snd ℝ K ℝ).smulRight (S.Ω z - omegaF)‖ * ‖MD.β0 z‖ +
      ‖(fderiv ℝ MD.β0 z).comp (ContinuousLinearMap.fst ℝ K ℝ)‖) ≤
      (3 / 2 * (MD.M * ‖z‖) + cσ * (MD.M * ‖z‖ ^ 2)) * (MD.B * ‖z‖ ^ 3) + MD.B * ‖z‖ ^ 2 :=
    add_le_add (mul_le_mul hD'n hbz (norm_nonneg _) (by
      have h0 : 0 ≤ cσ := (norm_nonneg _).trans (hc 0)
      have := MD.M_nonneg; positivity)) hb'n
  exact mul_le_mul_of_nonneg_right this (norm_nonneg _)

/-- The derivative bound in the form `‖DGhat(p)‖ ≤ κ ‖z‖²` on `B_{R0} × ℝ` (eq:reset-Y-bounds, second line). -/
theorem Ghat_deriv_kappa : ∃ κ : ℝ, 0 ≤ κ ∧ ∀ p : K × ℝ, p.1 ∈ ball (0 : K) MD.R0 →
    ∃ L : K × ℝ →L[ℝ] K, HasFDerivAt MD.Ghat L p ∧ ‖L‖ ≤ κ * ‖p.1‖ ^ 2 := by
  obtain ⟨cσ, hcσ⟩ := exists_deriv_sig_bound
  have hc0 : 0 ≤ cσ := (norm_nonneg _).trans (hcσ 0)
  have hB := MD.B_nonneg
  have hM := MD.M_nonneg
  have hR := MD.R0_pos
  refine ⟨MD.B + (3 / 2 * (MD.M * MD.R0) + cσ * (MD.M * MD.R0 ^ 2)) * (MD.B * MD.R0), by positivity,
    fun p hp => ?_⟩
  obtain ⟨L, hL, hLn⟩ := MD.Ghat_deriv hcσ hp
  refine ⟨L, hL, hLn.trans ?_⟩
  have hn : ‖p.1‖ < MD.R0 := mem_ball_zero_iff.1 hp
  have h0 := norm_nonneg p.1
  have h1 : (3 / 2 * (MD.M * ‖p.1‖) + cσ * (MD.M * ‖p.1‖ ^ 2)) ≤
      (3 / 2 * (MD.M * MD.R0) + cσ * (MD.M * MD.R0 ^ 2)) := by gcongr
  have h2 : MD.B * ‖p.1‖ ^ 3 ≤ (MD.B * MD.R0) * ‖p.1‖ ^ 2 := by
    have : ‖p.1‖ ^ 3 ≤ MD.R0 * ‖p.1‖ ^ 2 := by
      have : ‖p.1‖ ^ 3 = ‖p.1‖ * ‖p.1‖ ^ 2 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hn.le (by positivity)
    calc MD.B * ‖p.1‖ ^ 3 ≤ MD.B * (MD.R0 * ‖p.1‖ ^ 2) := mul_le_mul_of_nonneg_left this hB
      _ = (MD.B * MD.R0) * ‖p.1‖ ^ 2 := by ring
  have h3 : (3 / 2 * (MD.M * ‖p.1‖) + cσ * (MD.M * ‖p.1‖ ^ 2)) * (MD.B * ‖p.1‖ ^ 3) ≤
      (3 / 2 * (MD.M * MD.R0) + cσ * (MD.M * MD.R0 ^ 2)) * ((MD.B * MD.R0) * ‖p.1‖ ^ 2) :=
    mul_le_mul h1 h2 (by positivity) (by positivity)
  nlinarith [h3]

end MoserData

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.contDiffAt_YcovX'
#print axioms QuantumNLS.ResetMoser.MoserData.norm_Yf_le
#print axioms QuantumNLS.ResetMoser.MoserData.dq_Yf_zero
#print axioms QuantumNLS.ResetMoser.MoserData.Ghat_contDiffAt
#print axioms QuantumNLS.ResetMoser.MoserData.Ghat_deriv
#print axioms QuantumNLS.ResetMoser.MoserData.Ghat_deriv_kappa
