import QuantumNLS.ResetMoserPrinted

/-!
# `thm:reset-moser` (LOCAL-017): the PROCEDURE clause, `S` is the time-one map of the flow of `Y_t = Ycov(t(Ω−ω), β⁰)`

Source: `symplectic_correction.tex:25`: "the procedure specified below constructs a real-analytic diffeomorphism `S : B_r → B_r`"; the procedure: `Y_t` with `ι_{Y_t} Ω^t = −β⁰`, `Ω^t = ω + t(Ω − ω)`,
`β⁰ = β − df` (`f` the Haar primitive), `S = S_1` the time-one map of `d/dt S_t = Y_t ∘ S_t`, `S_0 = id`, and `S^{-1}` the reversed flow.

The frozen `reset_moser_printed` (ResetMoserPrinted) exports only the EXISTENCE of `S`.  Here the SAME witness is identified: `Sm = MD.Sfl 1`, `Si = MD.Tinv`, where `MD = moserDataN (toHyp P) B.toNative`.

* `MoserData.Yf_lipschitz`, `flow_unique`, `flow_unique_back`: `Y_t` is Lipschitz on `B_{R0}` uniformly for `t ∈ [0,1]` (`Ghat_deriv_kappa`), so a solution of `γ' = Y_t(γ)` in `B_{R0}` with `γ 0 = z` is `S_t z`
  (forward uniqueness, Mathlib `ODE_solution_unique_of_mem_Icc_right`), and the backward solution with `γ 1 = w` has `γ 0 = S⁻¹ w` (`…_left`).
* `Srev`, `Srev_deriv`: the reversed flow `S⁻¹ = (Φ_{−1}(·, 1)).1`, `d/dτ Srev τ w = −Y_{1−τ}(Srev τ w)`, `Srev 1 = Tinv`.
* `sfl_corrects`: the printed conclusions for the explicit witnesses `(Sfl 1, Tinv)` (the body of `reset_moser_of_data`, with the witnesses kept).
* `PrintedHyp.moserY P t z = Ycov (t (Ω_z − ω)) β⁰_z` with `β⁰ = LOCAL017Haar.beta0 (betaR (toHyp P)) = β − df`, `f = LOCAL017Haar.primitive (betaR (toHyp P))`;  on `B_R`, `moserY = MD.Yf`.
* `reset_moser_printed_flow (P : PrintedHyp)`: for every bound datum `B`, `r = moserRadius`, the printed conclusions hold for `(Sm, Si)` AND `MoserFlowSpec`: `Sm = Φ_1`, `Φ_t` the flow of `Y_t` on `B_r`
  (`Φ_0 = id`, `∂_t Φ_t = Y_t ∘ Φ_t` on `[0,1]`, `‖Φ_t z‖ = ‖z‖`, uniqueness among `B_{4r}`-valued solutions), `Si` the reversed flow (`Ψ`, `∂_τ Ψ_τ = −Y_{1−τ}∘Ψ_τ`, `Si = Ψ_1`) and the backward uniqueness.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal NNReal
open Filter Set Metric Asymptotics
open scoped Classical

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.ResetMoserClamp QuantumNLS.LOCAL017SourceR19
  QuantumNLS.Ext025A4BanachComplexification

namespace MoserData

variable {S : Hyp} (MD : MoserData S)

theorem Yf_lipschitz : ∃ Lc : ℝ≥0, ∀ t ∈ Icc (0 : ℝ) 1, LipschitzOnWith Lc (MD.Yf t) (ball (0 : K) MD.R0) := by
  obtain ⟨κ, hκ, hL⟩ := MD.Ghat_deriv_kappa
  have hR := MD.R0_pos
  refine ⟨Real.toNNReal (κ * MD.R0 ^ 2), fun t ht => ?_⟩
  have hfeq : MD.Yf t = fun z => MD.Ghat (z, t) := by
    funext z
    rw [Ghat_apply, sig_eq (s := t) ⟨by linarith [ht.1], by linarith [ht.2]⟩]
  rw [hfeq]
  have key : ∀ z ∈ ball (0 : K) MD.R0, ∃ L' : K →L[ℝ] K,
      HasFDerivAt (fun z => MD.Ghat (z, t)) L' z ∧ ‖L'‖ ≤ κ * ‖z‖ ^ 2 := by
    intro z hz
    obtain ⟨L, hLd, hLn⟩ := hL (z, t) hz
    have hcomp := hLd.comp z (hasFDerivAt_prodMk_left (𝕜 := ℝ) z t)
    refine ⟨L.comp (ContinuousLinearMap.inl ℝ K ℝ), hcomp, ?_⟩
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc ‖L‖ * ‖ContinuousLinearMap.inl ℝ K ℝ‖ ≤ ‖L‖ * 1 :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_inl_le_one ℝ K ℝ) (norm_nonneg _)
      _ ≤ κ * ‖z‖ ^ 2 := by simpa using hLn
  refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) (fun z hz => ?_) (fun z hz => ?_) (convex_ball _ _)
  · obtain ⟨L', h, _⟩ := key z hz
    exact h.differentiableAt
  · obtain ⟨L', h, hn⟩ := key z hz
    rw [h.fderiv]
    have hz2 : ‖z‖ ^ 2 ≤ MD.R0 ^ 2 := by
      have := mem_ball_zero_iff.1 hz
      nlinarith [norm_nonneg z]
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
    exact hn.trans (mul_le_mul_of_nonneg_left hz2 hκ)

/-- Forward uniqueness: a `B_{R0}`-valued solution of `γ' = Y_t(γ)`, `γ 0 = z` on `[0,1]` is the Moser flow `S_t z`. -/
theorem flow_unique {z : K} (hz : ‖z‖ < MD.R0 / 4) {γ : ℝ → K} (h0 : γ 0 = z)
    (hc : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hd : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt γ (MD.Yf t (γ t)) (Ici t) t)
    (hm : ∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ ball (0 : K) MD.R0) :
    ∀ t ∈ Icc (0 : ℝ) 1, γ t = MD.Sfl t z := by
  obtain ⟨Lc, hLc⟩ := MD.Yf_lipschitz
  have hR := MD.R0_pos
  have hsfd : ∀ t, HasDerivAt (fun s => MD.Sfl s z) (MD.Yf (sig t) (MD.Sfl t z)) t := MD.Sfl_deriv hz.le
  have hcont : ContinuousOn (fun s => MD.Sfl s z) (Icc (0 : ℝ) 1) :=
    fun s _ => (hsfd s).continuousAt.continuousWithinAt
  exact ODE_solution_unique_of_mem_Icc_right (v := MD.Yf) (s := fun _ => ball (0 : K) MD.R0) (K := Lc)
    (a := 0) (b := 1) (fun t ht => hLc t ⟨ht.1, ht.2.le⟩) hc hd hm hcont
    (fun t ht => by
      have := hsfd t
      rw [sig_eq (s := t) ⟨by linarith [ht.1], by linarith [ht.2]⟩] at this
      exact this.hasDerivWithinAt)
    (fun t _ => by rw [mem_ball_zero_iff, MD.norm_Sfl]; linarith)
    (by rw [h0, MD.Sfl_zero])

/-- Backward uniqueness: a `B_{R0}`-valued solution on `[0,1]` with `γ 1 = w` has `γ 0 = S⁻¹ w`. -/
theorem flow_unique_back {w : K} (hw : ‖w‖ < MD.R0 / 4) {γ : ℝ → K} (h1 : γ 1 = w)
    (hc : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hd : ∀ t ∈ Ioc (0 : ℝ) 1, HasDerivWithinAt γ (MD.Yf t (γ t)) (Iic t) t)
    (hm : ∀ t ∈ Ioc (0 : ℝ) 1, γ t ∈ ball (0 : K) MD.R0) :
    γ 0 = MD.Tinv w := by
  obtain ⟨Lc, hLc⟩ := MD.Yf_lipschitz
  have hR := MD.R0_pos
  have hT : ‖MD.Tinv w‖ ≤ MD.R0 / 4 := by rw [MD.norm_Tinv]; exact hw.le
  have hsfd : ∀ t, HasDerivAt (fun s => MD.Sfl s (MD.Tinv w)) (MD.Yf (sig t) (MD.Sfl t (MD.Tinv w))) t :=
    MD.Sfl_deriv hT
  have hcont : ContinuousOn (fun s => MD.Sfl s (MD.Tinv w)) (Icc (0 : ℝ) 1) :=
    fun s _ => (hsfd s).continuousAt.continuousWithinAt
  have := ODE_solution_unique_of_mem_Icc_left (v := MD.Yf) (s := fun _ => ball (0 : K) MD.R0) (K := Lc)
    (f := γ) (g := fun s => MD.Sfl s (MD.Tinv w)) (a := 0) (b := 1)
    (fun t ht => hLc t ⟨ht.1.le, ht.2⟩) hc hd hm hcont
    (fun t ht => by
      have := hsfd t
      rw [sig_eq (s := t) ⟨by linarith [ht.1], by linarith [ht.2]⟩] at this
      exact this.hasDerivWithinAt)
    (fun t _ => by rw [mem_ball_zero_iff, MD.norm_Sfl, MD.norm_Tinv]; linarith)
    (by rw [h1, MD.Sfl_one_Tinv])
  have h0 := this ⟨le_rfl, zero_le_one⟩
  simpa [MD.Sfl_zero] using h0

/-- The reversed flow `τ ↦ (Φ_{−τ}(w, 1)).1`; `Srev 1 = Tinv`. -/
def Srev (τ : ℝ) (w : K) : K := (MD.Fl (-τ) (w, 1)).1

theorem Srev_zero (w : K) : MD.Srev 0 w = w := by simp [Srev, MD.Fl_zero]

theorem Srev_one (w : K) : MD.Srev 1 w = MD.Tinv w := rfl

theorem Srev_deriv {w : K} (hw : ‖w‖ ≤ MD.R0 / 4) (τ : ℝ) :
    HasDerivAt (fun s => MD.Srev s w) (-(MD.Yf (sig (1 - τ)) (MD.Srev τ w))) τ := by
  have h := MD.Fl_fst_deriv (w, 1) (-τ)
  have hn : ‖(MD.Fl (-τ) (w, 1)).1‖ ≤ MD.R0 / 4 := by rw [MD.norm_Fl]; exact hw
  rw [MD.cutF_one hn, one_smul] at h
  have e2 : (MD.Fl (-τ) (w, 1)).2 = 1 - τ := by rw [MD.Fl_snd]; ring
  have hG : MD.Ghat (MD.Fl (-τ) (w, 1)) = MD.Yf (sig (1 - τ)) (MD.Srev τ w) := by
    change MD.Yf (sig (MD.Fl (-τ) (w, 1)).2) (MD.Fl (-τ) (w, 1)).1 = _
    rw [e2]; rfl
  rw [hG] at h
  have := h.scomp τ (hasDerivAt_neg τ)
  refine this.congr_deriv ?_
  simp

/-- The printed conclusions, for the explicit witnesses `(S_1, S_1⁻¹)`. -/
def CorrectsWith (Ω : K → Form) (r : ℝ) (Sm Si : K → K) (C : ℝ) : Prop :=
  0 ≤ C ∧
    (∀ z ∈ ball (0 : K) r, Sm z ∈ ball (0 : K) r ∧ Si z ∈ ball (0 : K) r) ∧
    (∀ z ∈ ball (0 : K) r, Si (Sm z) = z ∧ Sm (Si z) = z) ∧
    AnalyticOnNhd ℝ Sm (ball (0 : K) r) ∧ AnalyticOnNhd ℝ Si (ball (0 : K) r) ∧
    (∀ z ∈ ball (0 : K) r, ∀ a b : K, Ω (Sm z) (fderiv ℝ Sm z a) (fderiv ℝ Sm z b) = omegaF a b) ∧
    (∀ (n : ℤ), ∀ z ∈ ball (0 : K) r, q n (Sm z) = q n z) ∧
    (∀ z ∈ ball (0 : K) r, ‖Sm z - z‖ ≤ C * ‖z‖ ^ 3) ∧
    (∀ z ∈ ball (0 : K) r, ‖fderiv ℝ Sm z - 1‖ + ‖fderiv ℝ Si z - 1‖ ≤ C * ‖z‖ ^ 2)

/-- The explicit witnesses `(Sfl 1, Tinv)` satisfy the printed conclusions on `B_{R0/4}` (proof as in `reset_moser_of_data`, witnesses retained). -/
theorem sfl_corrects : ∃ C : ℝ, CorrectsWith S.Ω (MD.R0 / 4) (MD.Sfl 1) MD.Tinv C := by
  have hR0 := MD.R0_pos
  obtain ⟨κ, hκ, hv⟩ := MD.exists_var_bound
  have hB := MD.B_nonneg
  refine ⟨MD.B + 2 * κ * Real.exp (κ * MD.R0 ^ 2), by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hn := mem_ball_zero_iff.1 hz
    exact ⟨by rw [mem_ball_zero_iff, MD.norm_Sfl]; exact hn, by rw [mem_ball_zero_iff, MD.norm_Tinv]; exact hn⟩
  · intro z _
    exact ⟨MD.Tinv_Sfl_one z, MD.Sfl_one_Tinv z⟩
  · intro z hz
    exact MD.Sfl_one_analyticAt (mem_ball_zero_iff.1 hz)
  · intro z hz
    exact MD.Tinv_analyticAt (mem_ball_zero_iff.1 hz)
  · intro z hz a b
    exact MD.pullback (mem_ball_zero_iff.1 hz) a b
  · intro n z _
    exact MD.q_Sfl n 1 z
  · intro z hz
    have hn := mem_ball_zero_iff.1 hz
    refine (MD.norm_Sfl_sub_le hn).trans ?_
    have h3 : 0 ≤ ‖z‖ ^ 3 := by positivity
    have : MD.B ≤ MD.B + 2 * κ * Real.exp (κ * MD.R0 ^ 2) := by
      have : 0 ≤ 2 * κ * Real.exp (κ * MD.R0 ^ 2) := by positivity
      linarith
    exact mul_le_mul_of_nonneg_right this h3
  · intro z hz
    have hn := mem_ball_zero_iff.1 hz
    have hz2 : ‖z‖ ^ 2 ≤ MD.R0 ^ 2 := by
      have : ‖z‖ ≤ MD.R0 := by linarith
      nlinarith [norm_nonneg z]
    have hexp : Real.exp (κ * ‖z‖ ^ 2) ≤ Real.exp (κ * MD.R0 ^ 2) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hz2 hκ)
    have h1 : ‖Lam (fderiv ℝ (MD.Fl 1) (z, 0)) - 1‖ ≤ κ * ‖z‖ ^ 2 * Real.exp (κ * ‖z‖ ^ 2) := by
      have := hv (z, 0) (by simpa using hn) 1 (by simp) 1 ⟨zero_le_one, le_rfl⟩
      simpa using this
    have h2 : ‖Lam (fderiv ℝ (MD.Fl (-1)) (z, 1)) - 1‖ ≤ κ * ‖z‖ ^ 2 * Real.exp (κ * ‖z‖ ^ 2) := by
      have := hv (z, 1) (by simpa using hn) (-1) (by simp) 1 ⟨zero_le_one, le_rfl⟩
      simpa using this
    have e1 : fderiv ℝ (MD.Sfl 1) z = Lam (fderiv ℝ (MD.Fl 1) (z, 0)) := MD.DS_eq 1 z
    have e2 : fderiv ℝ MD.Tinv z = Lam (fderiv ℝ (MD.Fl (-1)) (z, 1)) := (MD.hasFDerivAt_Tinv z).fderiv
    rw [e1, e2]
    have hk : 0 ≤ κ * ‖z‖ ^ 2 := by positivity
    have h1' : ‖Lam (fderiv ℝ (MD.Fl 1) (z, 0)) - 1‖ ≤ κ * ‖z‖ ^ 2 * Real.exp (κ * MD.R0 ^ 2) :=
      h1.trans (mul_le_mul_of_nonneg_left hexp hk)
    have h2' : ‖Lam (fderiv ℝ (MD.Fl (-1)) (z, 1)) - 1‖ ≤ κ * ‖z‖ ^ 2 * Real.exp (κ * MD.R0 ^ 2) :=
      h2.trans (mul_le_mul_of_nonneg_left hexp hk)
    have hBz : 0 ≤ MD.B * ‖z‖ ^ 2 := by positivity
    nlinarith [h1', h2', hBz]

end MoserData

/-- The Moser field of the printed data: `Y_t(z) = Ycov (t (Ω_z − ω)) β⁰_z`, `β⁰ = β − df` (`LOCAL017Haar.beta0`), `f` the Haar primitive of the radial primitive `β`. -/
def PrintedHyp.moserY (P : PrintedHyp) (t : ℝ) (z : K) : K :=
  Ycov (t • (P.Ω z - omegaF)) (LOCAL017Haar.beta0 (betaR P.toHyp) z)

theorem PrintedHyp.moserY_eq_Yf (P : PrintedHyp) (B : PrintedBounds P) (t : ℝ) {z : K}
    (hz : z ∈ ball (0 : K) P.R) : P.moserY t z = (moserDataN P.toHyp B.toNative).Yf t z := by
  unfold PrintedHyp.moserY MoserData.Yf Dt
  rw [show P.toHyp.Ω z = P.Ω z from P.Om_eq hz]
  rfl

/-- The flow clause: `Sm = Φ_1` for the flow `Φ` of `Y_t` on `B_r` (`Φ_0 = id`, `∂_t Φ_t = Y_t ∘ Φ_t` for `t ∈ [0,1]`, norm conserved, unique among `B_{R0}`-valued solutions), and `Si = Ψ_1` for the
reversed flow `Ψ` (`∂_τ Ψ_τ = −Y_{1−τ} ∘ Ψ_τ`), with backward uniqueness (a `B_{R0}`-valued solution with `γ 1 = w` has `γ 0 = Si w`). -/
def MoserFlowSpec (Y : ℝ → K → K) (R0 r : ℝ) (Sm Si : K → K) : Prop :=
  ∃ Φ Ψ : ℝ → K → K,
    (∀ z ∈ ball (0 : K) r, Φ 0 z = z ∧ (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s => Φ s z) (Y t (Φ t z)) t) ∧
      ∀ t, ‖Φ t z‖ = ‖z‖) ∧
    (∀ z ∈ ball (0 : K) r, Sm z = Φ 1 z) ∧
    (∀ z ∈ ball (0 : K) r, ∀ γ : ℝ → K, γ 0 = z → ContinuousOn γ (Icc (0 : ℝ) 1) →
      (∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt γ (Y t (γ t)) (Ici t) t) →
      (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ ball (0 : K) R0) → ∀ t ∈ Icc (0 : ℝ) 1, γ t = Φ t z) ∧
    (∀ w ∈ ball (0 : K) r, Ψ 0 w = w ∧ ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s => Ψ s w) (-(Y (1 - τ) (Ψ τ w))) τ) ∧
    (∀ w ∈ ball (0 : K) r, Si w = Ψ 1 w) ∧
    (∀ w ∈ ball (0 : K) r, ∀ γ : ℝ → K, γ 1 = w → ContinuousOn γ (Icc (0 : ℝ) 1) →
      (∀ t ∈ Ioc (0 : ℝ) 1, HasDerivWithinAt γ (Y t (γ t)) (Iic t) t) →
      (∀ t ∈ Ioc (0 : ℝ) 1, γ t ∈ ball (0 : K) R0) → γ 0 = Si w)

/-- **`thm:reset-moser` (LOCAL-017) with the PROCEDURE clause.**  Same hypotheses and conclusions as `reset_moser_printed`, for the SAME witness `(Sm, Si)`, which is moreover the time-one map of the flow of the
Moser field `Y_t = Ycov(t(Ω − ω), β⁰)`, `β⁰ = β − df` (`P.moserY`), `Si` the reversed flow (`MoserFlowSpec`, on `B_r`, `r = moserRadius ρ M`, `R0 = 4r`). -/
theorem reset_moser_printed_flow (P : PrintedHyp) :
    Nonempty (PrintedBounds P) ∧
    ∀ B : PrintedBounds P,
      0 < moserRadius B.radius B.realConstant ∧ moserRadius B.radius B.realConstant ≤ P.R ∧
        ∃ Sm Si : K → K, ∃ C : ℝ,
          MoserData.CorrectsWith P.Ω (moserRadius B.radius B.realConstant) Sm Si C ∧
          MoserFlowSpec P.moserY (moserR0 B.radius B.realConstant) (moserRadius B.radius B.realConstant) Sm Si := by
  refine ⟨PrintedBounds.exists P, fun B => ?_⟩
  set N := B.toNative with hN
  set MD := moserDataN P.toHyp N with hMD
  have hR0 : MD.R0 = moserR0 B.radius B.realConstant := rfl
  have h0 := moserR0_pos P.toHyp N
  have hRle : moserR0 B.radius B.realConstant ≤ P.R := (moserR0_le_R P.toHyp N).trans B.ρR
  have hr : moserRadius B.radius B.realConstant = MD.R0 / 4 := by rw [moserRadius_eq]; rfl
  have hballR : ball (0 : K) MD.R0 ⊆ ball (0 : K) P.R := ball_subset_ball hRle
  refine ⟨by rw [hr]; exact div_pos MD.R0_pos (by norm_num), by rw [hr]; linarith [MD.R0_pos], MD.Sfl 1, MD.Tinv, ?_⟩
  obtain ⟨C, hC⟩ := MD.sfl_corrects
  refine ⟨C, ?_, ?_⟩
  · rw [hr]
    obtain ⟨hC0, hmem, hinv, han, hanI, hpull, hq, h3, h2⟩ := hC
    refine ⟨hC0, hmem, hinv, han, hanI, ?_, hq, h3, h2⟩
    intro z hz a b
    have := hpull z hz a b
    have hS : MD.Sfl 1 z ∈ ball (0 : K) P.R :=
      hballR (ball_subset_ball (by linarith [MD.R0_pos]) ((hmem z hz).1))
    rwa [show P.toHyp.Ω (MD.Sfl 1 z) = P.Ω (MD.Sfl 1 z) from P.Om_eq hS] at this
  · rw [hr, ← hR0]
    have hY : ∀ t (u : K), u ∈ ball (0 : K) MD.R0 → P.moserY t u = MD.Yf t u :=
      fun t u hu => P.moserY_eq_Yf B t (hballR hu)
    refine ⟨fun t z => MD.Sfl t z, fun τ w => MD.Srev τ w, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro z hz
      have hzn := mem_ball_zero_iff.1 hz
      have hz' : ‖z‖ ≤ MD.R0 / 4 := hzn.le
      refine ⟨MD.Sfl_zero z, fun t ht => ?_, fun t => MD.norm_Sfl t z⟩
      have := MD.Sfl_deriv hz' t
      rw [sig_eq (s := t) ⟨by linarith [ht.1], by linarith [ht.2]⟩] at this
      rw [hY t _ (by rw [mem_ball_zero_iff, MD.norm_Sfl]; linarith [MD.R0_pos])]
      exact this
    · intro z _; rfl
    · intro z hz γ h0γ hc hd hm t ht
      have hzn := mem_ball_zero_iff.1 hz
      refine MD.flow_unique hzn h0γ hc (fun s hs => ?_) hm t ht
      rw [← hY s _ (hm s hs)]
      exact hd s hs
    · intro w hw
      have hwn := mem_ball_zero_iff.1 hw
      refine ⟨MD.Srev_zero w, fun τ hτ => ?_⟩
      have := MD.Srev_deriv hwn.le τ
      rw [sig_eq (s := 1 - τ) ⟨by linarith [hτ.2], by linarith [hτ.1]⟩] at this
      have hnorm : ‖MD.Srev τ w‖ = ‖w‖ := MD.norm_Fl (w, 1) (-τ)
      rw [hY _ _ (by rw [mem_ball_zero_iff, hnorm]; linarith [MD.R0_pos])]
      exact this
    · intro w _; rfl
    · intro w hw γ h1 hc hd hm
      have hwn := mem_ball_zero_iff.1 hw
      refine MD.flow_unique_back hwn h1 hc (fun s hs => ?_) hm
      rw [← hY s _ (hm s hs)]
      exact hd s hs

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.MoserData.Yf_lipschitz
#print axioms QuantumNLS.ResetMoser.MoserData.flow_unique
#print axioms QuantumNLS.ResetMoser.MoserData.flow_unique_back
#print axioms QuantumNLS.ResetMoser.MoserData.Srev_deriv
#print axioms QuantumNLS.ResetMoser.MoserData.sfl_corrects
#print axioms QuantumNLS.ResetMoser.reset_moser_printed_flow
