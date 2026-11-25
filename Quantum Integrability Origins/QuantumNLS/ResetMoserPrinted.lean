import QuantumNLS.ResetMoserRadius
import QuantumNLS.ResetMoserHypWitness
import QuantumNLS.ResetMoserAngleCube

/-!
# `thm:reset-moser` (LOCAL-017): the printed ball-local hypotheses, the bridge to `Hyp`, and the final theorem

Source: `symplectic_correction.tex:25`, Theorem `thm:reset-moser`: "Suppose that `Ω` is a real-analytic closed two-form on an open ball `B_R ⊂ ℋ`.  Suppose that its values are bounded alternating bilinear forms, analytically in the full
operator norm, and `Ω_z = ω + O(‖z‖²)`, `‖Ω_z − ω‖ < 1`.  Assume that the `q_n` pairwise Poisson commute for `Ω`, and their Hamiltonian flows exist on `B_R` and have time `2π` equal to the identity.  Then, on a smaller
ball `B_r` whose radius depends only on the analytic operator bounds for `Ω`, ... a real-analytic diffeomorphism `S : B_r → B_r` such that `S^*Ω = ω`, `q_n ∘ S = q_n`, `S(z) = z + O(‖z‖³)`.  Both `S` and `S^{-1}` have bounded
full Hilbert differentials ... `‖DS(z) − 1‖ + ‖DS^{-1}(z) − 1‖ ≤ C‖z‖²`."  ("Hamiltonian vector fields are defined by `ι_{X_f} Ω = df`.")

* `PrintedHyp`: the printed hypotheses with EVERY clause ball-local (`z ∈ B_R` only), `Ω_z − ω = O(‖z‖²)` as `z → 0` (an `IsBigO` at `0`, not a global bound), the Hamiltonian fields `X_n` given as DATA
  with the defining identity `ι_{X_n} Ω = dq_n` on `B_R` (not the Neumann-series construction), and the flows `φ_n` constrained only for starting points in `B_R`.
* `toHyp P : Hyp`: Ω is replaced by `ω` outside `B_R` and the flows by the identity outside `B_R` (so the global clauses of `Hyp` hold); `toHyp_Ω`, `toHyp_φ`: it has the same `Ω`, `φ` on `B_R`;
  `Xn_toHyp`: the Neumann-series field of `Hyp` equals the printed `X_n` on `B_R` (non-degeneracy of `Ω_z`); `Ω_quad` is derived from the local `O(‖z‖²)` and `‖Ω_z − ω‖ < 1`.
* `PrintedBounds P`: the analytic operator bounds of the printed `Ω`, stated in terms of `P.Ω` only: radius `ρ` of a holomorphic extension `G` of `Ω − ω` to the complex ball (`AnalyticOnNhd ℂ`), `‖G‖ ≤ C‖z‖²`, `‖DG‖ ≤ K`,
  real constant `M` of eq:reset-moser-form-bounds on `B_ρ`;  `PrintedBounds.toNative : PrintedBounds P → OperatorBounds (toHyp P)` (the radial primitive of `G` is holomorphic with the cubic bound) and `PrintedBounds.exists` (`Nonempty`).
* `reset_moser_printed`: THE theorem: printed hypotheses ⇒ printed conclusions, with `r = moserRadius ρ M = min (ρ/2, 1/(2(M+1)))/4` for every bound datum.
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

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.RealAnalyticDef QuantumNLS.LOCAL017SourceR19
  QuantumNLS.Ext025A4BanachComplexification

/-- The printed hypotheses of `thm:reset-moser`, ball-local. -/
structure PrintedHyp where
  R : ℝ
  R_pos : 0 < R
  /-- the two-form; only its values on `B_R` are constrained -/
  Ω : K → Form
  Ω_alt : ∀ z ∈ ball (0 : K) R, ∀ v w, Ω z v w = -Ω z w v
  Ω_analytic : ∀ z ∈ ball (0 : K) R, IsRealAnalyticPoly Ω z
  Ω_closed : ∀ z ∈ ball (0 : K) R, ∀ a b c : K,
    fderiv ℝ Ω z a b c + fderiv ℝ Ω z b c a + fderiv ℝ Ω z c a b = 0
  /-- `Ω_z = ω + O(‖z‖²)` as `z → 0` -/
  Ω_quad : (fun z => Ω z - omegaF) =O[𝓝 (0 : K)] (fun z => ‖z‖ ^ 2)
  Ω_lt : ∀ z ∈ ball (0 : K) R, ‖Ω z - omegaF‖ < 1
  /-- the Hamiltonian field of `q_n`: `ι_{X_n} Ω = dq_n` on `B_R` -/
  X : ℤ → K → K
  X_spec : ∀ n, ∀ z ∈ ball (0 : K) R, ∀ h : K, Ω z (X n z) h = fderiv ℝ (q n) z h
  /-- the Hamiltonian flows, for starting points in `B_R` -/
  φ : ℤ → ℝ → K → K
  φ_zero : ∀ n, ∀ z ∈ ball (0 : K) R, φ n 0 z = z
  φ_mem : ∀ n, ∀ z ∈ ball (0 : K) R, ∀ t, φ n t z ∈ ball (0 : K) R
  φ_deriv : ∀ n, ∀ z ∈ ball (0 : K) R, ∀ t, HasDerivAt (fun s => φ n s z) (X n (φ n t z)) t
  φ_period : ∀ n, ∀ z ∈ ball (0 : K) R, φ n (2 * Real.pi) z = z
  /-- pairwise Poisson commutation of the `q_n` for `Ω` -/
  poisson : ∀ m n, ∀ z ∈ ball (0 : K) R, Ω z (X m z) (X n z) = 0

namespace PrintedHyp

variable (P : PrintedHyp)

/-- `Ω` on `B_R`, `ω` outside. -/
def Om (z : K) : Form := if z ∈ ball (0 : K) P.R then P.Ω z else omegaF

theorem Om_eq {z : K} (hz : z ∈ ball (0 : K) P.R) : P.Om z = P.Ω z := by simp [Om, hz]

theorem Om_ev {z : K} (hz : z ∈ ball (0 : K) P.R) : P.Om =ᶠ[𝓝 z] P.Ω := by
  filter_upwards [isOpen_ball.mem_nhds hz] with y hy
  exact P.Om_eq hy

theorem fderiv_Om {z : K} (hz : z ∈ ball (0 : K) P.R) : fderiv ℝ P.Om z = fderiv ℝ P.Ω z :=
  (P.Om_ev hz).fderiv_eq

theorem fderiv2_Om {z : K} (hz : z ∈ ball (0 : K) P.R) :
    fderiv ℝ (fderiv ℝ P.Om) z = fderiv ℝ (fderiv ℝ P.Ω) z := by
  have : fderiv ℝ P.Om =ᶠ[𝓝 z] fderiv ℝ P.Ω := by
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy
    exact P.fderiv_Om hy
  exact this.fderiv_eq

/-- Non-degeneracy of `Ω_z` for `‖Ω_z − ω‖ < 1`. -/
theorem eq_zero_of_pairing {D : Form} (hD : ‖D - omegaF‖ < 1) {v : K} (h : ∀ w, D v w = 0) : v = 0 := by
  by_contra hv
  have hv0 : 0 < ‖v‖ := norm_pos_iff.2 hv
  have h1 := h (Complex.I • v)
  have h2 : (D - omegaF) v (Complex.I • v) = -(2 * ‖v‖ ^ 2) := by
    have : (D - omegaF) v (Complex.I • v) = D v (Complex.I • v) - omega v (Complex.I • v) := by
      simp [omegaF_apply]
    rw [this, h1, omega_I_smul]; ring
  have h3 : ‖(D - omegaF) v (Complex.I • v)‖ ≤ ‖D - omegaF‖ * ‖v‖ * ‖Complex.I • v‖ :=
    ((D - omegaF) v).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right ((D - omegaF).le_opNorm v) (norm_nonneg _))
  rw [h2, norm_smul, Complex.norm_I, one_mul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)] at h3
  have : ‖D - omegaF‖ * ‖v‖ * ‖v‖ < ‖v‖ * ‖v‖ := by
    have := mul_lt_mul_of_pos_right hD hv0
    nlinarith
  nlinarith

theorem X_eq_Xn {n : ℤ} {z : K} (hz : z ∈ ball (0 : K) P.R) : Xn P.Om n z = P.X n z := by
  have hD : ‖P.Om z - omegaF‖ < 1 := by rw [P.Om_eq hz]; exact P.Ω_lt z hz
  have h1 := Xn_spec hD n
  have : P.X n z - Xn P.Om n z = 0 := by
    refine eq_zero_of_pairing (D := P.Om z) hD fun w => ?_
    simp only [map_sub, ContinuousLinearMap.sub_apply, h1]
    rw [P.Om_eq hz, P.X_spec n z hz, sub_self]
  exact (sub_eq_zero.1 this).symm

theorem quad_global : ∃ C : ℝ, ∀ z ∈ ball (0 : K) P.R, ‖P.Ω z - omegaF‖ ≤ C * ‖z‖ ^ 2 := by
  obtain ⟨C0, hC0, hev⟩ := P.Ω_quad.exists_pos
  obtain ⟨ε, hε, hε'⟩ := Metric.eventually_nhds_iff.1 hev.bound
  refine ⟨max C0 (1 / ε ^ 2), fun z hz => ?_⟩
  by_cases hzε : ‖z‖ < ε
  · have := @hε' z (by rwa [dist_zero_right])
    simp only [norm_pow, norm_norm] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · replace hzε := not_lt.1 hzε
    have h1 := P.Ω_lt z hz
    have h2 : (1 : ℝ) ≤ (1 / ε ^ 2) * ‖z‖ ^ 2 := by
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
      nlinarith
    exact (h1.le.trans h2).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end PrintedHyp

theorem isRealAnalyticPoly_congr {f g : K → Form} {x : K} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ y, ‖y - x‖ < ε → f y = g y) (hf : IsRealAnalyticPoly f x) : IsRealAnalyticPoly g x := by
  obtain ⟨P, hP, r, hr, hconv⟩ := hf
  refine ⟨P, hP, min r ε, lt_min hr hε, fun y hy => ?_⟩
  have h1 := hconv y (lt_of_lt_of_le hy (min_le_left _ _))
  rw [h y (lt_of_lt_of_le hy (min_le_right _ _))] at h1
  exact h1

/-- **The bridge**: a `Hyp` datum from the printed ball-local hypotheses. -/
def PrintedHyp.toHyp (P : PrintedHyp) : Hyp where
  R := P.R
  R_pos := P.R_pos
  Ω := P.Om
  Ω_alt := fun z v w => by
    by_cases hz : z ∈ ball (0 : K) P.R
    · rw [P.Om_eq hz]; exact P.Ω_alt z hz v w
    · simp only [PrintedHyp.Om, hz, if_false]; exact omegaF_alt v w
  Ω_analytic := fun z hz => by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_ball z hz
    refine isRealAnalyticPoly_congr (f := P.Ω) hε (fun y hy => ?_) (P.Ω_analytic z hz)
    exact (P.Om_eq (hball (by simpa [dist_eq_norm] using hy))).symm
  Ω_closed := fun z hz a b c => by
    rw [P.fderiv_Om hz]; exact P.Ω_closed z hz a b c
  Ω_quad := by
    obtain ⟨C, hC⟩ := P.quad_global
    exact ⟨C, fun z hz => by rw [P.Om_eq hz]; exact hC z hz⟩
  Ω_lt := fun z hz => by rw [P.Om_eq hz]; exact P.Ω_lt z hz
  φ := fun n t z => if z ∈ ball (0 : K) P.R then P.φ n t z else z
  φ_zero := fun n z => by
    by_cases hz : z ∈ ball (0 : K) P.R
    · simp only [hz, if_true]; exact P.φ_zero n z hz
    · simp [hz]
  φ_mem := fun n z hz t => by simp only [hz, if_true]; exact P.φ_mem n z hz t
  φ_deriv := fun n z hz t => by
    simp only [hz, if_true]
    have := P.φ_deriv n z hz t
    rwa [← P.X_eq_Xn (P.φ_mem n z hz t)] at this
  φ_period := fun n z hz => by simp only [hz, if_true]; exact P.φ_period n z hz
  poisson := fun m n z hz => by
    rw [P.X_eq_Xn hz, P.X_eq_Xn hz, P.Om_eq hz]
    exact P.poisson m n z hz

theorem PrintedHyp.toHyp_Ω (P : PrintedHyp) {z : K} (hz : z ∈ ball (0 : K) P.R) : P.toHyp.Ω z = P.Ω z :=
  P.Om_eq hz

theorem PrintedHyp.toHyp_φ (P : PrintedHyp) (n : ℤ) (t : ℝ) {z : K} (hz : z ∈ ball (0 : K) P.R) :
    P.toHyp.φ n t z = P.φ n t z := by
  change (if z ∈ ball (0 : K) P.R then P.φ n t z else z) = _
  simp [hz]

/-- The radial primitive `β_z = ∫₀¹ t (Ω_{tz} − ω)(z, ·) dt` of the printed form. -/
def PrintedHyp.betaP (P : PrintedHyp) (z : K) : Cov := ∫ t in (0 : ℝ)..1, t • ((P.Ω (t • z) - omegaF) z)

theorem PrintedHyp.betaR_toHyp (P : PrintedHyp) {z : K} (hz : z ∈ ball (0 : K) P.R) :
    betaR P.toHyp z = P.betaP z := by
  unfold betaR PrintedHyp.betaP
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [uIcc_of_le zero_le_one] at ht
  simp only [Dl]
  rw [show P.toHyp.Ω (t • z) = P.Ω (t • z) from P.Om_eq (scale_mem' hz ht)]

/-- Real bounds of the printed `Ω` on `B_ρ` from the `Loc` bundle of the bridged datum, and conversely. -/
theorem PrintedHyp.loc_to (P : PrintedHyp) {ρ M : ℝ} (hL : Loc P.toHyp ρ M) :
    (∀ z ∈ ball (0 : K) ρ, ‖P.Ω z - omegaF‖ ≤ M * ‖z‖ ^ 2) ∧
    (∀ z ∈ ball (0 : K) ρ, ‖fderiv ℝ P.Ω z‖ ≤ M * ‖z‖) ∧
    (∀ z ∈ ball (0 : K) ρ, ‖fderiv ℝ (fderiv ℝ P.Ω) z‖ ≤ M) := by
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · have := hL.b2 z hz
    change ‖P.Om z - omegaF‖ ≤ _ at this
    rwa [P.Om_eq (ball_subset_ball hL.ρR hz)] at this
  · have := hL.b1 z hz
    change ‖fderiv ℝ P.Om z‖ ≤ _ at this
    rwa [P.fderiv_Om (ball_subset_ball hL.ρR hz)] at this
  · have := hL.b0 z hz
    change ‖fderiv ℝ (fderiv ℝ P.Om) z‖ ≤ _ at this
    rwa [P.fderiv2_Om (ball_subset_ball hL.ρR hz)] at this

theorem PrintedHyp.loc_of (P : PrintedHyp) {ρ M : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ P.R) (hM : 0 ≤ M)
    (h2 : ∀ z ∈ ball (0 : K) ρ, ‖P.Ω z - omegaF‖ ≤ M * ‖z‖ ^ 2)
    (h1 : ∀ z ∈ ball (0 : K) ρ, ‖fderiv ℝ P.Ω z‖ ≤ M * ‖z‖)
    (h0 : ∀ z ∈ ball (0 : K) ρ, ‖fderiv ℝ (fderiv ℝ P.Ω) z‖ ≤ M) : Loc P.toHyp ρ M where
  ρpos := hρ
  ρR := hρR
  M0 := hM
  b2 := fun z hz => by
    change ‖P.Om z - omegaF‖ ≤ _
    rw [P.Om_eq (ball_subset_ball hρR hz)]; exact h2 z hz
  b1 := fun z hz => by
    change ‖fderiv ℝ P.Om z‖ ≤ _
    rw [P.fderiv_Om (ball_subset_ball hρR hz)]; exact h1 z hz
  b0 := fun z hz => by
    change ‖fderiv ℝ (fderiv ℝ P.Om) z‖ ≤ _
    rw [P.fderiv2_Om (ball_subset_ball hρR hz)]; exact h0 z hz

/-- The analytic operator bounds of the printed `Ω`, in terms of `P.Ω` only: the radius `ρ` of the holomorphic extension `G` of `Ω − ω` to the complex ball `B^ℂ_ρ` (a convergent power series
there, `AnalyticOnNhd ℂ`), the uniform bounds `‖G‖ ≤ C‖z‖²` and `‖DG‖ ≤ K` of the extension (shrinking the ball gives them), and the real constant `M` of
`‖Ω_z − ω‖ ≤ M‖z‖²`, `‖DΩ_z‖ ≤ M‖z‖`, `‖D²Ω_z‖ ≤ M` on `B_ρ` (eq:reset-moser-form-bounds). -/
structure PrintedBounds (P : PrintedHyp) where
  radius : ℝ
  realConstant : ℝ
  complexConstant : ℝ
  derivConstant : ℝ
  ρpos : 0 < radius
  ρR : radius ≤ P.R
  M0 : 0 ≤ realConstant
  b2 : ∀ z ∈ ball (0 : K) radius, ‖P.Ω z - omegaF‖ ≤ realConstant * ‖z‖ ^ 2
  b1 : ∀ z ∈ ball (0 : K) radius, ‖fderiv ℝ P.Ω z‖ ≤ realConstant * ‖z‖
  b0 : ∀ z ∈ ball (0 : K) radius, ‖fderiv ℝ (fderiv ℝ P.Ω) z‖ ≤ realConstant
  C0 : 0 ≤ complexConstant
  K0 : 0 ≤ derivConstant
  G : CH → CForm
  hG : AnalyticOnNhd ℂ G (ball 0 radius)
  hGb : ∀ z ∈ ball (0 : CH) radius, ‖G z‖ ≤ complexConstant * ‖z‖ ^ 2
  hGd : ∀ z ∈ ball (0 : CH) radius, ‖fderiv ℂ G z‖ ≤ derivConstant
  hGreal : ∀ x ∈ ball (0 : K) radius, ∀ v w, G (Cx.ι x) (Cx.ι v) (Cx.ι w) = (((P.Ω x - omegaF) v w : ℝ) : ℂ)

def PrintedBounds.toNative {P : PrintedHyp} (B : PrintedBounds P) : OperatorBounds P.toHyp where
  radius := B.radius
  realConstant := B.realConstant
  complexConstant := B.complexConstant
  loc := P.loc_of B.ρpos B.ρR B.M0 B.b2 B.b1 B.b0
  constant_nonneg := B.C0
  form := B.G
  holomorphic := radial_holomorphic B.ρpos B.C0 B.K0 B.hG B.hGb B.hGd
  cubic := fun _ hz => radial_cubic B.C0 B.hGb hz
  real_slice := fun z hz h =>
    radial_real P.toHyp (P.loc_of B.ρpos B.ρR B.M0 B.b2 B.b1 B.b0) B.hG.continuousOn
      (fun x hx v w => by
        rw [B.hGreal x hx v w]
        have : P.toHyp.Ω x = P.Ω x := P.Om_eq (ball_subset_ball B.ρR hx)
        simp [Dl, this]) hz h

theorem PrintedBounds.exists (P : PrintedHyp) : Nonempty (PrintedBounds P) := by
  obtain ⟨R0, hR0, _, C, hC, G, hg, hb, he⟩ := source_complex_form P.toHyp
  obtain ⟨r, M, hL⟩ := P.toHyp.exists_loc
  have hdc : ContinuousAt (fderiv ℂ G) 0 :=
    ((hg 0 (mem_ball_self hR0)).contDiffAt (n := 1)).continuousAt_fderiv (by norm_num)
  obtain ⟨d, hd, hdb⟩ := Metric.continuousAt_iff.mp hdc 1 one_pos
  let R := min (r / 2) (min R0 d)
  have hR : 0 < R := lt_min (half_pos hL.ρpos) (lt_min hR0 hd)
  have hRR0 : R ≤ R0 := (min_le_right _ _).trans (min_le_left _ _)
  have hRd : R ≤ d := (min_le_right _ _).trans (min_le_right _ _)
  have hL' := loc_mono hL hR ((min_le_left _ _).trans (half_le_self hL.ρpos.le))
  obtain ⟨hb2, hb1, hb0⟩ := P.loc_to hL'
  let K1 := ‖fderiv ℂ G 0‖ + 1
  have hK : 0 ≤ K1 := by dsimp [K1]; positivity
  have hD : ∀ z ∈ ball (0 : CH) R, ‖fderiv ℂ G z‖ ≤ K1 := by
    intro z hz
    have hh := hdb ((ball_subset_ball hRd) hz)
    rw [dist_eq_norm] at hh
    have hh' := norm_sub_norm_le (fderiv ℂ G z) (fderiv ℂ G 0)
    dsimp [K1]
    linarith
  refine ⟨{ radius := R, realConstant := M, complexConstant := C, derivConstant := K1
            ρpos := hR, ρR := hL'.ρR, M0 := hL'.M0, b2 := hb2, b1 := hb1, b0 := hb0
            C0 := hC, K0 := hK, G := G, hG := hg.mono (ball_subset_ball hRR0)
            hGb := fun z hz => hb z (ball_subset_ball hRR0 hz), hGd := hD, hGreal := ?_ }⟩
  intro x hx v w
  have h1 := he x (ball_subset_ball hRR0 hx) v w
  have : P.toHyp.Ω x = P.Ω x := P.Om_eq (ball_subset_ball hL'.ρR hx)
  rw [h1]
  simp [Dl, this]

/-- Conversely every `Hyp` datum satisfies the printed ball-local hypotheses (with `X_n` the Neumann-series Hamiltonian field): so `Hyp` and `PrintedHyp` carry the same information on `B_R`. -/
def Hyp.toPrinted (S : Hyp) : PrintedHyp where
  R := S.R
  R_pos := S.R_pos
  Ω := S.Ω
  Ω_alt := fun z _ => S.Ω_alt z
  Ω_analytic := S.Ω_analytic
  Ω_closed := S.Ω_closed
  Ω_quad := by
    obtain ⟨C, hC⟩ := S.Ω_quad
    refine IsBigO.of_bound C ?_
    filter_upwards [ball_mem_nhds (0 : K) S.R_pos] with z hz
    simpa using hC z hz
  Ω_lt := S.Ω_lt
  X := Xn S.Ω
  X_spec := fun n z hz h => Xn_spec (S.Ω_lt z hz) n h
  φ := S.φ
  φ_zero := fun n z _ => S.φ_zero n z
  φ_mem := S.φ_mem
  φ_deriv := S.φ_deriv
  φ_period := S.φ_period
  poisson := S.poisson

/-- The printed hypotheses are satisfiable (the constant form `Ω = ω`), so `reset_moser_printed` is not vacuous. -/
def printedWitness : PrintedHyp := hypWitness.toPrinted

/-- The Haar primitive `f` of the construction (`β⁰ = β − df`, `β⁰ = LOCAL017Haar.beta0 (betaR (toHyp P))` is the Moser covector of `moserDataN`; `betaR (toHyp P) = P.betaP` on `B_R`, `betaR_toHyp`), on `B_ρ`,
in the source's angle-cube form (eq:reset-haar-primitive): `f(z) = −∫ ∫₀¹ β_{R_{tθ}z}(iΘ R_{tθ}z) dt dμ(θ)`, `μ` = product normalized Lebesgue measure on `[−π, π]^ℤ`, `β` the radial primitive of the printed `Ω`. -/
theorem PrintedHyp.haar_primitive_angle_cube (P : PrintedHyp) (B : PrintedBounds P) {z : K}
    (hz : z ∈ ball (0 : K) B.radius) :
    LOCAL017Haar.primitive (betaR P.toHyp) z =
      -∫ θ, (∫ t in (0 : ℝ)..1, betaR P.toHyp (LOCAL017Haar.Rot θ t z)
        (Ext025B7LocalPath.velocity θ (LOCAL017Haar.Rot θ t z))) ∂LOCAL017Haar.angleCube :=
  LOCAL017Haar.primitive_cube_interval (R := B.radius) (betaR P.toHyp)
    (fun _ hy => (betaR_hasFDerivAt P.toHyp B.toNative.loc hy).continuousAt.continuousWithinAt) hz

/-- The printed conclusions of `thm:reset-moser` on `B_r`, for the two-form `Ω`. -/
def Corrects (Ω : K → Form) (r : ℝ) : Prop :=
  ∃ Sm Si : K → K, ∃ C : ℝ, 0 ≤ C ∧
    (∀ z ∈ ball (0 : K) r, Sm z ∈ ball (0 : K) r ∧ Si z ∈ ball (0 : K) r) ∧
    (∀ z ∈ ball (0 : K) r, Si (Sm z) = z ∧ Sm (Si z) = z) ∧
    AnalyticOnNhd ℝ Sm (ball (0 : K) r) ∧ AnalyticOnNhd ℝ Si (ball (0 : K) r) ∧
    (∀ z ∈ ball (0 : K) r, ∀ a b : K, Ω (Sm z) (fderiv ℝ Sm z a) (fderiv ℝ Sm z b) = omegaF a b) ∧
    (∀ (n : ℤ), ∀ z ∈ ball (0 : K) r, q n (Sm z) = q n z) ∧
    (∀ z ∈ ball (0 : K) r, ‖Sm z - z‖ ≤ C * ‖z‖ ^ 3) ∧
    (∀ z ∈ ball (0 : K) r, ‖fderiv ℝ Sm z - 1‖ + ‖fderiv ℝ Si z - 1‖ ≤ C * ‖z‖ ^ 2)

/-- **`thm:reset-moser` (LOCAL-017), from the printed ball-local hypotheses.**  Under the printed hypotheses `P` the analytic operator bounds of `Ω` exist, and for EVERY datum `B` of
analytic operator bounds, on the ball `B_r`, `r = moserRadius B.radius B.realConstant = min (ρ/2, 1/(2(M+1)))/4` (an explicit function of the bounds `(ρ, M)` alone, `0 < r ≤ R`), there is a
real-analytic diffeomorphism `S : B_r → B_r` (with inverse `S⁻¹`) with `S^*Ω = ω`, `q_n ∘ S = q_n` for all `n ∈ ℤ`, `S(z) = z + O(‖z‖³)`, and `‖DS(z) − 1‖ + ‖DS⁻¹(z) − 1‖ ≤ C‖z‖²`
(full Hilbert operator norms). -/
theorem reset_moser_printed (P : PrintedHyp) :
    Nonempty (PrintedBounds P) ∧
    ∀ B : PrintedBounds P,
      0 < moserRadius B.radius B.realConstant ∧ moserRadius B.radius B.realConstant ≤ P.R ∧
        Corrects P.Ω (moserRadius B.radius B.realConstant) := by
  refine ⟨PrintedBounds.exists P, fun B => ?_⟩
  obtain ⟨h0, hR, Sm, Si, C, hC, hmem, hinv, han, hanI, hpull, hq, h3, h2⟩ :=
    reset_moser_radius P.toHyp B.toNative
  have hsub : ball (0 : K) (moserRadius B.radius B.realConstant) ⊆ ball (0 : K) P.R :=
    ball_subset_ball hR
  refine ⟨h0, hR, Sm, Si, C, hC, hmem, hinv, han, hanI, ?_, hq, h3, h2⟩
  intro z hz a b
  have := hpull z hz a b
  have hS : Sm z ∈ ball (0 : K) P.R := hsub (hmem z hz).1
  rwa [show P.toHyp.Ω (Sm z) = P.Ω (Sm z) from P.Om_eq hS] at this

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.PrintedHyp.toHyp
#print axioms QuantumNLS.ResetMoser.PrintedHyp.X_eq_Xn
#print axioms QuantumNLS.ResetMoser.PrintedHyp.quad_global
#print axioms QuantumNLS.ResetMoser.PrintedBounds.toNative
#print axioms QuantumNLS.ResetMoser.PrintedBounds.exists
#print axioms QuantumNLS.ResetMoser.Hyp.toPrinted
#print axioms QuantumNLS.ResetMoser.printedWitness
#print axioms QuantumNLS.ResetMoser.PrintedHyp.haar_primitive_angle_cube
#print axioms QuantumNLS.ResetMoser.reset_moser_printed
