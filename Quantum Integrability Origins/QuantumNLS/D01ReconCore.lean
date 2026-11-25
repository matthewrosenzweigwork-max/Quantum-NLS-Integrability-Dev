import QuantumNLS.TerraMultiRound18Flow

/-!
# `thm:global-D01-reconstruction` (R-701613DA), part 1: the global chart `Φ`, its inverse `Ψ`, and the exact identities

Source: `source-text/chapters/global/liouville_reconstruction.tex`: Theorem `thm:global-D01-reconstruction` (line 59) and the proof of the theorem (lines 296-382): equations
`(eq:global-D01-local-contraction)` `φ(F_{-s}u) = e^{-s/2} φ(u)`, `(eq:global-D01-forward)` `Φ(u) = e^{t/2} φ(F_{-t}u)`, `(eq:global-D01-inverse)` `Ψ(z) = F_t(φ^{-1}(e^{-t/2} z))`, the independence of `t`,
`|Φ_n(u)|² = e^t I_n(F_{-t}u) = I_n(u)`, `‖Φ(u)‖ = ‖u‖`, `Ψ∘Φ = id`, `Φ∘Ψ = id`, and `I(H) = ℓ¹_+`.

Read-only inputs: `D01LocalPrimitive` (R-81E9AAB6, accepted: `Hyp`, `Hyp.Dphi_Y`, `Hyp.norm_phi`, ...), and terra_multi's frozen flow `TerraMultiRound18Flow` (`flow`, `flow_spec`, `flow_add`, `flow_inverse`, `flow_action_mass`: the complete flow of `Y = W⁻¹ᾱ`, unconditional).
Nothing here uses the open GP-04 premise: the derivative-dependent parts (analyticity, symplecticity, `Φ^*ᾱ = ᾱ`) are in `D01ReconAnalytic` and carry `GP04CompactLocalAnalyticity` as a named hypothesis.

* `contr`: `φ(F_{-s}u) = e^{-s/2} φ(u)` for `u ∈ B_ε(H)`, `s ≥ 0` (as printed, "uniqueness of the scalar linear equation": `e^{s/2} φ(F_{-s}u)` has zero derivative);
* `Phi`, `Psi`: the printed formulas with the explicit admissible time `tOf r = 2 log(1 + 2r/ε)`;
* `Phi_eq`, `Psi_eq`: independence of the admissible time;
* `q_Phi`, `norm_Phi`, `Psi_Phi`, `Phi_Psi`, `act_surj`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology
open Filter Set

namespace QuantumNLS.D01Reconstruction

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.TerraMultiRound18Flow

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Hyp H)

/-! ## 1. Norms along the flow -/

theorem norm_flow (t : ℝ) (u : H) : ‖flow S t u‖ = Real.exp (t / 2) * ‖u‖ := by
  have hs := (flow_action_mass S t u).2
  have he : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hp : 0 ≤ Real.exp (t / 2) * ‖u‖ := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have hn := norm_nonneg (flow S t u)
  have h2 : ‖flow S t u‖ ^ 2 = (Real.exp (t / 2) * ‖u‖) ^ 2 := by
    rw [hs, mul_pow, he]
  exact (sq_eq_sq₀ hn hp).mp h2

theorem flow_mem {u : H} {t : ℝ} (h : Real.exp (t / 2) * ‖u‖ < S.ε) : flow S t u ∈ S.B := by
  rw [mem_ball_zero_iff, norm_flow]
  exact h

theorem flow_zero (u : H) : flow S 0 u = u := (flow_spec S u).1

theorem half_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (z : E) :
    (2⁻¹ : ℂ) • z = (2⁻¹ : ℝ) • z := by
  have : (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) := by simp
  rw [this]
  exact Complex.coe_smul _ _

/-! ## 2. The exact local contraction (`eq:global-D01-local-contraction`) -/

theorem contr {u : H} (hu : u ∈ S.B) {s : ℝ} (hs : 0 ≤ s) :
    S.phi (flow S (-s) u) = Real.exp (-s / 2) • S.phi u := by
  have hu' : ‖u‖ < S.ε := by simpa using hu
  have hball : ∀ x : ℝ, 0 ≤ x → flow S (-x) u ∈ S.B := fun x hx => by
    apply flow_mem
    have h1 : Real.exp (-x / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    calc Real.exp (-x / 2) * ‖u‖ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ < S.ε := by rw [one_mul]; exact hu'
  set g : ℝ → K := fun x => Real.exp (x / 2) • S.phi (flow S (-x) u) with hg
  have hder : ∀ x : ℝ, 0 ≤ x → HasDerivAt g 0 x := by
    intro x hx
    have hv := hball x hx
    have h1 : HasDerivAt (fun y : ℝ => flow S (-y) u) ((-1 : ℝ) • S.Y (flow S (-x) u)) x :=
      ((flow_spec S u).2 (-x)).scomp x (hasDerivAt_neg x)
    have h2 : HasDerivAt (fun y : ℝ => S.phi (flow S (-y) u))
        (fderiv ℝ S.phi (flow S (-x) u) ((-1 : ℝ) • S.Y (flow S (-x) u))) x :=
      (S.diff_phi hv).hasFDerivAt.comp_hasDerivAt x h1
    have h3 : HasDerivAt (fun y : ℝ => Real.exp (y / 2)) (Real.exp (x / 2) * (1 / 2)) x := by
      have := ((hasDerivAt_id x).div_const 2).exp
      exact this
    have h4 := h3.smul h2
    convert h4 using 1
    rw [map_smul, S.Dphi_Y hv, half_smul]
    module
  have hcont : ContinuousOn g (Icc 0 s) := fun x hx => (hder x hx.1).continuousAt.continuousWithinAt
  have hz : Real.exp (s / 2) • S.phi (flow S (-s) u) = S.phi u := by
    have := constant_of_has_deriv_right_zero hcont
      (fun x hx => (hder x hx.1).hasDerivWithinAt) s ⟨hs, le_rfl⟩
    simpa [hg, flow_zero] using this
  have e : -s / 2 + s / 2 = 0 := by ring
  calc S.phi (flow S (-s) u) = Real.exp (-s / 2) • (Real.exp (s / 2) • S.phi (flow S (-s) u)) := by
        rw [smul_smul, ← Real.exp_add, e, Real.exp_zero, one_smul]
    _ = Real.exp (-s / 2) • S.phi u := by rw [hz]

/-! ## 3. The admissible time and the maps `Φ`, `Ψ` -/

/-- Admissibility of `t` for a point of norm `r`: `t ≥ 0` and `e^{-t/2} r < ε`. -/
def Adm (t r : ℝ) : Prop := 0 ≤ t ∧ Real.exp (-t / 2) * r < S.ε

/-- The explicit admissible time `2 log(1 + 2r/ε)`. -/
def tOf (r : ℝ) : ℝ := 2 * Real.log (1 + 2 * r / S.ε)

theorem tOf_adm {r : ℝ} (hr : 0 ≤ r) : Adm S (tOf S r) r := by
  have hε := S.ε_pos
  have hy : 1 ≤ 1 + 2 * r / S.ε := by
    have : 0 ≤ 2 * r / S.ε := by positivity
    linarith
  have hypos : 0 < 1 + 2 * r / S.ε := by linarith
  refine ⟨?_, ?_⟩
  · unfold tOf
    have := Real.log_nonneg hy
    linarith
  · unfold tOf
    have e : Real.exp (-(2 * Real.log (1 + 2 * r / S.ε)) / 2) = (1 + 2 * r / S.ε)⁻¹ := by
      rw [show -(2 * Real.log (1 + 2 * r / S.ε)) / 2 = -Real.log (1 + 2 * r / S.ε) by ring,
        Real.exp_neg, Real.exp_log hypos]
    rw [e, inv_mul_lt_iff₀ hypos]
    have : 2 * r / S.ε * S.ε = 2 * r := by field_simp
    nlinarith

/-- `Φ(u) = e^{t/2} φ(F_{-t} u)` (`eq:global-D01-forward`), with the admissible time `tOf ‖u‖`. -/
def Phi (u : H) : K :=
  Real.exp (tOf S ‖u‖ / 2) • S.phi (flow S (-tOf S ‖u‖) u)

/-- `Ψ(z) = F_t(φ^{-1}(e^{-t/2} z))` (`eq:global-D01-inverse`), with the admissible time `tOf ‖z‖`. -/
def Psi (z : K) : H :=
  flow S (tOf S ‖z‖) (S.psi (Real.exp (-tOf S ‖z‖ / 2) • z))

theorem smul_mem_BK {t : ℝ} {z : K} (h : Real.exp (-t / 2) * ‖z‖ < S.ε) :
    Real.exp (-t / 2) • z ∈ S.BK := by
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact h

/-- Independence of the admissible time for `Φ`. -/
theorem Phi_aux {u : H} {t s : ℝ} (ht : Adm S t ‖u‖) (hs : Adm S s ‖u‖) (hts : t ≤ s) :
    Real.exp (s / 2) • S.phi (flow S (-s) u) = Real.exp (t / 2) • S.phi (flow S (-t) u) := by
  have hv : flow S (-t) u ∈ S.B := flow_mem S (by
    have : -t / 2 = -t / 2 := rfl
    simpa [neg_div] using ht.2)
  have h := contr S hv (s := s - t) (by linarith)
  have e : flow S (-(s - t)) (flow S (-t) u) = flow S (-s) u := by
    rw [← flow_add]
    congr 1
    ring
  rw [e] at h
  rw [h, smul_smul, ← Real.exp_add]
  congr 2
  ring

theorem Phi_eq {u : H} {t : ℝ} (ht : Adm S t ‖u‖) :
    Phi S u = Real.exp (t / 2) • S.phi (flow S (-t) u) := by
  have h0 := tOf_adm S (norm_nonneg u)
  unfold Phi
  rcases le_total (tOf S ‖u‖) t with h | h
  · exact (Phi_aux S h0 ht h).symm
  · exact Phi_aux S ht h0 h

theorem Phi_ball {u : H} (hu : u ∈ S.B) : Phi S u = S.phi u := by
  have hu' : ‖u‖ < S.ε := by simpa using hu
  have ht : Adm S 0 ‖u‖ := ⟨le_rfl, by simpa using hu'⟩
  rw [Phi_eq S ht]
  simp [flow_zero]

theorem BK_of_adm {t : ℝ} {z : K} (h : Adm S t ‖z‖) : Real.exp (-t / 2) • z ∈ S.BK :=
  smul_mem_BK S h.2

/-- Independence of the admissible time for `Ψ`. -/
theorem Psi_aux {z : K} {t s : ℝ} (ht : Adm S t ‖z‖) (hs : Adm S s ‖z‖) (hts : t ≤ s) :
    flow S s (S.psi (Real.exp (-s / 2) • z)) = flow S t (S.psi (Real.exp (-t / 2) • z)) := by
  have hzt := BK_of_adm S ht
  have hut : S.psi (Real.exp (-t / 2) • z) ∈ S.B := S.psi_maps hzt
  have hc := contr S hut (s := s - t) (by linarith)
  rw [S.phi_psi _ hzt, smul_smul, ← Real.exp_add] at hc
  have e1 : (-(s - t) / 2 + -t / 2) = -s / 2 := by ring
  rw [e1] at hc
  have hmem : flow S (-(s - t)) (S.psi (Real.exp (-t / 2) • z)) ∈ S.B := by
    have : Real.exp (-(s - t) / 2) * ‖S.psi (Real.exp (-t / 2) • z)‖ < S.ε := by
      have h1 : Real.exp (-(s - t) / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      have h2 : ‖S.psi (Real.exp (-t / 2) • z)‖ < S.ε := by simpa using hut
      calc Real.exp (-(s - t) / 2) * ‖S.psi (Real.exp (-t / 2) • z)‖
          ≤ 1 * ‖S.psi (Real.exp (-t / 2) • z)‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ < S.ε := by rw [one_mul]; exact h2
    exact flow_mem S this
  have hpsi : S.psi (Real.exp (-s / 2) • z) = flow S (-(s - t)) (S.psi (Real.exp (-t / 2) • z)) := by
    rw [← hc, S.psi_phi _ hmem]
  rw [hpsi, ← flow_add]
  congr 1
  ring

theorem Psi_eq {z : K} {t : ℝ} (ht : Adm S t ‖z‖) :
    Psi S z = flow S t (S.psi (Real.exp (-t / 2) • z)) := by
  have h0 := tOf_adm S (norm_nonneg z)
  unfold Psi
  rcases le_total (tOf S ‖z‖) t with h | h
  · exact (Psi_aux S h0 ht h).symm
  · exact Psi_aux S ht h0 h

/-! ## 4. The identities -/

theorem q_smul (a : ℝ) (n : ℤ) (z : K) : q n (a • z) = a ^ 2 * q n z := by
  unfold q
  have : (a • z) n = a • z n := rfl
  rw [this, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

theorem act_flow_apply (t : ℝ) (u : H) (n : ℤ) :
    S.act (flow S t u) n = Real.exp t * S.act u n := by
  have := (flow_action_mass S t u).1
  rw [this]
  rfl

/-- `|Φ_n(u)|² = I_n(u)`. -/
theorem q_Phi (u : H) (n : ℤ) : q n (Phi S u) = S.act u n := by
  have ht := tOf_adm S (norm_nonneg u)
  set t := tOf S ‖u‖ with htdef
  have hv : flow S (-t) u ∈ S.B := flow_mem S (by simpa [neg_div] using ht.2)
  unfold Phi
  rw [← htdef, q_smul, S.phi_q _ hv, act_flow_apply]
  have e : Real.exp (t / 2) ^ 2 * Real.exp (-t) = 1 := by
    have h0 : t / 2 + t / 2 + -t = 0 := by ring
    rw [pow_two, ← Real.exp_add, ← Real.exp_add, h0, Real.exp_zero]
  rw [← mul_assoc, e, one_mul]

theorem norm_Phi (u : H) : ‖Phi S u‖ = ‖u‖ := by
  have h1 : ‖Phi S u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [norm_sq_K, ← S.act_mass u]
    exact tsum_congr fun n => q_Phi S u n
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1

theorem adm_Phi {t : ℝ} {u : H} (h : Adm S t ‖u‖) : Adm S t ‖Phi S u‖ := by
  rwa [norm_Phi]

theorem norm_psi_BK {z : K} (hz : z ∈ S.BK) : ‖S.psi z‖ = ‖z‖ := by
  have h := S.norm_phi (S.psi_maps hz)
  rw [S.phi_psi z hz] at h
  exact h.symm

/-- `Ψ ∘ Φ = id`. -/
theorem Psi_Phi (u : H) : Psi S (Phi S u) = u := by
  have ht := tOf_adm S (norm_nonneg u)
  set t := tOf S ‖u‖ with htdef
  have hv : flow S (-t) u ∈ S.B := flow_mem S (by simpa [neg_div] using ht.2)
  have hP : Phi S u = Real.exp (t / 2) • S.phi (flow S (-t) u) := by
    unfold Phi; rw [← htdef]
  rw [Psi_eq S (adm_Phi S ht), hP, smul_smul, ← Real.exp_add]
  have : -t / 2 + t / 2 = 0 := by ring
  rw [this, Real.exp_zero, one_smul, S.psi_phi _ hv, ← flow_add]
  simp [flow_zero]

/-- `Φ ∘ Ψ = id`. -/
theorem Phi_Psi (z : K) : Phi S (Psi S z) = z := by
  have ht := tOf_adm S (norm_nonneg z)
  set t := tOf S ‖z‖ with htdef
  have hzt := BK_of_adm S ht
  set w := S.psi (Real.exp (-t / 2) • z) with hw
  have hwB : w ∈ S.B := S.psi_maps hzt
  have hPs : Psi S z = flow S t w := by
    unfold Psi; rw [← htdef]
  have hnorm : ‖Psi S z‖ = ‖z‖ := by
    rw [hPs, norm_flow, hw, norm_psi_BK S hzt, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), ← mul_assoc, ← Real.exp_add]
    have : t / 2 + -t / 2 = 0 := by ring
    rw [this]; simp
  have hadm : Adm S t ‖Psi S z‖ := by rwa [hnorm]
  rw [Phi_eq S hadm, hPs, ← flow_add]
  have : -t + t = 0 := by ring
  rw [this, flow_zero, hw, S.phi_psi _ hzt, smul_smul, ← Real.exp_add]
  have h2 : t / 2 + -t / 2 = 0 := by ring
  rw [h2]; simp

/-- Surjectivity of the action map: `I(H) = ℓ¹_+`. -/
theorem act_surj (a : L1) (ha : ∀ n, 0 ≤ a n) : ∃ u : H, S.act u = a := by
  have hsum : Summable fun n => ‖a n‖ := by
    have := (lp.memℓp a)
    rw [memℓp_gen_iff (by norm_num)] at this
    simpa using this
  have hz : Memℓp (fun n : ℤ => ((Real.sqrt (a n) : ℝ) : ℂ)) 2 := by
    rw [memℓp_gen_iff (by norm_num)]
    refine hsum.congr fun n => ?_
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      ENNReal.toReal_ofNat, Real.rpow_two]
    rw [Real.sq_sqrt (ha n)]
    exact abs_of_nonneg (ha n)
  set z : K := ⟨_, hz⟩ with hzdef
  refine ⟨Psi S z, ?_⟩
  ext n
  rw [← q_Phi S (Psi S z) n, Phi_Psi]
  show ‖((Real.sqrt (a n) : ℝ) : ℂ)‖ ^ 2 = a n
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (ha n)]

end QuantumNLS.D01Reconstruction

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.D01Reconstruction.contr
#print axioms QuantumNLS.D01Reconstruction.Phi_eq
#print axioms QuantumNLS.D01Reconstruction.Psi_eq
#print axioms QuantumNLS.D01Reconstruction.q_Phi
#print axioms QuantumNLS.D01Reconstruction.norm_Phi
#print axioms QuantumNLS.D01Reconstruction.Psi_Phi
#print axioms QuantumNLS.D01Reconstruction.Phi_Psi
#print axioms QuantumNLS.D01Reconstruction.act_surj
