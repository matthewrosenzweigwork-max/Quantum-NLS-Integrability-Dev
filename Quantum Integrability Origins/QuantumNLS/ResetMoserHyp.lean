import QuantumNLS.ResetMoserAnnihilate
import QuantumNLS.RealAnalyticDef

/-!
# `thm:reset-moser` (LOCAL-017), stage 1a: the hypotheses `Hyp` and the first consequences of Poisson commutation

Source: `symplectic_correction.tex`, Theorem `thm:reset-moser` (line 25): "Suppose that `Ω` is a real-analytic closed two-form on an open ball `B_R ⊂ ℋ`. Suppose that its values are bounded alternating bilinear forms, analytically in the full operator norm, and `Ω_z = ω + O(‖z‖²)`, `‖Ω_z − ω‖ < 1`. Assume that the `q_n` pairwise Poisson commute for `Ω`, and their Hamiltonian flows exist on `B_R` and have time `2π` equal to the identity." and the first paragraph of "Isotropy of every coordinate torus": "Every Hamiltonian flow of `q_j` preserves each `q_k` by the Poisson commutation assumption. In particular it preserves `ℋ_F` and the Hilbert norm. Its vector field at a point of `ℋ_F` lies in that subspace."

`Hyp` bundles the printed hypotheses literally (`ℋ = K = ℓ²(ℤ;ℂ)`, `ω = Jw`, DEF-017 analyticity in the full operator norm):
* `Xn Ω n z` is the `Ω`-Hamiltonian field of `q_n`, `ι_{X}Ω = dq_n`, constructed by the Neumann series (`Ycov`, so existence and uniqueness need no extra hypothesis);
* the flows `φ n t` of `Xn Ω n`, complete on `B_R` (they stay in the ball), with `φ n (2π) = id`;
* pairwise Poisson commutation `Ω_z(X_m, X_n) = 0`.

Results: `Xn_spec` (`Ω_z(X_n, h) = dq_n(z)h`), `dq_Xn` (`dq_k X_j = 0`), `flow_q` (`q_k ∘ φ_j^t = q_k`), `Xn_coord_zero` (the field preserves `ℋ_F`), `Xn_mem_Tz` (`X_j(z) ∈ 𝒯_z` for every `z ∈ B_R`).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.RealAnalyticDef

/-- The `Ω`-Hamiltonian field of `q_n`: `Ω_z(X, ·) = dq_n(z)`. -/
def Xn (Ω : K → Form) (n : ℤ) (z : K) : K := Ycov (Ω z - omegaF) (-(fderiv ℝ (q n) z))

theorem Xn_spec {Ω : K → Form} {z : K} (hD : ‖Ω z - omegaF‖ < 1) (n : ℤ) (h : K) :
    Ω z (Xn Ω n z) h = fderiv ℝ (q n) z h := by
  have := iota_Ycov hD (-(fderiv ℝ (q n) z)) h
  have e : (Ω z - omegaF) (Xn Ω n z) h = Ω z (Xn Ω n z) h - omega (Xn Ω n z) h := by
    simp [omegaF_apply]
  unfold Xn at *
  rw [e] at this
  simp at this
  linarith

/-- The hypotheses of `thm:reset-moser`. -/
structure Hyp where
  R : ℝ
  R_pos : 0 < R
  Ω : K → Form
  Ω_alt : ∀ z v w, Ω z v w = -Ω z w v
  Ω_analytic : ∀ z ∈ ball (0 : K) R, IsRealAnalyticPoly Ω z
  Ω_closed : ∀ z ∈ ball (0 : K) R, ∀ a b c : K,
    fderiv ℝ Ω z a b c + fderiv ℝ Ω z b c a + fderiv ℝ Ω z c a b = 0
  Ω_quad : ∃ C : ℝ, ∀ z ∈ ball (0 : K) R, ‖Ω z - omegaF‖ ≤ C * ‖z‖ ^ 2
  Ω_lt : ∀ z ∈ ball (0 : K) R, ‖Ω z - omegaF‖ < 1
  φ : ℤ → ℝ → K → K
  φ_zero : ∀ n z, φ n 0 z = z
  φ_mem : ∀ n, ∀ z ∈ ball (0 : K) R, ∀ t, φ n t z ∈ ball (0 : K) R
  φ_deriv : ∀ n, ∀ z ∈ ball (0 : K) R, ∀ t, HasDerivAt (fun s => φ n s z) (Xn Ω n (φ n t z)) t
  φ_period : ∀ n, ∀ z ∈ ball (0 : K) R, φ n (2 * Real.pi) z = z
  poisson : ∀ m n, ∀ z ∈ ball (0 : K) R, Ω z (Xn Ω m z) (Xn Ω n z) = 0

namespace Hyp

variable (S : Hyp)

theorem Ω_continuousOn : ContinuousOn S.Ω (ball (0 : K) S.R) := fun z hz =>
  ((analyticAt_of_isRealAnalyticPoly (S.Ω_analytic z hz)).continuousAt).continuousWithinAt

/-- `dq_k(z) X_j(z) = Ω_z(X_k, X_j) = 0`. -/
theorem dq_Xn {z : K} (hz : z ∈ ball (0 : K) S.R) (k j : ℤ) :
    fderiv ℝ (q k) z (Xn S.Ω j z) = 0 := by
  rw [← Xn_spec (S.Ω_lt z hz) k (Xn S.Ω j z), S.Ω_alt, S.poisson j k z hz, neg_zero]

/-- Every Hamiltonian flow of `q_j` preserves each `q_k`. -/
theorem flow_q {z : K} (hz : z ∈ ball (0 : K) S.R) (k j : ℤ) (t : ℝ) :
    q k (S.φ j t z) = q k z := by
  have hd : ∀ s : ℝ, HasDerivAt (fun r => q k (S.φ j r z)) 0 s := by
    intro s
    have h1 := (hasFDerivAt_q k (S.φ j s z)).comp_hasDerivAt s (S.φ_deriv j z hz s)
    have h2 := S.dq_Xn (S.φ_mem j z hz s) k j
    rw [(hasFDerivAt_q k (S.φ j s z)).fderiv] at h2
    rw [h2] at h1
    exact h1
  have hdiff : Differentiable ℝ (fun r => q k (S.φ j r z)) := fun s => (hd s).differentiableAt
  have := is_const_of_deriv_eq_zero hdiff (fun s => (hd s).deriv) t 0
  rw [S.φ_zero] at this
  exact this

/-- The field preserves the coordinate subspaces: a vanishing coordinate stays zero. -/
theorem Xn_coord_zero {z : K} (hz : z ∈ ball (0 : K) S.R) {k : ℤ} (hk : z k = 0) (j : ℤ) :
    (Xn S.Ω j z) k = 0 := by
  have hd := (evalR k).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (S.φ_deriv j z hz 0)
  have hz0 : ∀ s : ℝ, (S.φ j s z) k = 0 := by
    intro s
    have := S.flow_q hz k j s
    unfold q at this
    rw [hk, norm_zero] at this
    have h2 : ‖(S.φ j s z) k‖ ^ 2 = 0 := by simpa using this
    exact norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h2)
  have hconst : HasDerivAt (fun s : ℝ => (evalR k) (S.φ j s z)) 0 0 := by
    have : (fun s : ℝ => (evalR k) (S.φ j s z)) = fun _ => (0 : ℂ) := funext hz0
    rw [this]; exact hasDerivAt_const _ _
  have := hd.unique hconst
  rw [S.φ_zero] at this
  simpa using this

/-- `X_j(z) ∈ 𝒯_z` for every `z` in the ball and every `j`. -/
theorem Xn_mem_Tz {z : K} (hz : z ∈ ball (0 : K) S.R) (j : ℤ) : Xn S.Ω j z ∈ Tz z := by
  intro k
  by_cases hk : z k = 0
  · exact ⟨0, by rw [S.Xn_coord_zero hz hk j, hk]; simp⟩
  · have h0 := S.dq_Xn hz k j
    rw [fderiv_q_apply] at h0
    set w := (Xn S.Ω j z) k with hw
    have hre : (conj (z k) * w).re = 0 := by linarith
    have hwz : w = z k * (w / z k) := by field_simp
    have hc : (w / z k).re = 0 := by
      have e : conj (z k) * w = ((‖z k‖ ^ 2 : ℝ) : ℂ) * (w / z k) := by
        have h1 : conj (z k) * w = (conj (z k) * z k) * (w / z k) := by
          conv_lhs => rw [hwz]
          ring
        rw [h1, Complex.conj_mul']
        push_cast
        ring
      rw [e, Complex.re_ofReal_mul] at hre
      have hpos : 0 < ‖z k‖ ^ 2 := by positivity
      exact (mul_eq_zero.1 hre).resolve_left hpos.ne'
    have hcI : w / z k = Complex.I * ((w / z k).im : ℂ) := by
      apply Complex.ext <;> simp [hc]
    refine ⟨(w / z k).im, ?_⟩
    calc w = z k * (w / z k) := hwz
      _ = Complex.I * z k * ((w / z k).im : ℂ) := by
          conv_lhs => rw [hcI]
          ring

end Hyp

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.Xn_spec
#print axioms QuantumNLS.ResetMoser.Hyp.dq_Xn
#print axioms QuantumNLS.ResetMoser.Hyp.flow_q
#print axioms QuantumNLS.ResetMoser.Hyp.Xn_coord_zero
