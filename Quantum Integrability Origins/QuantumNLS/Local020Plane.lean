import Mathlib
import QuantumNLS.LocalSpectralReduced
import QuantumNLS.Local020Scale

/-! LOCAL-020 stage S7a: the plane-wave potential `pw a k x = a L^{-1/2} e^{i p_k x}` leaves the free doublet at `p_k`
invariant: `𝓛_u` acts on `span{χ_{k,0}, χ_{k,1}}` by `M = [[p_k, c̄],[c, p_k]]`, `c = 2i√(κ/L) a`.
`eig_pair`: if `(s,t)` is an eigenvector of `M` with eigenvalue `λ` then `(s χ_{k,0} + t χ_{k,1}, λ •)` lies in the graph
of `𝓛_u` on `D_{(-1)^k}`. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Filter Topology QuantumNLS.LocalSpectral ComplexConjugate
open scoped ENNReal

namespace QuantumNLS.Local020Plane

variable {L κ : ℝ}

/-- The plane-wave potential. -/
def pw (L : ℝ) (a : ℂ) (k : ℤ) (x : ℝ) : ℂ :=
  a * (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Complex.exp (Complex.I * (pm L k : ℂ) * (x : ℂ))

/-- The coupling `c = 2i √κ Λ a` (`Λ = L^{-1/2}`). -/
def cc' (κ Λ : ℝ) (a : ℂ) : ℂ := 2 * Complex.I * (Real.sqrt κ : ℂ) * (Λ : ℂ) * a

/-- The coupling `c = 2i √(κ/L) a`. -/
def cc (L κ : ℝ) (a : ℂ) : ℂ := cc' κ ((Real.sqrt L)⁻¹) a

theorem pt_eig (κ p Λ : ℝ) (a s t lam E0 E1 : ℂ) (h01 : E0 * E1 = 1) (hc : conj E1 = E0)
    (h1 : (p : ℂ) * s + conj (cc' κ Λ a) * t = lam * s) (h2 : (p : ℂ) * t + cc' κ Λ a * s = lam * t) :
    lopPt κ (a * (Λ : ℂ) * E1 ^ 2)
      (vec2 ((-(Complex.I * p / 2)) * (s * Λ * E0)) ((Complex.I * p / 2) * (t * Λ * E1)))
      (vec2 (s * Λ * E0) (t * Λ * E1)) = lam • vec2 (s * Λ * E0) (t * Λ * E1) := by
  have h2c : (starRingEnd ℂ) 2 = 2 := map_ofNat _ 2
  have hcc : conj (cc' κ Λ a) = -(2 * Complex.I * (Real.sqrt κ : ℂ) * (Λ : ℂ) * conj a) := by
    simp [cc', h2c]
  rw [hcc] at h1
  unfold cc' at h2
  unfold lopPt Jm
  ext i; fin_cases i
  · simp only [vec2, map_mul, map_pow, hc, Complex.conj_ofReal]
    simp
    linear_combination (Λ * E0) * h1 + (-2 * Complex.I * (Real.sqrt κ : ℂ) * conj a * Λ ^ 2 * t * E0) * h01
      + (-((p : ℂ) * s * Λ * E0)) * Complex.I_sq
  · simp only [vec2, map_mul, map_pow, hc, Complex.conj_ofReal]
    simp
    linear_combination (Λ * E1) * h2 + (2 * Complex.I * (Real.sqrt κ : ℂ) * a * Λ ^ 2 * s * E1) * h01
      + (-((p : ℂ) * t * Λ * E1)) * Complex.I_sq

theorem rate0 (L : ℝ) (k : ℤ) : rate L k 0 = -(Complex.I * (pm L k : ℂ) / 2) := by
  unfold rate sgn; simp; ring

theorem rate1 (L : ℝ) (k : ℤ) : rate L k 1 = Complex.I * (pm L k : ℂ) / 2 := by
  unfold rate sgn; simp

theorem chiFun_vec (L : ℝ) (k : ℤ) (s t : ℂ) (x : ℝ) :
    s • chiFun L k 0 x + t • chiFun L k 1 x =
      vec2 (s * (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Complex.exp (rate L k 0 * (x : ℂ)))
        (t * (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Complex.exp (rate L k 1 * (x : ℂ))) := by
  ext i; fin_cases i <;> simp [chiFun, vec2, EuclideanSpace.single_apply] <;> ring

theorem dchiFun_vec (L : ℝ) (k : ℤ) (s t : ℂ) (x : ℝ) :
    s • dchiFun L k 0 x + t • dchiFun L k 1 x =
      vec2 ((-(Complex.I * (pm L k : ℂ) / 2)) *
          (s * (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Complex.exp (rate L k 0 * (x : ℂ))))
        ((Complex.I * (pm L k : ℂ) / 2) *
          (t * (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Complex.exp (rate L k 1 * (x : ℂ)))) := by
  ext i; fin_cases i <;> simp [dchiFun, chiFun, vec2, EuclideanSpace.single_apply, rate0, rate1] <;> ring

theorem eig_pair (hL : 0 < L) (a : ℂ) (k : ℤ) (s t lam : ℂ)
    (h1 : (pm L k : ℂ) * s + conj (cc L κ a) * t = lam * s)
    (h2 : (pm L k : ℂ) * t + cc L κ a * s = lam * t) :
    (embed L k (vec2 s t), lam • embed L k (vec2 s t)) ∈ LuGraph L κ (pw L a k) (parity k) := by
  have hsa : ∀ x : ℝ, Complex.exp (rate L k 0 * (x : ℂ)) * Complex.exp (rate L k 1 * (x : ℂ)) = 1 := by
    intro x
    rw [← Complex.exp_add, ← add_mul, rate0, rate1]; simp
  have hcj : ∀ x : ℝ, conj (Complex.exp (rate L k 1 * (x : ℂ))) = Complex.exp (rate L k 0 * (x : ℂ)) := by
    intro x
    rw [← Complex.exp_conj]
    congr 1
    have h2c : (starRingEnd ℂ) 2 = 2 := map_ofNat _ 2
    rw [rate0, rate1]
    simp [Complex.conj_ofReal, h2c]
    ring
  have hpw : ∀ x : ℝ, pw L a k x = a * (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * (Complex.exp (rate L k 1 * (x : ℂ))) ^ 2 := by
    intro x
    unfold pw
    rw [← Complex.exp_nat_mul, rate1]
    congr 2
    push_cast; ring
  have hemb : (embed L k (vec2 s t) : ℝ → E2) =ᵐ[μI L] fun x => s • chiFun L k 0 x + t • chiFun L k 1 x := by
    rw [embed_apply]
    simp only [vec2_zero, vec2_one]
    filter_upwards [Lp.coeFn_add (s • chi L k 0) (t • chi L k 1), Lp.coeFn_smul s (chi L k 0),
      Lp.coeFn_smul t (chi L k 1), (memLp_chiFun L k 0).coeFn_toLp, (memLp_chiFun L k 1).coeFn_toLp]
      with x h1 h2 h3 h4 h5
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply]
    have e4 : (chi L k 0 : ℝ → E2) x = chiFun L k 0 x := h4
    have e5 : (chi L k 1 : ℝ → E2) x = chiFun L k 1 x := h5
    rw [e4, e5]
  refine ⟨fun x => s • chiFun L k 0 x + t • chiFun L k 1 x,
    fun x => s • dchiFun L k 0 x + t • dchiFun L k 1 x, ⟨hemb, ?_, ?_⟩, ?_, ?_⟩
  · exact ((memLp_dchiFun L k 0).const_smul s).add ((memLp_dchiFun L k 1).const_smul t)
  · intro x _
    have hd : ∀ y, HasDerivAt (fun x => s • chiFun L k 0 x + t • chiFun L k 1 x)
        (s • dchiFun L k 0 y + t • dchiFun L k 1 y) y := fun y =>
      ((hasDerivAt_chiFun L k 0 y).const_smul s).add ((hasDerivAt_chiFun L k 1 y).const_smul t)
    have hc : Continuous (fun y => s • dchiFun L k 0 y + t • dchiFun L k 1 y) := by
      have := continuous_dchiFun L k 0
      have := continuous_dchiFun L k 1
      fun_prop
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := x) (fun y _ => hd y)
      (hc.intervalIntegrable _ _)
    simp only
    rw [this, add_sub_cancel]
  · simp only
    rw [smul_add, chiFun_at_L hL.ne', chiFun_at_L hL.ne']
    simp [smul_comm _ (((parity k : ℤˣ) : ℤ) : ℂ)]
  · filter_upwards [Lp.coeFn_smul lam (embed L k (vec2 s t)), hemb] with x h h'
    rw [h, Pi.smul_apply, h']
    rw [chiFun_vec, dchiFun_vec, hpw x]
    exact (pt_eig κ (pm L k) ((Real.sqrt L)⁻¹) a s t lam _ _ (hsa x) (hcj x) h1 h2).symm

theorem norm_embed (hL : 0 < L) (n : ℤ) (v : E2) : ‖embed L n v‖ = ‖v‖ := by
  have := inner_embed hL n v v
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at this
  have h2 : ‖embed L n v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast this
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

theorem eig_nonzero (hL : 0 < L) (a : ℂ) (k : ℤ) (ha : cc L κ a ≠ 0) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    ∃ f : H2 L, f ≠ 0 ∧ (f, (((pm L k : ℝ) + ε * ‖cc L κ a‖ : ℝ) : ℂ) • f) ∈ LuGraph L κ (pw L a k) (parity k) := by
  set c := cc L κ a with hc
  have hn : (‖c‖ : ℂ) * (‖c‖ : ℂ) = c * conj c := by
    rw [Complex.mul_conj']; push_cast; ring
  have hsq : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hsqc : (ε : ℂ) * (ε : ℂ) = 1 := by exact_mod_cast hsq
  refine ⟨embed L k (vec2 (conj c) ((ε : ℂ) * (‖c‖ : ℂ))), ?_, ?_⟩
  · intro h0
    have := norm_embed hL k (vec2 (conj c) ((ε : ℂ) * (‖c‖ : ℂ)))
    rw [h0, norm_zero] at this
    have hv : vec2 (conj c) ((ε : ℂ) * (‖c‖ : ℂ)) = 0 := norm_eq_zero.1 this.symm
    have := congrArg (fun v : E2 => v 0) hv
    simp [vec2] at this
    exact ha this
  · have := eig_pair (κ := κ) hL a k (conj c) ((ε : ℂ) * (‖c‖ : ℂ)) (((pm L k : ℝ) + ε * ‖c‖ : ℝ) : ℂ) ?_ ?_
    · exact this
    · push_cast
      rw [← hc]
      ring
    · push_cast
      rw [← hc]
      linear_combination (-1 : ℂ) * hn + (-((‖c‖ : ℂ) * (‖c‖ : ℂ))) * hsqc

/-- A nonzero eigenvector excludes the existence of a resolvent. -/
theorem no_resolvent {u : ℝ → ℂ} {σ : ℤˣ} {lam : ℂ} {f : H2 L} (hf : f ≠ 0)
    (h : (f, lam • f) ∈ LuGraph L κ u σ) : ¬ ∃ R : H2 L →L[ℂ] H2 L, IsResolvent L κ u σ lam R := by
  rintro ⟨R, hR⟩
  have := hR.2 _ h
  simp at this
  exact hf this.symm

/-- **S7a.**  If a reduction `(α, β)` has the resolvent property of LOCAL-003 (every `lam` in the disc other than
`α ± |β|` is in the resolvent set), then for the plane-wave potential `α = p_k` and `|β| = |c|`. -/
theorem plane_modulus (hL : 0 < L) (a : ℂ) (k : ℤ) (ha : cc L κ a ≠ 0) {r : ℝ}
    (hcr : ‖cc L κ a‖ < r) {u : ℝ → ℂ} (hu : u =ᵐ[μI L] pw L a k) {α : ℝ} {β : ℂ}
    (hres : ∀ lam : ℂ, ‖lam - (pm L k : ℂ)‖ < r → lam ≠ ((α + ‖β‖ : ℝ) : ℂ) → lam ≠ ((α - ‖β‖ : ℝ) : ℂ) →
      ∃ R : H2 L →L[ℂ] H2 L, IsResolvent L κ u (parity k) lam R) :
    α = pm L k ∧ ‖β‖ = ‖cc L κ a‖ := by
  have hG := Local020Scale.LuGraph_congr_ae (κ := κ) hu (parity k)
  have hcpos : 0 < ‖cc L κ a‖ := norm_pos_iff.2 ha
  have key : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      ((((pm L k : ℝ) + ε * ‖cc L κ a‖ : ℝ)) : ℂ) = ((α + ‖β‖ : ℝ) : ℂ) ∨
      ((((pm L k : ℝ) + ε * ‖cc L κ a‖ : ℝ)) : ℂ) = ((α - ‖β‖ : ℝ) : ℂ) := by
    intro ε hε
    obtain ⟨f, hf0, hf⟩ := eig_nonzero (κ := κ) hL a k ha ε hε
    rw [← hG] at hf
    by_contra hcon
    push_neg at hcon
    apply no_resolvent hf0 hf
    apply hres _ _ hcon.1 hcon.2
    have : (((pm L k : ℝ) + ε * ‖cc L κ a‖ : ℝ) : ℂ) - (pm L k : ℂ) = ((ε * ‖cc L κ a‖ : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    rcases hε with rfl | rfl <;> simpa using hcr
  have k1 := key 1 (Or.inl rfl)
  have k2 := key (-1) (Or.inr rfl)
  simp only [Complex.ofReal_inj] at k1 k2
  have hβ := norm_nonneg β
  refine ⟨?_, ?_⟩ <;> rcases k1 with h1 | h1 <;> rcases k2 with h2 | h2 <;>
    first | linarith | (exfalso; linarith)

end QuantumNLS.Local020Plane

#print axioms QuantumNLS.Local020Plane.plane_modulus
