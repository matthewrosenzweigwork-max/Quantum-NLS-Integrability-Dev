import Mathlib
import NlsGge.NLS38.ZSZeroCurvature38
import NlsGge.NLS38.LinearODEParamDeriv38
import NlsGge.Spectral.ActualComplexZsDysonMonodromyTraceFactsV2
import NlsGge.Spectral.ActualComplexZsFundamentalIccAssemblyV1

/-!
# Lax isospectrality of the ZS half trace for classical solutions (38, B3)

For a classical (`C^2` in `x`, `C^1` in `t`, jointly continuous) 1-periodic solution of
`i u_t = -u_xx + 2|u|^2 u` (v2 `eq:nls`), the half trace `tr Ψ(1;z)/2` of the project's Dyson
monodromy `actualComplexZsDysonTsum` is independent of `t`, for every complex `z`.

Route (plan §5.2, risk R7).  `Ψ(·,t)` is the global fundamental matrix of `Ψ' = zsA z (U t x) Ψ`
from B2 (`exists_fundamental`); B2 gives `E = ∂ₜ Ψ`, and `Z = E - VΨ + ΨV(0)` solves
`Z' = A Z`, `Z(0) = 0` by B1 (`zs_zero_curvature`).  Hence `tr E(1) = 0` by periodicity.
Finally `Ψ(·,t) = actualComplexZsDysonTsum (U t) z` on `[0,2]` by the uniqueness theorem
`exists_actual_normalized_complexZs_fundamental_Icc_det_unique`, which identifies the two.
-/

set_option autoImplicit false
noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.Frobenius
open NlsGge.SpectralFoundations

namespace NlsGge.NLS38

/-- Half trace of the actual unit-period Dyson monodromy of a potential `U`. -/
def halfTraceOf (U : ℝ → ℂ) (z : ℂ) : ℂ :=
  Matrix.trace (actualComplexZsDysonTsum U z 1) / 2

/-! ### Entrywise calculus for `2 × 2` complex matrices -/

lemma hasDerivAt_mat2 {f : ℝ → Matrix (Fin 2) (Fin 2) ℂ} {f' : Matrix (Fin 2) (Fin 2) ℂ} {x : ℝ}
    (h : ∀ i j, HasDerivAt (fun y => f y i j) (f' i j) x) : HasDerivAt f f' x :=
  hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => h i j

lemma hasDerivAt_mat2_entry {f : ℝ → Matrix (Fin 2) (Fin 2) ℂ} {f' : Matrix (Fin 2) (Fin 2) ℂ}
    {x : ℝ} (h : HasDerivAt f f' x) (i j : Fin 2) :
    HasDerivAt (fun y => f y i j) (f' i j) x :=
  hasDerivAt_pi.1 (hasDerivAt_pi.1 h i) j

lemma continuous_mat2 {X : Type*} [TopologicalSpace X] {f : X → Matrix (Fin 2) (Fin 2) ℂ}
    (h : ∀ i j, Continuous fun x => f x i j) : Continuous f :=
  continuous_pi fun i => continuous_pi fun j => h i j

/-- `t`-derivative of `zsA z (u t)`: the `z`-diagonal is constant. -/
lemma hasDerivAt_zsA {u : ℝ → ℂ} {u' : ℂ} {t : ℝ} (h : HasDerivAt u u' t) (z : ℂ) :
    HasDerivAt (fun s => zsA z (u s))
      !![0, Complex.I * u'; -(Complex.I * conj u'), 0] t := by
  apply hasDerivAt_mat2
  intro i j
  have hc : HasDerivAt (fun s => conj (u s)) (conj u') t := h.star
  fin_cases i <;> fin_cases j <;> simp [zsA]
  · exact hasDerivAt_const _ _
  · exact h.const_mul _
  · exact hc.const_mul _ |>.neg
  · exact hasDerivAt_const _ _

/-- `x`-derivative of `zsV z (u x) (ux x)`, namely `zsVx`. -/
lemma hasDerivAt_zsV {u ux : ℝ → ℂ} {ux' : ℂ} {x : ℝ} (hu : HasDerivAt u (ux x) x)
    (hux : HasDerivAt ux ux' x) (z : ℂ) :
    HasDerivAt (fun y => zsV z (u y) (ux y)) (zsVx z (u x) (ux x) ux') x := by
  apply hasDerivAt_mat2
  intro i j
  have hc : HasDerivAt (fun s => conj (u s)) (conj (ux x)) x := hu.star
  have hcx : HasDerivAt (fun s => conj (ux s)) (conj ux') x := hux.star
  have hm : HasDerivAt (fun s => u s * conj (u s)) (ux x * conj (u x) + u x * conj (ux x)) x :=
    hu.mul hc
  fin_cases i <;> fin_cases j <;> simp [zsV, zsVx]
  · exact ((hm.const_mul Complex.I).const_sub _).congr_deriv (by ring)
  · exact (hu.const_mul _).sub hux
  · exact ((hc.const_mul _).neg.sub hcx).congr_deriv (by ring)
  · exact hm.const_mul _

/-! ### Identification of a global fundamental matrix with the Dyson sum (risk R7) -/

/-- If `G(0) = 1` and `G' = zsA z (u x) G` on all of `ℝ` for a continuous `u`, then `G` is the
project's Dyson sum `actualComplexZsDysonTsum u z` on `[0,2]`. -/
theorem fundamental_eq_dyson {u : ℝ → ℂ} (hu : Continuous u) (z : ℂ)
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hG0 : G 0 = 1)
    (hG : ∀ x, HasDerivAt G (zsA z (u x) * G x) x) :
    ∀ x ∈ Set.Icc (0 : ℝ) 2, G x = actualComplexZsDysonTsum u z x := by
  obtain ⟨F, -, -, -, huniq⟩ :=
    exists_actual_normalized_complexZs_fundamental_Icc_det_unique u z hu.continuousOn
  have h1 := huniq G hG0 (fun t _ => by
    rw [← zsA_eq_zsCoefficientComplex]; exact (hG t).hasDerivWithinAt)
  have h2 := huniq (fun t => actualComplexZsDysonTsum u z t)
    (actualComplexZsDysonTsum_initial_and_determinant_of_continuousOn u z hu.continuousOn).1
    (fun t ht => hasDerivWithinAt_actualComplexZsDysonTsum_of_continuousOn u z hu.continuousOn t ht)
  intro x hx
  exact (h1 hx).symm.trans (h2 hx)

/-! ### Lax isospectrality for classical solutions -/

set_option linter.unusedVariables false in
theorem halfTrace_const_of_classical (U Ux Uxx Ut : ℝ → ℝ → ℂ)
    (hU : Continuous (Function.uncurry U)) (hUx : Continuous (Function.uncurry Ux))
    (hUxx : Continuous (Function.uncurry Uxx)) (hUt : Continuous (Function.uncurry Ut))
    (h1 : ∀ t x, HasDerivAt (U t) (Ux t x) x) (h2 : ∀ t x, HasDerivAt (Ux t) (Uxx t x) x)
    (h3 : ∀ t x, HasDerivAt (fun s => U s x) (Ut t x) t)
    (hper : ∀ t x, U t (x + 1) = U t x ∧ Ux t (x + 1) = Ux t x)
    (hpde : ∀ t x, Complex.I * Ut t x = -Uxx t x + 2 * ((‖U t x‖ ^ 2 : ℝ) : ℂ) * U t x)
    (z : ℂ) (t : ℝ) :
    halfTraceOf (U t) z = halfTraceOf (U 0) z := by
  -- coefficient matrices
  set A : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun x s => zsA z (U s x) with hAdef
  set At : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ :=
    fun x s => !![0, Complex.I * Ut s x; -(Complex.I * conj (Ut s x)), 0] with hAtdef
  have hUc : ∀ s, Continuous (U s) := fun s => hU.comp (Continuous.prodMk continuous_const continuous_id)
  have hcont_swap : ∀ {f : ℝ → ℝ → ℂ}, Continuous (Function.uncurry f) →
      Continuous (fun p : ℝ × ℝ => f p.2 p.1) := fun {f} hf =>
    hf.comp (continuous_snd.prodMk continuous_fst)
  have hA : Continuous (Function.uncurry A) := by
    have hu := hcont_swap hU
    apply continuous_mat2
    intro i j
    have hc : Continuous fun p : ℝ × ℝ => conj (U p.2 p.1) := (Complex.continuous_conj.comp hu)
    fin_cases i <;> fin_cases j <;> simp [hAdef, zsA, Function.uncurry] <;> fun_prop
  have hAt : Continuous (Function.uncurry At) := by
    have hu := hcont_swap hUt
    apply continuous_mat2
    intro i j
    have hc : Continuous fun p : ℝ × ℝ => conj (Ut p.2 p.1) := (Complex.continuous_conj.comp hu)
    fin_cases i <;> fin_cases j <;> simp [hAtdef, Function.uncurry] <;> fun_prop
  have hdt : ∀ x s, HasDerivAt (fun r => A x r) (At x s) s := fun x s => hasDerivAt_zsA (h3 s x) z
  obtain ⟨Ψ, hΨ0, hΨ⟩ := exists_fundamental A hA
  obtain ⟨E, hEt, hE0, hEx⟩ := hasDerivAt_param_linearODE A At hA hAt hdt Ψ hΨ0 hΨ
  -- the trace of the monodromy is constant in the parameter
  have hE1 : ∀ s, Matrix.trace (E 1 s) = 0 := by
    intro s
    set V : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun x => zsV z (U s x) (Ux s x) with hVdef
    have hV : ∀ x, HasDerivAt V (zsVx z (U s x) (Ux s x) (Uxx s x)) x :=
      fun x => hasDerivAt_zsV (h1 s x) (h2 s x) z
    set W : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun x => E x s - V x * Ψ x s + Ψ x s * V 0 with hWdef
    have hcurv : ∀ x, At x s = zsVx z (U s x) (Ux s x) (Uxx s x) -
        (A x s * V x - V x * A x s) := by
      intro x
      have hp := hpde s x
      have hn : ((‖U s x‖ ^ 2 : ℝ) : ℂ) = U s x * conj (U s x) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [hn] at hp
      exact zs_zero_curvature z (U s x) (Ux s x) (Uxx s x) (Ut s x) hp
    have hW : ∀ x, HasDerivAt W (A x s * W x) x := by
      intro x
      have hd := (((hEx x s).sub ((hV x).mul (hΨ x s))).add ((hΨ x s).mul_const (V 0)))
      refine hd.congr_deriv ?_
      rw [hcurv x]
      simp only [hWdef]
      noncomm_ring
    have hW0 : W 0 = 0 := by simp [hWdef, hE0, hΨ0]
    have hW1 : W 1 = 0 := linear_ode_unique A hA s W hW0 hW 1
    have hE : E 1 s = V 1 * Ψ 1 s - Ψ 1 s * V 0 := by
      have h := hW1
      simp only [hWdef] at h
      rw [← sub_eq_zero, ← h]; abel
    have hV1 : V 1 = V 0 := by
      have := hper s 0
      simp only [hVdef, zero_add] at this ⊢
      rw [this.1, this.2]
    rw [hE, hV1, Matrix.trace_sub, Matrix.trace_mul_comm (V 0) (Ψ 1 s), sub_self]
  have hconst : ∀ s, Matrix.trace (Ψ 1 s) = Matrix.trace (Ψ 1 0) := by
    have hd : ∀ s, HasDerivAt (fun r => Matrix.trace (Ψ 1 r)) 0 s := by
      intro s
      have hs := hEt 1 s
      have e := fun i j => hasDerivAt_mat2_entry hs i j
      simp only [Matrix.trace_fin_two]
      have h0 := hE1 s
      rw [Matrix.trace_fin_two] at h0
      exact ((e 0 0).add (e 1 1)).congr_deriv h0
    intro s
    exact is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt) (fun r => (hd r).deriv) s 0
  -- identification with the Dyson sum
  have hid : ∀ s, halfTraceOf (U s) z = Matrix.trace (Ψ 1 s) / 2 := by
    intro s
    unfold halfTraceOf
    rw [← fundamental_eq_dyson (hUc s) z (G := fun x => Ψ x s) (hΨ0 s) (hΨ · s) 1
      ⟨by norm_num, by norm_num⟩]
  rw [hid t, hid 0, hconst t]

/-! ### Regression probe: the plane-wave solution -/

/-- Phase of the plane wave `a e^{2πi k x - i ω t}`, `ω = (2πk)^2 + 2|a|^2`. -/
def planeWavePhase (a : ℂ) (k : ℤ) (t x : ℝ) : ℂ :=
  2 * Real.pi * Complex.I * k * x - Complex.I * (((2 * Real.pi * k) ^ 2 + 2 * ‖a‖ ^ 2 : ℝ) * t : ℝ)

/-- The plane-wave solution `a e^{2πi k x - i ω t}` of `i u_t = -u_xx + 2|u|^2 u`. -/
def planeWave (a : ℂ) (k : ℤ) (t x : ℝ) : ℂ := a * Complex.exp (planeWavePhase a k t x)

theorem halfTrace_planeWave_const (a : ℂ) (k : ℤ) (z : ℂ) (t : ℝ) :
    halfTraceOf (planeWave a k t) z = halfTraceOf (planeWave a k 0) z := by
  set ω : ℝ := (2 * Real.pi * k) ^ 2 + 2 * ‖a‖ ^ 2 with hω
  set c : ℂ := 2 * Real.pi * Complex.I * k with hc
  have hlin : ∀ s : ℝ, HasDerivAt (fun r : ℝ => (r : ℂ)) 1 s := fun s => (hasDerivAt_id s).ofReal_comp
  have hphx : ∀ t x, HasDerivAt (fun y : ℝ => planeWavePhase a k t y) c x := by
    intro t x
    have e : (fun y : ℝ => planeWavePhase a k t y) =
        fun y : ℝ => c * (y : ℂ) - Complex.I * ((ω * t : ℝ) : ℂ) := by
      funext y; simp only [planeWavePhase, hc, hω]
    rw [e]
    simpa using ((hlin x).const_mul c).sub_const (Complex.I * ((ω * t : ℝ) : ℂ))
  have hpht : ∀ t x, HasDerivAt (fun s : ℝ => planeWavePhase a k s x) (-(Complex.I * ω)) t := by
    intro t x
    have e : (fun s : ℝ => planeWavePhase a k s x) =
        fun s : ℝ => c * (x : ℂ) - (Complex.I * ω) * (s : ℂ) := by
      funext s; simp only [planeWavePhase, hc, hω]; push_cast; ring
    rw [e]
    simpa using ((hlin t).const_mul (Complex.I * (ω : ℂ))).const_sub (c * (x : ℂ))
  have hexp : ∀ t x, HasDerivAt (fun y : ℝ => planeWave a k t y) (c * planeWave a k t x) x := by
    intro t x
    have := ((hphx t x).cexp).const_mul a
    refine this.congr_deriv ?_
    simp only [planeWave]; ring
  have hexpx : ∀ t x, HasDerivAt (fun y : ℝ => c * planeWave a k t y) (c * (c * planeWave a k t x)) x :=
    fun t x => (hexp t x).const_mul c
  have hexpt : ∀ t x, HasDerivAt (fun s : ℝ => planeWave a k s x) (-(Complex.I * ω) * planeWave a k t x) t := by
    intro t x
    have := ((hpht t x).cexp).const_mul a
    refine this.congr_deriv ?_
    simp only [planeWave]; ring
  have hnorm : ∀ t x, ‖planeWave a k t x‖ = ‖a‖ := by
    intro t x
    have e : planeWavePhase a k t x =
        ((2 * Real.pi * k * x - ((2 * Real.pi * k) ^ 2 + 2 * ‖a‖ ^ 2) * t : ℝ) : ℂ) * Complex.I := by
      unfold planeWavePhase; push_cast; ring
    simp only [planeWave, e, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hcont : Continuous (Function.uncurry (planeWave a k)) := by
    unfold planeWave planeWavePhase Function.uncurry
    fun_prop
  have key := halfTrace_const_of_classical (planeWave a k) (fun t x => c * planeWave a k t x)
    (fun t x => c * (c * planeWave a k t x)) (fun t x => -(Complex.I * ω) * planeWave a k t x)
    hcont (by fun_prop) (by fun_prop) (by fun_prop) hexp hexpx hexpt
    (fun t x => by
      have hp : planeWave a k t (x + 1) = planeWave a k t x := by
        have : planeWavePhase a k t (x + 1) = planeWavePhase a k t x + k * (2 * Real.pi * Complex.I) := by
          unfold planeWavePhase; push_cast; ring
        unfold planeWave
        rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      exact ⟨hp, by rw [hp]⟩)
    (fun t x => by
      have hn : ((‖planeWave a k t x‖ ^ 2 : ℝ) : ℂ) = ((‖a‖ ^ 2 : ℝ) : ℂ) := by rw [hnorm]
      rw [hn]
      simp only [hc, hω]
      push_cast
      linear_combination (-(2 * (‖a‖ : ℂ) ^ 2) * planeWave a k t x) * Complex.I_sq) z t
  exact key

end NlsGge.NLS38
