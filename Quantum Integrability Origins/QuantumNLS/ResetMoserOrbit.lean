import QuantumNLS.ResetMoserTorusPeriod
import QuantumNLS.Ext025B7LocalPath
import QuantumNLS.LOCAL017HaarAngular

/-!
# `thm:reset-moser` (LOCAL-017), stage 3e (item 2(c), conclusion): a periodic primitive of `β` on every finite coordinate torus

Source: `symplectic_correction.tex`, "The periods of a radial primitive": "Lifting again to `ℝ^{|F|}` gives a periodic primitive of this restricted one-form."
This is the finite-torus primitive that item 3 (the Haar primitive, `LOCAL017Haar*`) consumes as its `OrbitPotential` interface.

* `Gint_periodic`: `G` takes the same value at angle vectors differing by `2πℤ` on the support;
* `valueO S T z w = G((arg(w_n/z_n))_n)`; `Hyp.valueO_rotate`: on the torus of `z`, `valueO(R_θ z) = G(θ)` for every real angle vector `θ`;
* **`Hyp.orbitPot`**: for every `z ∈ B_ρ` with finite support, `Nonempty (LOCAL017Haar.OrbitPotential (betaR S) z)`, the frozen interface of
  `LOCAL017HaarAngular` (value function; continuity on the torus; derivative along every literal ray `LOCAL017Haar.ray` equal to
  `β_{R_{tθ}w}(iΘ R_{tθ}w)`), i.e. exactly the `hpot` hypothesis of `LOCAL017Haar.reset_moser_hann`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric MeasureTheory
open scoped Interval

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.RealAnalyticDef
open QuantumNLS.ResetMoserFlow QuantumNLS.ResetMoserSurface
open QuantumNLS.Ext025B7LocalPath ActionTorus

theorem Gint_shiftN (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {z : K} (hz : z ∈ ball (0 : K) ρ)
    {T : Finset ℤ} (hT : ∀ n, z n ≠ 0 ↔ n ∈ T) {j : ℤ} (hj : j ∈ T) (n : ℤ) (θ : ℤ → ℝ) :
    Gint S T z (fun k => θ k + if k = j then 2 * Real.pi * n else 0) = Gint S T z θ := by
  induction n using Int.induction_on generalizing θ with
  | zero => simp
  | succ n ih =>
    have h := S.Gint_shift hL hz hT hj (fun k => θ k + if k = j then 2 * Real.pi * ((n : ℤ) : ℝ) else 0)
    rw [ih] at h
    rw [← h]
    refine Gint_congr S T z fun k _ => ?_
    simp only [shiftJ]
    split_ifs <;> push_cast <;> ring
  | pred n ih =>
    have h := S.Gint_shift hL hz hT hj (fun k => θ k + if k = j then 2 * Real.pi * ((-(n : ℤ) - 1 : ℤ) : ℝ) else 0)
    have e : Gint S T z (shiftJ j (2 * Real.pi) (fun k => θ k + if k = j then 2 * Real.pi * ((-(n : ℤ) - 1 : ℤ) : ℝ) else 0)) =
        Gint S T z (fun k => θ k + if k = j then 2 * Real.pi * ((-(n : ℤ) : ℤ) : ℝ) else 0) := by
      refine Gint_congr S T z fun k _ => ?_
      simp only [shiftJ]
      split_ifs <;> push_cast <;> ring
    rw [e, ih] at h
    exact h.symm

theorem Gint_periodic (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {z : K} (hz : z ∈ ball (0 : K) ρ)
    {T : Finset ℤ} (hT : ∀ n, z n ≠ 0 ↔ n ∈ T) (θ θ'' : ℤ → ℝ)
    (h : ∀ k ∈ T, ∃ n : ℤ, θ'' k = θ k + 2 * Real.pi * n) : Gint S T z θ'' = Gint S T z θ := by
  choose! m hm using h
  have key : ∀ F : Finset ℤ, F ⊆ T → ∀ θ : ℤ → ℝ,
      Gint S T z (fun k => θ k + if k ∈ F then 2 * Real.pi * (m k) else 0) = Gint S T z θ := by
    intro F
    induction F using Finset.induction_on with
    | empty => intro _ θ; simp
    | insert a F ha ih =>
      intro hF θ
      have haT : a ∈ T := hF (Finset.mem_insert_self a F)
      have hFT : F ⊆ T := fun x hx => hF (Finset.mem_insert_of_mem hx)
      have h1 := Gint_shiftN S hL hz hT haT (m a) (fun k => θ k + if k ∈ F then 2 * Real.pi * (m k) else 0)
      have h2 := ih hFT θ
      rw [← h2, ← h1]
      refine Gint_congr S T z fun k _ => ?_
      by_cases hk : k = a
      · subst hk; simp [ha]
      · simp [hk, Finset.mem_insert]
        try (split_ifs <;> ring)
  have := key T (subset_refl T) θ
  rw [← this]
  exact Gint_congr S T z fun k hk => by simp [hk, hm k hk]

theorem exp_arg_unit {u : ℂ} (hu : ‖u‖ = 1) : Complex.exp (Complex.I * (Complex.arg u : ℂ)) = u := by
  have := Complex.norm_mul_exp_arg_mul_I u
  rw [hu] at this
  simpa [mul_comm] using this

theorem arg_of_exp {u : ℂ} (hu : ‖u‖ = 1) {x : ℝ} (h : Complex.exp (Complex.I * (x : ℂ)) = u) :
    ∃ n : ℤ, Complex.arg u = x + 2 * Real.pi * n := by
  have h1 := exp_arg_unit hu
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h1.trans h.symm)
  refine ⟨n, ?_⟩
  have h2 : Complex.I * (Complex.arg u : ℂ) = Complex.I * ((x + 2 * Real.pi * n : ℝ) : ℂ) := by
    rw [hn]; push_cast; ring
  exact_mod_cast mul_left_cancel₀ Complex.I_ne_zero h2

theorem arg_exp_shift (x : ℝ) : ∃ n : ℤ, Complex.arg (Complex.exp (Complex.I * (x : ℂ))) = x + 2 * Real.pi * n :=
  arg_of_exp (Complex.norm_exp_I_mul_ofReal x) rfl

/-- The value function. -/
def valueO (S : Hyp) (T : Finset ℤ) (z : K) (w : K) : ℝ := Gint S T z (fun n => Complex.arg (w n / z n))

theorem Gint_cont (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {z : K} (hz : z ∈ ball (0 : K) ρ)
    {T : Finset ℤ} (hT : ∀ n, z n ≠ 0 → n ∈ T) : Continuous (fun θ : ℤ → ℝ => Gint S T z θ) := by
  unfold Gint
  have hzn := mem_ball_zero_iff.1 hz
  have hmem : ∀ (θ : ℤ → ℝ) (r : ℝ), Emb T (sg z θ r) ∈ ball (0 : K) ρ := fun θ r => by
    rw [mem_ball_zero_iff, norm_Emb_sg hT]; exact hzn
  have hβc : ContinuousOn (betaR S) (ball (0 : K) ρ) := fun x hx =>
    (betaR_hasFDerivAt S hL hx).continuousAt.continuousWithinAt
  have h1 : Continuous (fun p : (ℤ → ℝ) × ℝ => Emb T (sg z p.1 p.2)) :=
    Emb_continuous T fun k _ => by
      unfold sg
      have h3 : Continuous fun a : (ℤ → ℝ) × ℝ => a.1 k := (continuous_apply k).comp continuous_fst
      exact (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_snd.mul h3)))).mul continuous_const
  have h2 : Continuous (fun p : (ℤ → ℝ) × ℝ => Emb T (uu z p.1 p.2)) :=
    Emb_continuous T fun k _ => by
      unfold uu sg
      have h3 : Continuous fun a : (ℤ → ℝ) × ℝ => a.1 k := (continuous_apply k).comp continuous_fst
      exact (continuous_const.mul (Complex.continuous_ofReal.comp h3)).mul
        ((Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_snd.mul h3)))).mul continuous_const)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun θ r => betaR S (Emb T (sg z θ r)) (Emb T (uu z θ r)))
    ((hβc.comp_continuous h1 (fun p => hmem p.1 p.2)).clm_apply h2) 0 1

theorem Hyp.valueO_rotate (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {z : K} (hz : z ∈ ball (0 : K) ρ)
    {T : Finset ℤ} (hT : ∀ n, z n ≠ 0 ↔ n ∈ T) (θ : ℤ → ℝ) :
    valueO S T z (rotate (fun n => Circle.exp (θ n)) z) = Gint S T z θ := by
  unfold valueO
  refine Gint_periodic S hL hz hT θ _ fun k hk => ?_
  have hkz := (hT k).2 hk
  have : (rotate (fun n => Circle.exp (θ n)) z) k / z k = Complex.exp (Complex.I * (θ k : ℂ)) := by
    rw [rotate_apply, Circle.coe_exp]
    field_simp
  rw [this]
  exact arg_exp_shift (θ k)

theorem LOCAL017Haar.ray_rotate (θ : AngleBox) (η : ℤ → Circle) (z : K) (s : ℝ) :
    LOCAL017Haar.ray θ s (rotate η z) = rotate (fun n => Circle.exp (Complex.arg (η n) + s * (θ n).val)) z := by
  ext n
  simp only [LOCAL017Haar.ray, rotate_apply]
  have h1 : ((η n : Circle) : ℂ) = ((Circle.exp (Complex.arg (η n)) : Circle) : ℂ) := by
    rw [Circle.exp_arg]
  have h2 : ((Circle.exp (Complex.arg (η n) + s * (θ n).val) : Circle) : ℂ) =
      ((η n : Circle) : ℂ) * ((Circle.exp (s * (θ n).val) : Circle) : ℂ) := by
    rw [Circle.exp_add, Circle.coe_mul, ← h1]
  rw [h2]
  ring

theorem Hyp.orbitPot_derivative (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {z : K} (hz : z ∈ ball (0 : K) ρ)
    {T : Finset ℤ} (hT : ∀ n, z n ≠ 0 ↔ n ∈ T) (η : ℤ → Circle) (θ : AngleBox) (t : ℝ) :
    HasDerivAt (fun s => valueO S T z (LOCAL017Haar.ray θ s (rotate η z)))
      (betaR S (LOCAL017Haar.ray θ t (rotate η z)) (velocity θ (LOCAL017Haar.ray θ t (rotate η z)))) t := by
  set c : ℝ → ℤ → ℝ := fun s k => Complex.arg (η k) + s * (θ k).val with hc
  have hval : (fun s => valueO S T z (LOCAL017Haar.ray θ s (rotate η z))) = fun s => Gint S T z (c s) := by
    funext s
    rw [LOCAL017Haar.ray_rotate]
    exact S.valueO_rotate hL hz hT (c s)
  rw [hval]
  have hdc : ∀ k ∈ T, ∀ s, HasDerivAt (fun s => c s k) ((θ k).val) s := by
    intro k _ s
    have := ((hasDerivAt_id s).mul_const (θ k).val).const_add (Complex.arg (η k))
    simpa [hc] using this
  have hd := S.Gint_hasDerivAt hL hz (fun n hn => (hT n).1 hn) (θ := c) (θ' := fun _ k => (θ k).val)
    hdc (fun k _ => continuous_const) t
  have hw : Emb T (sg z (c t) 1) = LOCAL017Haar.ray θ t (rotate η z) := by
    ext n
    rw [Emb_apply, LOCAL017Haar.ray_rotate, rotate_apply, Circle.coe_exp]
    by_cases hn : n ∈ T
    · simp only [hn, if_true, sg, one_mul]
      rw [mul_comm Complex.I]
    · have : z n = 0 := by
        by_contra h; exact hn ((hT n).1 h)
      simp [hn, this]
  have hwn : ∀ n, Emb T (sg z (c t) 1) n = LOCAL017Haar.ray θ t (rotate η z) n := fun n => by rw [hw]
  have hv : Emb T (vv z (c t) (fun k => (θ k).val) 1) = velocity θ (LOCAL017Haar.ray θ t (rotate η z)) := by
    ext n
    rw [Emb_apply, velocity_apply, ← hwn n, Emb_apply]
    by_cases hn : n ∈ T
    · simp only [hn, if_true, vv, one_mul]
    · simp [hn]
  refine hd.congr_deriv ?_
  rw [hw]
  exact congrArg _ hv

theorem Hyp.orbitPot (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {z : K} (hz : z ∈ ball (0 : K) ρ)
    (hfin : {n | z n ≠ 0}.Finite) : Nonempty (LOCAL017Haar.OrbitPotential (betaR S) z) := by
  set T := hfin.toFinset with hTdef
  have hT : ∀ n, z n ≠ 0 ↔ n ∈ T := fun n => by simp [hTdef]
  refine ⟨⟨valueO S T z, ?_, fun η θ t => S.orbitPot_derivative hL hz hT η θ t⟩⟩
  refine continuous_iff_continuousAt.2 fun ψ₀ => ?_
  set ℓ : (ℤ → Circle) → ℤ → ℝ := fun ψ k =>
    if k ∈ T then Complex.arg (ψ₀ k : ℂ) + Complex.arg ((ψ k : ℂ) * conj (ψ₀ k : ℂ)) else 0 with hℓ
  have hmc : ∀ k, (ψ₀ k : ℂ) * conj (ψ₀ k : ℂ) = 1 := fun k => by
    rw [Complex.mul_conj', Circle.norm_coe]; simp
  have heq : (fun ψ : ℤ → Circle => valueO S T z (rotate ψ z)) = fun ψ => Gint S T z (ℓ ψ) := by
    funext ψ
    unfold valueO
    refine Gint_periodic S hL hz hT (ℓ ψ) _ fun k hk => ?_
    have hkz := (hT k).2 hk
    have hq : (rotate ψ z) k / z k = (ψ k : ℂ) := by
      rw [rotate_apply]; field_simp
    rw [hq]
    refine arg_of_exp (Circle.norm_coe _) ?_
    simp only [hℓ, hk, if_true]
    push_cast
    rw [mul_add, Complex.exp_add, exp_arg_unit (Circle.norm_coe _),
      exp_arg_unit (by rw [norm_mul, Complex.norm_conj, Circle.norm_coe, Circle.norm_coe, one_mul])]
    calc (ψ₀ k : ℂ) * ((ψ k : ℂ) * conj (ψ₀ k : ℂ)) = (ψ k : ℂ) * ((ψ₀ k : ℂ) * conj (ψ₀ k : ℂ)) := by ring
      _ = (ψ k : ℂ) := by rw [hmc k, mul_one]
  rw [heq]
  have hlc : ContinuousAt ℓ ψ₀ := by
    refine continuousAt_pi.2 fun k => ?_
    by_cases hk : k ∈ T
    · simp only [hℓ, hk, if_true]
      refine continuousAt_const.add ?_
      have hf : Continuous (fun ψ : ℤ → Circle => (ψ k : ℂ) * conj (ψ₀ k : ℂ)) :=
        (continuous_subtype_val.comp (continuous_apply k)).mul continuous_const
      have hs : (ψ₀ k : ℂ) * conj (ψ₀ k : ℂ) ∈ Complex.slitPlane := by
        rw [hmc k]; exact Complex.one_mem_slitPlane
      exact ContinuousAt.comp (g := Complex.arg) (f := fun ψ : ℤ → Circle => (ψ k : ℂ) * conj (ψ₀ k : ℂ))
        (Complex.continuousAt_arg hs) hf.continuousAt
    · simp only [hℓ, hk, if_false]
      exact continuousAt_const
  exact ContinuousAt.comp (g := fun θ : ℤ → ℝ => Gint S T z θ) (f := ℓ)
    (Gint_cont S hL hz (fun n hn => (hT n).1 hn)).continuousAt hlc

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.Gint_periodic
#print axioms QuantumNLS.ResetMoser.arg_exp_shift
#print axioms QuantumNLS.ResetMoser.Hyp.orbitPot_derivative
#print axioms QuantumNLS.ResetMoser.Hyp.orbitPot
