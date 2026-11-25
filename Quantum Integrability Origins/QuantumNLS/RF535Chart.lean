import Mathlib
import QuantumNLS.Ext025A4D01Discharge

/-!
# R-F5355ABD `thm:global-actual-chart` (`actual_chart.tex:15`), stage 3: intertwining of the product action with the coordinate rotations

For any `S : D01LocalPrimitive.Hyp H` and any `Φ : H → ℓ²` with the properties `PhiData S Φ` (differentiable, `q_n ∘ Φ = I_n`, `Φ^*ω = ω` infinitesimally, surjective differentials; all supplied by the accepted R-701613DA for `Φ = Phi S`):
* `fderiv_Phi_ham`: `DΦ(c) X_{I_n}(c) = X_{q_n}(Φ c) = -i Φ(c)_n e_n` (from `ι_X ω = dI_n`, `I_n = q_n ∘ Φ`, full symplecticity and surjectivity of `DΦ(c)`; the printed "full symplectic chain rule and the exact action identities");
* `Phi_rho_single`: `Φ(ρ_{t e_n} u) = R_{t e_n} Φ(u)` for all real times (uniqueness of the Lipschitz ODE `z' = X_{q_n}(z)` on `ℓ²`, Mathlib `ODE_solution_unique_univ`);
* `Phi_rho_sum`: finite compositions; `Phi_rho`: the full product torus, from joint continuity of `ρ` and finite-angle approximation `trunc θ N → θ` in the product topology (the printed "joint continuity and finite-angle approximation in the product topology");
* `fibre_image`: `Φ` carries `{u | I(u) = a}` exactly onto `{z | |z_n|² = a_n}` (surjectivity and the exact inverse; arbitrary zero sets and infinite support);
* `orbit_positive` / `orbit_zero`: the individual orbit `t ↦ ρ_{t e_n} u` has exactly the periods `2πℤ` (least positive period `2π`) when `I_n(u) > 0` and is fixed when `I_n(u) = 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open Set Filter Topology Metric
open scoped ComplexConjugate

namespace QuantumNLS.RF535Chart
open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The properties of the chart `Φ : H → ℓ²` of `thm:global-D01-reconstruction` that drive the
intertwining with the coordinate rotations. -/
structure PhiData (S : Hyp H) (Φ : H → K) : Prop where
  diff : Differentiable ℝ Φ
  mass : ∀ u n, q n (Φ u) = S.act u n
  symp : ∀ u h k, omega (fderiv ℝ Φ u h) (fderiv ℝ Φ u k) = omega h k
  surj : ∀ u, Function.Surjective (fderiv ℝ Φ u)

/-- Full symplecticity turns the Hamiltonian field of `I_n` into the coordinate rotation generator. -/
theorem fderiv_Phi_ham (S : Hyp H) {Φ : H → K} (hΦ : PhiData S Φ) (n : ℤ) (c : H) :
    fderiv ℝ Φ c (hamField (fun v => S.act v n) c) = Xq n (Φ c) := by
  refine omega_eq_of_forall fun w => ?_
  obtain ⟨k, rfl⟩ := hΦ.surj c w
  rw [hΦ.symp, omega_hamField, omega_Xq_eq_fderiv]
  have h := (hasFDerivAt_q n (Φ c)).comp c (hΦ.diff c).hasFDerivAt
  have e : (q n ∘ Φ) = fun v => S.act v n := funext fun v => hΦ.mass v n
  rw [e] at h
  rw [h.fderiv, ContinuousLinearMap.comp_apply, (hasFDerivAt_q n (Φ c)).fderiv]

/-- The individual circle: `Φ ∘ ρ_{x e_n} = R_{x e_n} ∘ Φ`. -/
theorem Phi_rho_single (S : Hyp H) {Φ : H → K} (hΦ : PhiData S Φ) (n : ℤ) (x : Real.Angle) (u : H) :
    Φ (S.rho (Pi.single n x) u) = Rot (Pi.single n x) (Φ u) := by
  obtain ⟨t, rfl⟩ := angle_surj x
  have hc : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Φ (S.rho (Pi.single n (s : Real.Angle)) u))
      (Xq n (Φ (S.rho (Pi.single n (s : Real.Angle)) u))) s := fun s => by
    have := (hΦ.diff _).hasFDerivAt.comp_hasDerivAt s (S.rho_flow n u s)
    exact this.congr_deriv (fderiv_Phi_ham S hΦ n _)
  have h0 : (fun s : ℝ => Φ (S.rho (Pi.single n (s : Real.Angle)) u)) 0 =
      (fun s : ℝ => Rot (Pi.single n (s : Real.Angle)) (Φ u)) 0 := by
    simp only [Real.Angle.coe_zero, Pi.single_zero, S.rho_zero, id_eq, Rot_zero]
  have := congrFun (ODE_solution_unique_univ (v := fun _ => Xq n) (K := 1) (s := fun _ => univ)
    (fun _ => (lipschitz_Xq n).lipschitzOnWith) (fun s => ⟨hc s, trivial⟩)
    (fun s => ⟨hasDerivAt_Rot_single n (Φ u) s, trivial⟩) h0) t
  exact this

/-- Finite products of circles. -/
theorem Phi_rho_sum (S : Hyp H) {Φ : H → K} (hΦ : PhiData S Φ) (θ : Tor) (s : Finset ℤ) (u : H) :
    Φ (S.rho (∑ n ∈ s, Pi.single n (θ n)) u) = Rot (∑ n ∈ s, Pi.single n (θ n)) (Φ u) := by
  classical
  induction s using Finset.induction_on generalizing u with
  | empty => simp [S.rho_zero, Rot_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, S.rho_add, Function.comp_apply, Rot_add, ← ih, ← Phi_rho_single S hΦ]

/-- **Intertwining**: `Φ ∘ ρ_θ = R_θ ∘ Φ` for every point `θ` of the product torus. -/
theorem Phi_rho (S : Hyp H) {Φ : H → K} (hΦ : PhiData S Φ) (θ : Tor) (u : H) :
    Φ (S.rho θ u) = Rot θ (Φ u) := by
  have h1 : Tendsto (fun N : ℕ => Φ (S.rho (trunc θ N) u)) atTop (𝓝 (Φ (S.rho θ u))) :=
    ((hΦ.diff.continuous.comp S.rho_cont).tendsto (θ, u)).comp
      ((tendsto_trunc θ).prodMk_nhds tendsto_const_nhds)
  have h2 : Tendsto (fun N : ℕ => Rot (trunc θ N) (Φ u)) atTop (𝓝 (Rot θ (Φ u))) := tendsto_Rot_trunc θ (Φ u)
  refine tendsto_nhds_unique h1 (h2.congr fun N => ?_)
  exact (Phi_rho_sum S hΦ θ (Finset.Icc (-(N : ℤ)) N) u).symm


/-- Exact action fibres go onto the full coordinate-modulus torus. -/
theorem fibre_image (S : Hyp H) {Φ : H → K} {Ψ : K → H} (hΦΨ : ∀ z, Φ (Ψ z) = z)
    (hmass : ∀ u n, q n (Φ u) = S.act u n) (a : L1) :
    Φ '' {u | S.act u = a} = {z : K | ∀ n, ‖z n‖ ^ 2 = a n} := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩ n
    have := hmass u n
    rw [← hu]
    exact this
  · intro hz
    refine ⟨Ψ z, ?_, hΦΨ z⟩
    refine Subtype.ext (funext fun n => ?_)
    show S.act (Ψ z) n = a n
    rw [← hmass, hΦΨ]
    exact hz n

theorem ph_eq_one_iff (t : ℝ) : ph (t : Real.Angle) = 1 ↔ ∃ k : ℤ, t = 2 * Real.pi * k := by
  rw [ph_coe, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    have h := congrArg Complex.im hk
    simp at h
    push_cast
    nlinarith [h]
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    rw [hk]
    push_cast
    ring

/-- The orbit of a positive action has exactly the periods `2π ℤ`. -/
theorem orbit_positive (S : Hyp H) {Φ : H → K} {Ψ : K → H} (hΦ : PhiData S Φ) (hΨΦ : ∀ u, Ψ (Φ u) = u)
    (n : ℤ) (u : H) (hu : 0 < S.act u n) (t : ℝ) :
    S.rho (Pi.single n (t : Real.Angle)) u = u ↔ ∃ k : ℤ, t = 2 * Real.pi * k := by
  have hz : Φ u n ≠ 0 := by
    intro h0
    have := hΦ.mass u n
    simp only [q, h0, norm_zero] at this
    rw [← this] at hu
    norm_num at hu
  have key : S.rho (Pi.single n (t : Real.Angle)) u = u ↔ Rot (Pi.single n (t : Real.Angle)) (Φ u) = Φ u := by
    constructor
    · intro h
      rw [← Phi_rho_single S hΦ, h]
    · intro h
      have := Phi_rho_single S hΦ n (t : Real.Angle) u
      rw [h] at this
      calc S.rho (Pi.single n (t : Real.Angle)) u = Ψ (Φ (S.rho (Pi.single n (t : Real.Angle)) u)) := (hΨΦ _).symm
        _ = Ψ (Φ u) := by rw [this]
        _ = u := hΨΦ u
  rw [key, ← ph_eq_one_iff]
  constructor
  · intro h
    have := congrFun (congrArg (fun z : K => (z : ℤ → ℂ)) h) n
    simp only [Rot_apply, Pi.single_eq_same] at this
    have h2 : (ph (t : Real.Angle) - 1) * Φ u n = 0 := by linear_combination this
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact sub_eq_zero.1 h3
    · exact absurd h3 hz
  · intro h
    refine lp.ext (funext fun m => ?_)
    rw [Rot_apply]
    by_cases hm : m = n
    · subst hm; rw [Pi.single_eq_same, h, one_mul]
    · rw [Pi.single_eq_of_ne hm, ph_zero, one_mul]

/-- A zero action coordinate is fixed by its circle. -/
theorem orbit_zero (S : Hyp H) {Φ : H → K} {Ψ : K → H} (hΦ : PhiData S Φ) (hΨΦ : ∀ u, Ψ (Φ u) = u)
    (n : ℤ) (u : H) (hu : S.act u n = 0) (t : ℝ) : S.rho (Pi.single n (t : Real.Angle)) u = u := by
  have hz : Φ u n = 0 := by
    have := hΦ.mass u n
    rw [hu] at this
    simpa [q] using this
  have h1 := Phi_rho_single S hΦ n (t : Real.Angle) u
  have h2 : Rot (Pi.single n (t : Real.Angle)) (Φ u) = Φ u := by
    refine lp.ext (funext fun m => ?_)
    rw [Rot_apply]
    by_cases hm : m = n
    · subst hm; rw [hz, mul_zero]
    · rw [Pi.single_eq_of_ne hm, ph_zero, one_mul]
  rw [h2] at h1
  calc S.rho (Pi.single n (t : Real.Angle)) u = Ψ (Φ (S.rho (Pi.single n (t : Real.Angle)) u)) := (hΨΦ _).symm
    _ = Ψ (Φ u) := by rw [h1]
    _ = u := hΨΦ u

end QuantumNLS.RF535Chart

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.RF535Chart.fderiv_Phi_ham
#print axioms QuantumNLS.RF535Chart.Phi_rho_single
#print axioms QuantumNLS.RF535Chart.Phi_rho
#print axioms QuantumNLS.RF535Chart.fibre_image
#print axioms QuantumNLS.RF535Chart.orbit_positive
#print axioms QuantumNLS.RF535Chart.orbit_zero
