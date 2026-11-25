import Mathlib
import QuantumNLS.Ext006BogoliubovAlg
import QuantumNLS.Ext006VacuumRecurrence

/-! PROP-023 / FIN-CORE-BD-02, gap 1 (stage C): a pure quasifree vacuum is a weak squeezed vacuum.

`PureQuasifree ξ`: `ξ = V Ω` for a unitary `V` of the occupation Fock space that implements a
Bogoliubov map `(α, β)` (bounded, `IsBogoliubov`), in the weak form of `V a_d V^* = ∑_c α_{dc} a_c +
β_{dc} a_c^*`: for all `d` and finite occupations `m, n`,
`⟨e_n, V a_d e_m⟩ = (α x)_d + (β y)_d` with `x_c = ⟨e_n, a_c V e_m⟩ = √(n_c+1) (V e_m)(n+e_c)` and
`y_c = ⟨e_n, a_c^* V e_m⟩ = √n_c (V e_m)(n-e_c)`.

`quasifree_weak`: then `ξ` satisfies `Ext006VacuumRecurrence.WeakVacuum K` with the symmetric kernel
`K = α^{-1} β` (entries `K_{ab} = ⟨e_a, K e_b⟩`). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.Ext006QuasifreeWeak
open Occupation Ext006VacuumRecurrence Ext006BogoliubovAlg

lemma n_le_total (n : Occ) (c : ℤ) : n c ≤ total n := by
  by_cases hc : c ∈ n.support
  · exact Finset.single_le_sum (f := fun i => n i) (fun _ _ => Nat.zero_le _) hc
  · have : n c = 0 := by simpa using hc
    omega

lemma summable_sq (w : Fock) : Summable (fun m : Occ => ‖w m‖ ^ 2) := by
  have hs := lp.hasSum_norm (E := fun _ : Occ => ℂ) (p := 2) (by norm_num) w
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs.summable

def xcoord (w : Fock) (n : Occ) (c : ℤ) : ℂ :=
  (Real.sqrt ((n c : ℝ) + 1) : ℂ) * w (n + e c)

def ycoord (w : Fock) (n : Occ) (c : ℤ) : ℂ :=
  (Real.sqrt (n c : ℝ) : ℂ) * w (n - e c)

lemma norm_sq_sqrt_mul (a : ℝ) (ha : 0 ≤ a) (z : ℂ) :
    ‖(Real.sqrt a : ℂ) * z‖ ^ 2 = a * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt ha]

lemma memℓp_xcoord (w : Fock) (n : Occ) : Memℓp (xcoord w n) 2 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  have hinj : Function.Injective (fun c : ℤ => n + e c) := by
    intro a b hab
    have := add_left_cancel hab
    exact (Finsupp.single_left_injective one_ne_zero) this
  have hs := (summable_sq w).comp_injective hinj
  refine Summable.of_nonneg_of_le (fun c => by positivity) (fun c => ?_)
    (hs.mul_left ((total n : ℝ) + 1))
  simp only [xcoord, Function.comp]
  rw [norm_sq_sqrt_mul _ (by positivity)]
  have := n_le_total n c
  have h2 : ((n c : ℝ) + 1) ≤ (total n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ this
  exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)

lemma memℓp_ycoord (w : Fock) (n : Occ) : Memℓp (ycoord w n) 2 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  apply summable_of_ne_finset_zero (s := n.support)
  intro c hc
  have : n c = 0 := by simpa using hc
  simp [ycoord, this]

def xvec (w : Fock) (n : Occ) : H := ⟨xcoord w n, memℓp_xcoord w n⟩
def yvec (w : Fock) (n : Occ) : H := ⟨ycoord w n, memℓp_ycoord w n⟩

lemma xvec_apply (w : Fock) (n : Occ) (c : ℤ) : xvec w n c = xcoord w n c := rfl
lemma yvec_apply (w : Fock) (n : Occ) (c : ℤ) : yvec w n c = ycoord w n c := rfl

/-- The weak form of `V a_d V^* = ∑_c α_{dc} a_c + β_{dc} a_c^*`. -/
def Implements (V : Fock ≃ₗᵢ[ℂ] Fock) (α β : H →L[ℂ] H) : Prop :=
  ∀ (d : ℤ) (m n : Occ),
    (Real.sqrt (m d : ℝ) : ℂ) * (V (lp.single 2 (m - e d) (1 : ℂ))) n =
      (α (xvec (V (lp.single 2 m (1 : ℂ))) n)) d + (β (yvec (V (lp.single 2 m (1 : ℂ))) n)) d

/-- A pure quasifree vacuum: `ξ = V Ω` for a unitary `V` implementing a Bogoliubov map. -/
def PureQuasifree (ξ : Occ → ℂ) : Prop :=
  ∃ (V : Fock ≃ₗᵢ[ℂ] Fock) (α β : H →L[ℂ] H), IsBogoliubov α β ∧ Implements V α β ∧
    ∀ n, ξ n = (V (lp.single 2 (0 : Occ) (1 : ℂ))) n

lemma yvec_eq_sum (w : Fock) (n : Occ) :
    yvec w n = ∑ c ∈ n.support, ycoord w n c • lp.single 2 c (1 : ℂ) := by
  apply lp.ext
  funext d
  rw [lp.coeFn_sum]
  rw [Finset.sum_apply]
  have hterm : ∀ c : ℤ, ((ycoord w n c • (lp.single 2 c (1 : ℂ) : H) : H) d : ℂ) =
      if c = d then ycoord w n c else 0 := by
    intro c
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    by_cases h : d = c
    · subst h
      simp [lp.single_apply_self]
    · have h' : c ≠ d := Ne.symm h
      simp [lp.single_apply_ne _ _ _ h, h']
  simp_rw [hterm]
  rw [Finset.sum_ite_eq']
  by_cases hd : d ∈ n.support
  · simp [hd, yvec_apply]
  · have : n d = 0 := by simpa using hd
    simp [hd, yvec_apply, ycoord, this]

theorem quasifree_weak {ξ : Occ → ℂ} (h : PureQuasifree ξ) :
    ∃ K : Kernel, (∀ i j, K i j = K j i) ∧ WeakVacuum K ξ := by
  obtain ⟨V, α, β, hB, hI, hξ⟩ := h
  obtain ⟨K, hK1, hK2, hinj⟩ := exists_kernel hB
  set w : Fock := V (lp.single 2 (0 : Occ) (1 : ℂ)) with hw
  have hξw : ξ = fun n => w n := funext hξ
  refine ⟨fun a b => (K (lp.single 2 b (1 : ℂ))) a, ?_, ?_⟩
  · intro i j
    have h1 := tp_entry K j i
    rw [hK2] at h1
    exact h1
  · intro a m
    rw [hξw]
    -- annihilation equation at the vacuum: α x + β y = 0
    have hrel : ∀ d, (α (xvec w m)) d + (β (yvec w m)) d = 0 := by
      intro d
      have := hI d 0 m
      simpa using this.symm
    have hzero : α (xvec w m) + β (yvec w m) = 0 := by
      apply lp.ext
      funext d
      simpa using hrel d
    have hx : xvec w m = -(K (yvec w m)) := by
      apply hinj
      rw [map_neg, hK1]
      exact eq_neg_of_add_eq_zero_left hzero
    have hcoord := congrArg (fun z : H => z a) hx
    simp only [xvec_apply, xcoord, lp.coeFn_neg, Pi.neg_apply] at hcoord
    rw [yvec_eq_sum, map_sum, lp.coeFn_sum] at hcoord
    simp only [Finset.sum_apply, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at hcoord
    rw [hcoord, neg_inj]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [ycoord]
    ring

end QuantumNLS.Ext006QuasifreeWeak
#print axioms QuantumNLS.Ext006QuasifreeWeak.quasifree_weak
