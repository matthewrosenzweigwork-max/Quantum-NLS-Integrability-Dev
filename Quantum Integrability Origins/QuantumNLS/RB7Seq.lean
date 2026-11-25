import Mathlib
import QuantumNLS.RB7Flow

/-!
# R-7B122087 `thm:hierarchy`, stage S+T assembled: rotation-invariant `C²` functionals give the constant-action flows

`SeqData V ι` is the printed hypothesis package of the sequence-side argument: for each order `r ∈ ι` a `C²` real functional
`F_r` on the weighted space `WSeq (W r)` (printed: `F_r = I_{r+1} ∘ (Z^{new})^{-1}` on `h^s`, `s = 3(r+2)+1`), invariant under every
coordinatewise rotation (printed: "`F_r` is invariant under all coordinatewise rotations"), together with comparison weights `W r ≤ C_r V`
(`h^a ↪ h^{s_r}` for `a ≥ s_r`).  Nothing about charts, REG-015 or DEF-024 is used; those enter only when `F_r` is produced.

Proved here (printed proof, second to fourth paragraphs, in sequence coordinates):

* the frequencies `Ω_{r,j}(z) = Re(conj z_j ∇_j F_r(incl z))/|z_j|²`, `∇_j F_r = Ω_{r,j} z_j`  (`SeqData.grad_eq`), constant on modulus tori;
* the flow `z_j(t) = e^{-i Σ_r t_r Ω_{r,j}(z)} z_j` (group law, finite families commute, moduli and every `F_r` conserved);
* `|Ω_{r,j}(z)| ≤ C_z (W_r)_j` and smoothness in `t` into every weighted space `WSeq V` for smooth data (`nu_bound`, `flow_smul_contDiff`);
* the full orbit is relatively compact (inside the compact modulus torus), `(t,z) ↦ flow t z` is jointly continuous;
* density: invariance of a continuous functional on finitely supported sequences extends to all of `WSeq W` (`inv_of_finite`);
* for the DEF-002 scale `h^b`: the `ν`-moment summability needed for time smoothness holds for every `z ∈ ⋂_b h^b` (`hzP_of_Hinf`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate Topology
open Filter Set Metric

namespace QuantumNLS.RB7

open QuantumNLS.Sobolev
open QuantumNLS.Sobolev.PosWeight

/-! ## Density: invariance on finitely supported sequences extends -/

section Density

variable {W : PosWeight}

/-- Truncation to a finite set of coordinates. -/
def trunc (S : Finset ℤ) (z : WSeq W) : WSeq W :=
  WSeq.mk W (fun j => if j ∈ S then z.val j else 0) (z.summable.of_nonneg_of_le
    (fun n => mul_nonneg (W.pos n).le (sq_nonneg _)) (fun n => by
      by_cases h : n ∈ S <;> simp [h, mul_nonneg, (W.pos n).le]))

@[simp] theorem trunc_val (S : Finset ℤ) (z : WSeq W) (j : ℤ) :
    (trunc S z).val j = if j ∈ S then z.val j else 0 := rfl

theorem rot_trunc (u : ℤ → Circle) (S : Finset ℤ) (z : WSeq W) : rot u (trunc S z) = trunc S (rot u z) :=
  WSeq.ext (funext fun j => by by_cases h : j ∈ S <;> simp [h])

theorem tendsto_trunc (z : WSeq W) : Tendsto (fun S : Finset ℤ => trunc S z) atTop (𝓝 z) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun s : Finset ℤ => ∑ j ∈ s, W.w j * ‖z.val j‖ ^ 2) atTop (𝓝 (‖z‖ ^ 2)) :=
    hasSum_norm_sq W z
  have h1 : Tendsto (fun S : Finset ℤ => ‖z‖ ^ 2 - ∑ j ∈ S, W.w j * ‖z.val j‖ ^ 2) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := ‖z‖ ^ 2)).sub h0
    rwa [sub_self] at this
  have key : ∀ S : Finset ℤ, ‖trunc S z - z‖ ^ 2 = ‖z‖ ^ 2 - ∑ j ∈ S, W.w j * ‖z.val j‖ ^ 2 := by
    intro S
    classical
    have hS : HasSum (fun j => if j ∈ S then W.w j * ‖z.val j‖ ^ 2 else 0)
        (∑ j ∈ S, W.w j * ‖z.val j‖ ^ 2) := by
      have : HasSum (fun j => if j ∈ S then W.w j * ‖z.val j‖ ^ 2 else 0)
          (∑ j ∈ S, (if j ∈ S then W.w j * ‖z.val j‖ ^ 2 else 0)) :=
        hasSum_sum_of_ne_finset_zero (fun j hj => by simp [hj])
      rwa [Finset.sum_congr rfl (fun j hj => if_pos hj)] at this
    have hd := (hasSum_norm_sq W z).sub hS
    have hq := hasSum_norm_sq W (trunc S z - z)
    have : (fun j => W.w j * ‖(trunc S z - z).val j‖ ^ 2) =
        fun j => W.w j * ‖z.val j‖ ^ 2 - (if j ∈ S then W.w j * ‖z.val j‖ ^ 2 else 0) := by
      funext j; by_cases h : j ∈ S <;> simp [h]
    rw [this] at hq
    exact hq.unique hd
  have h2 : Tendsto (fun S : Finset ℤ => ‖trunc S z - z‖ ^ 2) atTop (𝓝 0) := by
    simpa only [key] using h1
  have h3 := h2.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using h3

/-- A continuous functional invariant under rotations on finitely supported sequences is invariant everywhere. -/
theorem inv_of_finite (F : WSeq W → ℝ) (hF : Continuous F)
    (hfin : ∀ (u : ℤ → Circle) (S : Finset ℤ) (z : WSeq W), F (rot u (trunc S z)) = F (trunc S z))
    (u : ℤ → Circle) (z : WSeq W) : F (rot u z) = F z := by
  have h1 : Tendsto (fun S : Finset ℤ => F (rot u (trunc S z))) atTop (𝓝 (F (rot u z))) :=
    (hF.tendsto _).comp (((continuous_rot u).tendsto z).comp (tendsto_trunc z))
  have h2 : Tendsto (fun S : Finset ℤ => F (trunc S z)) atTop (𝓝 (F z)) :=
    (hF.tendsto _).comp (tendsto_trunc z)
  have h3 : (fun S : Finset ℤ => F (rot u (trunc S z))) = fun S => F (trunc S z) := funext fun S => hfin u S z
  rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

end Density

/-! ## The sequence data and its flows -/

structure SeqData (V : PosWeight) (ι : Type) where
  W : ι → PosWeight
  F : ∀ r, WSeq (W r) → ℝ
  C : ι → ℝ
  hC : ∀ r, 0 ≤ C r
  hle : ∀ r n, (W r).w n ≤ C r * V.w n
  smooth : ∀ r, ContDiff ℝ 2 (F r)
  inv : ∀ r u z, F r (rot u z) = F r z

namespace SeqData

variable {V : PosWeight} {ι : Type} [Fintype ι] (S : SeqData V ι)

/-- The inclusion `h(V) ↪ h(W r)`. -/
def down (r : ι) : WSeq V →L[ℂ] WSeq (S.W r) := incl (S.W r) V (S.hC r) (S.hle r)

@[simp] theorem down_val (r : ι) (z : WSeq V) : (S.down r z).val = z.val := rfl

theorem down_rot (r : ι) (u : ℤ → Circle) (z : WSeq V) : S.down r (rot u z) = rot u (S.down r z) :=
  WSeq.ext rfl

/-- The rotation-invariant frequency data. -/
def D : FreqData V ι where
  Ω r z j := freq (S.F r) (S.down r z) j
  inv r u z j := by
    rw [S.down_rot, freq_rot ((S.smooth r).differentiable (by norm_num)) (S.inv r)]
  cont r z j hz := by
    have h1 : (S.down r z).val j ≠ 0 := by simpa using hz
    exact (freq_continuousAt (S.smooth r) (S.down r z) j h1).comp (S.down r).continuous.continuousAt

theorem D_Ω (r : ι) (z : WSeq V) (j : ℤ) : S.D.Ω r z j = freq (S.F r) (S.down r z) j := rfl

/-- `∇_j F_r = Ω_{r,j} z_j` (the printed `w_j = ω_{r,j} z_j`, vanishing at zero coordinates). -/
theorem grad_eq (r : ι) (z : WSeq V) (j : ℤ) :
    grad (fderiv ℝ (S.F r) (S.down r z)) j = (S.D.Ω r z j : ℂ) * z.val j :=
  grad_eq_freq_mul ((S.smooth r).differentiable (by norm_num)) (S.inv r) (S.down r z) j

/-- The division-free Hessian estimate `|Ω_{r,j}(z)| ≤ C_z (W_r)_j`. -/
theorem freq_bound' (z : WSeq V) : ∃ K : ℝ, 0 ≤ K ∧ ∀ r j, |S.D.Ω r z j| ≤ K * (S.W r).w j := by
  choose K hK0 hK using fun r => freq_bound (S.smooth r) (S.inv r) (S.down r z)
  refine ⟨∑ r, K r, Finset.sum_nonneg fun r _ => hK0 r, fun r j => ?_⟩
  have h1 := hK r j
  have h2 : K r ≤ ∑ r, K r := Finset.single_le_sum (f := K) (fun r _ => hK0 r) (Finset.mem_univ r)
  have := (S.W r).pos j
  calc |S.D.Ω r z j| ≤ K r * (S.W r).w j := h1
    _ ≤ (∑ r, K r) * (S.W r).w j := mul_le_mul_of_nonneg_right h2 this.le

/-- The weight `P_j = Σ_r (W_r)_j`. -/
def P (j : ℤ) : ℝ := ∑ r, (S.W r).w j

theorem P_nonneg (j : ℤ) : 0 ≤ S.P j := Finset.sum_nonneg fun r _ => ((S.W r).pos j).le

/-- Frequency of the joint direction `s`: `ν_j = Σ_r s_r Ω_{r,j}(z)`. -/
def nu (s : ι → ℝ) (z : WSeq V) (j : ℤ) : ℝ := ∑ r, s r * S.D.Ω r z j

theorem nu_bound (s : ι → ℝ) (z : WSeq V) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j, |S.nu s z j| ≤ K * S.P j := by
  obtain ⟨K, hK0, hK⟩ := S.freq_bound' z
  refine ⟨(∑ r, |s r|) * K, mul_nonneg (Finset.sum_nonneg fun r _ => abs_nonneg _) hK0, fun j => ?_⟩
  calc |S.nu s z j| ≤ ∑ r, |s r * S.D.Ω r z j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r, |s r| * (K * S.P j) := by
        refine Finset.sum_le_sum fun r _ => ?_
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ((hK r j).trans ?_) (abs_nonneg _)
        exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun r => (S.W r).w j)
          (fun r _ => ((S.W r).pos j).le) (Finset.mem_univ r)) hK0
    _ = (∑ r, |s r|) * K * S.P j := by rw [← Finset.sum_mul]; ring

/-- Summability of the `ν`-moments from that of the `P`-moments. -/
theorem hz_of (s : ι → ℝ) (z : WSeq V)
    (hzP : ∀ k : ℕ, Summable fun j => V.w j * S.P j ^ (2 * k) * ‖z.val j‖ ^ 2) (k : ℕ) :
    Summable fun j => V.w j * S.nu s z j ^ (2 * k) * ‖z.val j‖ ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := S.nu_bound s z
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (mul_nonneg (V.pos j).le
    (Even.pow_nonneg (even_two_mul _) _)) (sq_nonneg _)) (fun j => ?_) ((hzP k).mul_left (K ^ (2 * k)))
  have h1 : S.nu s z j ^ 2 ≤ (K * S.P j) ^ 2 := sq_le_sq' (abs_le.1 (hK j)).1 (abs_le.1 (hK j)).2
  have h2 : S.nu s z j ^ (2 * k) ≤ (K * S.P j) ^ (2 * k) := by
    rw [pow_mul, pow_mul]; exact pow_le_pow_left₀ (sq_nonneg _) h1 k
  have h3 : (K * S.P j) ^ (2 * k) = K ^ (2 * k) * S.P j ^ (2 * k) := mul_pow _ _ _
  have := V.pos j
  calc V.w j * S.nu s z j ^ (2 * k) * ‖z.val j‖ ^ 2
      ≤ V.w j * (K * S.P j) ^ (2 * k) * ‖z.val j‖ ^ 2 := by gcongr
    _ = K ^ (2 * k) * (V.w j * S.P j ^ (2 * k) * ‖z.val j‖ ^ 2) := by rw [h3]; ring

theorem angle_smul (s : ι → ℝ) (τ : ℝ) (z : WSeq V) (j : ℤ) :
    angle S.D (τ • s) z j = -(τ * S.nu s z j) := by
  simp only [angle, nu, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun r _ => by ring

theorem flow_smul_eq (s : ι → ℝ) (z : WSeq V)
    (hz : ∀ k : ℕ, Summable fun j => V.w j * S.nu s z j ^ (2 * k) * ‖z.val j‖ ^ 2) (τ : ℝ) :
    flow S.D (τ • s) z = dcurve hz 0 τ := by
  refine WSeq.ext (funext fun j => ?_)
  show (flow S.D (τ • s) z).val j = coef (S.nu s z) z 0 τ j
  rw [flow_val, angle_smul]
  simp [coef]

/-- **Time smoothness of every constant-action flow** (single direction `s`) for data with finite `P`-moments. -/
theorem flow_smul_contDiff (s : ι → ℝ) (z : WSeq V)
    (hzP : ∀ k : ℕ, Summable fun j => V.w j * S.P j ^ (2 * k) * ‖z.val j‖ ^ 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun τ : ℝ => flow S.D (τ • s) z) := by
  have hz := S.hz_of s z hzP
  have e : (fun τ : ℝ => flow S.D (τ • s) z) = fun τ => dcurve hz 0 τ :=
    funext fun τ => S.flow_smul_eq s z hz τ
  rw [e]
  exact curve_contDiff hz

/-- The time derivative of the flow is the coordinatewise Hamiltonian equation `ż_j = -i Σ_r s_r ∇_j F_r`. -/
theorem flow_hasDerivAt (s : ι → ℝ) (z : WSeq V)
    (hzP : ∀ k : ℕ, Summable fun j => V.w j * S.P j ^ (2 * k) * ‖z.val j‖ ^ 2) (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => flow S.D (τ • s) z) (dcurve (S.hz_of s z hzP) 1 τ) τ := by
  have hz := S.hz_of s z hzP
  have e : (fun τ : ℝ => flow S.D (τ • s) z) = fun τ => dcurve hz 0 τ :=
    funext fun τ => S.flow_smul_eq s z hz τ
  rw [e]
  exact hasDerivAt_dcurve hz 0 τ

/-- The derivative's coordinates are `-i Σ_r s_r ∇_j F_r` at the flowed point. -/
theorem dcurve_one_val (s : ι → ℝ) (z : WSeq V)
    (hz : ∀ k : ℕ, Summable fun j => V.w j * S.nu s z j ^ (2 * k) * ‖z.val j‖ ^ 2) (τ : ℝ) (j : ℤ) :
    (dcurve hz 1 τ).val j =
      -Complex.I * ∑ r, (s r : ℂ) * grad (fderiv ℝ (S.F r) (S.down r (flow S.D (τ • s) z))) j := by
  have h1 : ∀ r, grad (fderiv ℝ (S.F r) (S.down r (flow S.D (τ • s) z))) j =
      (S.D.Ω r z j : ℂ) * (flow S.D (τ • s) z).val j := fun r => by
    rw [S.grad_eq, freq_flow]
  simp only [h1]
  have h2 : (flow S.D (τ • s) z).val j = (dcurve hz 0 τ).val j := by rw [S.flow_smul_eq s z hz]
  rw [h2]
  have h3 : coef (S.nu s z) z 1 τ j =
      (-Complex.I * ((S.nu s z j : ℝ) : ℂ)) * coef (S.nu s z) z 0 τ j := by
    simp only [coef, pow_one, pow_zero, one_mul]; ring
  have h4 : ((S.nu s z j : ℝ) : ℂ) * coef (S.nu s z) z 0 τ j =
      ∑ r, (s r : ℂ) * ((S.D.Ω r z j : ℂ) * coef (S.nu s z) z 0 τ j) := by
    simp only [nu]; push_cast; rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  change coef (S.nu s z) z 1 τ j = -Complex.I * ∑ r, (s r : ℂ) * ((S.D.Ω r z j : ℂ) * coef (S.nu s z) z 0 τ j)
  rw [h3, mul_assoc, h4]

end SeqData

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.inv_of_finite
#print axioms QuantumNLS.RB7.SeqData.flow_smul_contDiff
#print axioms QuantumNLS.RB7.SeqData.dcurve_one_val
#print axioms QuantumNLS.RB7.SeqData.grad_eq
