import Mathlib
import QuantumNLS.Ext002MonoFields
import QuantumNLS.Ext002MonoKernels

/-!
# EXT-002 / V-01 full monodromy (owner decision D4), stage M3: fixed-sector monodromy entries

Source: Vlaar thesis eqs. (2.4.1)-(2.4.4) (printed pp. 20-21) and the monodromy matrix display
`T_λ = [[A_λ, γB_λ], [C_λ, D_λ]]` (printed p. 17, after (2.2.4)), with trace `A_λ + D_λ`
((2.2.5), p. 18). On `D_N` the series run over `n = 0,…,N` (as printed).

* Interval and translation: Vlaar's interval is `J = [−L/2, L/2]`
  (A04.tex:17, `source/chapters/foundations/A04.tex`); a torus point `t ∈ 𝕋_L` with canonical
  representative `rep t ∈ [0,L)` has source coordinate `u = rep t − L/2` (`centered`), i.e. the
  translation by `L/2` of A04.tex:33-35 and periodic_basis.tex:356-358.
* Entries, with `n` the power of the coupling `c` (= Vlaar's `γ`):
  - `A_N = Σₙ cⁿ W_{n,n}(sourceA)` with `sourceA` = Vlaar (2.4.1) including `e^{−izL/2}`
    (frozen `Ext002MonoKernels.sourceA`): sector preserving `H_N → H_N`;
  - `D_N = Σₙ cⁿ W_{n,n}(sourceD)`, Vlaar (2.4.4): `H_N → H_N`;
  - `B_N = Σₙ cⁿ W_{n+1,n}(sourceCreationKernel)`, Vlaar (2.4.2): `H_N → H_{N+1}`;
  - `C_N = Σₙ cⁿ W_{n,n+1}(sourceAnnihilationKernel)`, Vlaar (2.4.3): `H_{N+1} → H_N`;
  where `W` is the weak normal-ordered monomial of normalized fields (`Ext002MonoFields`).
  B and C are built from their own source kernels; nothing is inferred from the transfer.
* Gauge (convention recorded in the M1 review record): the matrix is the UNGAUGED translated
  monodromy `[[A, cB], [C, D]]`; the printed gauge `e^{izL/2}` multiplies the transfer
  (periodic_basis.tex:358, A04.tex:34-36) and is applied in the trace identity (stage M5).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace QuantumNLS.Ext002MonoEntries
open PhysicalTensor TensorCarrier BethePhysicalTransfer Ext002MonoLift Ext002MonoFields
open BetheTransferKernelAdjoint BetheTransferOperators Ext002OddKernels Ext002MonoKernels
open BetheWeakGradient

/-! ### Scalar facts for the off-diagonal kernels -/

theorem measurableSet_oddOrder (r : ℕ) (L : ℝ) :
    MeasurableSet {p : (Fin (r+1) → ℝ) × (Fin r → ℝ) | oddOrder L p.1 p.2} := by
  simp only [oddOrder, PlusOrder]
  measurability

theorem measurable_oddDisplacement (r : ℕ) :
    Measurable (fun p : (Fin (r+1) → ℝ) × (Fin r → ℝ) => oddDisplacement p.1 p.2) := by
  unfold oddDisplacement
  fun_prop

theorem measurable_creationKernel (r : ℕ) (L : ℝ) (z : ℂ) :
    Measurable (fun p : (Fin (r+1) → ℝ) × (Fin r → ℝ) => creationKernel L z p.1 p.2) := by
  unfold creationKernel
  exact Measurable.ite (measurableSet_oddOrder r L)
    (Complex.continuous_exp.measurable.comp
      ((measurable_const.mul measurable_const).mul
        (Complex.continuous_ofReal.measurable.comp (measurable_oddDisplacement r))))
    measurable_const

theorem measurable_annihilationKernel (r : ℕ) (L : ℝ) (z : ℂ) :
    Measurable (fun p : (Fin r → ℝ) × (Fin (r+1) → ℝ) => annihilationKernel L z p.1 p.2) := by
  unfold annihilationKernel
  apply Measurable.ite ((measurableSet_oddOrder r L).preimage measurable_swap)
  · unfold oddDisplacement
    fun_prop
  · exact measurable_const

theorem norm_exp_I_mul_le (z : ℂ) (t : ℝ) :
    ‖Complex.exp (Complex.I * z * t)‖ ≤ Real.exp (|z.im| * |t|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, one_mul, sub_zero, mul_zero, zero_sub]
  have h1 := neg_le_abs (z.im * t)
  rw [abs_mul] at h1
  linarith

/-- On the odd chamber the signed sum lies in `[0, 2L]`. -/
theorem oddDisplacement_range {r : ℕ} {L : ℝ} (hL : 0 ≤ L) {x : Fin (r+1) → ℝ}
    {y : Fin r → ℝ} (h : oddOrder L x y) :
    0 ≤ oddDisplacement x y ∧ oddDisplacement x y ≤ 2 * L := by
  obtain ⟨hp, hx0, hxL, -⟩ := h
  have hd := displacement_range hL hp
  have he : oddDisplacement x y =
      displacement (fun i => x i.castSucc) y + x (Fin.last r) := by
    simp only [oddDisplacement, displacement, Fin.sum_univ_castSucc, Finset.sum_sub_distrib]
    ring
  rw [he]
  constructor <;> linarith [hd.1, hd.2]

theorem norm_creationKernel_le {r : ℕ} {L : ℝ} (hL : 0 ≤ L) (z : ℂ)
    (x : Fin (r+1) → ℝ) (y : Fin r → ℝ) :
    ‖creationKernel L z x y‖ ≤ Real.exp (|z.im| * (2 * L)) := by
  classical
  unfold creationKernel
  split_ifs with h
  · obtain ⟨h0, h1⟩ := oddDisplacement_range hL h
    refine (norm_exp_I_mul_le z _).trans (Real.exp_le_exp.mpr ?_)
    rw [abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  · rw [norm_zero]; positivity

theorem norm_annihilationKernel_le {r : ℕ} {L : ℝ} (hL : 0 ≤ L) (z : ℂ)
    (x : Fin r → ℝ) (y : Fin (r+1) → ℝ) :
    ‖annihilationKernel L z x y‖ ≤ Real.exp (|z.im| * (2 * L)) := by
  classical
  unfold annihilationKernel
  split_ifs with h
  · obtain ⟨h0, h1⟩ := oddDisplacement_range hL h
    refine le_trans (le_of_eq ?_) ((norm_exp_I_mul_le z (L - oddDisplacement y x)).trans
      (Real.exp_le_exp.mpr ?_))
    · simp [Complex.ofReal_sub]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [abs_le]
    constructor <;> linarith
  · rw [norm_zero]; positivity

/-- From `e^{a} S = R` to `S = e^{-a} R`. -/
theorem gauge_inv {a S R : ℂ} (h : Complex.exp a * S = R) : S = Complex.exp (-a) * R := by
  rw [← h, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]

variable (L : ℝ) [Fact (0 < L)]

/-- Source coordinate `u = rep t − L/2 ∈ [−L/2, L/2)` of torus points (A04.tex:33-35). -/
def centered {n : ℕ} (x : Fin n → AddCircle L) : Fin n → ℝ :=
  fun i => representatives L x i - L/2

/-! ### The four source kernels on the torus -/

theorem sourceA_centered {r : ℕ} (z : ℂ) (x y : Fin r → AddCircle L) :
    sourceA L z (centered L x) (centered L y) =
      Complex.exp (-(Complex.I * z * L / 2)) *
        rawPlus L z (representatives L x) (representatives L y) :=
  gauge_inv (sourceA_gauge L z (representatives L x) (representatives L y))

theorem sourceD_centered {r : ℕ} (z : ℂ) (x y : Fin r → AddCircle L) :
    sourceD L z (centered L x) (centered L y) =
      Complex.exp (-(Complex.I * z * L / 2)) *
        rawMinus L z (representatives L x) (representatives L y) :=
  gauge_inv (sourceD_gauge L z (representatives L x) (representatives L y))

theorem sourceB_centered {r : ℕ} (z : ℂ) (x : Fin (r+1) → AddCircle L)
    (y : Fin r → AddCircle L) :
    sourceCreationKernel L z (centered L x) (centered L y) =
      Complex.exp (-(Complex.I * z * L / 2)) *
        creationKernel L z (representatives L x) (representatives L y) :=
  gauge_inv (sourceCreationKernel_gauge L z (representatives L x) (representatives L y))

theorem sourceC_centered {r : ℕ} (z : ℂ) (x : Fin r → AddCircle L)
    (y : Fin (r+1) → AddCircle L) :
    sourceAnnihilationKernel L z (centered L x) (centered L y) =
      Complex.exp (-(Complex.I * z * L / 2)) *
        annihilationKernel L z (representatives L x) (representatives L y) :=
  gauge_inv (sourceAnnihilationKernel_gauge L z (representatives L x) (representatives L y))

theorem measurable_reps_pair (r s : ℕ) :
    Measurable (fun p : (Fin r → AddCircle L) × (Fin s → AddCircle L) =>
      (representatives L p.1, representatives L p.2)) :=
  ((measurable_representatives r L).comp measurable_fst).prodMk
    ((measurable_representatives s L).comp measurable_snd)

/-- Vlaar (2.4.1) kernel with `n` creation and `n` annihilation variables. -/
def kernelA (n : ℕ) (z : ℂ) : MonoKernel L n n where
  fn p := sourceA L z (centered L p.1) (centered L p.2)
  measurable := by
    simp only [sourceA_centered]
    exact measurable_const.mul ((measurable_rawPlus n L z).comp (measurable_reps_pair L n n))
  bound := ‖Complex.exp (-(Complex.I * z * L / 2))‖ * Real.exp (L * |z.im|)
  bound_nonneg := by positivity
  norm_le p := by
    rw [sourceA_centered, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_rawPlus_le L (Fact.out : 0 < L).le z _ _)
      (norm_nonneg _)

/-- Vlaar (2.4.4) kernel. -/
def kernelD (n : ℕ) (z : ℂ) : MonoKernel L n n where
  fn p := sourceD L z (centered L p.1) (centered L p.2)
  measurable := by
    simp only [sourceD_centered]
    exact measurable_const.mul ((measurable_rawMinus n L z).comp (measurable_reps_pair L n n))
  bound := ‖Complex.exp (-(Complex.I * z * L / 2))‖ * Real.exp (L * |z.im|)
  bound_nonneg := by positivity
  norm_le p := by
    rw [sourceD_centered, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_rawMinus_le L (Fact.out : 0 < L).le z _ _)
      (norm_nonneg _)

/-- Vlaar (2.4.2) kernel: `n+1` creation and `n` annihilation variables. -/
def kernelB (n : ℕ) (z : ℂ) : MonoKernel L (n+1) n where
  fn p := sourceCreationKernel L z (centered L p.1) (centered L p.2)
  measurable := by
    simp only [sourceB_centered]
    exact measurable_const.mul
      ((measurable_creationKernel n L z).comp (measurable_reps_pair L (n+1) n))
  bound := ‖Complex.exp (-(Complex.I * z * L / 2))‖ * Real.exp (|z.im| * (2 * L))
  bound_nonneg := by positivity
  norm_le p := by
    rw [sourceB_centered, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_creationKernel_le (Fact.out : 0 < L).le z _ _)
      (norm_nonneg _)

/-- Vlaar (2.4.3) kernel: `n` creation and `n+1` annihilation variables. -/
def kernelC (n : ℕ) (z : ℂ) : MonoKernel L n (n+1) where
  fn p := sourceAnnihilationKernel L z (centered L p.1) (centered L p.2)
  measurable := by
    simp only [sourceC_centered]
    exact measurable_const.mul
      ((measurable_annihilationKernel n L z).comp (measurable_reps_pair L n (n+1)))
  bound := ‖Complex.exp (-(Complex.I * z * L / 2))‖ * Real.exp (|z.im| * (2 * L))
  bound_nonneg := by positivity
  norm_le p := by
    rw [sourceC_centered, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_annihilationKernel_le (Fact.out : 0 < L).le z _ _)
      (norm_nonneg _)

/-! ### Fixed-sector entries -/

/-- Transport of an operator between sectors along equalities of particle numbers. -/
def castSectorMap {a b a' b' : ℕ} (ha : a = a') (hb : b = b')
    (T : H L a →L[ℂ] H L b) : H L a' →L[ℂ] H L b' := by
  subst ha
  subst hb
  exact T

theorem sector_eq (N : ℕ) (n : Fin (N+1)) : (n : ℕ) + (N - n) = N :=
  Nat.add_sub_of_le (Nat.le_of_lt_succ n.isLt)

theorem sector_succ_eq (N : ℕ) (n : Fin (N+1)) : (n : ℕ) + 1 + (N - n) = N + 1 := by
  have := sector_eq N n
  omega

/-- `A_N(z) : H_N → H_N`, Vlaar (2.4.1) on `D_N`, coupling `c`. -/
def entryA (N : ℕ) (c : ℝ) (z : ℂ) : H L N →L[ℂ] H L N :=
  ∑ n : Fin (N+1), ((c : ℂ) ^ (n : ℕ)) •
    KernelDefinition.castSymSectorOperator (sector_eq N n) (monomial L (N - n) (kernelA L n z))

/-- `D_N(z) : H_N → H_N`, Vlaar (2.4.4). -/
def entryD (N : ℕ) (c : ℝ) (z : ℂ) : H L N →L[ℂ] H L N :=
  ∑ n : Fin (N+1), ((c : ℂ) ^ (n : ℕ)) •
    KernelDefinition.castSymSectorOperator (sector_eq N n) (monomial L (N - n) (kernelD L n z))

/-- `B_N(z) : H_N → H_{N+1}`, Vlaar (2.4.2). -/
def entryB (N : ℕ) (c : ℝ) (z : ℂ) : H L N →L[ℂ] H L (N+1) :=
  ∑ n : Fin (N+1), ((c : ℂ) ^ (n : ℕ)) •
    castSectorMap L (sector_eq N n) (sector_succ_eq N n) (monomial L (N - n) (kernelB L n z))

/-- `C_N(z) : H_{N+1} → H_N`, Vlaar (2.4.3). -/
def entryC (N : ℕ) (c : ℝ) (z : ℂ) : H L (N+1) →L[ℂ] H L N :=
  ∑ n : Fin (N+1), ((c : ℂ) ^ (n : ℕ)) •
    castSectorMap L (sector_succ_eq N n) (sector_eq N n) (monomial L (N - n) (kernelC L n z))

/-- A fixed-sector `2×2` monodromy `[[A, cB], [C, D]]` at particle number `N`:
`A, D` preserve `H_N`; `cB : H_N → H_{N+1}`; `C : H_{N+1} → H_N`. -/
structure SectorMonodromy (N : ℕ) where
  A : H L N →L[ℂ] H L N
  cB : H L N →L[ℂ] H L (N+1)
  C : H L (N+1) →L[ℂ] H L N
  D : H L N →L[ℂ] H L N

/-- Partial trace over `ℂ²`, Vlaar (2.2.5). -/
def SectorMonodromy.trace {N : ℕ} (T : SectorMonodromy L N) : H L N →L[ℂ] H L N := T.A + T.D

/-- The source monodromy matrix `T_z = [[A_z, cB_z], [C_z, D_z]]` (Vlaar p. 17) in the
fixed sectors, translated to `(0,L)`, ungauged. -/
def monodromy (N : ℕ) (c : ℝ) (z : ℂ) : SectorMonodromy L N where
  A := entryA L N c z
  cB := (c : ℂ) • entryB L N c z
  C := entryC L N c z
  D := entryD L N c z

theorem monodromy_trace (N : ℕ) (c : ℝ) (z : ℂ) :
    (monodromy L N c z).trace = entryA L N c z + entryD L N c z := rfl

/-- The translated-and-gauged diagonal kernels are the DEF-048 kernels (from M1). -/
theorem kernelA_gauge (n : ℕ) (z : ℂ) (p : (Fin n → AddCircle L) × (Fin n → AddCircle L)) :
    Complex.exp (Complex.I * z * L / 2) * (kernelA L n z).fn p =
      (plusKernel L n z).fn p :=
  sourceA_gauge L z (representatives L p.1) (representatives L p.2)

theorem kernelD_gauge (n : ℕ) (z : ℂ) (p : (Fin n → AddCircle L) × (Fin n → AddCircle L)) :
    Complex.exp (Complex.I * z * L / 2) * (kernelD L n z).fn p =
      (minusKernel L n z).fn p :=
  sourceD_gauge L z (representatives L p.1) (representatives L p.2)

end QuantumNLS.Ext002MonoEntries

#print axioms QuantumNLS.Ext002MonoEntries.kernelA
#print axioms QuantumNLS.Ext002MonoEntries.kernelD
#print axioms QuantumNLS.Ext002MonoEntries.kernelB
#print axioms QuantumNLS.Ext002MonoEntries.kernelC
#print axioms QuantumNLS.Ext002MonoEntries.entryA
#print axioms QuantumNLS.Ext002MonoEntries.entryB
#print axioms QuantumNLS.Ext002MonoEntries.entryC
#print axioms QuantumNLS.Ext002MonoEntries.entryD
#print axioms QuantumNLS.Ext002MonoEntries.monodromy
#print axioms QuantumNLS.Ext002MonoEntries.monodromy_trace
#print axioms QuantumNLS.Ext002MonoEntries.kernelA_gauge
#print axioms QuantumNLS.Ext002MonoEntries.kernelD_gauge
