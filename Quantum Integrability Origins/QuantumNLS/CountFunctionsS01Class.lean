import QuantumNLS.CountFunctionsS01Poisson

/-!
# CountFunctionsS01Class: the first-order class of expressions

PRINTED SOURCE `source-text/chapters/core/canonical_algebra.tex:38` (sha256 `b2a1e9c4…0395`):
  "Fix a finite label set `J`. The first-order class consists of expressions obtained by finitely many sums,
   products, scalar multiples, and adjoints from `E^q_{N,ab}`, `a,b∈J`, and `f(B_{N,J})`, where `f` is `C²` on a
   neighborhood of `[0,1]^J`. Its classical expression replaces these generators by `c_ab` and `f(a_J)`. Each
   expression and each function is fixed independently of `N`."

`Expr J` is exactly that class (constructors `gen`, `fn`, `add`, `mul`, `smul`, `adj`).  Its operator realization
`Expr.op b g` (on `HN L N`, gauged Bethe basis `(b, g)`) uses the gauged transfers `E^q_{N,ab}` and the functional
calculus `countOp`; its classical expression `Expr.cl` is the function `z ↦ ...` on `ℂ^J` with `c_ab = z_a z̄_b` and
`f(a_J)`, `a_j = |z_j|²`.  `Expr0 J` is the adjoint-free fragment into which every expression is normalized
(`Expr.nf`); `Expr.op_eq_op0` / `Expr.cl_eq_cl0` prove the normalization preserves operator and classical expression.
No acceptance claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open scoped InnerProductSpace ComplexConjugate
open QuantumNLS Occupation OccupationHilbert BetheCoefficientTransform BetheOccupationGauge
open QuantumNLS.CountFunctionsS01Ops QuantumNLS.CountFunctionsS01Calc QuantumNLS.CountFunctionsS01Poisson

namespace QuantumNLS.CountFunctionsS01Class

lemma c2Near_conj {J : Finset ℤ} {f : (↥J → ℝ) → ℂ} (hf : C2Near J f) :
    C2Near J (fun x => conj (f x)) := by
  obtain ⟨U, hU, hcU, hC⟩ := hf
  exact ⟨U, hU, hcU, (Complex.conjCLE.contDiff : ContDiff ℝ 2 (Complex.conjCLE : ℂ →L[ℝ] ℂ)).comp_contDiffOn hC⟩

lemma c2Near_differentiableAt {J : Finset ℤ} {f : (↥J → ℝ) → ℂ} (hf : C2Near J f) {x : ↥J → ℝ}
    (hx : x ∈ cube J) : DifferentiableAt ℝ f x := by
  obtain ⟨U, hU, hcU, hC⟩ := hf
  exact (hC.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds (hcU hx))

/-- The adjoint-free fragment of the class. -/
inductive Expr0 (J : Finset ℤ) where
  | gen (a b : ↥J)
  | fn (f : (↥J → ℝ) → ℂ) (hf : C2Near J f)
  | add (A B : Expr0 J)
  | mul (A B : Expr0 J)
  | smul (c : ℂ) (A : Expr0 J)

/-- **The first-order class** (`canonical_algebra.tex:38`): finite sums, products, scalar multiples and adjoints of the
transfers `E^q_{N,ab}` (`a, b ∈ J`) and of `f(B_{N,J})` with `f` `C²` on a neighborhood of `[0,1]^J`. -/
inductive Expr (J : Finset ℤ) where
  | gen (a b : ↥J)
  | fn (f : (↥J → ℝ) → ℂ) (hf : C2Near J f)
  | add (A B : Expr J)
  | mul (A B : Expr J)
  | smul (c : ℂ) (A : Expr J)
  | adj (A : Expr J)

variable {J : Finset ℤ}

/-! ### Classical expressions -/

/-- The classical expression of an adjoint-free expression (`c_ab ↦ z_a z̄_b`, `f(B) ↦ f(a_J)`, `a_j = |z_j|²`). -/
def Expr0.cl : Expr0 J → CPt J → ℂ
  | .gen a b => genF a b
  | .fn f _ => cntF f
  | .add A B => fun z => A.cl z + B.cl z
  | .mul A B => fun z => A.cl z * B.cl z
  | .smul c A => fun z => c * A.cl z

/-- The classical expression of an expression of the class (adjoint = complex conjugation). -/
def Expr.cl : Expr J → CPt J → ℂ
  | .gen a b => genF a b
  | .fn f _ => cntF f
  | .add A B => fun z => A.cl z + B.cl z
  | .mul A B => fun z => A.cl z * B.cl z
  | .smul c A => fun z => c * A.cl z
  | .adj A => fun z => conj (A.cl z)

/-! ### Operators -/

section Ops

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- The operator of an adjoint-free expression at the gauged Bethe basis `(b, g)`. -/
def Expr0.op (b : BetheBasis L N) (g : Gauge) : Expr0 J → (HN L N →L[ℂ] HN L N)
  | .gen a c => CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ)
  | .fn f _ => countOp b g J f
  | .add A B => A.op b g + B.op b g
  | .mul A B => A.op b g * B.op b g
  | .smul c A => c • A.op b g

/-- The operator of an expression of the class. -/
def Expr.op (b : BetheBasis L N) (g : Gauge) : Expr J → (HN L N →L[ℂ] HN L N)
  | .gen a c => CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ)
  | .fn f _ => countOp b g J f
  | .add A B => A.op b g + B.op b g
  | .mul A B => A.op b g * B.op b g
  | .smul c A => c • A.op b g
  | .adj A => (A.op b g).adjoint

end Ops

/-! ### Normalization: pushing adjoints to the leaves -/

/-- `nf false A` is `A` and `nf true A` is `A^*`, both with the adjoints pushed to the leaves. -/
def Expr.nf : Bool → Expr J → Expr0 J
  | false, .gen a b => .gen a b
  | true, .gen a b => .gen b a
  | false, .fn f hf => .fn f hf
  | true, .fn f hf => .fn (fun x => conj (f x)) (c2Near_conj hf)
  | s, .add A B => .add (A.nf s) (B.nf s)
  | false, .mul A B => .mul (A.nf false) (B.nf false)
  | true, .mul A B => .mul (B.nf true) (A.nf true)
  | false, .smul c A => .smul c (A.nf false)
  | true, .smul c A => .smul (conj c) (A.nf true)
  | s, .adj A => A.nf (!s)

theorem Expr.cl_nf : ∀ (s : Bool) (A : Expr J) (z : CPt J),
    (A.nf s).cl z = if s then conj (A.cl z) else A.cl z
  | false, .gen a b, z => rfl
  | true, .gen a b, z => by simp [Expr.nf, Expr0.cl, Expr.cl, genF, mul_comm]
  | false, .fn f hf, z => rfl
  | true, .fn f hf, z => by simp [Expr.nf, Expr0.cl, Expr.cl, cntF]
  | false, .add A B, z => by simp [Expr.nf, Expr0.cl, Expr.cl, Expr.cl_nf false A z, Expr.cl_nf false B z]
  | true, .add A B, z => by simp [Expr.nf, Expr0.cl, Expr.cl, Expr.cl_nf true A z, Expr.cl_nf true B z]
  | false, .mul A B, z => by simp [Expr.nf, Expr0.cl, Expr.cl, Expr.cl_nf false A z, Expr.cl_nf false B z]
  | true, .mul A B, z => by
      simp [Expr.nf, Expr0.cl, Expr.cl, Expr.cl_nf true A z, Expr.cl_nf true B z, mul_comm]
  | false, .smul c A, z => by simp [Expr.nf, Expr0.cl, Expr.cl, Expr.cl_nf false A z]
  | true, .smul c A, z => by simp [Expr.nf, Expr0.cl, Expr.cl, Expr.cl_nf true A z]
  | false, .adj A, z => by
      have := Expr.cl_nf true A z
      simpa [Expr.nf, Expr.cl] using this
  | true, .adj A, z => by
      have := Expr.cl_nf false A z
      simp [Expr.nf, Expr.cl, this]

section OpNf

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

lemma adjoint_mul' (A B : HN L N →L[ℂ] HN L N) : (A * B).adjoint = B.adjoint * A.adjoint :=
  ContinuousLinearMap.adjoint_comp A B

lemma adjoint_smul' (c : ℂ) (A : HN L N →L[ℂ] HN L N) : (c • A).adjoint = conj c • A.adjoint :=
  (ContinuousLinearMap.adjoint : (HN L N →L[ℂ] HN L N) ≃ₗᵢ⋆[ℂ] (HN L N →L[ℂ] HN L N)).map_smulₛₗ c A

lemma physical_adjoint' (b : BetheBasis L N) (g : Gauge) (a c : ℤ) :
    (CartesianOccupationTransfer.physical b g a c).adjoint = CartesianOccupationTransfer.physical b g c a := by
  rw [physical_eq_conjOp, physical_eq_conjOp, conjOp_adjoint, E_adjoint]

theorem Expr.op_nf (b : BetheBasis L N) (g : Gauge) :
    ∀ (s : Bool) (A : Expr J), (A.nf s).op b g = if s then (A.op b g).adjoint else A.op b g
  | false, .gen a c => rfl
  | true, .gen a c => by
      simp [Expr.nf, Expr0.op, Expr.op, physical_adjoint']
  | false, .fn f hf => rfl
  | true, .fn f hf => by
      simp only [Expr.nf, Expr0.op, Expr.op, ite_true]
      rw [countOp_adjoint b g J (BddOn.of_continuousOn hf.continuousOn)]
  | false, .add A B => by simp [Expr.nf, Expr0.op, Expr.op, Expr.op_nf b g false A, Expr.op_nf b g false B]
  | true, .add A B => by
      simp [Expr.nf, Expr0.op, Expr.op, Expr.op_nf b g true A, Expr.op_nf b g true B]
  | false, .mul A B => by simp [Expr.nf, Expr0.op, Expr.op, Expr.op_nf b g false A, Expr.op_nf b g false B]
  | true, .mul A B => by
      simp [Expr.nf, Expr0.op, Expr.op, Expr.op_nf b g true A, Expr.op_nf b g true B, adjoint_mul']
  | false, .smul c A => by simp [Expr.nf, Expr0.op, Expr.op, Expr.op_nf b g false A]
  | true, .smul c A => by
      simp [Expr.nf, Expr0.op, Expr.op, Expr.op_nf b g true A, adjoint_smul']
  | false, .adj A => by
      have := Expr.op_nf b g true A
      simpa [Expr.nf, Expr.op] using this
  | true, .adj A => by
      have := Expr.op_nf b g false A
      simp [Expr.nf, Expr.op, this]

end OpNf

/-! ### Differentiability of the classical expressions on the closed polydisc -/

theorem Expr0.differentiableAt_cl : ∀ (A : Expr0 J) (z : CPt J), apt z ∈ cube J → DifferentiableAt ℝ A.cl z
  | .gen a b, z, _ => differentiableAt_genF a b z
  | .fn f hf, z, hz => differentiableAt_cntF (c2Near_differentiableAt hf hz)
  | .add A B, z, hz => (A.differentiableAt_cl z hz).add (B.differentiableAt_cl z hz)
  | .mul A B, z, hz => (A.differentiableAt_cl z hz).mul (B.differentiableAt_cl z hz)
  | .smul c A, z, hz => (A.differentiableAt_cl z hz).const_mul c

end QuantumNLS.CountFunctionsS01Class
