import QuantumNLS.Prop022OQuadraticKet

/-! PROP-022 takeover, stage O4b. The CCR commutator of the finite-mode
quadratic polynomial with a finite-mode field, on the literal CCR core:
  [QFS S, phi_S(g)] = i phi_S(Lambda g),
  (Lambda g)_l = -i sum_{j in S} (a_lj g_j - c_lj conj g_j),
for hermitian a and symmetric c. Everything is derived from the frozen
creation/annihilation relations; no commutator is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.Prop022OCommutator
open Occupation Prop022OQuadraticKet

/-- The finite-mode field a*(h) + a(h) on the CCR core. -/
def phiFS (S : Finset ℤ) (h : ℤ → ℂ) : Module.End ℂ FS :=
  ∑ l ∈ S, (h l • Cre l + conj (h l) • Ann l)

/-- The coordinate generator of the linearized equation. -/
def Lam (α c : ℤ → ℤ → ℂ) (S : Finset ℤ) (g : ℤ → ℂ) (l : ℤ) : ℂ :=
  -Complex.I * ∑ j ∈ S, (α l j * g j - c l j * conj (g j))

/-! ### Vector-level CCR on the core -/

lemma ann_cre_v (a b : ℤ) (v : FS) :
    Ann a (Cre b v) = Cre b (Ann a v) + (if a = b then (1 : ℂ) else 0) • v := by
  have h := LinearMap.congr_fun (Ann_Cre_comm a b) v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    Module.End.one_apply] at h
  rw [← h]
  abel

lemma cre_cre_v (a b : ℤ) (v : FS) : Cre a (Cre b v) = Cre b (Cre a v) := by
  have h := LinearMap.congr_fun (Cre_Cre_comm a b) v
  simpa only [Module.End.mul_apply] using h

lemma ann_ann_v (a b : ℤ) (v : FS) : Ann a (Ann b v) = Ann b (Ann a v) := by
  have h := LinearMap.congr_fun (Ann_Ann_comm a b) v
  simpa only [Module.End.mul_apply] using h

/-- The finite field applied to a core vector. -/
def phiV (S : Finset ℤ) (h : ℤ → ℂ) (v : FS) : FS :=
  ∑ l ∈ S, (h l • Cre l v + conj (h l) • Ann l v)

lemma phiFS_apply (S : Finset ℤ) (h : ℤ → ℂ) (v : FS) : phiFS S h v = phiV S h v := by
  simp only [phiFS, phiV, LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smul_apply]

/-- The finite quadratic polynomial applied to a core vector. -/
def QV (α c : ℤ → ℤ → ℂ) (S : Finset ℤ) (v : FS) : FS :=
  ∑ i ∈ S, ∑ j ∈ S, (α i j • Cre i (Ann j v) + (c i j / 2) • Cre i (Cre j v) +
    (conj (c i j) / 2) • Ann j (Ann i v))

lemma QFS_apply (α c : ℤ → ℤ → ℂ) (S : Finset ℤ) (v : FS) : QFS α c S v = QV α c S v := by
  simp only [QFS, QV, LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.mul_apply]

lemma sum_delta (S : Finset ℤ) (i : ℤ) (hi : i ∈ S) (f : ℤ → ℂ) :
    ∑ l ∈ S, (if i = l then f l else 0) = f i := by
  rw [Finset.sum_ite_eq, if_pos hi]

lemma sum_delta' (S : Finset ℤ) (i : ℤ) (hi : i ∈ S) (f : ℤ → ℂ) :
    ∑ l ∈ S, (if l = i then f l else 0) = f i := by
  rw [Finset.sum_ite_eq', if_pos hi]

/-- Commutator of the quadratic polynomial with one creator. -/
lemma QV_cre (α c : ℤ → ℤ → ℂ) (S : Finset ℤ) (l : ℤ) (hl : l ∈ S) (v : FS) :
    QV α c S (Cre l v) - Cre l (QV α c S v) =
      ∑ i ∈ S, α i l • Cre i v + ∑ j ∈ S, (conj (c l j) / 2) • Ann j v +
        ∑ i ∈ S, (conj (c i l) / 2) • Ann i v := by
  have hterm : ∀ i ∈ S, ∀ j ∈ S,
      (α i j • Cre i (Ann j (Cre l v)) + (c i j / 2) • Cre i (Cre j (Cre l v)) +
        (conj (c i j) / 2) • Ann j (Ann i (Cre l v))) -
      (α i j • Cre l (Cre i (Ann j v)) + (c i j / 2) • Cre l (Cre i (Cre j v)) +
        (conj (c i j) / 2) • Cre l (Ann j (Ann i v))) =
      (α i j * (if j = l then 1 else 0)) • Cre i v +
        (conj (c i j) / 2 * (if i = l then 1 else 0)) • Ann j v +
        (conj (c i j) / 2 * (if j = l then 1 else 0)) • Ann i v := by
    intro i _ j _
    simp only [ann_cre_v, map_add, map_smul]
    rw [cre_cre_v i l (Ann j v), cre_cre_v j l v, cre_cre_v i l (Cre j v)]
    module
  have hsum : QV α c S (Cre l v) - Cre l (QV α c S v) = ∑ i ∈ S, ∑ j ∈ S,
      ((α i j * (if j = l then 1 else 0)) • Cre i v +
        (conj (c i j) / 2 * (if i = l then 1 else 0)) • Ann j v +
        (conj (c i j) / 2 * (if j = l then 1 else 0)) • Ann i v) := by
    simp only [QV, map_sum, map_add, map_smul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact hterm i hi j hj
  rw [hsum]
  simp only [Finset.sum_add_distrib]
  congr 1
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_smul]
    congr 1
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', hl, if_true]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_smul]
    congr 1
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', hl, if_true]
  · apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_smul]
    congr 1
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', hl, if_true]

/-- Commutator of the quadratic polynomial with one annihilator. -/
lemma QV_ann (α c : ℤ → ℤ → ℂ) (S : Finset ℤ) (l : ℤ) (hl : l ∈ S) (v : FS) :
    QV α c S (Ann l v) - Ann l (QV α c S v) =
      ∑ j ∈ S, (-(α l j)) • Ann j v + ∑ i ∈ S, (-(c i l) / 2) • Cre i v +
        ∑ j ∈ S, (-(c l j) / 2) • Cre j v := by
  have hterm : ∀ i ∈ S, ∀ j ∈ S,
      (α i j • Cre i (Ann j (Ann l v)) + (c i j / 2) • Cre i (Cre j (Ann l v)) +
        (conj (c i j) / 2) • Ann j (Ann i (Ann l v))) -
      (α i j • Ann l (Cre i (Ann j v)) + (c i j / 2) • Ann l (Cre i (Cre j v)) +
        (conj (c i j) / 2) • Ann l (Ann j (Ann i v))) =
      (-(α i j) * (if l = i then 1 else 0)) • Ann j v +
        (-(c i j) / 2 * (if l = j then 1 else 0)) • Cre i v +
        (-(c i j) / 2 * (if l = i then 1 else 0)) • Cre j v := by
    intro i _ j _
    simp only [ann_cre_v, map_add, map_smul]
    rw [ann_ann_v l j v, ann_ann_v l j (Ann i v), ann_ann_v l i v]
    module
  have hsum : QV α c S (Ann l v) - Ann l (QV α c S v) = ∑ i ∈ S, ∑ j ∈ S,
      ((-(α i j) * (if l = i then 1 else 0)) • Ann j v +
        (-(c i j) / 2 * (if l = j then 1 else 0)) • Cre i v +
        (-(c i j) / 2 * (if l = i then 1 else 0)) • Cre j v) := by
    simp only [QV, map_sum, map_add, map_smul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact hterm i hi j hj
  rw [hsum]
  simp only [Finset.sum_add_distrib]
  congr 1
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_smul]
    congr 1
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, hl, if_true]
  · apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_smul]
    congr 1
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, hl, if_true]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_smul]
    congr 1
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, hl, if_true]

/-- **CCR commutator identity** on core vectors. -/
theorem QV_comm (α c : ℤ → ℤ → ℂ) (S : Finset ℤ) (g : ℤ → ℂ)
    (hα : ∀ i j, α i j = conj (α j i)) (hc : ∀ i j, c i j = c j i) (v : FS) :
    QV α c S (phiV S g v) - phiV S g (QV α c S v) =
      Complex.I • phiV S (Lam α c S g) v := by
  have hlin : QV α c S (phiV S g v) =
      ∑ l ∈ S, (g l • QV α c S (Cre l v) + conj (g l) • QV α c S (Ann l v)) := by
    rw [← QFS_apply, phiV, map_sum]
    simp only [map_add, map_smul, QFS_apply]
  have hL : QV α c S (phiV S g v) - phiV S g (QV α c S v) =
      ∑ l ∈ S, (g l • (QV α c S (Cre l v) - Cre l (QV α c S v)) +
        conj (g l) • (QV α c S (Ann l v) - Ann l (QV α c S v))) := by
    rw [hlin, phiV, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _
    module
  rw [hL, Finset.sum_congr rfl (fun l hl => by rw [QV_cre α c S l hl v, QV_ann α c S l hl v])]
  have hL2 : ∀ l ∈ S,
      g l • (∑ i ∈ S, α i l • Cre i v + ∑ j ∈ S, (conj (c l j) / 2) • Ann j v +
        ∑ i ∈ S, (conj (c i l) / 2) • Ann i v) +
      conj (g l) • (∑ j ∈ S, (-(α l j)) • Ann j v + ∑ i ∈ S, (-(c i l) / 2) • Cre i v +
        ∑ j ∈ S, (-(c l j) / 2) • Cre j v) =
      ∑ x ∈ S, ((g l * α x l - conj (g l) * c x l) • Cre x v +
        (g l * conj (c x l) - conj (g l) * α l x) • Ann x v) := by
    intro l _
    simp only [Finset.smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [hc l x]
    module
  rw [Finset.sum_congr rfl hL2, Finset.sum_comm, phiV, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [smul_add, smul_smul, smul_smul]
  have h1 : Complex.I * Lam α c S g x = ∑ l ∈ S, (α x l * g l - c x l * conj (g l)) := by
    simp only [Lam]
    rw [← mul_assoc, show Complex.I * -Complex.I = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg],
      one_mul]
  have h2 : Complex.I * conj (Lam α c S g x) =
      ∑ l ∈ S, (conj (c x l) * g l - α l x * conj (g l)) := by
    simp only [Lam, map_mul, map_neg, Complex.conj_I, map_sum, map_sub]
    rw [← mul_assoc, show Complex.I * -(-Complex.I) = -1 by
      rw [neg_neg, Complex.I_mul_I], neg_one_mul, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro l _
    rw [hα l x, Complex.conj_conj]
    ring
  rw [h1, h2, Finset.sum_smul, Finset.sum_smul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  module

end QuantumNLS.Prop022OCommutator

#print axioms QuantumNLS.Prop022OCommutator.QV_comm
