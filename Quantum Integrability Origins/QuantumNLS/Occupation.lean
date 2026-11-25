import Mathlib.Data.Finsupp.Weight
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Finsupp.Interval

/-!
# Finite occupation arrays and donor/receiver transfers (source U4 / DEF-006, DEF-026)

Source: report commit 3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f,
* `chapters/definitions.tex` DEF-006: `𝓜_N` is the set of finitely supported arrays
  `m : ℤ → ℕ` of nonnegative integers with `∑ₙ mₙ = N`;
* `chapters/definitions.tex` DEF-026: `E_{N,ab} = N⁻¹ a_b^* a_a` removes a particle at the
  donor `a`, adds one at the receiver `b`; for `a ≠ b` the coefficient is
  `N⁻¹ √(m_a (m_b+1))`; `E_{N,aa} = m_a / N`;
* `chapters/core/occupation_transfers.tex`: `W^q_{N,ab} Ψ_m = q(m) conj(q(m - e_a + e_b)) Ψ_{m-e_a+e_b}`
  when `m_a ≥ 1`, zero otherwise; the transfers preserve every exterior occupation.

This file is purely finite combinatorics of the occupation index and of the real (ungauged)
matrix coefficient.  It does NOT realize the Hilbert space `Sym^N ℓ²(ℤ)`, the Bethe basis, the
gauge `q_N`, the operators `E_{N,ab}`, or the canonical commutation relations; it only proves
the index/coefficient identities that those later realizations must use.
-/

namespace QuantumNLS.Occupation

open Finsupp

noncomputable section

/-- An occupation array: a finitely supported function `ℤ → ℕ` (DEF-006). -/
abbrev Occ := ℤ →₀ ℕ

/-- The unit array `e_a`. -/
abbrev e (a : ℤ) : Occ := Finsupp.single a 1

/-- Total particle number `∑ₙ mₙ`. -/
def total (m : Occ) : ℕ := m.degree

/-- The set `𝓜_N` of complete occupation arrays of total `N` (DEF-006). -/
def IsArray (N : ℕ) (m : Occ) : Prop := total m = N

/-- The type `𝓜_N`. -/
abbrev Arr (N : ℕ) := {m : Occ // IsArray N m}

/-- The donor-to-receiver index shift `m ↦ m - e_a + e_b` (natural subtraction;
it is the intended transfer exactly when the donor is occupied, `1 ≤ m a`). -/
def shift (a b : ℤ) (m : Occ) : Occ := m - e a + e b

/-- The occupied-donor condition `m_a ≥ 1` (the domain of the partial shift `W_{N,ab}`). -/
def DonorOK (a : ℤ) (m : Occ) : Prop := 1 ≤ m a

instance (a : ℤ) (m : Occ) : Decidable (DonorOK a m) := by unfold DonorOK; infer_instance

/-- The partial transfer on indices: `none` (zero vector) when the donor is empty. -/
def transfer (a b : ℤ) (m : Occ) : Option Occ :=
  if DonorOK a m then some (shift a b m) else none

/-- DEF-026 matrix coefficient of `E_{N,ab}` on the basis vector `m`:
`N⁻¹ √(m_a (m_b+1))` for `a ≠ b`, and `m_a / N` for `a = b`. -/
def coef (N : ℕ) (a b : ℤ) (m : Occ) : ℝ :=
  if a = b then (m a : ℝ) / N else Real.sqrt ((m a : ℝ) * ((m b : ℝ) + 1)) / N

/-! ### Basic arithmetic of the shift -/

lemma single_le_of_donorOK {a : ℤ} {m : Occ} (h : DonorOK a m) : e a ≤ m := by
  rw [Finsupp.single_le_iff]; exact h

lemma shift_sub_add {a : ℤ} {m : Occ} (h : DonorOK a m) : (m - e a) + e a = m :=
  tsub_add_cancel_of_le (single_le_of_donorOK h)

/-- Exterior occupations are preserved exactly. -/
lemma shift_apply_exterior {a b c : ℤ} (m : Occ) (hca : c ≠ a) (hcb : c ≠ b) :
    shift a b m c = m c := by
  simp [shift, hca.symm, hcb.symm]

/-- The donor loses one particle (`a ≠ b`, donor occupied). -/
lemma shift_apply_donor {a b : ℤ} (m : Occ) (hab : a ≠ b) :
    shift a b m a = m a - 1 := by
  simp [shift, hab]

/-- The receiver gains one particle (`a ≠ b`). -/
lemma shift_apply_receiver {a b : ℤ} (m : Occ) (hab : a ≠ b) :
    shift a b m b = m b + 1 := by
  simp [shift, hab.symm]

/-- Diagonal transfer is the identity on occupied donors. -/
lemma shift_self {a : ℤ} {m : Occ} (h : DonorOK a m) : shift a a m = m :=
  shift_sub_add h

/-- Count preservation: a transfer from an occupied donor preserves the total `N`. -/
theorem total_shift {a b : ℤ} {m : Occ} (h : DonorOK a m) : total (shift a b m) = total m := by
  have h2 := congrArg Finsupp.degree (shift_sub_add h)
  rw [map_add, Finsupp.degree_single] at h2
  unfold total shift
  rw [map_add, Finsupp.degree_single]
  omega

/-- The transfer maps `𝓜_N` to `𝓜_N` on the donor domain. -/
theorem isArray_shift {N : ℕ} {a b : ℤ} {m : Occ} (hm : IsArray N m) (h : DonorOK a m) :
    IsArray N (shift a b m) := by
  unfold IsArray at *; rw [total_shift h]; exact hm

/-- The shifted array, as an element of `𝓜_N`, when the donor is occupied. -/
def shiftArr {N : ℕ} (a b : ℤ) (m : Arr N) (h : DonorOK a m.1) : Arr N :=
  ⟨shift a b m.1, isArray_shift m.2 h⟩

/-- After a transfer from `a` to `b ≠ a`, the receiver `b` is occupied, so the reverse
transfer `b → a` is allowed (adjoint = reverse transfer). -/
lemma donorOK_shift_receiver {a b : ℤ} {m : Occ} (hab : a ≠ b) :
    DonorOK b (shift a b m) := by
  unfold DonorOK; rw [shift_apply_receiver m hab]; omega

/-- The reverse transfer undoes the transfer. -/
theorem shift_shift_reverse {a b : ℤ} {m : Occ} (h : DonorOK a m) :
    shift b a (shift a b m) = m := by
  unfold shift
  have h1 : (m - e a + e b) - e b = m - e a := by
    rw [add_tsub_cancel_right]
  rw [h1]; exact shift_sub_add h

/-- The transfer is injective on its donor domain. -/
theorem shift_injOn {a b : ℤ} {m m' : Occ} (h : DonorOK a m) (h' : DonorOK a m')
    (hs : shift a b m = shift a b m') : m = m' := by
  have := congrArg (shift b a) hs
  rwa [shift_shift_reverse h, shift_shift_reverse h'] at this

/-- Pointwise formula `m - e_a + e_b` (in `ℕ`, truncated at an empty donor). -/
theorem shift_apply (a b : ℤ) (m : Occ) (c : ℤ) :
    shift a b m c = m c - (if c = a then 1 else 0) + (if c = b then 1 else 0) := by
  simp [shift, Finsupp.single_apply, eq_comm]

/-- Each local occupation `B_{N,j} = m_j / N` changes by `(δ_{jb} - δ_{ja}) / N`
(first identity in the proof of `prop:exact-occupation-algebra`, index level). -/
theorem occupation_fraction_shift {N : ℕ} {a b : ℤ} {m : Occ} (h : DonorOK a m) (j : ℤ) :
    ((shift a b m j : ℕ) : ℝ) / N
      = (m j : ℝ) / N + ((if j = b then 1 else 0) - (if j = a then 1 else 0)) / N := by
  by_cases hab : a = b
  · subst hab; rw [shift_self h]; simp
  · by_cases h1 : j = a
    · subst h1
      have h1' : 1 ≤ m j := h
      rw [shift_apply_donor m hab, Nat.cast_sub h1']
      simp [hab]; ring
    · by_cases h2 : j = b
      · subst h2
        rw [shift_apply_receiver m hab]
        simp [h1]; ring
      · rw [shift_apply_exterior m h1 h2]; simp [h1, h2]

/-! ### Coefficient identities -/

lemma coef_offdiag {N : ℕ} {a b : ℤ} (hab : a ≠ b) (m : Occ) :
    coef N a b m = Real.sqrt ((m a : ℝ) * ((m b : ℝ) + 1)) / N := by
  simp [coef, hab]

lemma coef_diag (N : ℕ) (a : ℤ) (m : Occ) : coef N a a m = (m a : ℝ) / N := by
  simp [coef]

/-- The coefficient vanishes on an empty donor (the source's "zero when `m_a = 0`"). -/
lemma coef_empty_donor {N : ℕ} {a b : ℤ} {m : Occ} (h : m a = 0) : coef N a b m = 0 := by
  by_cases hab : a = b
  · subst hab; simp [coef, h]
  · simp [coef, hab, h]

/-- Squared coefficient `N⁻² m_a (m_b+1)`. -/
theorem coef_sq_offdiag {N : ℕ} {a b : ℤ} (hab : a ≠ b) (m : Occ) :
    coef N a b m ^ 2 = (m a : ℝ) * ((m b : ℝ) + 1) / (N : ℝ) ^ 2 := by
  rw [coef_offdiag hab, div_pow, Real.sq_sqrt]
  positivity

/-- **Donor/receiver adjoint symmetry.**  For `a ≠ b` and an occupied donor, the matrix element of
`E_{N,ab}` from `m` to `m' = m - e_a + e_b` equals the matrix element of the reverse transfer
`E_{N,ba}` from `m'` back to `m`: `⟨m'|E_ab|m⟩ = ⟨m|E_ba|m'⟩` (so `E_ab^* = E_ba` at the
coefficient level; the gauge phases `q(m) conj q(m')` are not involved here). -/
theorem coef_adjoint {N : ℕ} {a b : ℤ} (hab : a ≠ b) {m : Occ} (h : DonorOK a m) :
    coef N a b m = coef N b a (shift a b m) := by
  rw [coef_offdiag hab, coef_offdiag hab.symm, shift_apply_receiver m hab,
    shift_apply_donor m hab]
  have h1 : (((m a - 1 : ℕ)) : ℝ) + 1 = (m a : ℝ) := by
    have : 1 ≤ m a := h
    rw [Nat.cast_sub this]; push_cast; ring
  rw [h1]; push_cast
  congr 2; ring

/-- Round-trip coefficient `E_ba E_ab` on the basis vector `m` (no occupancy hypothesis):
`N⁻² m_a (m_b+1)`, including the empty-donor case where both sides are zero. -/
theorem coef_roundtrip {N : ℕ} {a b : ℤ} (hab : a ≠ b) (m : Occ) :
    coef N a b m * coef N b a (shift a b m) = (m a : ℝ) * ((m b : ℝ) + 1) / (N : ℝ) ^ 2 := by
  by_cases ha : m a = 0
  · rw [coef_empty_donor ha]; simp [ha]
  · have hA : DonorOK a m := Nat.one_le_iff_ne_zero.mpr ha
    rw [← coef_adjoint hab hA, ← sq]; exact coef_sq_offdiag hab m

/-- The index-level shadow of the exact occupation algebra
`[E_{ab}, E_{ba}] = N⁻¹ (E_{bb} - E_{aa})` (`eq:exact-algebra` with `c = b`, `d = a`):
(`E_ab E_ba` minus `E_ba E_ab`) on the basis vector `m` equals `(m_b - m_a)/N²`.
Stated through the coefficient chains `m → shift (b→a) → back` and `m → shift (a→b) → back`;
no gauge phases occur since `q(m) conj q(m') · q(m') conj q(m) = 1`. -/
theorem coef_commutator_pair {N : ℕ} {a b : ℤ} (hab : a ≠ b) (m : Occ) :
    coef N b a m * coef N a b (shift b a m) - coef N a b m * coef N b a (shift a b m)
      = ((m b : ℝ) - (m a : ℝ)) / (N : ℝ) ^ 2 := by
  rw [coef_roundtrip hab.symm m, coef_roundtrip hab m]
  ring

/-- Index-level commutation of two transfers with distinct occupied donors (`a ≠ c`): the
composite shifts `W_{ab} W_{cd}` and `W_{cd} W_{ab}` land on the same array.  (Case `b = c` or
`a = d` of the exact algebra involves the nontrivial coefficients and is not claimed here.) -/
theorem shift_comm_of_ne_donor {a b c d : ℤ} {m : Occ} (hac : a ≠ c)
    (ha : DonorOK a m) (hc : DonorOK c m) :
    shift a b (shift c d m) = shift c d (shift a b m) := by
  ext x
  simp only [shift_apply]
  have ha' : 1 ≤ m a := ha
  have hc' : 1 ≤ m c := hc
  by_cases h1 : x = a <;> by_cases h2 : x = b <;> by_cases h3 : x = c <;> by_cases h4 : x = d <;>
    simp_all

/-- Donor-domain closure: after the `c → d` transfer, `a ≠ c` is still an occupied donor
(so the composite `W_{ab}W_{cd}` is defined on the same domain in either order). -/
theorem donorOK_shift_of_ne {a c d : ℤ} {m : Occ} (hac : a ≠ c) (ha : DonorOK a m) :
    DonorOK a (shift c d m) := by
  unfold DonorOK at *
  rw [shift_apply]
  have : ¬ (a = c) := hac
  by_cases h : a = d <;> simp [h, this]
  omega

/-! ### General exact-algebra identity at coefficient level (eq:exact-algebra, index level)

`w a b m = N · coef N a b m` is the unnormalised weight (`m_a` on the diagonal, `√(m_a(m_b+1))`
off it).  The identity below is the coefficient-chain form of
`[a_b^* a_a, a_d^* a_c] = δ_{ad} a_b^* a_c − δ_{bc} a_d^* a_a` for ALL index coincidence patterns
(including diagonal and empty-donor cases); gauge phases cancel along the chains and are not used. -/

/-- Unnormalised weight `N · coef`. -/
def w (a b : ℤ) (m : Occ) : ℝ :=
  if a = b then (m a : ℝ) else Real.sqrt ((m a : ℝ) * ((m b : ℝ) + 1))

lemma coef_eq_w (N : ℕ) (a b : ℤ) (m : Occ) : coef N a b m = w a b m / N := by
  unfold coef w; split_ifs <;> rfl

lemma w_empty {a b : ℤ} {m : Occ} (h : m a = 0) : w a b m = 0 := by
  unfold w; split_ifs <;> simp [h]

lemma zero_or_succ (n : ℕ) : n = 0 ∨ ∃ k, n = k + 1 := by cases n <;> simp

/-- Coefficient-chain form of `[a_b^* a_a, a_d^* a_c] = δ_{ad} a_b^* a_c − δ_{bc} a_d^* a_a`
on the occupation basis: `(a_b^* a_a)(a_d^* a_c)` minus `(a_d^* a_c)(a_b^* a_a)`. -/
theorem w_commutator (a b c d : ℤ) (m : Occ) :
    w c d m * w a b (shift c d m) - w a b m * w c d (shift a b m)
      = (if a = d then w c b m else 0) - (if b = c then w a d m else 0) := by
  by_cases hab : a = b <;> by_cases hcd : c = d <;> by_cases hac : a = c <;> by_cases hbd : b = d <;>
    by_cases hbc : b = c <;> by_cases had : a = d <;> simp_all [w, shift_apply, eq_comm] <;>
  (rcases zero_or_succ (m a) with ha | ⟨ka, ha⟩ <;> rcases zero_or_succ (m c) with hc | ⟨kc, hc⟩ <;>
   rcases zero_or_succ (m d) with hd | ⟨kd, hd⟩ <;>
   simp (disch := positivity) [*, Real.sqrt_mul] <;> (try ring_nf) <;>
   (try simp (disch := positivity) [Real.sq_sqrt]) <;> (try ring_nf))

/-- Normalised form: `[E_{N,ab}, E_{N,cd}] = N⁻¹ (δ_{ad} E_{N,cb} − δ_{bc} E_{N,ad})` on the
coefficient chains of the occupation basis (`eq:exact-algebra`, second line, index/coefficient level).
Here the order is `E_{ab}E_{cd}` (first apply `cd`, landing on `shift c d m`) minus `E_{cd}E_{ab}`. -/
theorem coef_commutator (N : ℕ) (a b c d : ℤ) (m : Occ) :
    coef N c d m * coef N a b (shift c d m) - coef N a b m * coef N c d (shift a b m)
      = (1 / (N : ℝ)) * ((if a = d then coef N c b m else 0) - (if b = c then coef N a d m else 0)) := by
  simp only [coef_eq_w]
  have h := w_commutator a b c d m
  have e : w c d m / N * (w a b (shift c d m) / N) - w a b m / N * (w c d (shift a b m) / N)
      = (w c d m * w a b (shift c d m) - w a b m * w c d (shift a b m)) / (N : ℝ) ^ 2 := by ring
  rw [e, h]
  split_ifs <;> simp <;> ring


/-! ## T4: finite-support weighted-shift operators, overlap identities, adjointness, CCR

Everything below is over `ℂ`-valued finitely supported functions on occupation arrays (algebraic
core only; no completion to `ℓ²`, no Bethe basis, no gauge `q_N`).  `Top a b = a_b^* a_a` is the
weighted shift `|m⟩ ↦ w_{ab}(m)|m - e_a + e_b⟩`, zero on empty donors; `EOp N a b = N⁻¹ Top a b`.
Source: DEF-026 (`definitions.tex:157`), `occupation_transfers.tex` eq:W/eq:E,
`wick_calculus.tex:131` eq:full-CCR and eq:full-minors (gauge phases cancel along the chains and
the operator identities hold for the ungauged operators; gauged versions are a separate task). -/

/-- Basis ket `|m⟩` of the finite-support space over all occupation arrays. -/
abbrev ket (m : Occ) : Occ →₀ ℂ := Finsupp.single m (1 : ℂ)

/-- Finite-support carrier (all particle-number sectors at once; `E_ab` preserves `total`). -/
abbrev FS := Occ →₀ ℂ

/-- Unnormalised weighted shift `a_b^* a_a` on the occupation basis:
`|m⟩ ↦ w_{ab}(m) |m - e_a + e_b⟩` (zero when the donor is empty, since `w = 0` there). -/
def Top (a b : ℤ) : Module.End ℂ FS :=
  Finsupp.linearCombination ℂ (fun m : Occ => (w a b m : ℂ) • ket (shift a b m))

lemma Top_ket (a b : ℤ) (m : Occ) : Top a b (ket m) = (w a b m : ℂ) • ket (shift a b m) := by
  simp [Top]

/-- Normalised transfer `E_{N,ab} = N⁻¹ a_b^* a_a` (ungauged). -/
def EOp (N : ℕ) (a b : ℤ) : Module.End ℂ FS := ((N : ℂ)⁻¹) • Top a b

lemma EOp_ket (N : ℕ) (a b : ℤ) (m : Occ) :
    EOp N a b (ket m) = (coef N a b m : ℂ) • ket (shift a b m) := by
  rw [EOp, LinearMap.smul_apply, Top_ket, smul_smul, coef_eq_w]
  congr 1; push_cast; ring

lemma ext_ket {f g : Module.End ℂ FS} (h : ∀ m, f (ket m) = g (ket m)) : f = g :=
  Finsupp.lhom_ext (fun m c => by
    have : Finsupp.single m c = c • ket m := by simp
    rw [this, map_smul, map_smul, h m])

lemma w_ne_zero_donor {a b : ℤ} {m : Occ} (h : w a b m ≠ 0) : DonorOK a m := by
  by_contra hd
  apply h
  exact w_empty (by unfold DonorOK at hd; omega)

/-- Integer-valued occupation of a donor-occupied shift. -/
lemma shift_apply_int {a b : ℤ} {m : Occ} (h : DonorOK a m) (x : ℤ) :
    (shift a b m x : ℤ) = (m x : ℤ) - (if x = a then 1 else 0) + (if x = b then 1 else 0) := by
  rw [shift_apply]
  have : x = a → 1 ≤ m x := by rintro rfl; exact h
  split_ifs <;> omega

lemma occ_ext_int {p q : Occ} (h : ∀ x, (p x : ℤ) = (q x : ℤ)) : p = q := by
  ext x; exact_mod_cast h x

/-- Target arrays of the unconditional overlap cases (no occupancy hypotheses):
`δ_{ad}`: `m → (c→a) → (a→b)` lands on `m - e_c + e_b`. -/
theorem shift_shift_ad (a b c : ℤ) (m : Occ) : shift a b (shift c a m) = shift c b m := by
  unfold shift; rw [add_tsub_cancel_right]

/-- `δ_{bc}`: `m → (a→c) → (c→d)` lands on `m - e_a + e_d`. -/
theorem shift_shift_bc (a c d : ℤ) (m : Occ) : shift c d (shift a c m) = shift a d m := by
  unfold shift; rw [add_tsub_cancel_right]

/-- Two-step target in integers: `m - e_c + e_d - e_a + e_b`. -/
def tz (a b c d : ℤ) (m : Occ) (x : ℤ) : ℤ :=
  (m x : ℤ) - (if x = c then 1 else 0) + (if x = d then 1 else 0)
    - (if x = a then 1 else 0) + (if x = b then 1 else 0)

lemma shift_shift_int {a b c d : ℤ} {m : Occ} (hc : DonorOK c m) (ha : DonorOK a (shift c d m))
    (x : ℤ) : (shift a b (shift c d m) x : ℤ) = tz a b c d m x := by
  rw [shift_apply_int ha, shift_apply_int hc]; unfold tz; ring

/-- Overlap identity: when both chains are defined (occupied donors) the two orders reach the
same array. -/
theorem shift_shift_comm {a b c d : ℤ} {m : Occ} (hc : DonorOK c m) (ha : DonorOK a (shift c d m))
    (hc' : DonorOK c (shift a b m)) (ha' : DonorOK a m) :
    shift a b (shift c d m) = shift c d (shift a b m) := by
  apply occ_ext_int
  intro x
  rw [shift_shift_int hc ha, shift_apply_int hc' , shift_apply_int ha']
  unfold tz; ring


lemma tz_swap (a b c d : ℤ) (m : Occ) (x : ℤ) : tz c d a b m x = tz a b c d m x := by
  unfold tz; ring

lemma four_terms (kA kB kC kD : ℝ) (TA TB TC TD U : Occ)
    (hA : kA ≠ 0 → TA = U) (hB : kB ≠ 0 → TB = U) (hC : kC ≠ 0 → TC = U) (hD : kD ≠ 0 → TD = U)
    (h : kA - kB - (kC - kD) = 0) :
    (kA : ℂ) • ket TA - (kB : ℂ) • ket TB = (kC : ℂ) • ket TC - (kD : ℂ) • ket TD := by
  have e : ∀ (k : ℝ) (T : Occ), (k ≠ 0 → T = U) → (k : ℂ) • ket T = (k : ℂ) • ket U := by
    intro k T hk
    by_cases h0 : k = 0
    · simp [h0]
    · rw [hk h0]
  rw [e kA TA hA, e kB TB hB, e kC TC hC, e kD TD hD, ← sub_smul, ← sub_smul]
  have : ((kA : ℂ) - kB) = (kC : ℂ) - kD := by
    have := congrArg (fun r : ℝ => (r : ℂ)) (sub_eq_zero.mp h)
    push_cast at this
    exact this
  rw [this]

/-- **Full CCR on the finite-support basis** (`eq:full-CCR`, ungauged, unnormalised form):
`[a_b^* a_a, a_d^* a_c] = δ_{ad} a_b^* a_c − δ_{bc} a_d^* a_a`, as an identity of linear maps
on finitely supported functions on occupation arrays (every sector at once), for all labels. -/
theorem Top_comm (a b c d : ℤ) :
    Top a b * Top c d - Top c d * Top a b
      = (if a = d then (1 : ℂ) else 0) • Top c b - (if b = c then (1 : ℂ) else 0) • Top a d := by
  apply ext_ket; intro m
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, Top_ket, map_smul]
  rw [smul_smul, smul_smul, smul_smul, smul_smul]
  have hδ1 : (if a = d then (1 : ℂ) else 0) = (((if a = d then (1 : ℝ) else 0) : ℝ) : ℂ) := by
    split_ifs <;> simp
  have hδ2 : (if b = c then (1 : ℂ) else 0) = (((if b = c then (1 : ℝ) else 0) : ℝ) : ℂ) := by
    split_ifs <;> simp
  rw [hδ1, hδ2]
  simp only [← Complex.ofReal_mul]
  have hw := w_commutator a b c d m
  -- the four scalar/target pairs
  have claimA : w c d m * w a b (shift c d m) ≠ 0 →
      ∀ x, (shift a b (shift c d m) x : ℤ) = tz a b c d m x := by
    intro h x
    rcases mul_ne_zero_iff.mp h with ⟨h1, h2⟩
    exact shift_shift_int (w_ne_zero_donor h1) (w_ne_zero_donor h2) x
  have claimB : w a b m * w c d (shift a b m) ≠ 0 →
      ∀ x, (shift c d (shift a b m) x : ℤ) = tz a b c d m x := by
    intro h x
    rcases mul_ne_zero_iff.mp h with ⟨h1, h2⟩
    rw [shift_shift_int (w_ne_zero_donor h1) (w_ne_zero_donor h2) x, tz_swap]
  have claimC : (if a = d then (1 : ℝ) else 0) * w c b m ≠ 0 →
      ∀ x, (shift c b m x : ℤ) = tz a b c d m x := by
    intro h x
    by_cases had : a = d
    · subst had
      have h2 : w c b m ≠ 0 := by simpa using h
      rw [shift_apply_int (w_ne_zero_donor h2)]; unfold tz; ring
    · simp [had] at h
  have claimD : (if b = c then (1 : ℝ) else 0) * w a d m ≠ 0 →
      ∀ x, (shift a d m x : ℤ) = tz a b c d m x := by
    intro h x
    by_cases hbc : b = c
    · subst hbc
      have h2 : w a d m ≠ 0 := by simpa using h
      rw [shift_apply_int (w_ne_zero_donor h2)]; unfold tz; ring
    · simp [hbc] at h
  have scal : (w c d m * w a b (shift c d m)) - (w a b m * w c d (shift a b m))
      - ((if a = d then (1 : ℝ) else 0) * w c b m - (if b = c then (1 : ℝ) else 0) * w a d m) = 0 := by
    rw [hw]; split_ifs <;> simp
  by_cases hex : ∃ U : Occ, ∀ x, (U x : ℤ) = tz a b c d m x
  · obtain ⟨U, hU⟩ := hex
    exact four_terms _ _ _ _ _ _ _ _ U
      (fun h => occ_ext_int (fun x => (claimA h x).trans (hU x).symm))
      (fun h => occ_ext_int (fun x => (claimB h x).trans (hU x).symm))
      (fun h => occ_ext_int (fun x => (claimC h x).trans (hU x).symm))
      (fun h => occ_ext_int (fun x => (claimD h x).trans (hU x).symm)) scal
  · have z : ∀ (k : ℝ) (T : Occ), (k ≠ 0 → ∀ x, (T x : ℤ) = tz a b c d m x) → k = 0 := by
      intro k T hk
      by_contra h0
      exact hex ⟨T, hk h0⟩
    have zA := z _ _ claimA
    have zB := z _ _ claimB
    have zC := z _ _ claimC
    have zD := z _ _ claimD
    rw [zA, zB, zC, zD]
    simp


/-- Normalised CCR (`eq:full-CCR`, ungauged): `[E_{N,ab}, E_{N,cd}] = N⁻¹(δ_{ad}E_{N,cb} − δ_{bc}E_{N,ad})`.
(Holds for every `N`; for `N = 0` both sides vanish since `N⁻¹ = 0`.) -/
theorem EOp_comm (N : ℕ) (a b c d : ℤ) :
    EOp N a b * EOp N c d - EOp N c d * EOp N a b
      = ((N : ℂ)⁻¹) • ((if a = d then (1 : ℂ) else 0) • EOp N c b
          - (if b = c then (1 : ℂ) else 0) • EOp N a d) := by
  apply ext_ket; intro m
  have h := congrArg (fun T : Module.End ℂ FS => ((N : ℂ)⁻¹ * (N : ℂ)⁻¹) • T (ket m))
    (Top_comm a b c d)
  have e1 : ∀ δ : ℂ, (N : ℂ)⁻¹ * (N : ℂ)⁻¹ * δ = (N : ℂ)⁻¹ * (δ * (N : ℂ)⁻¹) := fun δ => by ring
  simp only [EOp, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, map_smul,
    smul_sub, smul_smul, e1] at h ⊢
  exact h

lemma w_minors (a b c d : ℤ) (m : Occ) :
    w c d m * w a b (shift c d m) - w c b m * w a d (shift c b m)
      = (if a = d then w c b m else 0) - (if a = b then w c d m else 0) := by
  by_cases hab : a = b <;> by_cases hcd : c = d <;> by_cases hac : a = c <;> by_cases hbd : b = d <;>
    by_cases hbc : b = c <;> by_cases had : a = d <;> simp_all [w, shift_apply, eq_comm] <;>
  (rcases zero_or_succ (m a) with ha | ⟨ka, ha⟩ <;> rcases zero_or_succ (m c) with hc | ⟨kc, hc⟩ <;>
   rcases zero_or_succ (m d) with hd | ⟨kd, hd⟩ <;>
   simp (disch := positivity) [*, Real.sqrt_mul] <;> (try ring_nf) <;>
   (try simp (disch := positivity) [Real.sq_sqrt]) <;> (try ring_nf))

/-- `eq:full-minors` (ungauged, unnormalised): moving the middle annihilation past the middle
creation, `a_b^*a_a a_d^*a_c − a_d^*a_a a_b^*a_c = δ_{ad} a_b^*a_c − δ_{ab} a_d^*a_c`. -/
theorem Top_minors (a b c d : ℤ) :
    Top a b * Top c d - Top a d * Top c b
      = (if a = d then (1 : ℂ) else 0) • Top c b - (if a = b then (1 : ℂ) else 0) • Top c d := by
  apply ext_ket; intro m
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, Top_ket, map_smul]
  rw [smul_smul, smul_smul, smul_smul, smul_smul]
  have hδ1 : (if a = d then (1 : ℂ) else 0) = (((if a = d then (1 : ℝ) else 0) : ℝ) : ℂ) := by
    split_ifs <;> simp
  have hδ2 : (if a = b then (1 : ℂ) else 0) = (((if a = b then (1 : ℝ) else 0) : ℝ) : ℂ) := by
    split_ifs <;> simp
  rw [hδ1, hδ2]
  simp only [← Complex.ofReal_mul]
  have hw := w_minors a b c d m
  have claimA : w c d m * w a b (shift c d m) ≠ 0 →
      ∀ x, (shift a b (shift c d m) x : ℤ) = tz a b c d m x := by
    intro h x
    rcases mul_ne_zero_iff.mp h with ⟨h1, h2⟩
    exact shift_shift_int (w_ne_zero_donor h1) (w_ne_zero_donor h2) x
  have claimB : w c b m * w a d (shift c b m) ≠ 0 →
      ∀ x, (shift a d (shift c b m) x : ℤ) = tz a b c d m x := by
    intro h x
    rcases mul_ne_zero_iff.mp h with ⟨h1, h2⟩
    rw [shift_shift_int (w_ne_zero_donor h1) (w_ne_zero_donor h2) x]; unfold tz; ring
  have claimC : (if a = d then (1 : ℝ) else 0) * w c b m ≠ 0 →
      ∀ x, (shift c b m x : ℤ) = tz a b c d m x := by
    intro h x
    by_cases had : a = d
    · subst had
      have h2 : w c b m ≠ 0 := by simpa using h
      rw [shift_apply_int (w_ne_zero_donor h2)]; unfold tz; ring
    · simp [had] at h
  have claimD : (if a = b then (1 : ℝ) else 0) * w c d m ≠ 0 →
      ∀ x, (shift c d m x : ℤ) = tz a b c d m x := by
    intro h x
    by_cases hab : a = b
    · subst hab
      have h2 : w c d m ≠ 0 := by simpa using h
      rw [shift_apply_int (w_ne_zero_donor h2)]; unfold tz; ring
    · simp [hab] at h
  have scal : (w c d m * w a b (shift c d m)) - (w c b m * w a d (shift c b m))
      - ((if a = d then (1 : ℝ) else 0) * w c b m - (if a = b then (1 : ℝ) else 0) * w c d m) = 0 := by
    rw [hw]; split_ifs <;> simp
  by_cases hex : ∃ U : Occ, ∀ x, (U x : ℤ) = tz a b c d m x
  · obtain ⟨U, hU⟩ := hex
    exact four_terms _ _ _ _ _ _ _ _ U
      (fun h => occ_ext_int (fun x => (claimA h x).trans (hU x).symm))
      (fun h => occ_ext_int (fun x => (claimB h x).trans (hU x).symm))
      (fun h => occ_ext_int (fun x => (claimC h x).trans (hU x).symm))
      (fun h => occ_ext_int (fun x => (claimD h x).trans (hU x).symm)) scal
  · have z : ∀ (k : ℝ) (T : Occ), (k ≠ 0 → ∀ x, (T x : ℤ) = tz a b c d m x) → k = 0 := by
      intro k T hk
      by_contra h0
      exact hex ⟨T, hk h0⟩
    rw [z _ _ claimA, z _ _ claimB, z _ _ claimC, z _ _ claimD]
    simp

/-! ### Adjointness: `(a_b^* a_a)^* = a_a^* a_b` on the finite-support basis -/

/-- The standard (conjugate-linear in the first slot) pairing on finitely supported functions. -/
def ip (u v : FS) : ℂ := u.sum fun m x => (starRingEnd ℂ) x * v m

lemma ip_ket_left (m : Occ) (v : FS) : ip (ket m) v = v m := by
  simp [ip]

lemma ip_add_left (u u' v : FS) : ip (u + u') v = ip u v + ip u' v := by
  unfold ip
  rw [Finsupp.sum_add_index']
  · intro i; simp
  · intro i x y; rw [map_add]; ring

lemma ip_smul_left (c : ℂ) (u v : FS) : ip (c • u) v = (starRingEnd ℂ) c * ip u v := by
  unfold ip
  rw [Finsupp.sum_smul_index']
  · rw [Finsupp.mul_sum]; apply Finsupp.sum_congr; intro i _; simp [mul_assoc]
  · intro i; simp

lemma ip_ket_right (u : FS) (m : Occ) : ip u (ket m) = (starRingEnd ℂ) (u m) := by
  unfold ip
  simp only [Finsupp.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finsupp.sum_ite_eq]
  by_cases h : m ∈ u.support
  · simp [h]
  · simp [h, Finsupp.notMem_support_iff.mp h]

lemma w_real_cast (a b : ℤ) (m : Occ) : (starRingEnd ℂ) (w a b m : ℂ) = (w a b m : ℂ) :=
  Complex.conj_ofReal _

lemma w_adjoint {a b : ℤ} {m : Occ} (h : DonorOK a m) : w a b m = w b a (shift a b m) := by
  by_cases hab : a = b
  · subst hab; rw [shift_self h]
  · have := coef_adjoint (N := 1) hab h
    rw [coef_eq_w, coef_eq_w] at this
    simpa using this

lemma w_adjoint_aux (a b : ℤ) (m n : Occ) :
    (if shift a b m = n then w a b m else 0) = (if shift b a n = m then w b a n else 0) := by
  by_cases h1 : shift a b m = n <;> by_cases h2 : shift b a n = m
  · subst h1
    simp only [ite_true, h2]
    by_cases hd : DonorOK a m
    · exact w_adjoint hd
    · have hm : m a = 0 := by unfold DonorOK at hd; omega
      exfalso
      have := congrArg (fun p : Occ => p a) h2
      simp only [shift_apply] at this
      split_ifs at this <;> omega
  · simp only [h1, h2, ite_true, ite_false]
    subst h1
    by_cases hd : DonorOK a m
    · exact absurd (shift_shift_reverse hd) h2
    · exact w_empty (by unfold DonorOK at hd; omega)
  · simp only [h1, h2, ite_true, ite_false]
    subst h2
    by_cases hd : DonorOK b n
    · exact absurd (shift_shift_reverse hd) h1
    · exact (w_empty (by unfold DonorOK at hd; omega)).symm
  · simp [h1, h2]

/-- Basis-level adjointness: `⟨ket n, Top a b ket m⟩ = ⟨Top b a ket n, ket m⟩`. -/
theorem Top_adjoint_ket (a b : ℤ) (m n : Occ) :
    ip (ket n) (Top a b (ket m)) = ip (Top b a (ket n)) (ket m) := by
  have key := w_adjoint_aux a b m n
  have L : ip (ket n) (Top a b (ket m)) = ((if shift a b m = n then w a b m else 0 : ℝ) : ℂ) := by
    rw [Top_ket, ip_ket_left]
    by_cases h : shift a b m = n <;> simp [h]
  have R : ip (Top b a (ket n)) (ket m) = ((if shift b a n = m then w b a n else 0 : ℝ) : ℂ) := by
    rw [Top_ket, ip_smul_left, ip_ket_left, w_real_cast]
    by_cases h : shift b a n = m <;> simp [h]
  rw [L, R, key]

lemma ip_zero_left (v : FS) : ip 0 v = 0 := by simp [ip]

lemma ip_zero_right (u : FS) : ip u 0 = 0 := by simp [ip]

lemma ip_add_right (u v v' : FS) : ip u (v + v') = ip u v + ip u v' := by
  unfold ip
  simp only [Finsupp.add_apply, mul_add]
  rw [Finsupp.sum_add]

lemma ip_smul_right (c : ℂ) (u v : FS) : ip u (c • v) = c * ip u v := by
  unfold ip
  rw [Finsupp.mul_sum]
  apply Finsupp.sum_congr; intro i _; simp only [Finsupp.smul_apply, smul_eq_mul]; ring

lemma single_eq_smul_ket (m : Occ) (c : ℂ) : (Finsupp.single m c : FS) = c • ket m := by simp

/-- **Adjointness** `(a_b^* a_a)^* = a_a^* a_b`: `⟨u, Top_ab v⟩ = ⟨Top_ba u, v⟩` for all finitely
supported `u, v` (the weights are real, no gauge phase enters). -/
theorem Top_adjoint (a b : ℤ) (u v : FS) : ip u (Top a b v) = ip (Top b a u) v := by
  induction u using Finsupp.induction_linear with
  | zero => simp [ip_zero_left]
  | add u u' hu hu' => rw [map_add, ip_add_left, ip_add_left, hu, hu']
  | single n c =>
    rw [single_eq_smul_ket, map_smul, ip_smul_left, ip_smul_left]
    congr 1
    induction v using Finsupp.induction_linear with
    | zero => simp [ip_zero_right]
    | add v v' hv hv' => rw [map_add, ip_add_right, ip_add_right, hv, hv']
    | single m d =>
      rw [single_eq_smul_ket, map_smul, ip_smul_right, ip_smul_right, Top_adjoint_ket]

theorem EOp_adjoint (N : ℕ) (a b : ℤ) (u v : FS) : ip u (EOp N a b v) = ip (EOp N b a u) v := by
  unfold EOp
  simp only [LinearMap.smul_apply]
  rw [ip_smul_right, ip_smul_left, Top_adjoint, map_inv₀, Complex.conj_natCast]

/-- `N > 0`: the unnormalised weighted shift is `N · E_{N,ab}`. -/
theorem Top_eq_N_smul_EOp {N : ℕ} (hN : 0 < N) (a b : ℤ) : Top a b = (N : ℂ) • EOp N a b := by
  unfold EOp
  rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hN.ne'), one_smul]

/-! ### Sector `𝓜_N`: restriction to `Arr N →₀ ℂ` -/

/-- Finite-support functions on the complete arrays of total `N` (the basis of `ℓ²(𝓜_N)`'s
algebraic core). -/
abbrev Sector (N : ℕ) := Arr N →₀ ℂ

/-- Embedding of the sector into the all-sector space. -/
def emb (N : ℕ) : Sector N →ₗ[ℂ] FS := Finsupp.lmapDomain ℂ ℂ (Subtype.val : Arr N → Occ)

lemma emb_injective (N : ℕ) : Function.Injective (emb N) :=
  Finsupp.mapDomain_injective Subtype.val_injective

lemma emb_apply (N : ℕ) (v : Sector N) (m : Arr N) : emb N v m.1 = v m := by
  simp only [emb, Finsupp.lmapDomain_apply]
  exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective v m

lemma emb_ket (N : ℕ) (m : Arr N) : emb N (Finsupp.single m (1 : ℂ)) = ket m.1 := by
  simp [emb]

/-- The weighted shift on the sector `𝓜_N` (defined on its own basis; an empty donor gives zero,
exactly as in `occupation_transfers.tex`). -/
def TN (N : ℕ) (a b : ℤ) : Module.End ℂ (Sector N) :=
  Finsupp.linearCombination ℂ (fun m : Arr N =>
    if h : DonorOK a m.1 then (w a b m.1 : ℂ) • Finsupp.single (shiftArr a b m h) (1 : ℂ) else 0)

/-- The sector operator is the restriction of the all-sector operator. -/
theorem emb_TN (N : ℕ) (a b : ℤ) (v : Sector N) : emb N (TN N a b v) = Top a b (emb N v) := by
  have : (emb N).comp (TN N a b) = (Top a b).comp (emb N) := by
    apply Finsupp.lhom_ext
    intro m c
    have h1 : (Finsupp.single m c : Sector N) = c • Finsupp.single m (1 : ℂ) := by simp
    simp only [LinearMap.comp_apply, h1, map_smul, emb_ket]
    congr 1
    simp only [TN, Finsupp.linearCombination_single, one_smul]
    by_cases h : DonorOK a m.1
    · simp only [h, ↓reduceDIte, map_smul, emb_ket, Top_ket]; rfl
    · have : w a b m.1 = 0 := w_empty (by unfold DonorOK at h; omega)
      simp [h, Top_ket, this]
  exact LinearMap.congr_fun this v

/-- Sector CCR (unnormalised): `[a_b^*a_a, a_d^*a_c] = δ_{ad} a_b^*a_c − δ_{bc} a_d^*a_a` on
finitely supported functions on `𝓜_N`. -/
theorem TN_comm (N : ℕ) (a b c d : ℤ) :
    TN N a b * TN N c d - TN N c d * TN N a b
      = (if a = d then (1 : ℂ) else 0) • TN N c b - (if b = c then (1 : ℂ) else 0) • TN N a d := by
  apply LinearMap.ext; intro v
  apply emb_injective N
  have := LinearMap.congr_fun (Top_comm a b c d) (emb N v)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, map_sub, map_smul,
    emb_TN] at this ⊢
  exact this

/-- Sector minors identity (`eq:full-minors`, unnormalised). -/
theorem TN_minors (N : ℕ) (a b c d : ℤ) :
    TN N a b * TN N c d - TN N a d * TN N c b
      = (if a = d then (1 : ℂ) else 0) • TN N c b - (if a = b then (1 : ℂ) else 0) • TN N c d := by
  apply LinearMap.ext; intro v
  apply emb_injective N
  have := LinearMap.congr_fun (Top_minors a b c d) (emb N v)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, map_sub, map_smul,
    emb_TN] at this ⊢
  exact this

/-- Normalised sector operator `E_{N,ab} = N⁻¹ a_b^* a_a` on `𝓜_N`. -/
def EN (N : ℕ) (a b : ℤ) : Module.End ℂ (Sector N) := ((N : ℂ)⁻¹) • TN N a b

/-- The pairing on the sector, defined through the embedding. -/
def ipS (N : ℕ) (u v : Sector N) : ℂ := ip (emb N u) (emb N v)

/-- It is the expected `∑ₘ conj(uₘ) vₘ`. -/
theorem ipS_eq (N : ℕ) (u v : Sector N) : ipS N u v = u.sum fun m x => (starRingEnd ℂ) x * v m := by
  unfold ipS
  induction u using Finsupp.induction_linear with
  | zero => simp [ip_zero_left]
  | add u u' hu hu' =>
    rw [map_add, ip_add_left, hu, hu', Finsupp.sum_add_index']
    · intro i; simp
    · intro i x y; rw [map_add]; ring
  | single m c =>
    have h1 : (Finsupp.single m c : Sector N) = c • Finsupp.single m (1 : ℂ) := by simp
    rw [Finsupp.sum_single_index (by simp), h1, map_smul, emb_ket, ip_smul_left, ip_ket_left,
      emb_apply]

theorem TN_adjoint (N : ℕ) (a b : ℤ) (u v : Sector N) :
    ipS N u (TN N a b v) = ipS N (TN N b a u) v := by
  unfold ipS
  rw [emb_TN, emb_TN]
  exact Top_adjoint a b _ _

/-- Normalised sector CCR for `N > 0`:
`[E_{N,ab}, E_{N,cd}] = N⁻¹(δ_{ad} E_{N,cb} − δ_{bc} E_{N,ad})`. -/
theorem EN_comm {N : ℕ} (hN : 0 < N) (a b c d : ℤ) :
    EN N a b * EN N c d - EN N c d * EN N a b
      = ((N : ℂ)⁻¹) • ((if a = d then (1 : ℂ) else 0) • EN N c b
          - (if b = c then (1 : ℂ) else 0) • EN N a d) := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  apply LinearMap.ext; intro v
  have h := LinearMap.congr_fun (TN_comm N a b c d) v
  simp only [EN, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, map_smul,
    smul_sub, smul_smul] at h ⊢
  have e1 : ∀ δ : ℂ, (N : ℂ)⁻¹ * (N : ℂ)⁻¹ * δ = (N : ℂ)⁻¹ * (δ * (N : ℂ)⁻¹) := fun δ => by ring
  have h2 := congrArg (fun x : Sector N => ((N : ℂ)⁻¹ * (N : ℂ)⁻¹) • x) h
  simp only [smul_sub, smul_smul, e1] at h2
  exact h2

theorem EN_adjoint (N : ℕ) (a b : ℤ) (u v : Sector N) :
    ipS N u (EN N a b v) = ipS N (EN N b a u) v := by
  unfold ipS EN
  simp only [LinearMap.smul_apply, map_smul]
  rw [ip_smul_right, ip_smul_left, map_inv₀, Complex.conj_natCast]
  have := TN_adjoint N a b u v
  unfold ipS at this
  rw [this]

/-! ## Gauged transfers `W^q`, `E^q` (DEF-025 gauge, `occupation_transfers.tex` eq:W, eq:E)

For ANY unit-modulus `q : Occ → ℂ` (a pointwise function on all arrays; the report's `q_N` is one
such, selected elsewhere), `Tq q a b = D_q^* Top_ab D_q` has coefficients
`q(m) conj q(m') w_ab(m)`.  The gauged CCR and minors identities are gauge independent. -/

/-- Diagonal gauge multiplication `|m⟩ ↦ q(m)|m⟩` (DEF-025 rephasing). -/
def Dg (q : Occ → ℂ) : Module.End ℂ FS :=
  Finsupp.linearCombination ℂ (fun m : Occ => q m • ket m)

lemma Dg_ket (q : Occ → ℂ) (m : Occ) : Dg q (ket m) = q m • ket m := by simp [Dg]

/-- Unit-modulus gauge. -/
def UnitGauge (q : Occ → ℂ) : Prop := ∀ m, Complex.normSq (q m) = 1

lemma unit_mul_conj {q : Occ → ℂ} (hq : UnitGauge q) (m : Occ) :
    q m * (starRingEnd ℂ) (q m) = 1 := by
  rw [Complex.mul_conj, hq m]; simp

lemma Dg_conj_mul {q : Occ → ℂ} (hq : UnitGauge q) :
    Dg (fun m => (starRingEnd ℂ) (q m)) * Dg q = 1 := by
  apply ext_ket; intro m
  simp only [Module.End.mul_apply, Dg_ket, map_smul, smul_smul, Module.End.one_apply]
  rw [unit_mul_conj hq, one_smul]

lemma Dg_mul_conj {q : Occ → ℂ} (hq : UnitGauge q) :
    Dg q * Dg (fun m => (starRingEnd ℂ) (q m)) = 1 := by
  apply ext_ket; intro m
  simp only [Module.End.mul_apply, Dg_ket, map_smul, smul_smul, Module.End.one_apply]
  rw [mul_comm, unit_mul_conj hq, one_smul]

/-- Gauged unnormalised transfer `W^q`-weighted: `Tq q a b = D_q^* Top_ab D_q`, i.e.
`|m⟩ ↦ q(m) conj(q(m')) w_ab(m) |m'⟩` with `m' = m - e_a + e_b`
(`occupation_transfers.tex` eq:W, eq:E before the factor `N⁻¹`). -/
def Tq (q : Occ → ℂ) (a b : ℤ) : Module.End ℂ FS :=
  Dg (fun m => (starRingEnd ℂ) (q m)) * Top a b * Dg q

theorem Tq_ket (q : Occ → ℂ) (a b : ℤ) (m : Occ) :
    Tq q a b (ket m)
      = (q m * (starRingEnd ℂ) (q (shift a b m)) * (w a b m : ℂ)) • ket (shift a b m) := by
  simp only [Tq, Module.End.mul_apply, Dg_ket, map_smul, Top_ket, smul_smul]
  congr 1; ring

/-- Normalised gauged transfer `E^q_{N,ab} = N⁻¹ Tq`, with coefficient
`N⁻¹ √(m_a(m_b+1)) q(m) conj q(m')` as in eq:E. -/
def EqOp (q : Occ → ℂ) (N : ℕ) (a b : ℤ) : Module.End ℂ FS := ((N : ℂ)⁻¹) • Tq q a b

theorem EqOp_ket (q : Occ → ℂ) (N : ℕ) (a b : ℤ) (m : Occ) :
    EqOp q N a b (ket m)
      = (q m * (starRingEnd ℂ) (q (shift a b m)) * (coef N a b m : ℂ)) • ket (shift a b m) := by
  rw [EqOp, LinearMap.smul_apply, Tq_ket, smul_smul, coef_eq_w]
  congr 1; push_cast; ring

lemma Dg_Dgc_apply {q : Occ → ℂ} (hq : UnitGauge q) (x : FS) :
    Dg q (Dg (fun m => (starRingEnd ℂ) (q m)) x) = x := by
  have := LinearMap.congr_fun (Dg_mul_conj hq) x
  simpa using this

/-- Gauged CCR (`eq:full-CCR` for `E^q`) at the unnormalised level: independent of the gauge. -/
theorem Tq_comm {q : Occ → ℂ} (hq : UnitGauge q) (a b c d : ℤ) :
    Tq q a b * Tq q c d - Tq q c d * Tq q a b
      = (if a = d then (1 : ℂ) else 0) • Tq q c b - (if b = c then (1 : ℂ) else 0) • Tq q a d := by
  apply LinearMap.ext; intro v
  have h2 := congrArg (Dg (fun m => (starRingEnd ℂ) (q m)))
    (LinearMap.congr_fun (Top_comm a b c d) (Dg q v))
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, map_sub,
    map_smul] at h2
  simp only [Tq, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, Dg_Dgc_apply hq]
  exact h2

/-- Gauge multiplication is adjoint to multiplication by the conjugate phase. -/
theorem Dg_adjoint (q : Occ → ℂ) (u v : FS) :
    ip u (Dg q v) = ip (Dg (fun m => (starRingEnd ℂ) (q m)) u) v := by
  induction u using Finsupp.induction_linear with
  | zero => simp [ip_zero_left]
  | add u u' hu hu' => rw [map_add, ip_add_left, ip_add_left, hu, hu']
  | single n c =>
    rw [single_eq_smul_ket, map_smul, ip_smul_left, ip_smul_left]
    congr 1
    induction v using Finsupp.induction_linear with
    | zero => simp [ip_zero_right]
    | add v v' hv hv' => rw [map_add, ip_add_right, ip_add_right, hv, hv']
    | single m d =>
      rw [single_eq_smul_ket, map_smul, ip_smul_right, ip_smul_right, Dg_ket, Dg_ket, ip_smul_right,
        ip_smul_left, ip_ket_left]
      simp only [Finsupp.single_apply, Complex.conj_conj]
      by_cases h : n = m
      · subst h; simp
      · simp [Ne.symm h]

lemma conj_conj_fun (q : Occ → ℂ) : (fun m => (starRingEnd ℂ) ((starRingEnd ℂ) (q m))) = q := by
  funext m; exact Complex.conj_conj _

/-- Gauged adjointness: `(Tq_ab)^* = Tq_ba` (any gauge function; only unit modulus makes `Dg`
unitary). -/
theorem Tq_adjoint (q : Occ → ℂ) (a b : ℤ) (u v : FS) :
    ip u (Tq q a b v) = ip (Tq q b a u) v := by
  simp only [Tq, Module.End.mul_apply]
  rw [Dg_adjoint, conj_conj_fun, Top_adjoint]
  exact Dg_adjoint q _ v

/-- Gauged `eq:full-minors` (unnormalised). -/
theorem Tq_minors {q : Occ → ℂ} (hq : UnitGauge q) (a b c d : ℤ) :
    Tq q a b * Tq q c d - Tq q a d * Tq q c b
      = (if a = d then (1 : ℂ) else 0) • Tq q c b - (if a = b then (1 : ℂ) else 0) • Tq q c d := by
  apply LinearMap.ext; intro v
  have h2 := congrArg (Dg (fun m => (starRingEnd ℂ) (q m)))
    (LinearMap.congr_fun (Top_minors a b c d) (Dg q v))
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, map_sub,
    map_smul] at h2
  simp only [Tq, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, Dg_Dgc_apply hq]
  exact h2

/-- Normalised gauged CCR, `eq:full-CCR` for `E^q_{N,ab}` (`wick_calculus.tex:131`):
`[E^q_{N,ab}, E^q_{N,cd}] = N⁻¹(δ_{ad}E^q_{N,cb} − δ_{bc}E^q_{N,ad})`. -/
theorem EqOp_comm {q : Occ → ℂ} (hq : UnitGauge q) (N : ℕ) (a b c d : ℤ) :
    EqOp q N a b * EqOp q N c d - EqOp q N c d * EqOp q N a b
      = ((N : ℂ)⁻¹) • ((if a = d then (1 : ℂ) else 0) • EqOp q N c b
          - (if b = c then (1 : ℂ) else 0) • EqOp q N a d) := by
  apply ext_ket; intro m
  have h := congrArg (fun T : Module.End ℂ FS => ((N : ℂ)⁻¹ * (N : ℂ)⁻¹) • T (ket m))
    (Tq_comm hq a b c d)
  have e1 : ∀ δ : ℂ, (N : ℂ)⁻¹ * (N : ℂ)⁻¹ * δ = (N : ℂ)⁻¹ * (δ * (N : ℂ)⁻¹) := fun δ => by ring
  simp only [EqOp, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, map_smul,
    smul_sub, smul_smul, e1] at h ⊢
  exact h

theorem EqOp_adjoint (q : Occ → ℂ) (N : ℕ) (a b : ℤ) (u v : FS) :
    ip u (EqOp q N a b v) = ip (EqOp q N b a u) v := by
  unfold EqOp
  simp only [LinearMap.smul_apply]
  rw [ip_smul_right, ip_smul_left, Tq_adjoint q, map_inv₀, Complex.conj_natCast]

/-! ### Coefficient bound on `𝓜_N` -/

/-- Two distinct labels carry at most `N` particles together. -/
lemma occ_add_le_total {a b : ℤ} (hab : a ≠ b) (m : Occ) : m a + m b ≤ total m := by
  unfold total
  rw [Finsupp.degree_apply, ← Finset.sum_pair hab]
  exact Finset.sum_le_sum_of_ne_zero (fun x _ hx => Finsupp.mem_support_iff.mpr hx)

/-- Source coefficient bound at the arithmetic level (`wick_calculus.tex`, `eq:full-coefficient-bound`
ingredient): for `N > 0` and a complete array of total `N`, every matrix coefficient of `E_{N,ab}`
lies in `[0, 1]`. -/
theorem coef_nonneg (N : ℕ) (a b : ℤ) (m : Occ) : 0 ≤ coef N a b m := by
  unfold coef; split_ifs <;> positivity

lemma occ_le_total (a : ℤ) (m : Occ) : m a ≤ total m := by
  unfold total
  rw [Finsupp.degree_apply]
  calc m a = ∑ i ∈ ({a} : Finset ℤ), m i := by simp
    _ ≤ ∑ i ∈ m.support, m i :=
      Finset.sum_le_sum_of_ne_zero (fun x _ hx => Finsupp.mem_support_iff.mpr hx)

theorem coef_le_one {N : ℕ} (hN : 0 < N) {m : Occ} (hm : IsArray N m) (a b : ℤ) :
    coef N a b m ≤ 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hm' : total m = N := hm
  unfold coef
  split_ifs with hab
  · rw [div_le_one hNr]
    have := occ_le_total a m
    exact_mod_cast hm' ▸ this
  · rw [div_le_one hNr]
    apply Real.sqrt_le_iff.mpr
    refine ⟨hNr.le, ?_⟩
    have hs := occ_add_le_total hab m
    rw [hm'] at hs
    have key : m a * (m b + 1) ≤ N ^ 2 := by
      rcases Nat.eq_zero_or_pos (m a) with h0 | h0
      · simp [h0]
      · have h1 : m a ≤ N := by omega
        have h2 : m b + 1 ≤ N := by omega
        calc m a * (m b + 1) ≤ N * N := Nat.mul_le_mul h1 h2
          _ = N ^ 2 := by ring
    exact_mod_cast key

/-! ### Diagonal operators `E_{N,aa} = B_{N,a}` and `∑_a B_{N,a} = Id` -/

/-- On the diagonal the shift is the identity whenever the coefficient is nonzero. -/
theorem EOp_diag_ket (N : ℕ) (a : ℤ) (m : Occ) :
    EOp N a a (ket m) = ((m a : ℂ) / N) • ket m := by
  rw [EOp_ket]
  by_cases h : DonorOK a m
  · rw [shift_self h, coef_diag]; push_cast; rfl
  · have hm : m a = 0 := by unfold DonorOK at h; omega
    rw [coef_empty_donor hm]; simp [hm]

/-- Finite-label partial sums of the diagonal occupations are bounded by one coefficientwise. -/
theorem sum_diag_coef_le_one {N : ℕ} {m : Occ} (hm : IsArray N m) (hN : 0 < N) (S : Finset ℤ) :
    ∑ a ∈ S, coef N a a m ≤ 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hm' : total m = N := hm
  simp only [coef_diag]
  rw [← Finset.sum_div, div_le_one hNr]
  have : ∑ a ∈ S, m a ≤ total m := by
    unfold total; rw [Finsupp.degree_apply]
    exact Finset.sum_le_sum_of_ne_zero (fun x _ hx => Finsupp.mem_support_iff.mpr hx)
  have : ((∑ a ∈ S, m a : ℕ) : ℝ) ≤ N := by exact_mod_cast hm' ▸ this
  simpa using this

/-- `∑_a B_{N,a} = Id` on a basis vector (any finite label set containing its support). -/
theorem sum_diag_ket {N : ℕ} (hN : 0 < N) {m : Occ} (hm : IsArray N m) {S : Finset ℤ}
    (hS : m.support ⊆ S) : ∑ a ∈ S, EOp N a a (ket m) = ket m := by
  have hm' : total m = N := hm
  have hsum : ∑ a ∈ S, m a = N := by
    rw [← hm']; unfold total; rw [Finsupp.degree_apply]
    symm; apply Finset.sum_subset hS
    intro i _ hi; simpa using hi
  simp only [EOp_diag_ket]
  rw [← Finset.sum_smul, ← Finset.sum_div, ← Nat.cast_sum, hsum]
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [div_self this, one_smul]

/-- `∑_a B_{N,a} = Id` for every finitely supported vector on arrays of total `N`, with the sum
over any finite label set containing all labels occurring in its support. -/
theorem sum_diag_fs {N : ℕ} (hN : 0 < N) (v : FS) (hv : ∀ m ∈ v.support, IsArray N m)
    {S : Finset ℤ} (hS : ∀ m ∈ v.support, m.support ⊆ S) : ∑ a ∈ S, EOp N a a v = v := by
  have hv' : v = ∑ m ∈ v.support, v m • ket m := by
    conv_lhs => rw [← Finsupp.sum_single v]
    unfold Finsupp.sum
    exact Finset.sum_congr rfl (fun m _ => single_eq_smul_ket m (v m))
  conv_lhs => rw [hv']
  simp only [map_sum, map_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [hv']
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.smul_sum, sum_diag_ket hN (hv m hm) (hS m hm)]

/-! ### Gauged sector operators -/

/-- Diagonal gauge on the sector `𝓜_N`. -/
def DgN (N : ℕ) (q : Occ → ℂ) : Module.End ℂ (Sector N) :=
  Finsupp.linearCombination ℂ (fun m : Arr N => q m.1 • Finsupp.single m (1 : ℂ))

theorem emb_DgN (N : ℕ) (q : Occ → ℂ) (v : Sector N) : emb N (DgN N q v) = Dg q (emb N v) := by
  have : (emb N).comp (DgN N q) = (Dg q).comp (emb N) := by
    apply Finsupp.lhom_ext
    intro m c
    have h1 : (Finsupp.single m c : Sector N) = c • Finsupp.single m (1 : ℂ) := by simp
    simp only [LinearMap.comp_apply, h1, map_smul, emb_ket, DgN, Finsupp.linearCombination_single,
      one_smul, Dg_ket]
  exact LinearMap.congr_fun this v

/-- Gauged unnormalised transfer on `𝓜_N` (`E^q` before the factor `N⁻¹`). -/
def TqN (N : ℕ) (q : Occ → ℂ) (a b : ℤ) : Module.End ℂ (Sector N) :=
  DgN N (fun m => (starRingEnd ℂ) (q m)) * TN N a b * DgN N q

theorem emb_TqN (N : ℕ) (q : Occ → ℂ) (a b : ℤ) (v : Sector N) :
    emb N (TqN N q a b v) = Tq q a b (emb N v) := by
  simp only [TqN, Tq, Module.End.mul_apply, emb_DgN, emb_TN]

/-- Normalised gauged transfer on `𝓜_N`: `E^q_{N,ab} = N⁻¹ Tq`. -/
def EqN (N : ℕ) (q : Occ → ℂ) (a b : ℤ) : Module.End ℂ (Sector N) := ((N : ℂ)⁻¹) • TqN N q a b

theorem emb_EqN (N : ℕ) (q : Occ → ℂ) (a b : ℤ) (v : Sector N) :
    emb N (EqN N q a b v) = EqOp q N a b (emb N v) := by
  simp only [EqN, EqOp, LinearMap.smul_apply, map_smul, emb_TqN]

theorem emb_EN (N : ℕ) (a b : ℤ) (v : Sector N) :
    emb N (EN N a b v) = EOp N a b (emb N v) := by
  simp only [EN, EOp, LinearMap.smul_apply, map_smul, emb_TN]

theorem TqN_comm {q : Occ → ℂ} (hq : UnitGauge q) (N : ℕ) (a b c d : ℤ) :
    TqN N q a b * TqN N q c d - TqN N q c d * TqN N q a b
      = (if a = d then (1 : ℂ) else 0) • TqN N q c b
        - (if b = c then (1 : ℂ) else 0) • TqN N q a d := by
  apply LinearMap.ext; intro v
  apply emb_injective N
  have := LinearMap.congr_fun (Tq_comm hq a b c d) (emb N v)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, map_sub, map_smul,
    emb_TqN] at this ⊢
  exact this

theorem TqN_minors {q : Occ → ℂ} (hq : UnitGauge q) (N : ℕ) (a b c d : ℤ) :
    TqN N q a b * TqN N q c d - TqN N q a d * TqN N q c b
      = (if a = d then (1 : ℂ) else 0) • TqN N q c b
        - (if a = b then (1 : ℂ) else 0) • TqN N q c d := by
  apply LinearMap.ext; intro v
  apply emb_injective N
  have := LinearMap.congr_fun (Tq_minors hq a b c d) (emb N v)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, map_sub, map_smul,
    emb_TqN] at this ⊢
  exact this

theorem TqN_adjoint (N : ℕ) (q : Occ → ℂ) (a b : ℤ) (u v : Sector N) :
    ipS N u (TqN N q a b v) = ipS N (TqN N q b a u) v := by
  unfold ipS
  rw [emb_TqN, emb_TqN]
  exact Tq_adjoint q a b _ _

/-- Normalised gauged sector CCR (`eq:full-CCR` for `E^q_{N,ab}` on `𝓜_N`). -/
theorem EqN_comm {q : Occ → ℂ} (hq : UnitGauge q) (N : ℕ) (a b c d : ℤ) :
    EqN N q a b * EqN N q c d - EqN N q c d * EqN N q a b
      = ((N : ℂ)⁻¹) • ((if a = d then (1 : ℂ) else 0) • EqN N q c b
          - (if b = c then (1 : ℂ) else 0) • EqN N q a d) := by
  apply LinearMap.ext; intro v
  have h := LinearMap.congr_fun (TqN_comm hq N a b c d) v
  simp only [EqN, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, map_smul,
    smul_sub, smul_smul] at h ⊢
  have e1 : ∀ δ : ℂ, (N : ℂ)⁻¹ * (N : ℂ)⁻¹ * δ = (N : ℂ)⁻¹ * (δ * (N : ℂ)⁻¹) := fun δ => by ring
  have h2 := congrArg (fun x : Sector N => ((N : ℂ)⁻¹ * (N : ℂ)⁻¹) • x) h
  simp only [smul_sub, smul_smul, e1] at h2
  exact h2

theorem EqN_adjoint (N : ℕ) (q : Occ → ℂ) (a b : ℤ) (u v : Sector N) :
    ipS N u (EqN N q a b v) = ipS N (EqN N q b a u) v := by
  unfold ipS
  rw [emb_EqN, emb_EqN]
  exact EqOp_adjoint q N a b _ _

/-- With the gauge acting, the diagonal transfer is still `B_a`: the phases cancel. -/
theorem Tq_diag {q : Occ → ℂ} (hq : UnitGauge q) (a : ℤ) : Tq q a a = Top a a := by
  apply ext_ket; intro m
  rw [Tq_ket, Top_ket]
  by_cases h : DonorOK a m
  · rw [shift_self h]
    have := unit_mul_conj hq m
    rw [this, one_mul]
  · have hm : m a = 0 := by unfold DonorOK at h; omega
    simp [w_empty hm]

theorem EqN_diag {q : Occ → ℂ} (hq : UnitGauge q) (N : ℕ) (a : ℤ) : EqN N q a a = EN N a a := by
  apply LinearMap.ext; intro v
  apply emb_injective N
  rw [emb_EqN, emb_EN]
  simp only [EqOp, EOp, LinearMap.smul_apply, Tq_diag hq]

lemma emb_support {N : ℕ} (v : Sector N) {m : Occ} (hm : m ∈ (emb N v).support) :
    ∃ m' ∈ v.support, m'.1 = m := by
  have : (emb N v).support ⊆ v.support.image Subtype.val := by
    simp only [emb, Finsupp.lmapDomain_apply]
    exact Finsupp.mapDomain_support
  simpa using this hm

/-- `∑_a B_{N,a} = Id` on the sector (`N > 0`), with the sum over any finite label set containing
all labels occurring in the support of `v` (the diagonal gauged transfer is the same). -/
theorem sum_diag_sector {N : ℕ} (hN : 0 < N) (v : Sector N) {S : Finset ℤ}
    (hS : ∀ m ∈ v.support, m.1.support ⊆ S) : ∑ a ∈ S, EN N a a v = v := by
  apply emb_injective N
  rw [map_sum]
  simp only [emb_EN]
  apply sum_diag_fs hN
  · intro m hm
    obtain ⟨m', _, rfl⟩ := emb_support v hm
    exact m'.2
  · intro m hm
    obtain ⟨m', hm', rfl⟩ := emb_support v hm
    exact hS m' hm'

theorem sum_diag_sector_gauged {q : Occ → ℂ} (hq : UnitGauge q) {N : ℕ} (hN : 0 < N)
    (v : Sector N) {S : Finset ℤ} (hS : ∀ m ∈ v.support, m.1.support ⊆ S) :
    ∑ a ∈ S, EqN N q a a v = v := by
  simp only [EqN_diag hq]
  exact sum_diag_sector hN v hS

/-! ### Finite-support norm bounds `‖E_{N,ab} v‖ ≤ ‖v‖` (`N > 0`)

`E_ba E_ab` is diagonal on the occupation basis with entries `coef²`, and `coef ≤ 1` on `𝓜_N`.
This is the finite-support form of the source bound "every transfer has norm at most one"
(`wick_calculus.tex`, around `eq:full-coefficient-bound`); extension to `ℓ²` by density is left to
`OccupationHilbert.lean`. -/

lemma coef_ne_zero_donor {N : ℕ} {a b : ℤ} {m : Occ} (h : coef N a b m ≠ 0) : DonorOK a m := by
  by_contra hd
  exact h (coef_empty_donor (by unfold DonorOK at hd; omega))

/-- `E_ab` followed by its reverse is the diagonal operator with entries `coef²`. -/
theorem coef_pair_sq (N : ℕ) (a b : ℤ) (m : Occ) :
    coef N a b m * coef N b a (shift a b m) = coef N a b m ^ 2 := by
  by_cases h0 : coef N a b m = 0
  · rw [h0]; ring
  · have hd := coef_ne_zero_donor h0
    by_cases hab : a = b
    · subst hab; rw [shift_self hd]; ring
    · rw [← coef_adjoint hab hd]; ring

theorem EOp_ba_ab_ket (N : ℕ) (a b : ℤ) (m : Occ) :
    (EOp N b a * EOp N a b) (ket m) = ((coef N a b m ^ 2 : ℝ) : ℂ) • ket m := by
  rw [Module.End.mul_apply, EOp_ket, map_smul, EOp_ket, smul_smul]
  by_cases h0 : coef N a b m = 0
  · simp [h0]
  · have hd := coef_ne_zero_donor h0
    rw [shift_shift_reverse hd]
    congr 1
    have := coef_pair_sq N a b m
    have h := congrArg (fun r : ℝ => (r : ℂ)) this
    push_cast at h ⊢
    exact h

lemma ip_sum_left {ι : Type*} (s : Finset ι) (f : ι → FS) (v : FS) :
    ip (∑ i ∈ s, f i) v = ∑ i ∈ s, ip (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ip_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ip_add_left, ih]

lemma fs_expand (v : FS) : v = ∑ m ∈ v.support, v m • ket m := by
  conv_lhs => rw [← Finsupp.sum_single v]
  unfold Finsupp.sum
  exact Finset.sum_congr rfl (fun m _ => single_eq_smul_ket m (v m))

lemma re_sum' {ι : Type*} (s : Finset ι) (f : ι → ℂ) : (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re :=
  map_sum Complex.reAddGroupHom f s

lemma ip_self_re (v : FS) : (ip v v).re = ∑ m ∈ v.support, Complex.normSq (v m) := by
  unfold ip Finsupp.sum
  rw [re_sum']
  apply Finset.sum_congr rfl
  intro m _
  show ((starRingEnd ℂ) (v m) * v m).re = _
  rw [← Complex.normSq_eq_conj_mul_self]; simp

/-- Real part of `⟨D v, v⟩` for the diagonal operator with real entries `c m`. -/
lemma ip_diag_re (c : Occ → ℝ) (D : Module.End ℂ FS)
    (hD : ∀ m, D (ket m) = ((c m : ℝ) : ℂ) • ket m) (v : FS) :
    (ip (D v) v).re = ∑ m ∈ v.support, c m * Complex.normSq (v m) := by
  have e : D v = ∑ m ∈ v.support, v m • D (ket m) := by
    conv_lhs => rw [fs_expand v]
    simp only [map_sum, map_smul]
  rw [e, ip_sum_left, re_sum']
  apply Finset.sum_congr rfl
  intro m _
  rw [hD, smul_smul, ip_smul_left, ip_ket_left]
  have : (starRingEnd ℂ) (v m * ((c m : ℝ) : ℂ)) * v m
      = ((c m * Complex.normSq (v m) : ℝ) : ℂ) := by
    push_cast; rw [Complex.normSq_eq_conj_mul_self]
    simp only [map_mul, Complex.conj_ofReal]; ring
  rw [this, Complex.ofReal_re]

/-- **Finite-support norm bound** (`‖E_{N,ab}‖ ≤ 1`, `N > 0`, source `eq:full-coefficient-bound`
at the level of a single transfer): for finitely supported `v` on arrays of total `N`,
`‖E_{N,ab} v‖² ≤ ‖v‖²`. -/
theorem EOp_norm_le {N : ℕ} (hN : 0 < N) (a b : ℤ) (v : FS) (hv : ∀ m ∈ v.support, IsArray N m) :
    (ip (EOp N a b v) (EOp N a b v)).re ≤ (ip v v).re := by
  have h1 : ip (EOp N a b v) (EOp N a b v) = ip ((EOp N b a * EOp N a b) v) v := by
    rw [Module.End.mul_apply]; exact EOp_adjoint N a b _ v
  rw [h1, ip_diag_re (fun m => coef N a b m ^ 2) _ (EOp_ba_ab_ket N a b) v, ip_self_re]
  apply Finset.sum_le_sum
  intro m hm
  have h0 := coef_nonneg N a b m
  have h1 := coef_le_one hN (hv m hm) a b
  have hn := Complex.normSq_nonneg (v m)
  have : coef N a b m ^ 2 ≤ 1 := by nlinarith
  nlinarith

/-- Sector version of the finite-support bound: `‖E_{N,ab} v‖² ≤ ‖v‖²` for `N > 0`. -/
theorem EN_norm_le {N : ℕ} (hN : 0 < N) (a b : ℤ) (v : Sector N) :
    (ipS N (EN N a b v) (EN N a b v)).re ≤ (ipS N v v).re := by
  unfold ipS
  rw [emb_EN]
  apply EOp_norm_le hN
  intro m hm
  obtain ⟨m', _, rfl⟩ := emb_support v hm
  exact m'.2

lemma UnitGauge.conj {q : Occ → ℂ} (hq : UnitGauge q) :
    UnitGauge (fun m => (starRingEnd ℂ) (q m)) := by
  intro m; simp [hq m]

/-- Unit-modulus gauge multiplication is isometric for the pairing. -/
theorem ip_Dg_self {q : Occ → ℂ} (hq : UnitGauge q) (w : FS) : ip (Dg q w) (Dg q w) = ip w w := by
  rw [Dg_adjoint q (Dg q w) w]
  have := LinearMap.congr_fun (Dg_conj_mul hq) w
  simp only [Module.End.mul_apply, Module.End.one_apply] at this
  rw [this]

theorem ipS_DgN_self {q : Occ → ℂ} (hq : UnitGauge q) (N : ℕ) (u : Sector N) :
    ipS N (DgN N q u) (DgN N q u) = ipS N u u := by
  unfold ipS; rw [emb_DgN]; exact ip_Dg_self hq _

/-- The gauged transfer is the ungauged one conjugated by the diagonal gauge. -/
theorem EqN_eq (N : ℕ) (q : Occ → ℂ) (a b : ℤ) (v : Sector N) :
    EqN N q a b v = DgN N (fun m => (starRingEnd ℂ) (q m)) (EN N a b (DgN N q v)) := by
  simp [EqN, EN, TqN, map_smul]

/-- `‖E^q_{N,ab} v‖² ≤ ‖v‖²` for every unit-modulus gauge, `N > 0`. -/
theorem EqN_norm_le {q : Occ → ℂ} (hq : UnitGauge q) {N : ℕ} (hN : 0 < N) (a b : ℤ)
    (v : Sector N) : (ipS N (EqN N q a b v) (EqN N q a b v)).re ≤ (ipS N v v).re := by
  rw [EqN_eq, ipS_DgN_self hq.conj]
  have := EN_norm_le hN a b (DgN N q v)
  rwa [ipS_DgN_self hq] at this

/-! ### Creation/annihilation operators on the finite-support Fock space

`Ann a = b_a`, `Cre a = b_a^*`; `Top a b = b_b^* b_a` (the identification used in
`prop:exact-occupation-algebra`), the canonical commutation relations `[b_a, b_b^*] = δ_ab`,
`[b_a,b_b] = 0 = [b_a^*,b_b^*]`, and adjointness `b_a^* = (b_a)^*`.  Algebraic finite-support
statements only (no domains/closures). -/

/-- Annihilation `b_a|m⟩ = √m_a |m - e_a⟩` on the finite-support Fock space (zero if `m_a = 0`). -/
def Ann (a : ℤ) : Module.End ℂ FS :=
  Finsupp.linearCombination ℂ (fun m : Occ => (Real.sqrt (m a) : ℂ) • ket (m - e a))

/-- Creation `b_a^*|m⟩ = √(m_a+1) |m + e_a⟩`. -/
def Cre (a : ℤ) : Module.End ℂ FS :=
  Finsupp.linearCombination ℂ (fun m : Occ => (Real.sqrt ((m a : ℝ) + 1) : ℂ) • ket (m + e a))

lemma Ann_ket (a : ℤ) (m : Occ) : Ann a (ket m) = (Real.sqrt (m a) : ℂ) • ket (m - e a) := by
  simp [Ann]

lemma Cre_ket (a : ℤ) (m : Occ) :
    Cre a (ket m) = (Real.sqrt ((m a : ℝ) + 1) : ℂ) • ket (m + e a) := by
  simp [Cre]

lemma w_eq_sqrt_prod (a b : ℤ) (m : Occ) :
    w a b m = Real.sqrt (m a) * Real.sqrt (((m - e a) b : ℕ) + 1) := by
  by_cases hab : a = b
  · subst hab
    simp only [w, ↓reduceIte]
    rcases zero_or_succ (m a) with h0 | ⟨k, hk⟩
    · simp [h0]
    · have : (m - e a) a = k := by simp [hk]
      rw [this, hk]
      push_cast
      rw [← Real.sqrt_mul (by positivity), Real.sqrt_mul_self (by positivity)]
  · simp only [w, hab, ↓reduceIte]
    have : (m - e a) b = m b := by simp [Ne.symm hab]
    rw [this, Real.sqrt_mul (by positivity)]

/-- The occupation transfer is `a_b^* a_a` (the identification used in
`prop:exact-occupation-algebra`, here proved on the finite-support Fock space). -/
theorem Top_eq_Cre_Ann (a b : ℤ) : Top a b = Cre b * Ann a := by
  apply ext_ket; intro m
  rw [Module.End.mul_apply, Ann_ket, map_smul, Cre_ket, smul_smul, Top_ket]
  unfold shift
  congr 1
  have := w_eq_sqrt_prod a b m
  have h := congrArg (fun r : ℝ => (r : ℂ)) this
  push_cast at h ⊢
  exact h

lemma add_sub_comm_occ {a b : ℤ} {m : Occ} (hab : a ≠ b) :
    (m + e b) - e a = (m - e a) + e b := by
  ext x
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  by_cases hxa : a = x <;> by_cases hxb : b = x
  · exact absurd (hxa.trans hxb.symm) hab
  all_goals simp [hxa, hxb]

/-- **Canonical commutation relations on the finite-support Fock space**:
`[b_a, b_b^*] = δ_{ab}`. -/
theorem Ann_Cre_comm (a b : ℤ) :
    Ann a * Cre b - Cre b * Ann a = (if a = b then (1 : ℂ) else 0) • (1 : Module.End ℂ FS) := by
  apply ext_ket; intro m
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Ann_ket, Cre_ket, map_smul, smul_smul,
    LinearMap.smul_apply, Module.End.one_apply]
  by_cases hab : a = b
  · subst hab
    simp only [↓reduceIte]
    rw [add_tsub_cancel_right]
    have h1 : (m + e a) a = m a + 1 := by simp
    rw [h1]
    rcases zero_or_succ (m a) with h0 | ⟨k, hk⟩
    · simp [h0]
    · have h2 : (m - e a) a = k := by simp [hk]
      have h3 : m - e a + e a = m := shift_sub_add (by unfold DonorOK; omega)
      rw [h2, h3, hk, ← sub_smul]
      congr 1
      push_cast
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity),
        Real.mul_self_sqrt (by positivity)]
      push_cast; ring
  · simp only [hab, ↓reduceIte]
    have h1 : (m + e b) a = m a := by simp [hab]
    have h2 : (m - e a) b = m b := by simp [Ne.symm hab]
    rw [h1, h2, add_sub_comm_occ hab, ← sub_smul]
    simp only [zero_smul]
    have : (↑√(↑(m b) + 1) * ↑√(↑(m a) : ℝ) : ℂ) - ↑√(↑(m a) : ℝ) * ↑√(↑(m b : ℝ) + 1) = 0 := by ring
    rw [this, zero_smul]

/-- Creation operators commute. -/
theorem Cre_Cre_comm (a b : ℤ) : Cre a * Cre b = Cre b * Cre a := by
  apply ext_ket; intro m
  simp only [Module.End.mul_apply, Cre_ket, map_smul, smul_smul]
  by_cases hab : a = b
  · subst hab; rfl
  · have h1 : (m + e b) a = m a := by simp [hab]
    have h2 : (m + e a) b = m b := by simp [Ne.symm hab]
    rw [h1, h2, add_right_comm m (e b) (e a)]
    congr 1; ring

/-- Annihilation operators commute. -/
theorem Ann_Ann_comm (a b : ℤ) : Ann a * Ann b = Ann b * Ann a := by
  apply ext_ket; intro m
  simp only [Module.End.mul_apply, Ann_ket, map_smul, smul_smul]
  by_cases hab : a = b
  · subst hab; rfl
  · have h1 : (m - e b) a = m a := by simp [hab]
    have h2 : (m - e a) b = m b := by simp [Ne.symm hab]
    rw [h1, h2, (tsub_right_comm (a := m) (b := e b) (c := e a)).symm]
    congr 1; ring

/-- Generic reduction of an adjointness identity to the occupation basis. -/
theorem adjoint_of_ket (A B : Module.End ℂ FS)
    (h : ∀ m n, ip (ket n) (A (ket m)) = ip (B (ket n)) (ket m)) (u v : FS) :
    ip u (A v) = ip (B u) v := by
  induction u using Finsupp.induction_linear with
  | zero => simp [ip_zero_left]
  | add u u' hu hu' => rw [map_add, ip_add_left, ip_add_left, hu, hu']
  | single n c =>
    rw [single_eq_smul_ket, map_smul, ip_smul_left, ip_smul_left]
    congr 1
    induction v using Finsupp.induction_linear with
    | zero => simp [ip_zero_right]
    | add v v' hv hv' => rw [map_add, ip_add_right, ip_add_right, hv, hv']
    | single m d =>
      rw [single_eq_smul_ket, map_smul, ip_smul_right, ip_smul_right, h]

lemma cre_ann_aux (a : ℤ) (m n : Occ) :
    (if m + e a = n then Real.sqrt ((m a : ℝ) + 1) else 0)
      = (if n - e a = m then Real.sqrt (n a) else 0) := by
  by_cases h1 : m + e a = n <;> by_cases h2 : n - e a = m
  · subst h1; simp
  · subst h1; exact absurd (add_tsub_cancel_right m (e a)) h2
  · subst h2
    have : n a = 0 := by
      by_contra hne
      apply h1
      exact (shift_sub_add (a := a) (m := n) (by unfold DonorOK; omega)).symm ▸ rfl
    simp [h1, this]
  · simp [h1, h2]

theorem Cre_adjoint (a : ℤ) (u v : FS) : ip u (Cre a v) = ip (Ann a u) v := by
  apply adjoint_of_ket
  intro m n
  have key := cre_ann_aux a m n
  have L : ip (ket n) (Cre a (ket m))
      = ((if m + e a = n then Real.sqrt ((m a : ℝ) + 1) else 0 : ℝ) : ℂ) := by
    rw [Cre_ket, ip_ket_left]
    by_cases h : m + e a = n <;> simp [h]
  have R : ip (Ann a (ket n)) (ket m)
      = ((if n - e a = m then Real.sqrt (n a) else 0 : ℝ) : ℂ) := by
    rw [Ann_ket, ip_smul_left, ip_ket_left, Complex.conj_ofReal]
    by_cases h : n - e a = m <;> simp [h]
  rw [L, R, key]

/-! ### Exact norm identities, sector tracking, and the monomial bound (`eq:full-Wick`)

`‖b_a v‖² = ∑ m_a|v_m|²`, `‖b_a^* v‖² = ∑ (m_a+1)|v_m|²`; on sector `k` these are `≤ k‖v‖²`,
`≤ (k+1)‖v‖²`.  Chaining `d` annihilations then `d` creations gives
`‖(b^*)^β b^α v‖² ≤ (N)_d (N)_d ‖v‖²` hence `‖N^{-d}(b^*)^β b^α‖ ≤ 1` (source
`wick_calculus.tex` before `eq:full-coefficient-bound`), with `(N)_d = fall N d` and no
truncated-commutator step.  The polynomial bound `‖W_N(f)‖ ≤ ‖f‖_coeff` is the triangle inequality
over the finitely many monomials and needs the normed carrier of `OccupationHilbert.lean`. -/

/-- `n_a = b_a^* b_a = Top a a` is the occupation number `m_a` on kets. -/
theorem Top_diag_ket (a : ℤ) (m : Occ) : Top a a (ket m) = ((m a : ℝ) : ℂ) • ket m := by
  rw [Top_ket]
  by_cases h : DonorOK a m
  · rw [shift_self h]; simp [w]
  · have hm : m a = 0 := by unfold DonorOK at h; omega
    simp [w_empty hm, hm]

/-- `b_a b_a^*|m⟩ = (m_a+1)|m⟩`. -/
theorem Ann_Cre_ket (a : ℤ) (m : Occ) :
    Ann a (Cre a (ket m)) = (((m a : ℝ) + 1 : ℝ) : ℂ) • ket m := by
  rw [Cre_ket, map_smul, Ann_ket, smul_smul, add_tsub_cancel_right]
  have h1 : (m + e a) a = m a + 1 := by simp
  rw [h1]
  congr 1
  push_cast
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  push_cast; ring

/-- **Exact norm identity** `‖b_a v‖² = ∑_m m_a |v_m|²` (`= ⟨v, n_a v⟩`). -/
theorem ip_Ann_self_re (a : ℤ) (v : FS) :
    (ip (Ann a v) (Ann a v)).re = ∑ m ∈ v.support, (m a : ℝ) * Complex.normSq (v m) := by
  have h1 : ip (Ann a v) (Ann a v) = ip (Top a a v) v := by
    rw [← Top_adjoint a a v v, Top_eq_Cre_Ann, Module.End.mul_apply, Cre_adjoint]
  rw [h1]
  exact ip_diag_re (fun m => (m a : ℝ)) (Top a a) (Top_diag_ket a) v

/-- **Exact norm identity** `‖b_a^* v‖² = ∑_m (m_a+1) |v_m|²`. -/
theorem ip_Cre_self_re (a : ℤ) (v : FS) :
    (ip (Cre a v) (Cre a v)).re = ∑ m ∈ v.support, ((m a : ℝ) + 1) * Complex.normSq (v m) := by
  have h1 : ip (Cre a v) (Cre a v) = ip ((Ann a * Cre a) v) v := by
    rw [Module.End.mul_apply]; exact Cre_adjoint a (Cre a v) v
  rw [h1]
  exact ip_diag_re (fun m => (m a : ℝ) + 1) (Ann a * Cre a)
    (fun m => by rw [Module.End.mul_apply]; exact Ann_Cre_ket a m) v

/-! ### Sector tracking -/

/-- `v` is supported on arrays of total `k`. -/
def InSector (k : ℕ) (v : FS) : Prop := ∀ m ∈ v.support, total m = k

lemma total_sub_e {a : ℤ} {m : Occ} (h : 1 ≤ m a) : total (m - e a) + 1 = total m := by
  have h2 := congrArg Finsupp.degree (shift_sub_add (a := a) (m := m) h)
  rw [map_add, Finsupp.degree_single] at h2
  unfold total; exact h2

lemma total_add_e (a : ℤ) (m : Occ) : total (m + e a) = total m + 1 := by
  unfold total; rw [map_add, Finsupp.degree_single]

lemma Ann_support {a : ℤ} (v : FS) {m' : Occ} (hm' : m' ∈ (Ann a v).support) :
    ∃ m ∈ v.support, 1 ≤ m a ∧ m' = m - e a := by
  have e1 : Ann a v = ∑ m ∈ v.support, (v m * (Real.sqrt (m a) : ℂ)) • ket (m - e a) := by
    conv_lhs => rw [fs_expand v]
    simp only [map_sum, map_smul, Ann_ket, smul_smul]
  rw [e1] at hm'
  obtain ⟨m, hm, hmem⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hm')
  have hne : (v m * (Real.sqrt (m a) : ℂ)) ≠ 0 := by
    intro h0; rw [h0, zero_smul] at hmem; simp at hmem
  have hsq : Real.sqrt (m a) ≠ 0 := by
    intro h0; apply hne; simp [h0]
  have hma : 1 ≤ m a := by
    by_contra h1
    have : m a = 0 := by omega
    apply hsq; simp [this]
  refine ⟨m, hm, hma, ?_⟩
  have := Finsupp.support_smul hmem
  simpa using this

lemma Cre_support {a : ℤ} (v : FS) {m' : Occ} (hm' : m' ∈ (Cre a v).support) :
    ∃ m ∈ v.support, m' = m + e a := by
  have e1 : Cre a v = ∑ m ∈ v.support, (v m * (Real.sqrt ((m a : ℝ) + 1) : ℂ)) • ket (m + e a) := by
    conv_lhs => rw [fs_expand v]
    simp only [map_sum, map_smul, Cre_ket, smul_smul]
  rw [e1] at hm'
  obtain ⟨m, hm, hmem⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hm')
  refine ⟨m, hm, ?_⟩
  have := Finsupp.support_smul hmem
  simpa using this

theorem Ann_inSector {a : ℤ} {k : ℕ} {v : FS} (hv : InSector k v) : InSector (k - 1) (Ann a v) := by
  intro m' hm'
  obtain ⟨m, hm, hma, rfl⟩ := Ann_support v hm'
  have := total_sub_e hma
  have := hv m hm
  omega

theorem Cre_inSector {a : ℤ} {k : ℕ} {v : FS} (hv : InSector k v) : InSector (k + 1) (Cre a v) := by
  intro m' hm'
  obtain ⟨m, hm, rfl⟩ := Cre_support v hm'
  rw [total_add_e, hv m hm]

/-- One annihilation: `‖b_a v‖² ≤ k ‖v‖²` on sector `k`. -/
theorem Ann_norm_le {a : ℤ} {k : ℕ} {v : FS} (hv : InSector k v) :
    (ip (Ann a v) (Ann a v)).re ≤ (k : ℝ) * (ip v v).re := by
  rw [ip_Ann_self_re, ip_self_re, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  have h1 : m a ≤ k := (hv m hm) ▸ occ_le_total a m
  have : (m a : ℝ) ≤ k := by exact_mod_cast h1
  have := Complex.normSq_nonneg (v m)
  nlinarith

/-- One creation: `‖b_a^* v‖² ≤ (k+1) ‖v‖²` on sector `k`. -/
theorem Cre_norm_le {a : ℤ} {k : ℕ} {v : FS} (hv : InSector k v) :
    (ip (Cre a v) (Cre a v)).re ≤ ((k : ℝ) + 1) * (ip v v).re := by
  rw [ip_Cre_self_re, ip_self_re, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  have h1 : m a ≤ k := (hv m hm) ▸ occ_le_total a m
  have : (m a : ℝ) ≤ k := by exact_mod_cast h1
  have := Complex.normSq_nonneg (v m)
  nlinarith

/-! ### Monomials `N^{-d} (b^*)^β b^α` and the bound `‖W_N(z^α z̄^β)‖ ≤ 1` -/

/-- Ordered product of annihilations `b_{a_1} b_{a_2} ⋯` (all orders agree by `Ann_Ann_comm`). -/
def AnnProd : List ℤ → Module.End ℂ FS
  | [] => 1
  | a :: l => Ann a * AnnProd l

/-- Ordered product of creations. -/
def CreProd : List ℤ → Module.End ℂ FS
  | [] => 1
  | a :: l => Cre a * CreProd l

/-- Descending factorial `k (k-1) ⋯ (k-n+1)` (zero when `n > k`): the source's `(N)_d`. -/
def fall (k n : ℕ) : ℕ := ∏ j ∈ Finset.range n, (k - j)

/-- Rising product `(s+1)(s+2) ⋯ (s+n)`. -/
def rise (s n : ℕ) : ℕ := ∏ j ∈ Finset.range n, (s + j + 1)

theorem AnnProd_bound (l : List ℤ) {k : ℕ} {v : FS} (hv : InSector k v) :
    InSector (k - l.length) (AnnProd l v) ∧
      (ip (AnnProd l v) (AnnProd l v)).re ≤ (fall k l.length : ℝ) * (ip v v).re := by
  induction l with
  | nil => simpa [AnnProd, fall] using hv
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := ih
    have hs := Ann_inSector (a := a) h1
    have hn := Ann_norm_le (a := a) h1
    refine ⟨?_, ?_⟩
    · have : k - l.length - 1 = k - (a :: l).length := by simp; omega
      rw [AnnProd, Module.End.mul_apply]; rwa [← this]
    · rw [AnnProd, Module.End.mul_apply]
      have hf : (fall k (a :: l).length : ℝ) = (fall k l.length : ℝ) * ((k - l.length : ℕ) : ℝ) := by
        simp only [List.length_cons, fall, Finset.prod_range_succ]; push_cast; ring
      rw [hf]
      have h0 : 0 ≤ ((k - l.length : ℕ) : ℝ) := Nat.cast_nonneg _
      calc _ ≤ ((k - l.length : ℕ) : ℝ) * (ip (AnnProd l v) (AnnProd l v)).re := hn
        _ ≤ ((k - l.length : ℕ) : ℝ) * ((fall k l.length : ℝ) * (ip v v).re) :=
            mul_le_mul_of_nonneg_left h2 h0
        _ = _ := by ring

theorem CreProd_bound (l : List ℤ) {s : ℕ} {v : FS} (hv : InSector s v) :
    InSector (s + l.length) (CreProd l v) ∧
      (ip (CreProd l v) (CreProd l v)).re ≤ (rise s l.length : ℝ) * (ip v v).re := by
  induction l with
  | nil => simpa [CreProd, rise] using hv
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := ih
    have hs := Cre_inSector (a := a) h1
    have hn := Cre_norm_le (a := a) h1
    refine ⟨?_, ?_⟩
    · have : s + l.length + 1 = s + (a :: l).length := by simp; omega
      rw [CreProd, Module.End.mul_apply]; rwa [← this]
    · rw [CreProd, Module.End.mul_apply]
      have hr : (rise s (a :: l).length : ℝ) = (rise s l.length : ℝ) * ((s + l.length : ℝ) + 1) := by
        simp only [List.length_cons, rise, Finset.prod_range_succ]; push_cast; ring
      rw [hr]
      have h0 : 0 ≤ ((s + l.length : ℕ) : ℝ) + 1 := by positivity
      calc _ ≤ (((s + l.length : ℕ) : ℝ) + 1) * (ip (CreProd l v) (CreProd l v)).re := hn
        _ ≤ (((s + l.length : ℕ) : ℝ) + 1) * ((rise s l.length : ℝ) * (ip v v).re) :=
            mul_le_mul_of_nonneg_left h2 h0
        _ = _ := by push_cast; ring

/-- `(N)_d ≤ N^d`, and `(N)_d = 0` for `d > N`. -/
lemma fall_le_pow (N d : ℕ) : fall N d ≤ N ^ d := by
  unfold fall
  calc ∏ j ∈ Finset.range d, (N - j) ≤ ∏ j ∈ Finset.range d, N :=
        Finset.prod_le_prod (fun j _ => Nat.sub_le N j)
    _ = N ^ d := by simp

lemma fall_eq_zero {N d : ℕ} (h : N < d) : fall N d = 0 :=
  Finset.prod_eq_zero (Finset.mem_range.mpr h) (Nat.sub_self N)

lemma rise_le_pow {N d : ℕ} (h : d ≤ N) : rise (N - d) d ≤ N ^ d := by
  unfold rise
  calc ∏ j ∈ Finset.range d, (N - d + j + 1) ≤ ∏ j ∈ Finset.range d, N :=
        Finset.prod_le_prod (fun j hj => by have := Finset.mem_range.mp hj; omega)
    _ = N ^ d := by simp

/-- **Monomial bound** (`eq:full-Wick`, `eq:full-coefficient-bound`; ungauged finite-support form):
for `N > 0`, `d` annihilations and `d` creations on a vector supported on arrays of total `N`,
`‖N^{-d} (b^*)^β b^α v‖ ≤ ‖v‖`. (The two index lists record `α`, `β` with `|α| = |β| = d`.) -/
theorem monomial_norm_le {N : ℕ} (hN : 0 < N) (l l' : List ℤ) (hlen : l'.length = l.length)
    {v : FS} (hv : InSector N v) :
    (ip (((N : ℂ)⁻¹ ^ l.length) • (CreProd l' (AnnProd l v)))
        (((N : ℂ)⁻¹ ^ l.length) • (CreProd l' (AnnProd l v)))).re ≤ (ip v v).re := by
  obtain ⟨hA1, hA2⟩ := AnnProd_bound l hv
  obtain ⟨_, hC2⟩ := CreProd_bound l' hA1
  rw [hlen] at hC2
  set d := l.length with hd
  have hr : ((N : ℂ)⁻¹ ^ d) = ((((N : ℝ)⁻¹ ^ d : ℝ)) : ℂ) := by push_cast; rfl
  rw [hr, ip_smul_left, ip_smul_right, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
    Complex.re_ofReal_mul]
  have hnn : 0 ≤ (ip v v).re := by rw [ip_self_re]; exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)
  have hprod : (rise (N - d) d : ℝ) * (fall N d : ℝ) ≤ ((N : ℝ) ^ d) * ((N : ℝ) ^ d) := by
    by_cases hdN : d ≤ N
    · have h1 : (rise (N - d) d : ℝ) ≤ (N : ℝ) ^ d := by exact_mod_cast rise_le_pow hdN
      have h2 : (fall N d : ℝ) ≤ (N : ℝ) ^ d := by exact_mod_cast fall_le_pow N d
      exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)
    · rw [fall_eq_zero (by omega)]; simp; positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hscale : (N : ℝ)⁻¹ ^ d * (N : ℝ)⁻¹ ^ d * ((N : ℝ) ^ d * (N : ℝ) ^ d) = 1 := by
    have h1 : (N : ℝ)⁻¹ ^ d * (N : ℝ) ^ d = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hNr.ne', one_pow]
    calc (N : ℝ)⁻¹ ^ d * (N : ℝ)⁻¹ ^ d * ((N : ℝ) ^ d * (N : ℝ) ^ d)
        = ((N : ℝ)⁻¹ ^ d * (N : ℝ) ^ d) * ((N : ℝ)⁻¹ ^ d * (N : ℝ) ^ d) := by ring
      _ = 1 := by rw [h1]; ring
  have hA : (ip (AnnProd l v) (AnnProd l v)).re ≤ (fall N d : ℝ) * (ip v v).re := by
    simpa using hA2
  have step : (ip (CreProd l' (AnnProd l v)) (CreProd l' (AnnProd l v))).re
      ≤ (rise (N - d) d : ℝ) * ((fall N d : ℝ) * (ip v v).re) :=
    hC2.trans (mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg _))
  have hc : 0 ≤ (N : ℝ)⁻¹ ^ d * (N : ℝ)⁻¹ ^ d := by positivity
  calc (N : ℝ)⁻¹ ^ d * (N : ℝ)⁻¹ ^ d * (ip (CreProd l' (AnnProd l v)) (CreProd l' (AnnProd l v))).re
      ≤ (N : ℝ)⁻¹ ^ d * (N : ℝ)⁻¹ ^ d * ((rise (N - d) d : ℝ) * ((fall N d : ℝ) * (ip v v).re)) :=
        mul_le_mul_of_nonneg_left step hc
    _ = (N : ℝ)⁻¹ ^ d * (N : ℝ)⁻¹ ^ d * ((rise (N - d) d : ℝ) * (fall N d : ℝ)) * (ip v v).re := by ring
    _ ≤ (N : ℝ)⁻¹ ^ d * (N : ℝ)⁻¹ ^ d * (((N : ℝ) ^ d) * ((N : ℝ) ^ d)) * (ip v v).re :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hc) hnn
    _ = (ip v v).re := by rw [hscale, one_mul]

lemma AnnProd_eq (l : List ℤ) : AnnProd l = (l.map Ann).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [AnnProd, ih]

lemma CreProd_eq (l : List ℤ) : CreProd l = (l.map Cre).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [CreProd, ih]

lemma pairwise_commute_of {f : ℤ → Module.End ℂ FS} (h : ∀ a b, f a * f b = f b * f a) (l : List ℤ) :
    l.Pairwise (fun a b => Commute (f a) (f b)) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a l ih => exact List.pairwise_cons.mpr ⟨fun b _ => h a b, ih⟩

/-- The product of annihilations does not depend on the order of the labels. -/
theorem AnnProd_perm {l l' : List ℤ} (h : l.Perm l') : AnnProd l = AnnProd l' := by
  rw [AnnProd_eq, AnnProd_eq]
  apply List.Perm.prod_eq' (h.map Ann)
  rw [List.pairwise_map]
  exact pairwise_commute_of (fun a b => Ann_Ann_comm a b) l

theorem CreProd_perm {l l' : List ℤ} (h : l.Perm l') : CreProd l = CreProd l' := by
  rw [CreProd_eq, CreProd_eq]
  apply List.Perm.prod_eq' (h.map Cre)
  rw [List.pairwise_map]
  exact pairwise_commute_of (fun a b => Cre_Cre_comm a b) l

/-- Label list of a multi-index `α` (each label `a` repeated `α a` times; any listing). -/
def labels (α : ℤ →₀ ℕ) : List ℤ := α.toMultiset.toList

lemma labels_length (α : ℤ →₀ ℕ) : (labels α).length = α.degree := by
  unfold labels
  rw [Multiset.length_toList, Finsupp.card_toMultiset]
  rfl

/-- `b^α = ∏_a b_a^{α_a}` -/
def AnnMono (α : ℤ →₀ ℕ) : Module.End ℂ FS := AnnProd (labels α)

/-- `(b^*)^β = ∏_a (b_a^*)^{β_a}` -/
def CreMono (β : ℤ →₀ ℕ) : Module.End ℂ FS := CreProd (labels β)

/-- The ungauged Wick monomial `N^{-d} (b^*)^β b^α` of `eq:full-Wick` on finitely supported
vectors (`d = |α| = |β|`). -/
def WMono (N : ℕ) (α β : ℤ →₀ ℕ) : Module.End ℂ FS :=
  ((N : ℂ)⁻¹ ^ α.degree) • (CreMono β * AnnMono α)

/-- **`eq:full-coefficient-bound` for a monomial** (finite-support form): on a vector supported on
arrays of total `N > 0`, `‖W_N(z^α z̄^β) v‖ ≤ ‖v‖` when `|α| = |β|`. -/
theorem WMono_norm_le {N : ℕ} (hN : 0 < N) {α β : ℤ →₀ ℕ} (hαβ : β.degree = α.degree) {v : FS}
    (hv : InSector N v) : (ip (WMono N α β v) (WMono N α β v)).re ≤ (ip v v).re := by
  have h := monomial_norm_le hN (labels α) (labels β)
    (by rw [labels_length, labels_length, hαβ]) hv
  rw [labels_length] at h
  simpa [WMono, CreMono, AnnMono, Module.End.mul_apply] using h

/-! ### Sector-typed creation and annihilation -/

lemma isArray_sub_e {N : ℕ} {a : ℤ} {m : Occ} (hm : IsArray (N + 1) m) (h : DonorOK a m) :
    IsArray N (m - e a) := by
  have := total_sub_e h
  unfold IsArray at *; omega

lemma isArray_add_e {N : ℕ} (a : ℤ) {m : Occ} (hm : IsArray N m) : IsArray (N + 1) (m + e a) := by
  unfold IsArray at *; rw [total_add_e, hm]

/-- Annihilation `Sector (N+1) → Sector N`, `|m⟩ ↦ √m_a |m − e_a⟩` (zero on an empty site). -/
def AnnN (N : ℕ) (a : ℤ) : Sector (N + 1) →ₗ[ℂ] Sector N :=
  Finsupp.linearCombination ℂ (fun m : Arr (N + 1) =>
    if h : DonorOK a m.1 then
      (Real.sqrt (m.1 a) : ℂ) • Finsupp.single (⟨m.1 - e a, isArray_sub_e m.2 h⟩ : Arr N) (1 : ℂ)
    else 0)

/-- Creation `Sector N → Sector (N+1)`, `|m⟩ ↦ √(m_a+1) |m + e_a⟩`. -/
def CreN (N : ℕ) (a : ℤ) : Sector N →ₗ[ℂ] Sector (N + 1) :=
  Finsupp.linearCombination ℂ (fun m : Arr N =>
    (Real.sqrt ((m.1 a : ℝ) + 1) : ℂ) •
      Finsupp.single (⟨m.1 + e a, isArray_add_e a m.2⟩ : Arr (N + 1)) (1 : ℂ))

theorem emb_AnnN (N : ℕ) (a : ℤ) (v : Sector (N + 1)) : emb N (AnnN N a v) = Ann a (emb (N + 1) v) := by
  have : (emb N).comp (AnnN N a) = (Ann a).comp (emb (N + 1)) := by
    apply Finsupp.lhom_ext
    intro m c
    have h1 : (Finsupp.single m c : Sector (N + 1)) = c • Finsupp.single m (1 : ℂ) := by simp
    simp only [LinearMap.comp_apply, h1, map_smul, emb_ket]
    congr 1
    simp only [AnnN, Finsupp.linearCombination_single, one_smul]
    by_cases h : DonorOK a m.1
    · simp only [h, ↓reduceDIte, map_smul, emb_ket, Ann_ket]
    · have hm : m.1 a = 0 := by unfold DonorOK at h; omega
      simp [h, Ann_ket, hm]
  exact LinearMap.congr_fun this v

theorem emb_CreN (N : ℕ) (a : ℤ) (v : Sector N) : emb (N + 1) (CreN N a v) = Cre a (emb N v) := by
  have : (emb (N + 1)).comp (CreN N a) = (Cre a).comp (emb N) := by
    apply Finsupp.lhom_ext
    intro m c
    have h1 : (Finsupp.single m c : Sector N) = c • Finsupp.single m (1 : ℂ) := by simp
    simp only [LinearMap.comp_apply, h1, map_smul, emb_ket]
    congr 1
    simp only [CreN, Finsupp.linearCombination_single, one_smul, map_smul, emb_ket, Cre_ket]
  exact LinearMap.congr_fun this v

/-- `‖b_a v‖² = ∑ m_a |v_m|²` on the sector (exact, no inequality). -/
theorem AnnN_norm_sq (N : ℕ) (a : ℤ) (v : Sector (N + 1)) :
    (ipS N (AnnN N a v) (AnnN N a v)).re
      = ∑ m ∈ (emb (N + 1) v).support, (m a : ℝ) * Complex.normSq (emb (N + 1) v m) := by
  unfold ipS; rw [emb_AnnN]; exact ip_Ann_self_re a _

theorem CreN_norm_sq (N : ℕ) (a : ℤ) (v : Sector N) :
    (ipS (N + 1) (CreN N a v) (CreN N a v)).re
      = ∑ m ∈ (emb N v).support, ((m a : ℝ) + 1) * Complex.normSq (emb N v m) := by
  unfold ipS; rw [emb_CreN]; exact ip_Cre_self_re a _

/-- Sector bounds `‖b_a v‖² ≤ (N+1)‖v‖²` and `‖b_a^* v‖² ≤ (N+1)‖v‖²`. -/
theorem AnnN_norm_le (N : ℕ) (a : ℤ) (v : Sector (N + 1)) :
    (ipS N (AnnN N a v) (AnnN N a v)).re ≤ ((N : ℝ) + 1) * (ipS (N + 1) v v).re := by
  unfold ipS; rw [emb_AnnN]
  have := Ann_norm_le (a := a) (k := N + 1) (v := emb (N + 1) v) (by
    intro m hm; obtain ⟨m', _, rfl⟩ := emb_support v hm; exact m'.2)
  simpa using this

theorem CreN_norm_le (N : ℕ) (a : ℤ) (v : Sector N) :
    (ipS (N + 1) (CreN N a v) (CreN N a v)).re ≤ ((N : ℝ) + 1) * (ipS N v v).re := by
  unfold ipS; rw [emb_CreN]
  exact Cre_norm_le (a := a) (k := N) (v := emb N v) (by
    intro m hm; obtain ⟨m', _, rfl⟩ := emb_support v hm; exact m'.2)

theorem CreN_adjoint (N : ℕ) (a : ℤ) (u : Sector (N + 1)) (v : Sector N) :
    ipS (N + 1) u (CreN N a v) = ipS N (AnnN N a u) v := by
  unfold ipS; rw [emb_CreN, emb_AnnN]; exact Cre_adjoint a _ _

/-- `N E_{N+1,ab}`-type factorisation: `a_b^* a_a` on the sector `𝓜_{N+1}` is `CreN ∘ AnnN`. -/
theorem TN_eq_CreN_AnnN (N : ℕ) (a b : ℤ) (v : Sector (N + 1)) :
    TN (N + 1) a b v = CreN N b (AnnN N a v) := by
  apply emb_injective (N + 1)
  rw [emb_TN, emb_CreN, emb_AnnN, Top_eq_Cre_Ann, Module.End.mul_apply]

/-! ### Normal ordering `eq:full-normal-order` (one label)

`b^p (b^*)^q = ∑_s C(p,s) C(q,s) s! (b^*)^{q-s} b^{p-s}`, proved abstractly from `A C = C A + 1`
(source proof: `p=1` then induction on `p` with Pascal's identity; no truncated creation
commutator) and instantiated on the finite-support Fock space.  Different labels commute
(`Ann_Cre_ne`, `Ann_Ann_comm`, `Cre_Cre_comm`), so the multi-label formula is the product. -/

lemma coef_pascal (p q s : ℕ) :
    p.choose (s + 1) * q.choose (s + 1) * (s + 1).factorial
      + p.choose s * q.choose s * s.factorial * (q - s)
      = (p + 1).choose (s + 1) * q.choose (s + 1) * (s + 1).factorial := by
  rw [Nat.choose_succ_succ, Nat.factorial_succ]
  have h := Nat.choose_succ_right_eq q s
  have h2 : p.choose s * q.choose s * s.factorial * (q - s)
      = p.choose s * q.choose (s + 1) * ((s + 1) * s.factorial) := by
    calc p.choose s * q.choose s * s.factorial * (q - s)
        = p.choose s * s.factorial * (q.choose s * (q - s)) := by ring
      _ = p.choose s * s.factorial * (q.choose (s + 1) * (s + 1)) := by rw [h]
      _ = _ := by ring
  rw [h2]; ring

section ring

variable {R : Type*} [Ring R] {A C : R}

/-- `A C^{q+1} = C^{q+1} A + (q+1) C^q` from `A C = C A + 1`. -/
lemma ann_cre_pow_succ (h : A * C = C * A + 1) (q : ℕ) :
    A * C ^ (q + 1) = C ^ (q + 1) * A + ((q + 1 : ℕ) : R) * C ^ q := by
  induction q with
  | zero => simpa using h
  | succ q ih =>
    have e : A * C ^ (q + 1 + 1) = (A * C) * C ^ (q + 1) := by rw [pow_succ' C (q + 1), mul_assoc]
    rw [e, h, add_mul, one_mul, mul_assoc, ih, mul_add]
    have hc : C * (((q + 1 : ℕ) : R) * C ^ q) = ((q + 1 : ℕ) : R) * C ^ (q + 1) := by
      rw [← mul_assoc, ← Nat.cast_comm, mul_assoc, ← pow_succ']
    rw [hc]
    have : C * (C ^ (q + 1) * A) = C ^ (q + 1 + 1) * A := by rw [← mul_assoc, ← pow_succ']
    rw [this]
    push_cast
    simp only [add_mul, one_mul, add_assoc]

/-- Truncated form: `A C^q = C^q A + q C^{q-1}`. -/
lemma ann_cre_pow (h : A * C = C * A + 1) (q : ℕ) :
    A * C ^ q = C ^ q * A + (q : R) * C ^ (q - 1) := by
  cases q with
  | zero => simp
  | succ q => simpa using ann_cre_pow_succ h q

/-- Normal-ordering coefficient `C(p,s) C(q,s) s!`. -/
def nocoef (p q s : ℕ) : ℕ := p.choose s * q.choose s * s.factorial

/-- **Single-oscillator normal ordering** (`eq:full-normal-order`):
`A^p C^q = ∑_{s ≤ p} C(p,s) C(q,s) s! C^{q-s} A^{p-s}` whenever `A C = C A + 1`
(terms with `s > q` vanish since `C(q,s) = 0`; this is the sum to `min(p,q)`). -/
theorem normal_order (h : A * C = C * A + 1) (p q : ℕ) :
    A ^ p * C ^ q = ∑ s ∈ Finset.range (p + 1),
      (nocoef p q s : R) * (C ^ (q - s) * A ^ (p - s)) := by
  induction p with
  | zero => simp [nocoef]
  | succ p ih =>
    have step : ∀ s ∈ Finset.range (p + 1), A * ((nocoef p q s : R) * (C ^ (q - s) * A ^ (p - s)))
        = (nocoef p q s : R) * (C ^ (q - s) * A ^ (p + 1 - s))
          + (nocoef p q s : R) * ((q - s : ℕ) : R) * (C ^ (q - (s + 1)) * A ^ (p - s)) := by
      intro s hs
      have hsp : s ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
      rw [← mul_assoc, ← Nat.cast_comm, mul_assoc, ← mul_assoc A, ann_cre_pow h (q - s), add_mul,
        mul_assoc, mul_assoc, mul_assoc]
      have : p + 1 - s = (p - s) + 1 := by omega
      rw [this, pow_succ' A (p - s), mul_add, Nat.sub_sub]
    -- the two sums
    have hpas : ∀ s, (nocoef (p + 1) q (s + 1) : R)
        = (nocoef p q (s + 1) : R) + (nocoef p q s : R) * ((q - s : ℕ) : R) := by
      intro s
      have : nocoef (p + 1) q (s + 1) = nocoef p q (s + 1) + nocoef p q s * (q - s) := by
        unfold nocoef; exact (coef_pascal p q s).symm
      rw [this, Nat.cast_add, Nat.cast_mul]
    calc A ^ (p + 1) * C ^ q = A * (A ^ p * C ^ q) := by rw [pow_succ', mul_assoc]
      _ = ∑ s ∈ Finset.range (p + 1), A * ((nocoef p q s : R) * (C ^ (q - s) * A ^ (p - s))) := by
          rw [ih, Finset.mul_sum]
      _ = ∑ s ∈ Finset.range (p + 1),
            ((nocoef p q s : R) * (C ^ (q - s) * A ^ (p + 1 - s))
              + (nocoef p q s : R) * ((q - s : ℕ) : R) * (C ^ (q - (s + 1)) * A ^ (p - s))) :=
          Finset.sum_congr rfl step
      _ = ∑ s ∈ Finset.range (p + 1), (nocoef p q s : R) * (C ^ (q - s) * A ^ (p + 1 - s))
            + ∑ s ∈ Finset.range (p + 1),
              (nocoef p q s : R) * ((q - s : ℕ) : R) * (C ^ (q - (s + 1)) * A ^ (p - s)) :=
          Finset.sum_add_distrib
      _ = _ := by
          rw [Finset.sum_range_succ' (fun s => (nocoef (p + 1) q s : R) * (C ^ (q - s) * A ^ (p + 1 - s))) (p + 1)]
          have hT : ∑ s ∈ Finset.range (p + 1),
              (nocoef (p + 1) q (s + 1) : R) * (C ^ (q - (s + 1)) * A ^ (p + 1 - (s + 1)))
              = ∑ s ∈ Finset.range (p + 1), (nocoef p q (s + 1) : R) * (C ^ (q - (s + 1)) * A ^ (p - s))
                + ∑ s ∈ Finset.range (p + 1),
                  (nocoef p q s : R) * ((q - s : ℕ) : R) * (C ^ (q - (s + 1)) * A ^ (p - s)) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro s _
            rw [hpas s, add_mul, Nat.add_sub_add_right]
          rw [hT]
          have h1 : ∑ s ∈ Finset.range (p + 1),
              (nocoef p q (s + 1) : R) * (C ^ (q - (s + 1)) * A ^ (p - s))
              = ∑ s ∈ Finset.range p, (nocoef p q (s + 1) : R) * (C ^ (q - (s + 1)) * A ^ (p - s)) := by
            rw [Finset.sum_range_succ]
            have : nocoef p q (p + 1) = 0 := by simp [nocoef]
            rw [this]; simp
          rw [h1]
          rw [Finset.sum_range_succ' (fun s => (nocoef p q s : R) * (C ^ (q - s) * A ^ (p + 1 - s))) p]
          have h2 : ∀ s ∈ Finset.range p, (nocoef p q (s + 1) : R) * (C ^ (q - (s + 1)) * A ^ (p + 1 - (s + 1)))
              = (nocoef p q (s + 1) : R) * (C ^ (q - (s + 1)) * A ^ (p - s)) := by
            intro s _; rw [Nat.add_sub_add_right]
          rw [Finset.sum_congr rfl h2]
          simp [nocoef]
          abel

end ring

/-- `b_a b_a^* = b_a^* b_a + 1` on the finite-support Fock space. -/
theorem Ann_Cre_same (a : ℤ) : Ann a * Cre a = Cre a * Ann a + 1 := by
  apply LinearMap.ext; intro v
  have := LinearMap.congr_fun (Ann_Cre_comm a a) v
  simp only [LinearMap.sub_apply, ↓reduceIte, one_smul,
    Module.End.one_apply] at this
  simp only [LinearMap.add_apply, Module.End.one_apply]
  exact sub_eq_iff_eq_add'.mp this

/-- Different labels commute: `b_a b_b^* = b_b^* b_a` for `a ≠ b`. -/
theorem Ann_Cre_ne (a b : ℤ) (hab : a ≠ b) : Ann a * Cre b = Cre b * Ann a := by
  apply LinearMap.ext; intro v
  have := LinearMap.congr_fun (Ann_Cre_comm a b) v
  simp only [LinearMap.sub_apply, hab, ↓reduceIte, zero_smul] at this
  exact sub_eq_zero.mp this

/-- `eq:full-normal-order` on the occupation Fock space (one label):
`b_a^p (b_a^*)^q = ∑_{s ≤ p} C(p,s) C(q,s) s! (b_a^*)^{q-s} b_a^{p-s}`. -/
theorem Ann_Cre_normal_order (a : ℤ) (p q : ℕ) :
    Ann a ^ p * Cre a ^ q = ∑ s ∈ Finset.range (p + 1),
      (nocoef p q s : Module.End ℂ FS) * (Cre a ^ (q - s) * Ann a ^ (p - s)) :=
  normal_order (R := Module.End ℂ FS) (A := Ann a) (C := Cre a) (Ann_Cre_same a) p q

/-! ### Multi-label normal ordering and the finite-`N` monomial Wick product

Source: proof of `thm:full-wick` (`wick_calculus.tex`): the one-oscillator formula
`eq:full-normal-order`, "different labels commute, so the product of these identities gives the
multiindex formula", and `eq:full-product`
`W_N(f)W_N(g) = ∑_γ N^{-|γ|}/γ! W_N((∂_z^γ f)(∂_{z̄}^γ g))` on monomials.
`multi_normal_order`: `b^α (b^*)^β = ∑_{γ ≤ α} C(α,γ)C(β,γ)γ! (b^*)^{β−γ} b^{α−γ}`;
`WMono_mul`: exact `N⁻¹` powers; `mcoef_mul_mfac`: `C(α,γ)C(β',γ)γ!·γ! = (α)_γ (β')_γ`, i.e. the
`1/γ!`-weighted derivative coefficient of the source (`∂_z^γ z^α = (α)_γ z^{α−γ}`). The symbol
(polynomial-function) side is not formalised here. -/

lemma AnnProd_append (l l' : List ℤ) : AnnProd (l ++ l') = AnnProd l * AnnProd l' := by
  induction l with
  | nil => simp [AnnProd]
  | cons a l ih => simp [AnnProd, ih, mul_assoc]

lemma CreProd_append (l l' : List ℤ) : CreProd (l ++ l') = CreProd l * CreProd l' := by
  induction l with
  | nil => simp [CreProd]
  | cons a l ih => simp [CreProd, ih, mul_assoc]

lemma labels_add_perm (α α' : ℤ →₀ ℕ) : (labels (α + α')).Perm (labels α ++ labels α') := by
  apply Multiset.coe_eq_coe.mp
  unfold labels
  rw [Multiset.coe_toList, ← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_toList,
    Finsupp.toMultiset_add]

lemma labels_single_perm (a : ℤ) (n : ℕ) : (labels (Finsupp.single a n)).Perm (List.replicate n a) := by
  apply Multiset.coe_eq_coe.mp
  unfold labels
  rw [Multiset.coe_toList, Finsupp.toMultiset_single, Multiset.coe_replicate, Multiset.nsmul_singleton]

lemma AnnProd_replicate (a : ℤ) (n : ℕ) : AnnProd (List.replicate n a) = Ann a ^ n := by
  induction n with
  | zero => simp [AnnProd]
  | succ n ih => rw [List.replicate_succ, AnnProd, ih, pow_succ']

lemma CreProd_replicate (a : ℤ) (n : ℕ) : CreProd (List.replicate n a) = Cre a ^ n := by
  induction n with
  | zero => simp [CreProd]
  | succ n ih => rw [List.replicate_succ, CreProd, ih, pow_succ']

theorem AnnMono_add (α α' : ℤ →₀ ℕ) : AnnMono (α + α') = AnnMono α * AnnMono α' := by
  unfold AnnMono
  rw [AnnProd_perm (labels_add_perm α α'), AnnProd_append]

theorem CreMono_add (β β' : ℤ →₀ ℕ) : CreMono (β + β') = CreMono β * CreMono β' := by
  unfold CreMono
  rw [CreProd_perm (labels_add_perm β β'), CreProd_append]

theorem AnnMono_single (a : ℤ) (n : ℕ) : AnnMono (Finsupp.single a n) = Ann a ^ n := by
  unfold AnnMono; rw [AnnProd_perm (labels_single_perm a n), AnnProd_replicate]

theorem CreMono_single (a : ℤ) (n : ℕ) : CreMono (Finsupp.single a n) = Cre a ^ n := by
  unfold CreMono; rw [CreProd_perm (labels_single_perm a n), CreProd_replicate]

theorem AnnMono_zero : AnnMono 0 = 1 := by
  unfold AnnMono labels; simp [AnnProd]

theorem CreMono_zero : CreMono 0 = 1 := by
  unfold CreMono labels; simp [CreProd]

lemma mem_labels {β : ℤ →₀ ℕ} {b : ℤ} (h : b ∈ labels β) : β b ≠ 0 := by
  unfold labels at h
  have := (Multiset.count_pos).mpr (Multiset.mem_toList.mp h)
  rw [Finsupp.count_toMultiset] at this
  omega

lemma Ann_comm_CreProd (a : ℤ) {l : List ℤ} (h : ∀ b ∈ l, b ≠ a) :
    Commute (Ann a) (CreProd l) := by
  induction l with
  | nil => simp [CreProd]
  | cons b l ih =>
    have hb : a ≠ b := fun e => h b (List.mem_cons_self) e.symm
    have h1 : Commute (Ann a) (Cre b) := Ann_Cre_ne a b hb
    have h2 := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    exact h1.mul_right h2

lemma Ann_pow_comm_CreMono (a : ℤ) {β : ℤ →₀ ℕ} (h : β a = 0) (n : ℕ) :
    Ann a ^ n * CreMono β = CreMono β * Ann a ^ n := by
  have : Commute (Ann a) (CreMono β) :=
    Ann_comm_CreProd a (fun b hb hba => mem_labels hb (hba ▸ h))
  exact (this.pow_left n).eq

/-- Single-label contraction against a multi-index of creations:
`b_a^n (b^*)^{β} = ∑_s C(n,s) C(β_a,s) s! (b^*)^{β − s e_a} b_a^{n−s}`. -/
theorem Ann_pow_CreMono (a : ℤ) (n : ℕ) (β : ℤ →₀ ℕ) :
    Ann a ^ n * CreMono β = ∑ s ∈ Finset.range (n + 1),
      (nocoef n (β a) s : Module.End ℂ FS) * (CreMono (β - Finsupp.single a s) * Ann a ^ (n - s)) := by
  set β'' : ℤ →₀ ℕ := Finsupp.erase a β with hβ''
  have hβa : β'' a = 0 := by simp [hβ'']
  have hsplit : β = Finsupp.single a (β a) + β'' := by
    ext b; by_cases hb : b = a
    · subst hb; simp [hβ'']
    · simp [hβ'', hb]
  have hcre : CreMono β = Cre a ^ (β a) * CreMono β'' := by
    conv_lhs => rw [hsplit]
    rw [CreMono_add, CreMono_single]
  rw [hcre, ← mul_assoc, Ann_Cre_normal_order, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  have hsub : β - Finsupp.single a s = Finsupp.single a (β a - s) + β'' := by
    ext b; by_cases hb : b = a
    · subst hb; simp [hβ'']
    · simp [hβ'', hb]
  rw [hsub, CreMono_add, CreMono_single]
  have hc := Ann_pow_comm_CreMono a hβa (n - s)
  simp only [mul_assoc]
  rw [hc]

/-! ### Multi-index combinatorial coefficients -/

/-- `∏_b C(α_b, γ_b)` (product over `supp γ`; zero iff some `γ_b > α_b`). -/
def mch (α γ : ℤ →₀ ℕ) : ℕ := γ.prod (fun b k => (α b).choose k)

/-- `γ! = ∏_b γ_b!`. -/
def mfac (γ : ℤ →₀ ℕ) : ℕ := γ.prod (fun _ k => k.factorial)

/-- `C(α,γ) C(β,γ) γ!` -/
def mcoef (α β γ : ℤ →₀ ℕ) : ℕ := mch α γ * mch β γ * mfac γ

lemma disjoint_single_support {γ : ℤ →₀ ℕ} {a : ℤ} (h : γ a = 0) (s : ℕ) :
    Disjoint γ.support (Finsupp.single a s).support :=
  Finset.disjoint_of_subset_right Finsupp.support_single_subset
    (Finset.disjoint_singleton_right.mpr (by simpa using h))

lemma mch_add_single (α : ℤ →₀ ℕ) {γ : ℤ →₀ ℕ} {a : ℤ} (h : γ a = 0) (s : ℕ) :
    mch α (γ + Finsupp.single a s) = mch α γ * (α a).choose s := by
  unfold mch
  rw [Finsupp.prod_add_index_of_disjoint (disjoint_single_support h s),
    Finsupp.prod_single_index (by simp)]

lemma mfac_add_single {γ : ℤ →₀ ℕ} {a : ℤ} (h : γ a = 0) (s : ℕ) :
    mfac (γ + Finsupp.single a s) = mfac γ * s.factorial := by
  unfold mfac
  rw [Finsupp.prod_add_index_of_disjoint (disjoint_single_support h s),
    Finsupp.prod_single_index (by simp)]

lemma mch_congr {α α' γ : ℤ →₀ ℕ} (h : ∀ b ∈ γ.support, α b = α' b) : mch α γ = mch α' γ := by
  unfold mch
  exact Finsupp.prod_congr (fun b hb => by rw [h b hb])

/-- Coefficient factorisation for peeling the label `a` off `α = n e_a + α₀`. -/
lemma mcoef_peel {a : ℤ} {n : ℕ} {α₀ : ℤ →₀ ℕ} (ha : α₀ a = 0) {γ₀ : ℤ →₀ ℕ} (hγ : γ₀ ≤ α₀)
    (β : ℤ →₀ ℕ) (s : ℕ) :
    mcoef (Finsupp.single a n + α₀) β (γ₀ + Finsupp.single a s)
      = mcoef α₀ β γ₀ * nocoef n (β a) s := by
  have hγa : γ₀ a = 0 := by have := hγ a; omega
  unfold mcoef nocoef
  rw [mch_add_single _ hγa, mch_add_single _ hγa, mfac_add_single hγa]
  have h1 : mch (Finsupp.single a n + α₀) γ₀ = mch α₀ γ₀ := by
    apply mch_congr
    intro b hb
    have hba : b ≠ a := fun e => by subst e; simp [hγa] at hb
    simp [Ne.symm hba]
  rw [h1]
  have h2 : (Finsupp.single a n + α₀) a = n := by simp [ha]
  rw [h2]
  ring

/-- Splitting the interval below `n e_a + α₀` along the label `a`. -/
lemma sum_Iic_single_add {M : Type*} [AddCommMonoid M] (a : ℤ) (n : ℕ) {α₀ : ℤ →₀ ℕ}
    (ha : α₀ a = 0) (F : (ℤ →₀ ℕ) → M) :
    ∑ γ ∈ Finset.Iic (Finsupp.single a n + α₀), F γ
      = ∑ γ₀ ∈ Finset.Iic α₀, ∑ s ∈ Finset.range (n + 1), F (γ₀ + Finsupp.single a s) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij' (fun x _ => x.1 + Finsupp.single a x.2) (fun γ _ => (Finsupp.erase a γ, γ a))
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_product, Finset.mem_Iic, Finset.mem_range] at hx
    rw [Finset.mem_Iic]
    intro b
    have h1 := hx.1 b
    by_cases hb : b = a
    · subst hb; simp [ha] at h1 ⊢; omega
    · simp [hb] at h1 ⊢; exact h1
  · intro γ hγ
    have hγ : γ ≤ Finsupp.single a n + α₀ := Finset.mem_Iic.mp hγ
    rw [Finset.mem_product, Finset.mem_Iic, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · intro b
      by_cases hb : b = a
      · subst hb; simp [ha]
      · have := hγ b; simp [hb] at this ⊢; exact this
    · have := hγ a; simp [ha] at this; omega
  · intro x hx
    rw [Finset.mem_product, Finset.mem_Iic, Finset.mem_range] at hx
    have hx1a : x.1 a = 0 := by have := hx.1 a; omega
    ext1
    · ext b; by_cases hb : b = a
      · subst hb; simp [hx1a]
      · simp [hb]
    · simp [hx1a]
  · intro γ _
    exact Finsupp.erase_add_single a γ
  · intro x _; rfl

/-- **Multi-label normal ordering** (monomial level, `eq:full-normal-order` multiindex product):
`b^α (b^*)^β = ∑_{γ ≤ α} C(α,γ) C(β,γ) γ! (b^*)^{β−γ} b^{α−γ}`
(terms with `γ ≰ β` vanish because `C(β,γ) = 0`). -/
theorem multi_normal_order (α β : ℤ →₀ ℕ) :
    AnnMono α * CreMono β = ∑ γ ∈ Finset.Iic α,
      (mcoef α β γ : Module.End ℂ FS) * (CreMono (β - γ) * AnnMono (α - γ)) := by
  revert β
  refine Finsupp.induction α ?_ ?_
  · intro β
    have hI : Finset.Iic (0 : ℤ →₀ ℕ) = {0} := by
      ext γ; simp [Finset.mem_Iic]
    rw [hI, Finset.sum_singleton]
    simp [AnnMono_zero, mcoef, mch, mfac]
  · intro a n α₀ ha hn ih β
    have ha0 : α₀ a = 0 := by simpa using ha
    rw [AnnMono_add, AnnMono_single, mul_assoc, ih β, Finset.mul_sum,
      sum_Iic_single_add a n ha0 (fun γ => (mcoef (Finsupp.single a n + α₀) β γ : Module.End ℂ FS)
        * (CreMono (β - γ) * AnnMono (Finsupp.single a n + α₀ - γ)))]
    apply Finset.sum_congr rfl
    intro γ₀ hγ₀
    have hγ : γ₀ ≤ α₀ := Finset.mem_Iic.mp hγ₀
    have hγa : γ₀ a = 0 := by have := hγ a; omega
    rw [← mul_assoc, ← Nat.cast_comm, mul_assoc, ← mul_assoc (Ann a ^ n), Ann_pow_CreMono a n (β - γ₀),
      Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    have hsn : s ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    have hβ : (β - γ₀) a = β a := by simp [hγa]
    have hcoef := mcoef_peel (n := n) ha0 hγ β s
    have hC : β - γ₀ - Finsupp.single a s = β - (γ₀ + Finsupp.single a s) := tsub_tsub _ _ _
    have hA : Finsupp.single a (n - s) + (α₀ - γ₀)
        = Finsupp.single a n + α₀ - (γ₀ + Finsupp.single a s) := by
      ext b; by_cases hb : b = a
      · subst hb; simp [hγa, ha0]
      · simp [hb]
    have hAm : Ann a ^ (n - s) * AnnMono (α₀ - γ₀)
        = AnnMono (Finsupp.single a n + α₀ - (γ₀ + Finsupp.single a s)) := by
      rw [← hA, AnnMono_add, AnnMono_single]
    rw [hβ, hC, hcoef, Nat.cast_mul]
    simp only [mul_assoc]
    rw [hAm]

/-- Operator product of two ordered monomials, before the `N`-scaling. -/
theorem mono_mul (α β α' β' : ℤ →₀ ℕ) :
    (CreMono β * AnnMono α) * (CreMono β' * AnnMono α') = ∑ γ ∈ Finset.Iic α,
      (mcoef α β' γ : Module.End ℂ FS) * (CreMono (β + (β' - γ)) * AnnMono (α - γ + α')) := by
  have e : CreMono β * AnnMono α * (CreMono β' * AnnMono α')
      = CreMono β * (AnnMono α * CreMono β') * AnnMono α' := by simp only [mul_assoc]
  rw [e, multi_normal_order α β', Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro γ _
  have hc := Nat.cast_comm (mcoef α β' γ) (CreMono β)
  rw [← mul_assoc, hc.symm, mul_assoc]
  rw [CreMono_add, AnnMono_add]
  simp only [mul_assoc]

lemma degree_tsub_add {α γ : ℤ →₀ ℕ} (h : γ ≤ α) : (α - γ).degree + γ.degree = α.degree := by
  rw [← map_add, tsub_add_cancel_of_le h]

/-- **Finite-`N` Wick product at monomial level** (`eq:full-product` for monomials, exact `N`
powers):
`W_N(z^α z̄^β) W_N(z^{α'} z̄^{β'}) = ∑_{γ ≤ α} N^{-|γ|} C(α,γ) C(β',γ) γ!
    W_N(z^{α−γ+α'} z̄^{β+β'−γ})`,
with `W_N(z^α z̄^β) = N^{-|α|} (b^*)^β b^α` (`WMono`). -/
theorem WMono_mul (N : ℕ) (α β α' β' : ℤ →₀ ℕ) :
    WMono N α β * WMono N α' β' = ∑ γ ∈ Finset.Iic α,
      ((N : ℂ)⁻¹ ^ γ.degree * (mcoef α β' γ : ℂ)) • WMono N (α - γ + α') (β + (β' - γ)) := by
  unfold WMono
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, mono_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  have hγ' : γ ≤ α := Finset.mem_Iic.mp hγ
  have hd := degree_tsub_add hγ'
  have hsc : ((N : ℂ)⁻¹ ^ α.degree * (N : ℂ)⁻¹ ^ α'.degree)
      = (N : ℂ)⁻¹ ^ γ.degree * (N : ℂ)⁻¹ ^ (α - γ + α').degree := by
    rw [map_add, ← hd, pow_add, pow_add]; ring
  have hmul : ∀ X : Module.End ℂ FS, (mcoef α β' γ : Module.End ℂ FS) * X = (mcoef α β' γ : ℂ) • X := by
    intro X; rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℂ]
  rw [hmul, smul_smul, smul_smul, hsc]
  congr 1
  ring

/-- Source form of the combinatorial factor: `C(α,γ) C(β',γ) γ!` times `γ!` is
`(α)_γ (β')_γ` with falling factorials `(α)_γ = ∏_b α_b!/(α_b−γ_b)!`, i.e. the coefficient
`N^{-|γ|}/γ! · ∂_z^γ ∂_{z̄}^γ` of `eq:full-product` on monomials. -/
def mdesc (α γ : ℤ →₀ ℕ) : ℕ := γ.prod (fun b k => (α b).descFactorial k)

theorem mcoef_mul_mfac (α β' γ : ℤ →₀ ℕ) :
    mcoef α β' γ * mfac γ = mdesc α γ * mdesc β' γ := by
  unfold mcoef mdesc mch mfac
  have h : ∀ α₁ : ℤ →₀ ℕ, γ.prod (fun b k => (α₁ b).choose k) * γ.prod (fun _ k => k.factorial)
      = γ.prod (fun b k => (α₁ b).descFactorial k) := by
    intro α₁
    rw [← Finsupp.prod_mul]
    apply Finsupp.prod_congr
    intro b _
    rw [Nat.descFactorial_eq_factorial_mul_choose]; ring
  calc γ.prod (fun b k => (α b).choose k) * γ.prod (fun b k => (β' b).choose k)
        * γ.prod (fun _ k => k.factorial) * γ.prod (fun _ k => k.factorial)
      = (γ.prod (fun b k => (α b).choose k) * γ.prod (fun _ k => k.factorial))
        * (γ.prod (fun b k => (β' b).choose k) * γ.prod (fun _ k => k.factorial)) := by ring
    _ = _ := by rw [h α, h β']

/-! Axiom audit (printed at compile time). -/
#print axioms total_shift
#print axioms isArray_shift
#print axioms shift_shift_reverse
#print axioms shift_injOn
#print axioms occupation_fraction_shift
#print axioms coef_adjoint
#print axioms coef_roundtrip
#print axioms coef_commutator_pair
#print axioms shift_comm_of_ne_donor
#print axioms donorOK_shift_of_ne
#print axioms w_commutator
#print axioms coef_commutator
#print axioms shift_shift_ad
#print axioms shift_shift_bc
#print axioms shift_shift_comm
#print axioms Top_comm
#print axioms EOp_comm
#print axioms Top_minors
#print axioms Top_adjoint
#print axioms EOp_adjoint
#print axioms Top_eq_N_smul_EOp
#print axioms emb_TN
#print axioms TN_comm
#print axioms TN_minors
#print axioms TN_adjoint
#print axioms ipS_eq
#print axioms EN_comm
#print axioms EN_adjoint
#print axioms w_minors
#print axioms Dg_conj_mul
#print axioms Dg_mul_conj
#print axioms Tq_ket
#print axioms EqOp_ket
#print axioms Tq_comm
#print axioms Tq_minors
#print axioms Dg_adjoint
#print axioms Tq_adjoint
#print axioms EqOp_comm
#print axioms EqOp_adjoint
#print axioms coef_nonneg
#print axioms coef_le_one
#print axioms occ_add_le_total
#print axioms EOp_diag_ket
#print axioms sum_diag_coef_le_one
#print axioms sum_diag_ket
#print axioms sum_diag_fs
#print axioms emb_DgN
#print axioms emb_TqN
#print axioms emb_EqN
#print axioms emb_EN
#print axioms TqN_comm
#print axioms TqN_minors
#print axioms TqN_adjoint
#print axioms EqN_comm
#print axioms EqN_adjoint
#print axioms Tq_diag
#print axioms EqN_diag
#print axioms sum_diag_sector
#print axioms sum_diag_sector_gauged
#print axioms coef_pair_sq
#print axioms EOp_ba_ab_ket
#print axioms ip_self_re
#print axioms ip_diag_re
#print axioms EOp_norm_le
#print axioms EN_norm_le
#print axioms ip_Dg_self
#print axioms ipS_DgN_self
#print axioms EqN_eq
#print axioms EqN_norm_le
#print axioms w_eq_sqrt_prod
#print axioms Top_eq_Cre_Ann
#print axioms Ann_Cre_comm
#print axioms Cre_Cre_comm
#print axioms Ann_Ann_comm
#print axioms adjoint_of_ket
#print axioms Cre_adjoint
#print axioms Top_diag_ket
#print axioms Ann_Cre_ket
#print axioms ip_Ann_self_re
#print axioms ip_Cre_self_re
#print axioms Ann_support
#print axioms Cre_support
#print axioms Ann_inSector
#print axioms Cre_inSector
#print axioms Ann_norm_le
#print axioms Cre_norm_le
#print axioms AnnProd_bound
#print axioms CreProd_bound
#print axioms monomial_norm_le
#print axioms AnnProd_perm
#print axioms CreProd_perm
#print axioms labels_length
#print axioms WMono_norm_le
#print axioms emb_AnnN
#print axioms emb_CreN
#print axioms AnnN_norm_sq
#print axioms CreN_norm_sq
#print axioms AnnN_norm_le
#print axioms CreN_norm_le
#print axioms CreN_adjoint
#print axioms TN_eq_CreN_AnnN
#print axioms coef_pascal
#print axioms ann_cre_pow_succ
#print axioms ann_cre_pow
#print axioms normal_order
#print axioms Ann_Cre_same
#print axioms Ann_Cre_ne
#print axioms Ann_Cre_normal_order
#print axioms AnnProd_append
#print axioms labels_add_perm
#print axioms labels_single_perm
#print axioms AnnMono_add
#print axioms CreMono_add
#print axioms AnnMono_single
#print axioms CreMono_single
#print axioms Ann_pow_comm_CreMono
#print axioms Ann_pow_CreMono
#print axioms mch_add_single
#print axioms mcoef_peel
#print axioms sum_Iic_single_add
#print axioms multi_normal_order
#print axioms mono_mul
#print axioms degree_tsub_add
#print axioms WMono_mul
#print axioms mcoef_mul_mfac

end

end QuantumNLS.Occupation
