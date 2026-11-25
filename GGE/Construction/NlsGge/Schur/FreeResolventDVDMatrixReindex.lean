import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

set_option autoImplicit false
open scoped ENNReal BigOperators

namespace NlsGge.Schur

private def dvdPairReindexEquiv {α β : Type*} :
    ((Bool × α) × (Bool × β)) ≃ ((Bool × Bool) × (β × α)) where
  toFun p := ((p.1.1, p.2.1), (p.2.2, p.1.2))
  invFun q := ((q.1.1, q.2.2), (q.1.2, q.2.1))
  left_inv p := by rcases p with ⟨⟨bi, a⟩, ⟨bo, b⟩⟩; rfl
  right_inv q := by rcases q with ⟨⟨bi, bo⟩, ⟨b, a⟩⟩; rfl

/-- Reindex the actual input/output paired parity matrix by its two parity
labels and the reversed Fourier coordinates, then discard the two zero
same-parity blocks. This isolates only ENNReal product summation and the
finite Bool cases; the entries themselves remain arbitrary. -/
theorem ENNReal_tsum_dvd_pair_reindex_offdiag
    {α β : Type*} (f : Bool × Bool → β × α → ℝ≥0∞)
    (hTT : ∀ q, f (true, true) q = 0)
    (hFF : ∀ q, f (false, false) q = 0) :
    (∑' input : Bool × α, ∑' output : Bool × β,
      f (input.1, output.1) (output.2, input.2)) =
      (∑' q : β × α, f (true, false) q) +
        (∑' q : β × α, f (false, true) q) := by
  let e := dvdPairReindexEquiv (α := α) (β := β)
  calc
    (∑' input : Bool × α, ∑' output : Bool × β,
      f (input.1, output.1) (output.2, input.2)) =
      ∑' p : (Bool × α) × (Bool × β),
        f (p.1.1, p.2.1) (p.2.2, p.1.2) := by
      exact (ENNReal.tsum_prod
        (f := fun input : Bool × α => fun output : Bool × β =>
          f (input.1, output.1) (output.2, input.2))).symm
    _ = ∑' q : (Bool × Bool) × (β × α), f q.1 q.2 := by
      exact e.tsum_eq (fun q => f q.1 q.2)
    _ = ∑' bc : Bool × Bool, ∑' q : β × α, f bc q := by
      exact ENNReal.tsum_prod
    _ = _ := by
      simp [tsum_fintype, Fintype.sum_prod_type, hTT, hFF, add_comm]

end NlsGge.Schur
