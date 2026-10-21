module

public import WeightedMIS.ExecutableAllHalf
public import WeightedMIS.ComputedInduced

/-!
# The actual deterministic weighted independent-set output

The function truncates negative weights, computes the half-integral LP point
by integral maximum flow, constructs the explicitly indexed residual ribbon,
solves its actual components, restores the fixed vertices, and prunes the
originally negative weights. All optimization and recovery data are computed.
The correctness theorem contains no supplied optimizer, matrix, or minimum path.
-/

@[expose] public section

namespace WeightedMIS.ExecutableMIS

open EmbeddingFaces Persistence

variable {n m : ℕ} {left right : Fin m → Fin n}

/-- A total, executable weighted independent-set solver on a finite indexed
ribbon graph, including disconnected inputs, loops, and isolated vertices. -/
def solve (R : Ribbon left right) (weights : Fin n → ℚ) : Finset (Fin n) :=
  let z := OriginalReduction.preprocessingPoint (left := left) (right := right) weights (List.finRange n)
  let keep := fun v => z v = 1 / 2
  let e := ComputedInduced.vertexEquiv keep
  let H := ComputedInduced.ribbon left right keep R
  let w := fun v => NegativeWeights.nonnegative weights (e v).val
  let J := ExecutableReduction.allHalfSolve H w
  let lifted := InducedReduction.lift (GraphRelabeling.mapSet e J)
  NegativeWeights.prune weights (replacement z lifted)

/-- The returned finite set is independent and maximizes the original rational
vertex weights. The proof certifies the actual output of `solve`. -/
theorem solve_correct (R : Ribbon left right) (weights : Fin n → ℚ) :
    Independent (EdgeTransport.Adj left right) (solve R weights) ∧
      ∀ J, Independent (EdgeTransport.Adj left right) J →
        weight weights J ≤ weight weights (solve R weights) := by
  let z := OriginalReduction.preprocessingPoint (left := left) (right := right) weights (List.finRange n)
  let keep := fun v => z v = 1 / 2
  let e := ComputedInduced.vertexEquiv keep
  let H := ComputedInduced.ribbon left right keep R
  let w := fun v => NegativeWeights.nonnegative weights (e v).val
  let J := ExecutableReduction.allHalfSolve H w
  have hz := OriginalReduction.preprocessingPoint_correct (left := left) (right := right)
    weights (List.finRange n) (fun v => List.mem_finRange v)
  have hr := InducedReduction.residual_optimal (EdgeTransport.Adj left right)
    (NegativeWeights.nonnegative weights) z hz.2 hz.1
  have hopt := ComputedInduced.half_optimal left right keep (NegativeWeights.nonnegative weights) hr
  have hJ := ExecutableReduction.allHalfSolve_correct H w
    (fun v => NegativeWeights.nonnegative_nonnegative weights _) hopt
  have hmap := GraphRelabeling.maximum_map e
    (EdgeTransport.Adj (ComputedInduced.localLeft left right keep) (ComputedInduced.localRight left right keep))
    (fun u v : {v : Fin n // keep v} => EdgeTransport.Adj left right u.val v.val)
    (ComputedInduced.local_adj left right keep)
    (fun v : {v : Fin n // keep v} => NegativeWeights.nonnegative weights v.val) J hJ.1 hJ.2
  have h := InducedReduction.residual_maximum (EdgeTransport.Adj left right)
    (NegativeWeights.nonnegative weights) z hz.2 hz.1 (GraphRelabeling.mapSet e J) hmap.1 hmap.2
  exact NegativeWeights.optimum_of_truncated (EdgeTransport.Adj left right) weights _ h.1 h.2.2

end WeightedMIS.ExecutableMIS
