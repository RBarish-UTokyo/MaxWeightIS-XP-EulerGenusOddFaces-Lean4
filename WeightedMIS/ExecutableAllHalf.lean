module

public import WeightedMIS.ExecutableComponent
public import WeightedMIS.ComputedComponentRibbon

/-!
# Executable assembly of all all-half components

The least reached numeric vertex determines each component. Its actual finite
indexed ribbon is solved in the representative branch, and the resulting sets
are combined using the representative partition. Empty fibers contribute
empty sets. All selected vertices are computed from the input graph.
-/

@[expose] public section

namespace WeightedMIS.ExecutableReduction

open EmbeddingFaces ComputedComponents Persistence

variable {n m : ℕ} {left right : Fin m → Fin n}

/-- The actual numeric component solution transported into its representative
fiber; nonrepresentative indices have empty fibers. -/
def fiberSolve (R : Ribbon left right) (weights : Fin n → ℚ) (root : Fin n) :
    Finset {v : Fin n // representative left right v = root} :=
  if hfix : representative left right root = root then
    GraphRelabeling.mapSet (representativeFiberEquiv left right root hfix)
      (connectedSolve (componentRibbon left right root R)
        (fun v => weights (vertexEquiv left right root v).val))
  else ∅

/-- Each computed fiber set is a maximum in its actual original adjacency. -/
theorem fiberSolve_correct (R : Ribbon left right) (weights : Fin n → ℚ)
    (hw : ∀ v, 0 ≤ weights v)
    (ho : Optimal (EdgeTransport.Adj left right) weights (fun _ => 1 / 2)) (root : Fin n) :
    Independent (fun u v : {v : Fin n // representative left right v = root} =>
      EdgeTransport.Adj left right u.val v.val) (fiberSolve R weights root) ∧
      ∀ J, Independent (fun u v : {v : Fin n // representative left right v = root} =>
          EdgeTransport.Adj left right u.val v.val) J →
        weight (fun v : {v : Fin n // representative left right v = root} => weights v.val) J ≤
          weight (fun v : {v : Fin n // representative left right v = root} => weights v.val)
            (fiberSolve R weights root) := by
  unfold fiberSolve
  split_ifs with hfix
  · have hlocal := connectedSolve_correct (componentRibbon left right root R)
      (fun v => weights (vertexEquiv left right root v).val)
      (local_connected left right root) (fun v => hw _) (local_half_optimal left right root weights ho)
    exact GraphRelabeling.maximum_map (representativeFiberEquiv left right root hfix)
      (EdgeTransport.Adj (localLeft left right root) (localRight left right root))
      (fun u v : {v : Fin n // representative left right v = root} =>
        EdgeTransport.Adj left right u.val v.val)
      (representativeFiber_adj left right root hfix)
      (fun v : {v : Fin n // representative left right v = root} => weights v.val)
      _ hlocal.1 hlocal.2
  · have hempty : IsEmpty {v : Fin n // representative left right v = root} := by
      refine ⟨fun v => hfix ?_⟩
      rw [← v.property, representative_idempotent]
    constructor
    · intro u; exact isEmptyElim u
    · intro J _
      have hj : J = ∅ := by ext v; exact isEmptyElim v
      rw [hj]

/-- Solve and assemble the actual components of an all-half instance. -/
def allHalfSolve (R : Ribbon left right) (weights : Fin n → ℚ) : Finset (Fin n) :=
  ComponentAssembly.assemble (representative left right) (fiberSolve R weights)

/-- The complete computed all-half output is maximum, including disconnected
inputs, isolated vertices, loops, and the empty graph. -/
theorem allHalfSolve_correct (R : Ribbon left right) (weights : Fin n → ℚ)
    (hw : ∀ v, 0 ≤ weights v)
    (ho : Optimal (EdgeTransport.Adj left right) weights (fun _ => 1 / 2)) :
    Independent (EdgeTransport.Adj left right) (allHalfSolve R weights) ∧
      ∀ J, Independent (EdgeTransport.Adj left right) J →
        weight weights J ≤ weight weights (allHalfSolve R weights) := by
  have hclosed : ∀ u v, EdgeTransport.Adj left right u v →
      representative left right u = representative left right v := by
    intro u v huv
    apply representative_eq_of_reachable left right
    exact (Incidence.componentOf_eq_iff left right u v).mp
      (ComponentAssembly.component_closed left right u v huv)
  exact ComponentAssembly.assemble_maximum (EdgeTransport.Adj left right)
    (representative left right) hclosed weights (fiberSolve R weights)
    (fun root => (fiberSolve_correct R weights hw ho root).1)
    (fun root => (fiberSolve_correct R weights hw ho root).2)

end WeightedMIS.ExecutableReduction
