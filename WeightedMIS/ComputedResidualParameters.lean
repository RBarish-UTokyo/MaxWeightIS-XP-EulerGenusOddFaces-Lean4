module

public import WeightedMIS.ComputedResidualGeometry
public import WeightedMIS.ComputedGeometryTransfer
public import WeightedMIS.IndexedActiveVertices
public import WeightedMIS.ExecutableMIS

/-!
# Original surface bounds for the matrices actually used by the solver

For every component of every computed induced graph, the actual complement
list is bounded by the original surface parameters. Both its geometric edge
restriction and its active-vertex correspondence are constructed from the
computed indices. Specializing the retained vertices to the actual maximum
flow preprocessing point gives the component matrices used by `solve`.
-/

@[expose] public section

namespace WeightedMIS.ComputedInduced

open EmbeddingFaces Incidence

variable {n m : ℕ} {left right : Fin m → Fin n}
    {F : Type*} [Fintype F] [DecidableEq F]
    (M : CellularEmbedding left right F)
    (keep : Fin n → Prop) [DecidablePred keep]
    (root : Fin (vertices keep).length)

/-- Actual residual-component complement rows satisfy the original surface
dimension bound, including the sharper orientable exponent. -/
theorem component_globalRows_bound (hcM : Connected left right)
    (hnb : ¬ Bipartite
      (ComputedComponents.localLeft (localLeft left right keep) (localRight left right keep) root)
      (ComputedComponents.localRight (localLeft left right keep) (localRight left right keep) root)) :
    (ComputedEmbeddedMatrices.globalRows (ComputedComponents.componentRibbon
      (localLeft left right keep) (localRight left right keep) root
      (ribbon left right keep M.sides.toRibbon))).length ≤
        Parameters.exponent M.eulerGenus (EmbeddedReduction.oddFaceCount M) ∧
      ∀ _O : M.sides.Orientation,
        (ComputedEmbeddedMatrices.globalRows (ComputedComponents.componentRibbon
          (localLeft left right keep) (localRight left right keep) root
          (ribbon left right keep M.sides.toRibbon))).length ≤
            Parameters.orientableExponent M.eulerGenus (EmbeddedReduction.oddFaceCount M) := by
  classical
  let q := originalComponentKeep left right keep root
  let ee := componentOriginalEdgeEquiv left right keep root
  let f := componentOriginalVertex left right keep root
  have hl := componentOriginalVertex_left left right keep root
  have hr := componentOriginalVertex_right left right keep root
  have hi := componentOriginalVertex_injective left right keep root
  have hc := ComputedComponents.local_connected (localLeft left right keep) (localRight left right keep) root
  have hne := nonempty_edges_of_nonbipartite hnb
  let ev := IndexedActiveVertices.activeEquiv q f ee hl hr hc hne hi
  exact ComputedEmbeddedMatrices.globalRows_deleted_parameter_bound M
    (ComputedComponents.componentRibbon (localLeft left right keep) (localRight left right keep) root
      (ribbon left right keep M.sides.toRibbon))
    q ee ev (IndexedActiveVertices.activeEquiv_left q f ee hl hr hc hne hi)
      (IndexedActiveVertices.activeEquiv_right q f ee hl hr hc hne hi)
      (componentOriginal_corner_map left right keep root M.sides.toRibbon) hcM hc hnb

end WeightedMIS.ComputedInduced

namespace WeightedMIS.ExecutableMIS

open EmbeddingFaces Incidence ComputedInduced

variable {n m : ℕ} {left right : Fin m → Fin n}
    {F : Type*} [Fintype F] [DecidableEq F] (M : CellularEmbedding left right F)

/-- The exact retention predicate evaluated by the executable solver. -/
def residualVertices (weights : Fin n → ℚ) (v : Fin n) : Prop :=
  OriginalReduction.preprocessingPoint (left := left) (right := right) weights (List.finRange n) v = 1 / 2

instance (weights : Fin n → ℚ) (v : Fin n) : Decidable (residualVertices (left := left) (right := right) weights v) :=
  inferInstanceAs (Decidable (_ = _))

/-- Every actual hard component processed by `solve` has at most the original
parameter exponent many computed integer signature coordinates. -/
theorem solve_component_parameter_bound (weights : Fin n → ℚ) (hcM : Connected left right)
    (root : Fin (vertices (residualVertices (left := left) (right := right) weights)).length)
    (hnb : ¬ Bipartite
      (ComputedComponents.localLeft (localLeft left right (residualVertices weights))
        (localRight left right (residualVertices weights)) root)
      (ComputedComponents.localRight (localLeft left right (residualVertices weights))
        (localRight left right (residualVertices weights)) root)) :
    (ComputedEmbeddedMatrices.globalRows (ComputedComponents.componentRibbon
      (localLeft left right (residualVertices weights)) (localRight left right (residualVertices weights)) root
      (ribbon left right (residualVertices weights) M.sides.toRibbon))).length ≤
        Parameters.exponent M.eulerGenus (EmbeddedReduction.oddFaceCount M) ∧
      ∀ _O : M.sides.Orientation,
        (ComputedEmbeddedMatrices.globalRows (ComputedComponents.componentRibbon
          (localLeft left right (residualVertices weights)) (localRight left right (residualVertices weights)) root
          (ribbon left right (residualVertices weights) M.sides.toRibbon))).length ≤
            Parameters.orientableExponent M.eulerGenus (EmbeddedReduction.oddFaceCount M) :=
  component_globalRows_bound M (residualVertices weights) root hcM hnb

end WeightedMIS.ExecutableMIS
