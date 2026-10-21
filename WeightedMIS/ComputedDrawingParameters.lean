module

public import WeightedMIS.ComputedResidualParameters
public import WeightedMIS.ComputedDrawingTransfer
public import WeightedMIS.RibbonDrawingRestriction

/-!
# Actual solver parameters on disconnected and noncellular drawings

Only the finite numeric ribbon is supplied to the solver. Its embedding into
a cellular completion is a mathematical witness consisting of genuine label
bijections and corner identities. Every hard residual component inherits the
original drawing's genus and total odd-region-boundary parameter bound.
-/

@[expose] public section

namespace WeightedMIS.ComputedDrawing

open EmbeddingFaces Incidence

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E] [DecidableEq F]
    {ambientLeft ambientRight : E → V} (M : CellularEmbedding ambientLeft ambientRight F)
    {n m : ℕ} {left right : Fin m → Fin n} (R : Ribbon left right)
    (drawing : E → Prop) [DecidablePred drawing]
    (ee : Fin m ≃ {e : E // drawing e}) (f : Fin n → V)
    (hf : Function.Injective f)
    (hl : ∀ e, f (left e) = ambientLeft (ee e).val)
    (hr : ∀ e, f (right e) = ambientRight (ee e).val)
    (hcorner : ∀ x, Flag.mapEquiv ee (R.corner x) =
      (M.sides.toRibbon.restrict drawing).corner (Flag.mapEquiv ee x))
    (keep : Fin n → Prop) [DecidablePred keep]
    (root : Fin (ComputedInduced.vertices keep).length)

/-- The exact single-stage ambient edge subset of a computed residual component. -/
def componentAmbientKeep : E → Prop :=
  Ribbon.drawingKeep drawing ee (ComputedInduced.originalComponentKeep left right keep root)

/-- The actual numeric residual-component edge IDs biject its ambient labels. -/
def componentAmbientEdgeEquiv :
    Fin (ComputedComponents.edges (ComputedInduced.localLeft left right keep)
      (ComputedInduced.localRight left right keep) root).length ≃
        {e : E // componentAmbientKeep (left := left) (right := right) drawing ee keep root e} :=
  (ComputedInduced.componentOriginalEdgeEquiv left right keep root).trans
    (Ribbon.drawingEdgeEquiv drawing ee (ComputedInduced.originalComponentKeep left right keep root))

include hcorner in
/-- Actual corner tracing commutes with both preprocessing and the original
retained-drawing witness. -/
theorem componentAmbient_corner_map
    (x : EmbeddingFaces.Flag (Fin (ComputedComponents.edges (ComputedInduced.localLeft left right keep)
      (ComputedInduced.localRight left right keep) root).length)) :
    Flag.mapEquiv (componentAmbientEdgeEquiv drawing ee keep root)
      ((ComputedComponents.componentRibbon (ComputedInduced.localLeft left right keep)
        (ComputedInduced.localRight left right keep) root (ComputedInduced.ribbon left right keep R)).corner x) =
      (M.sides.toRibbon.restrict (componentAmbientKeep (left := left) (right := right) drawing ee keep root)).corner
        (Flag.mapEquiv (componentAmbientEdgeEquiv drawing ee keep root) x) := by
  have h1 := ComputedInduced.componentOriginal_corner_map left right keep root R x
  have h2 := Ribbon.drawing_restrict_corner_map drawing ee
    (ComputedInduced.originalComponentKeep left right keep root) R M.sides.toRibbon hcorner
    (Flag.mapEquiv (ComputedInduced.componentOriginalEdgeEquiv left right keep root) x)
  exact (congrArg (Flag.mapEquiv (Ribbon.drawingEdgeEquiv drawing ee
    (ComputedInduced.originalComponentKeep left right keep root))) h1).trans h2

include hf hl hr hcorner in
/-- No ambient completion is input to the algorithm: its actual computed
coordinates satisfy this bound solely through the faithful drawing witness. -/
theorem component_globalRows_bound (hcM : Connected ambientLeft ambientRight)
    (hnb : ¬ Bipartite
      (ComputedComponents.localLeft (ComputedInduced.localLeft left right keep)
        (ComputedInduced.localRight left right keep) root)
      (ComputedComponents.localRight (ComputedInduced.localLeft left right keep)
        (ComputedInduced.localRight left right keep) root)) :
    (ComputedEmbeddedMatrices.globalRows (ComputedComponents.componentRibbon
      (ComputedInduced.localLeft left right keep) (ComputedInduced.localRight left right keep) root
      (ComputedInduced.ribbon left right keep R))).length ≤
        Parameters.exponent M.eulerGenus (M.sides.oddRegionCount drawing) ∧
      ∀ _O : M.sides.Orientation,
        (ComputedEmbeddedMatrices.globalRows (ComputedComponents.componentRibbon
          (ComputedInduced.localLeft left right keep) (ComputedInduced.localRight left right keep) root
          (ComputedInduced.ribbon left right keep R))).length ≤
            Parameters.orientableExponent M.eulerGenus (M.sides.oddRegionCount drawing) := by
  classical
  let q := componentAmbientKeep (left := left) (right := right) drawing ee keep root
  let e := componentAmbientEdgeEquiv (left := left) (right := right) drawing ee keep root
  let v := fun u => f (ComputedInduced.componentOriginalVertex left right keep root u)
  have hi : Function.Injective v := hf.comp (ComputedInduced.componentOriginalVertex_injective left right keep root)
  have hleft : ∀ a, v (ComputedComponents.localLeft (ComputedInduced.localLeft left right keep)
      (ComputedInduced.localRight left right keep) root a) = ambientLeft (e a).val := by
    intro a
    change f (ComputedInduced.componentOriginalVertex left right keep root _) = _
    rw [ComputedInduced.componentOriginalVertex_left]
    exact hl _
  have hright : ∀ a, v (ComputedComponents.localRight (ComputedInduced.localLeft left right keep)
      (ComputedInduced.localRight left right keep) root a) = ambientRight (e a).val := by
    intro a
    change f (ComputedInduced.componentOriginalVertex left right keep root _) = _
    rw [ComputedInduced.componentOriginalVertex_right]
    exact hr _
  have hc := ComputedComponents.local_connected (ComputedInduced.localLeft left right keep)
    (ComputedInduced.localRight left right keep) root
  have hne := nonempty_edges_of_nonbipartite hnb
  let ev := IndexedActiveVertices.activeEquiv q v e hleft hright hc hne hi
  exact ComputedEmbeddedMatrices.globalRows_drawing_parameter_bound M
    (ComputedComponents.componentRibbon (ComputedInduced.localLeft left right keep)
      (ComputedInduced.localRight left right keep) root (ComputedInduced.ribbon left right keep R))
    drawing q e ev (IndexedActiveVertices.activeEquiv_left q v e hleft hright hc hne hi)
      (IndexedActiveVertices.activeEquiv_right q v e hleft hright hc hne hi)
      (componentAmbient_corner_map M R drawing ee hcorner keep root) (fun _ h => h.1) hcM hc hnb

include hf hl hr hcorner in
/-- The actual deterministic output is a maximum for the original weights,
and every hard search it performs uses at most the original surface exponent
many computed coordinates. This is functional correctness and a dimension
bound; the fixed-machine running-time refinement is a separate theorem. -/
theorem solve_correct_and_parameters (weights : Fin n → ℚ)
    (hcM : Connected ambientLeft ambientRight) :
    let kept := ExecutableMIS.residualVertices (left := left) (right := right) weights
    Persistence.Independent (EdgeTransport.Adj left right) (ExecutableMIS.solve R weights) ∧
      (∀ J, Persistence.Independent (EdgeTransport.Adj left right) J →
        Persistence.weight weights J ≤ Persistence.weight weights (ExecutableMIS.solve R weights)) ∧
      ∀ root : Fin (ComputedInduced.vertices kept).length,
        ¬ Bipartite
          (ComputedComponents.localLeft (ComputedInduced.localLeft left right kept)
            (ComputedInduced.localRight left right kept) root)
          (ComputedComponents.localRight (ComputedInduced.localLeft left right kept)
            (ComputedInduced.localRight left right kept) root) →
        (ComputedEmbeddedMatrices.globalRows (ComputedComponents.componentRibbon
          (ComputedInduced.localLeft left right kept) (ComputedInduced.localRight left right kept) root
          (ComputedInduced.ribbon left right kept R))).length ≤
            Parameters.exponent M.eulerGenus (M.sides.oddRegionCount drawing) ∧
          ∀ _O : M.sides.Orientation,
            (ComputedEmbeddedMatrices.globalRows (ComputedComponents.componentRibbon
              (ComputedInduced.localLeft left right kept) (ComputedInduced.localRight left right kept) root
              (ComputedInduced.ribbon left right kept R))).length ≤
                Parameters.orientableExponent M.eulerGenus (M.sides.oddRegionCount drawing) := by
  refine ⟨(ExecutableMIS.solve_correct R weights).1, (ExecutableMIS.solve_correct R weights).2, ?_⟩
  intro root hnb
  exact component_globalRows_bound M R drawing ee f hf hl hr hcorner
    (ExecutableMIS.residualVertices weights) root hcM hnb

end WeightedMIS.ComputedDrawing
