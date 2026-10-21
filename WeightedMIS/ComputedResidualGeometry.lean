module

public import WeightedMIS.ComputedInduced
public import WeightedMIS.RibbonDeletionRelabeling

/-!
# Original-edge geometry of the computed residual components

The numerical component selected after induced-graph preprocessing is an
actual one-step restriction of the original edge bands. The equivalence below
uses only the computed edge lists, and its corner identity is derived from
the bounded first-return construction.
-/

@[expose] public section

namespace WeightedMIS.ComputedInduced

open EmbeddingFaces

variable {n m : ℕ} (left right : Fin m → Fin n)
    (keep : Fin n → Prop) [DecidablePred keep]
    (root : Fin (vertices keep).length)

/-- Component membership expressed on actual retained original edge labels. -/
def retainedComponent (e : {e : Fin m // edgeKeep left right keep e}) : Prop :=
  (edgeEquiv left right keep).symm e ∈
    ComputedComponents.edges (localLeft left right keep) (localRight left right keep) root

instance (e : {e : Fin m // edgeKeep left right keep e}) :
    Decidable (retainedComponent left right keep root e) := inferInstanceAs (Decidable (_ ∈ _))

/-- The single original-edge predicate selected by the numerical residual component. -/
def originalComponentKeep : Fin m → Prop :=
  NestedRetention.keep (edgeKeep left right keep) (retainedComponent left right keep root)

/-- Exact original edge labels of the actually computed numerical component. -/
def componentOriginalEdgeEquiv :
    Fin (ComputedComponents.edges (localLeft left right keep) (localRight left right keep) root).length ≃
      {e : Fin m // originalComponentKeep left right keep root e} :=
  (ComputedComponents.retainedEdgeEquiv (localLeft left right keep) (localRight left right keep) root).trans
    (((edgeEquiv left right keep).subtypeEquiv (fun e => by
      simp only [retainedComponent, Equiv.symm_apply_apply])).trans
      (NestedRetention.edgeEquiv (edgeKeep left right keep)
        (retainedComponent left right keep root)).symm)

/-- Actual original vertex labels of the computed residual component. -/
def componentOriginalVertex
    (v : Fin (ComputedComponents.vertices (localLeft left right keep) (localRight left right keep) root).length) :
    Fin n :=
  (vertexEquiv keep (ComputedComponents.vertexEquiv
    (localLeft left right keep) (localRight left right keep) root v).val).val

theorem componentOriginalVertex_injective :
    Function.Injective (componentOriginalVertex left right keep root) :=
  Subtype.val_injective.comp ((vertexEquiv keep).injective.comp
    (Subtype.val_injective.comp (ComputedComponents.vertexEquiv
      (localLeft left right keep) (localRight left right keep) root).injective))

theorem componentOriginalVertex_left
    (e : Fin (ComputedComponents.edges (localLeft left right keep) (localRight left right keep) root).length) :
    componentOriginalVertex left right keep root
      (ComputedComponents.localLeft (localLeft left right keep) (localRight left right keep) root e) =
        left (componentOriginalEdgeEquiv left right keep root e).val := by
  unfold componentOriginalVertex
  rw [ComputedComponents.vertexEquiv_localLeft]
  exact vertexEquiv_localLeft left right keep _

theorem componentOriginalVertex_right
    (e : Fin (ComputedComponents.edges (localLeft left right keep) (localRight left right keep) root).length) :
    componentOriginalVertex left right keep root
      (ComputedComponents.localRight (localLeft left right keep) (localRight left right keep) root e) =
        right (componentOriginalEdgeEquiv left right keep root e).val := by
  unfold componentOriginalVertex
  rw [ComputedComponents.vertexEquiv_localRight]
  exact vertexEquiv_localRight left right keep _

/-- First-stage numeric edge relabelling preserves every actual corner. -/
theorem ribbon_corner_map (R : Ribbon left right)
    (x : EmbeddingFaces.Flag (Fin (edges left right keep).length)) :
    Flag.mapEquiv (edgeEquiv left right keep) ((ribbon left right keep R).corner x) =
      (R.computedRestrict (edgeKeep left right keep)).corner (Flag.mapEquiv (edgeEquiv left right keep) x) :=
  (R.computedRestrict (edgeKeep left right keep)).relabelCorner_map (edgeEquiv left right keep) x

/-- A computed graph component is closed under the actual residual corners. -/
theorem retainedComponent_corner_closed (R : Ribbon left right)
    (x : EmbeddingFaces.Flag {e : Fin m // edgeKeep left right keep e})
    (hx : retainedComponent left right keep root x.edge) :
    retainedComponent left right keep root ((R.computedRestrict (edgeKeep left right keep)).corner x).edge := by
  let y := (Flag.mapEquiv (edgeEquiv left right keep)).symm x
  have hy := ComputedComponents.edges_corner_closed (localLeft left right keep) (localRight left right keep)
    root (ribbon left right keep R) y hx
  have he := congrArg (fun z => (edgeEquiv left right keep).symm z.edge)
    (ribbon_corner_map left right keep R y)
  have hyx : Flag.mapEquiv (edgeEquiv left right keep) y = x :=
    (Flag.mapEquiv (edgeEquiv left right keep)).apply_symm_apply x
  rw [hyx] at he
  simp only [Flag.mapEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply] at he
  change _ ∈ _
  rwa [← he]

/-- The computed two-stage component ribbon equals the single original-band
restriction under the explicit original edge-ID equivalence. -/
theorem componentOriginal_corner_map (R : Ribbon left right)
    (x : EmbeddingFaces.Flag
      (Fin (ComputedComponents.edges (localLeft left right keep) (localRight left right keep) root).length)) :
    Flag.mapEquiv (componentOriginalEdgeEquiv left right keep root)
      ((ComputedComponents.componentRibbon (localLeft left right keep) (localRight left right keep)
        root (ribbon left right keep R)).corner x) =
      (R.restrict (originalComponentKeep left right keep root)).corner
        (Flag.mapEquiv (componentOriginalEdgeEquiv left right keep root) x) := by
  classical
  let S := ribbon left right keep R
  let p := fun e => e ∈ ComputedComponents.edges (localLeft left right keep) (localRight left right keep) root
  let q := retainedComponent left right keep root
  let ee := edgeEquiv left right keep
  let hp : ∀ e, p e ↔ q (ee e) := fun e => by simp only [p, q, retainedComponent, ee, Equiv.symm_apply_apply]
  let a := Flag.mapEquiv (ComputedComponents.retainedEdgeEquiv
    (localLeft left right keep) (localRight left right keep) root) x
  have h1 := (S.computedRestrict p).relabelCorner_map
    (ComputedComponents.retainedEdgeEquiv (localLeft left right keep) (localRight left right keep) root) x
  have h2 := Ribbon.computedRestrict_map S (R.computedRestrict (edgeKeep left right keep)) ee
    (ribbon_corner_map left right keep R) p q hp a
  have h3 := R.computedRestrict_nested_closed (edgeKeep left right keep) q
    (retainedComponent_corner_closed left right keep root R)
    (Flag.mapEquiv (ee.subtypeEquiv hp) a)
  rw [R.computedRestrict_eq (NestedRetention.keep (edgeKeep left right keep) q)] at h3
  exact (congrArg (Flag.mapEquiv (NestedRetention.edgeEquiv (edgeKeep left right keep) q).symm)
    ((congrArg (Flag.mapEquiv (ee.subtypeEquiv hp)) h1).trans h2)).trans h3

end WeightedMIS.ComputedInduced
