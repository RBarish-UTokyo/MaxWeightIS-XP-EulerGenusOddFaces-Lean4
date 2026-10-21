module

public import WeightedMIS.ComputedRestriction
public import WeightedMIS.RibbonRelabeling
public import WeightedMIS.GraphRelabeling
public import WeightedMIS.InducedComponents

/-!
# Explicit finite indices for an induced retained graph

Vertex and edge IDs are obtained by filtering their numeric lists. Both
inverse maps use actual list-index lookup. The inherited corner matching is
computed by bounded splicing and transported to those finite edge IDs.
-/

@[expose] public section

namespace WeightedMIS.ComputedInduced

open EmbeddingFaces Incidence

variable {n m : ℕ} (left right : Fin m → Fin n) (keep : Fin n → Prop) [DecidablePred keep]

def edgeKeep (e : Fin m) : Prop := keep (left e) ∧ keep (right e)
instance (e : Fin m) : Decidable (edgeKeep left right keep e) := inferInstanceAs (Decidable (_ ∧ _))

def vertices : List (Fin n) := (List.finRange n).filter fun v => decide (keep v)
def edges : List (Fin m) := (List.finRange m).filter fun e => decide (edgeKeep left right keep e)

@[simp] theorem mem_vertices (v : Fin n) : v ∈ vertices keep ↔ keep v := by simp [vertices]
@[simp] theorem mem_edges (e : Fin m) : e ∈ edges left right keep ↔ edgeKeep left right keep e := by simp [edges]

def vertexEquiv : Fin (vertices keep).length ≃ {v : Fin n // keep v} :=
  (List.Nodup.getEquiv _ ((List.nodup_finRange n).filter _)).trans
    (Equiv.subtypeEquivRight (mem_vertices keep))

def edgeEquiv : Fin (edges left right keep).length ≃ {e : Fin m // edgeKeep left right keep e} :=
  (List.Nodup.getEquiv _ ((List.nodup_finRange m).filter _)).trans
    (Equiv.subtypeEquivRight (mem_edges left right keep))

def localLeft (e : Fin (edges left right keep).length) : Fin (vertices keep).length :=
  (vertexEquiv keep).symm ⟨left (edgeEquiv left right keep e).val, (edgeEquiv left right keep e).property.1⟩

def localRight (e : Fin (edges left right keep).length) : Fin (vertices keep).length :=
  (vertexEquiv keep).symm ⟨right (edgeEquiv left right keep e).val, (edgeEquiv left right keep e).property.2⟩

@[simp] theorem vertexEquiv_localLeft (e : Fin (edges left right keep).length) :
    (vertexEquiv keep (localLeft left right keep e)).val = left (edgeEquiv left right keep e).val := by
  simp only [localLeft, Equiv.apply_symm_apply]

@[simp] theorem vertexEquiv_localRight (e : Fin (edges left right keep).length) :
    (vertexEquiv keep (localRight left right keep e)).val = right (edgeEquiv left right keep e).val := by
  simp only [localRight, Equiv.apply_symm_apply]

/-- The actual stored induced endpoints have exactly induced original adjacency. -/
theorem local_adj (u v : Fin (vertices keep).length) :
    EdgeTransport.Adj (localLeft left right keep) (localRight left right keep) u v ↔
      EdgeTransport.Adj left right (vertexEquiv keep u).val (vertexEquiv keep v).val := by
  have hh := adj_relabel (vertexEquiv keep) (edgeEquiv left right keep)
    (leftU := localLeft left right keep) (rightU := localRight left right keep)
    (leftV := InducedComponents.edgeLeft left right keep)
    (rightV := InducedComponents.edgeRight left right keep)
    (fun e => Subtype.ext (vertexEquiv_localLeft left right keep e))
    (fun e => Subtype.ext (vertexEquiv_localRight left right keep e)) u v
  exact hh.trans (InducedComponents.adj_iff left right keep _ _)

/-- The actual induced ribbon on the explicitly stored numeric graph. -/
def ribbon (R : Ribbon left right) : Ribbon (localLeft left right keep) (localRight left right keep) :=
  (R.computedRestrict (edgeKeep left right keep)).relabel (edgeEquiv left right keep)
    (fun v => (vertexEquiv keep v).val)
    (Subtype.val_injective.comp (vertexEquiv keep).injective)
    (localLeft left right keep) (localRight left right keep)
    (vertexEquiv_localLeft left right keep) (vertexEquiv_localRight left right keep)

/-- Actual induced all-half optimality is preserved by the computed indices. -/
theorem half_optimal (weights : Fin n → ℚ)
    (ho : Persistence.Optimal (fun u v : {v : Fin n // keep v} => EdgeTransport.Adj left right u.val v.val)
      (fun v => weights v.val) (fun _ => 1 / 2)) :
    Persistence.Optimal (EdgeTransport.Adj (localLeft left right keep) (localRight left right keep))
      (fun v => weights (vertexEquiv keep v).val) (fun _ => 1 / 2) :=
  GraphRelabeling.half_optimal_pullback (vertexEquiv keep)
    (EdgeTransport.Adj (localLeft left right keep) (localRight left right keep))
    (fun u v : {v : Fin n // keep v} => EdgeTransport.Adj left right u.val v.val)
    (local_adj left right keep) (fun v : {v : Fin n // keep v} => weights v.val) ho

end WeightedMIS.ComputedInduced
