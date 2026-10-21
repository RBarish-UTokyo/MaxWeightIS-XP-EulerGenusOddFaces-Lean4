module

public import WeightedMIS.SparseSearchWeights

/-!
# Sparse search with encoded edge labels

A label encoder and its explicit left inverse connect opaque stored labels
with original edge IDs. The search only reads targets and weights, while the
recovered label decoder identifies exactly the expanded-graph path.
-/

@[expose] public section

namespace WeightedMIS.SparseSearchGraph.Labeled

open Expanded NodeEncoding EfficientSearch

variable {Label : Type*}

/-- Encode an outgoing target, exact natural weight, and original-edge label. -/
def encodedArc {r m d radius : ℕ} (η : Option (Fin m) → Label) (w : Fin m → ℕ)
    (entry : Option (Fin m) × Fin (nodeCount r d radius)) :
    EfficientSearch.Arc Label (vertexWidth r d radius) (costWidth r d radius w) :=
  ⟨vertexKey entry.2, encodeBits _ (labelValue w entry.1), η entry.1⟩

@[simp] theorem encodedArc_weight {r m d radius : ℕ} (η : Option (Fin m) → Label) (w : Fin m → ℕ)
    (entry : Option (Fin m) × Fin (nodeCount r d radius)) :
    (encodedArc η w entry).weight.value = labelValue w entry.1 :=
  encodeBits_value _ _ (weight_lt_capacity r d radius w entry.1)

/-- Enumerate only the actual outgoing lists, never vertex pairs. -/
def entries {r m d : ℕ} (η : Option (Fin m) → Label) (C : Fin m → Walks.Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ) (w : Fin m → ℕ) :
    List (RawArc Label (vertexWidth r d radius) (costWidth r d radius w)) :=
  (List.finRange (nodeCount r d radius)).flatMap fun s =>
    (SearchConstruction.encodedOutgoing C W π radius s).map fun e => (vertexKey s, encodedArc η w e)

def graph {r m d : ℕ} (η : Option (Fin m) → Label) (C : Fin m → Walks.Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ) (w : Fin m → ℕ) :
    Graph Label (vertexWidth r d radius) (costWidth r d radius w) :=
  Radix.fromEntries (entries η C W π radius w)

theorem graph_canonical {r m d : ℕ} (η : Option (Fin m) → Label) (C : Fin m → Walks.Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ) (w : Fin m → ℕ) :
    (graph η C W π radius w).canonical := Radix.fromEntries_canonical _

theorem mem_graph_iff {r m d : ℕ} (η : Option (Fin m) → Label) (C : Fin m → Walks.Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ) (w : Fin m → ℕ)
    (edge : RawArc Label (vertexWidth r d radius) (costWidth r d radius w)) :
    edge ∈ (graph η C W π radius w).elements ↔
      ∃ s e, e ∈ SearchConstruction.encodedOutgoing C W π radius s ∧
        (vertexKey s, encodedArc η w e) = edge := by
  simp only [graph, Radix.mem_fromEntries, entries, List.mem_flatMap, List.mem_map,
    List.mem_finRange, true_and]

theorem graph_size_le {r m d : ℕ} (η : Option (Fin m) → Label) (C : Fin m → Walks.Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ) (w : Fin m → ℕ) :
    (graph η C W π radius w).elements.length ≤ entryBound r m d radius := by
  rw [graph, Radix.fromEntries_size]
  unfold entries
  rw [List.length_flatMap]
  simp only [List.length_map]
  calc
    _ ≤ ((List.finRange (nodeCount r d radius)).map
      (fun _ => 2 * r + 2 * m + 2)).sum :=
        List.sum_le_sum fun s _ => encodedOutgoing_length_le C W π radius s
    _ = _ := by simp [entryBound]

theorem graph_weight_bound {r m d : ℕ} (η : Option (Fin m) → Label) (C : Fin m → Walks.Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ) (w : Fin m → ℕ) :
    GraphBound (graph η C W π radius w) (weightBound w) := by
  intro edge he
  obtain ⟨s, e, _he, rfl⟩ := (mem_graph_iff η C W π radius w edge).mp he
  simp only [encodedArc_weight]
  exact labelValue_le w e.1

theorem graph_no_overflow_width {r m d : ℕ} (η : Option (Fin m) → Label) (C : Fin m → Walks.Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ) (w : Fin m → ℕ) :
    ((graph η C W π radius w).elements.length + 2) * weightBound w <
      2 ^ costWidth r d radius w := by
  have hsize := graph_size_le η C W π radius w
  exact (Nat.mul_le_mul_right (weightBound w) (Nat.add_le_add_right hsize 2)).trans_lt
    (Nat.lt_size_self _)


end WeightedMIS.SparseSearchGraph.Labeled
