module

public import WeightedMIS.SparseSearchGraph

/-!
# Recovering the actual expanded path from sparse search

The forward predecessor list returned by the trie-based search has exactly the
labels of an expanded-graph path. Conversely, every expanded path is a walk in
the stored graph with the same natural weight, so the actual output is minimal.
-/

@[expose] public section

namespace WeightedMIS.SparseSearchGraph

open Expanded NodeEncoding EfficientSearch

variable {r m d : ℕ}

theorem graph_edge_step (C : Fin m → Walks.Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ) (w : Fin m → ℕ)
    (edge : RawArc (Option (Fin m)) (vertexWidth r d radius) (costWidth r d radius w))
    (he : edge ∈ (graph C W π radius w).elements) :
    Step C W π radius (decodeNode edge.1) edge.2.label (decodeNode edge.2.target) ∧
      edge.2.weight.value = labelValue w edge.2.label := by
  obtain ⟨s, e, hm, rfl⟩ := (mem_graph_iff C W π radius w edge).mp he
  constructor
  · simpa only [encodedArc, decode_vertexKey] using
      (SearchConstruction.mem_encodedOutgoing_iff C W π radius s e.2 e.1).mp hm
  · exact encodedArc_weight w e

/-- The precise stored arc corresponding to an expanded step. -/
def storedArc (C : Fin m → Walks.Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ) (w : Fin m → ℕ)
    {s t : Node (Fin r) (Fin d) radius} {label : Option (Fin m)}
    (h : Step C W π radius s label t) : StoredArc (graph C W π radius w) :=
  ⟨(nodeKey s, encodedArc w (label, nodeEquiv r d radius t)), by
    apply (mem_graph_iff C W π radius w _).mpr
    refine ⟨nodeEquiv r d radius s, (label, nodeEquiv r d radius t), ?_, rfl⟩
    apply (SearchConstruction.mem_encodedOutgoing_iff C W π radius _ _ label).mpr
    simpa using h⟩

@[simp] theorem storedArc_source (C : Fin m → Walks.Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ) (w : Fin m → ℕ)
    {s t : Node (Fin r) (Fin d) radius} {label : Option (Fin m)}
    (h : Step C W π radius s label t) :
    EfficientSearch.arcSource (storedArc C W π radius w h) = nodeKey s := rfl

@[simp] theorem storedArc_target (C : Fin m → Walks.Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ) (w : Fin m → ℕ)
    {s t : Node (Fin r) (Fin d) radius} {label : Option (Fin m)}
    (h : Step C W π radius s label t) :
    EfficientSearch.arcTarget (storedArc C W π radius w h) = nodeKey t := rfl

@[simp] theorem storedArc_weight (C : Fin m → Walks.Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ) (w : Fin m → ℕ)
    {s t : Node (Fin r) (Fin d) radius} {label : Option (Fin m)}
    (h : Step C W π radius s label t) :
    EfficientSearch.arcWeight (storedArc C W π radius w h) = labelValue w label :=
  encodedArc_weight w _

/-- Translate an expanded path by its actual steps into stored adjacency entries. -/
def storedPath {C : Fin m → Walks.Column (Fin r)}
    {W : Fin m → Fin d → ℤ} {π : Fin m → ZMod 2} {radius : ℕ} (w : Fin m → ℕ)
    {s t : Node (Fin r) (Fin d) radius} :
    Path C W π radius s t → List (StoredArc (graph C W π radius w))
  | .nil _ => []
  | .cons _ h tail => storedArc C W π radius w h :: storedPath w tail

theorem storedPath_walk {C : Fin m → Walks.Column (Fin r)}
    {W : Fin m → Fin d → ℤ} {π : Fin m → ZMod 2} {radius : ℕ} (w : Fin m → ℕ)
    {s t : Node (Fin r) (Fin d) radius} (p : Path C W π radius s t) :
    ShortestPath.IsWalk EfficientSearch.arcSource EfficientSearch.arcTarget
      (nodeKey s) (nodeKey t) (storedPath w p) := by
  induction p with
  | nil => rfl
  | cons label h tail ih => exact ⟨rfl, ih⟩

theorem storedPath_cost {C : Fin m → Walks.Column (Fin r)}
    {W : Fin m → Fin d → ℤ} {π : Fin m → ZMod 2} {radius : ℕ} (w : Fin m → ℕ)
    {s t : Node (Fin r) (Fin d) radius} (p : Path C W π radius s t) :
    Dijkstra.cost EfficientSearch.arcWeight (storedPath w p) = (p.labels.map w).sum := by
  induction p with
  | nil => rfl
  | cons label h tail ih =>
      cases label <;> simp [storedPath, Path.labels, Dijkstra.cost_cons, storedArc_weight,
        labelValue, ih]

/-- Original edge labels of the actual recovered forward trace. -/
def traceLabels {vbits cbits : ℕ} (path : Trace (Option (Fin m)) vbits cbits) : List (Fin m) :=
  path.filterMap (fun edge => edge.2.label)

theorem path_labels_cons {C : Fin m → Walks.Column (Fin r)}
    {W : Fin m → Fin d → ℤ} {π : Fin m → ZMod 2} {radius : ℕ}
    {s t u : Node (Fin r) (Fin d) radius} (label : Option (Fin m))
    (h : Step C W π radius s label t) (p : Path C W π radius t u) :
    (Path.cons label h p).labels = label.toList ++ p.labels := by
  cases label <;> rfl

theorem path_of_trace (C : Fin m → Walks.Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ) (w : Fin m → ℕ)
    (path : Trace (Option (Fin m)) (vertexWidth r d radius) (costWidth r d radius w))
    (s t : Bits (vertexWidth r d radius))
    (hmem : ∀ edge ∈ path, edge ∈ (graph C W π radius w).elements)
    (hwalk : ShortestPath.IsWalk rawSource rawTarget s t path) :
    ∃ p : Path C W π radius (decodeNode s) (decodeNode t), p.labels = traceLabels path := by
  induction path generalizing s with
  | nil =>
      have hst : s = t := hwalk
      subst s
      exact ⟨Path.nil _, rfl⟩
  | cons edge path ih =>
      obtain ⟨p, hp⟩ := ih edge.2.target
        (fun e he => hmem e (List.mem_cons_of_mem edge he)) hwalk.2
      have hs := (graph_edge_step C W π radius w edge (hmem edge List.mem_cons_self)).1
      have heq : edge.1 = s := hwalk.1
      rw [heq] at hs
      refine ⟨Path.cons edge.2.label hs p, ?_⟩
      rw [path_labels_cons, hp]
      cases hlabel : edge.2.label <;> simp [traceLabels, hlabel]

theorem traceLabels_cost (C : Fin m → Walks.Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ) (w : Fin m → ℕ)
    (path : Trace (Option (Fin m)) (vertexWidth r d radius) (costWidth r d radius w))
    (hmem : ∀ edge ∈ path, edge ∈ (graph C W π radius w).elements) :
    ((traceLabels path).map w).sum = Dijkstra.cost rawWeight path := by
  induction path with
  | nil => rfl
  | cons edge path ih =>
      have hw := (graph_edge_step C W π radius w edge (hmem edge List.mem_cons_self)).2
      have hi := ih (fun e he => hmem e (List.mem_cons_of_mem edge he))
      cases he : edge.2.label <;>
        simpa [traceLabels, Dijkstra.cost_cons, rawWeight, hw, he, labelValue] using hi

/-- The actual recovered trace encodes a minimum-weight expanded path. -/
theorem solve_expanded_minimum (C : Fin m → Walks.Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ) (w : Fin m → ℕ)
    (s t : Node (Fin r) (Fin d) radius) (reachable : Nonempty (Path C W π radius s t)) :
    ∃ distance trace, ∃ p : Path C W π radius s t,
      (recover (solve (graph C W π radius w) (nodeKey s)) (nodeKey t)).1 =
        some (distance, trace) ∧
      p.labels = traceLabels trace ∧
      (p.labels.map w).sum = distance.value ∧
      (∀ q : Path C W π radius s t, (p.labels.map w).sum ≤ (q.labels.map w).sum) ∧
      (solve (graph C W π radius w) (nodeKey s)).work +
        (recover (solve (graph C W π radius w) (nodeKey s)) (nodeKey t)).2 ≤
          (5 * costWidth r d radius w + 6 * vertexWidth r d radius + 26) *
            (entryBound r m d radius + 1) + 11 := by
  obtain ⟨q⟩ := reachable
  have hreach : ∃ path, ShortestPath.IsWalk
      (EfficientSearch.arcSource (graph := graph C W π radius w)) EfficientSearch.arcTarget
      (nodeKey s) (nodeKey t) path := ⟨storedPath w q, storedPath_walk w q⟩
  obtain ⟨distance, trace, hout, hmem, hwalk, hcost, hmin, hwork⟩ :=
    solve_specification (graph C W π radius w) (nodeKey s) (nodeKey t)
      (weightBound w) (graph_canonical C W π radius w) (graph_weight_bound C W π radius w)
      (graph_no_overflow_width C W π radius w) hreach
  have hpExists : ∃ p : Path C W π radius s t, p.labels = traceLabels trace := by
    have hs := decode_nodeKey s
    have ht := decode_nodeKey t
    have hex := path_of_trace C W π radius w trace (nodeKey s) (nodeKey t) hmem hwalk
    rw [hs, ht] at hex
    exact hex
  obtain ⟨p, hp⟩ := hpExists
  refine ⟨distance, trace, p, hout, hp, ?_, ?_, ?_⟩
  · rw [hp, traceLabels_cost C W π radius w trace hmem, hcost]
  · intro q
    rw [hp, traceLabels_cost C W π radius w trace hmem, hcost]
    have h := hmin (storedPath w q) (storedPath_walk w q)
    simpa only [storedPath_cost] using h
  · exact hwork.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right (graph_size_le C W π radius w) 1)) 11)

end WeightedMIS.SparseSearchGraph
