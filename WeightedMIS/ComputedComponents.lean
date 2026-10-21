module

public import WeightedMIS.GraphSearch
public import WeightedMIS.GraphComponents
public import WeightedMIS.EndpointRelabeling

/-!
# Deterministic component representatives and finite indexed subgraphs

Reachability is computed by the actual finite scan. The first reached vertex
in numeric order names a component. Vertex and edge lists use filters of
`List.finRange`, and inverse relabeling uses list index lookup.
-/

@[expose] public section

namespace WeightedMIS.ComputedComponents

open WeightedMIS.Incidence WeightedMIS.GraphSearch WeightedMIS.ShortestPath

variable {n m : ℕ} (left right : Fin m → Fin n)

theorem adjacent_reachable {a b : Fin n}
    (h : Adjacent left right (List.finRange m) a b) : Reachable left right a b := by
  obtain ⟨e, he⟩ := (adjacent_iff left right _ (fun e => List.mem_finRange e) a b).mp h
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨1, .forward e rfl (.nil _)⟩
  · exact ⟨1, .backward e rfl (.nil _)⟩

theorem route_reachable {a b : Fin n} (path : List (Fin n × Fin n))
    (hp : IsWalk Prod.fst Prod.snd a b path)
    (he : ∀ e ∈ path, Adjacent left right (List.finRange m) e.1 e.2) :
    Reachable left right a b := by
  induction path generalizing a with
  | nil =>
    change a = b at hp
    subst b
    exact reachable_refl left right a
  | cons e path ih =>
    have first := adjacent_reachable left right (he e List.mem_cons_self)
    have last := ih hp.2 (fun f hf => he f (List.mem_cons_of_mem e hf))
    rw [hp.1] at first
    exact reachable_trans left right first last

def routes (root : Fin n) := search left right (List.finRange m) (List.finRange n) root

theorem seen_iff_reachable (root v : Fin n) :
    v ∈ (routes left right root).seen ↔ Reachable left right root v := by
  have hs := MaxFlowReach.search_spec (Adjacent left right (List.finRange m))
    (List.finRange n) (fun v => List.mem_finRange v) root v
  change root ∈ (routes left right root).seen ∧ _ at hs
  constructor
  · intro hv
    have route := hs.2.1 hv
    exact route_reachable left right _ route.1 route.2.2
  · rintro ⟨length, path⟩
    exact closed_walk left right (List.finRange m) (fun e => List.mem_finRange e)
      _ hs.2.2 path hs.1

def firstReached (v : Fin n) : Option (Fin n) :=
  let reached := (routes left right v).seen
  (List.finRange n).find? (fun u => decide (u ∈ reached))

def representative (v : Fin n) : Fin n := (firstReached left right v).getD v

theorem firstReached_ne_none (v : Fin n) : firstReached left right v ≠ none := by
  intro he
  have hv := List.find?_eq_none.mp he v (List.mem_finRange v)
  have hs := (seen_iff_reachable left right v v).mpr (reachable_refl left right v)
  exact hv (by simpa only [decide_eq_true_eq] using hs)

theorem representative_reachable (v : Fin n) :
    Reachable left right v (representative left right v) := by
  cases he : firstReached left right v with
  | none => exact (firstReached_ne_none left right v he).elim
  | some u =>
    have hs := List.find?_some he
    have hu : u ∈ (routes left right v).seen := by simpa only [decide_eq_true_eq] using hs
    simpa [representative, he] using (seen_iff_reachable left right v u).mp hu

theorem representative_eq_of_reachable {v w : Fin n} (h : Reachable left right v w) :
    representative left right v = representative left right w := by
  have hs : (routes left right v).seen = (routes left right w).seen := by
    ext u
    rw [seen_iff_reachable, seen_iff_reachable]
    exact ⟨fun hu => reachable_trans left right (reachable_symm left right h) hu,
      fun hu => reachable_trans left right h hu⟩
  have hf : firstReached left right v = firstReached left right w := by
    simp only [firstReached, hs]
  cases he : firstReached left right v with
  | none => exact (firstReached_ne_none left right v he).elim
  | some u => simp [representative, ← hf, he]

theorem representative_eq_iff (v w : Fin n) :
    representative left right v = representative left right w ↔ Reachable left right v w := by
  constructor
  · intro he
    have hv := representative_reachable left right v
    have hw := representative_reachable left right w
    rw [he] at hv
    exact reachable_trans left right hv (reachable_symm left right hw)
  · exact representative_eq_of_reachable left right

theorem representative_idempotent (v : Fin n) :
    representative left right (representative left right v) = representative left right v :=
  (representative_eq_of_reachable left right (representative_reachable left right v)).symm

theorem representative_endpoints (e : Fin m) :
    representative left right (left e) = representative left right (right e) :=
  representative_eq_of_reachable left right ⟨1, .forward e rfl (.nil _)⟩

def roots : List (Fin n) :=
  (List.finRange n).filter (fun v => decide (representative left right v = v))

@[simp] theorem mem_roots (v : Fin n) :
    v ∈ roots left right ↔ representative left right v = v := by simp [roots]

theorem representative_mem_roots (v : Fin n) : representative left right v ∈ roots left right :=
  (mem_roots left right _).mpr (representative_idempotent left right v)

theorem roots_nodup : (roots left right).Nodup := (List.nodup_finRange n).filter _

theorem roots_length_le : (roots left right).length ≤ n := by
  simpa [roots] using List.length_filter_le
    (fun v => decide (representative left right v = v)) (List.finRange n)

def vertices (root : Fin n) : List (Fin n) :=
  (List.finRange n).filter (fun v => decide (v ∈ (routes left right root).seen))

def edges (root : Fin n) : List (Fin m) :=
  (List.finRange m).filter (fun e => decide (left e ∈ (routes left right root).seen))

@[simp] theorem mem_vertices (root v : Fin n) :
    v ∈ vertices left right root ↔ componentOf left right v = componentOf left right root := by
  simp only [vertices, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  rw [seen_iff_reachable, ← componentOf_eq_iff, eq_comm]

@[simp] theorem mem_edges (root : Fin n) (e : Fin m) :
    e ∈ edges left right root ↔ componentOf left right (left e) = componentOf left right root := by
  simp only [edges, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  rw [seen_iff_reachable, ← componentOf_eq_iff, eq_comm]

theorem vertices_nodup (root : Fin n) : (vertices left right root).Nodup :=
  (List.nodup_finRange n).filter _

theorem edges_nodup (root : Fin n) : (edges left right root).Nodup :=
  (List.nodup_finRange m).filter _

/-- Both directions are executable: list indexing and first-index search. -/
def vertexEquiv (root : Fin n) : Fin (vertices left right root).length ≃
    ComponentVertex left right (componentOf left right root) :=
  (List.Nodup.getEquiv _ (vertices_nodup left right root)).trans
    (Equiv.subtypeEquivRight (mem_vertices left right root))

def edgeEquiv (root : Fin n) : Fin (edges left right root).length ≃
    ComponentEdge left right (componentOf left right root) :=
  (List.Nodup.getEquiv _ (edges_nodup left right root)).trans
    (Equiv.subtypeEquivRight (mem_edges left right root))

def localLeft (root : Fin n) (e : Fin (edges left right root).length) :
    Fin (vertices left right root).length :=
  (vertexEquiv left right root).symm
    (componentLeft left right (componentOf left right root) (edgeEquiv left right root e))

def localRight (root : Fin n) (e : Fin (edges left right root).length) :
    Fin (vertices left right root).length :=
  (vertexEquiv left right root).symm
    (componentRight left right (componentOf left right root) (edgeEquiv left right root e))

@[simp] theorem vertexEquiv_localLeft (root : Fin n)
    (e : Fin (edges left right root).length) :
    vertexEquiv left right root (localLeft left right root e) =
      componentLeft left right (componentOf left right root) (edgeEquiv left right root e) :=
  Equiv.apply_symm_apply _ _

@[simp] theorem vertexEquiv_localRight (root : Fin n)
    (e : Fin (edges left right root).length) :
    vertexEquiv left right root (localRight left right root e) =
      componentRight left right (componentOf left right root) (edgeEquiv left right root e) :=
  Equiv.apply_symm_apply _ _

/-- Every indexed component has exactly the connectivity of its original edges. -/
theorem local_connected (root : Fin n) :
    Connected (localLeft left right root) (localRight left right root) :=
  connected_relabel (vertexEquiv left right root) (edgeEquiv left right root)
    (vertexEquiv_localLeft left right root) (vertexEquiv_localRight left right root)
    (component_connected left right _)

theorem vertices_length_le (root : Fin n) : (vertices left right root).length ≤ n := by
  simpa [vertices] using List.length_filter_le
    (fun v => decide (v ∈ (routes left right root).seen)) (List.finRange n)

theorem edges_length_le (root : Fin n) : (edges left right root).length ≤ m := by
  simpa [edges] using List.length_filter_le
    (fun e => decide (left e ∈ (routes left right root).seen)) (List.finRange m)

theorem vertices_length_pos (root : Fin n) : 0 < (vertices left right root).length := by
  exact List.length_pos_of_mem ((mem_vertices left right root root).mpr rfl)

/-- Numeric component indexing preserves the original graph adjacency exactly. -/
theorem local_adj (root : Fin n) (u v : Fin (vertices left right root).length) :
    EdgeTransport.Adj (localLeft left right root) (localRight left right root) u v ↔
      EdgeTransport.Adj (componentLeft left right (componentOf left right root))
        (componentRight left right (componentOf left right root))
        (vertexEquiv left right root u) (vertexEquiv left right root v) :=
  adj_relabel (vertexEquiv left right root) (edgeEquiv left right root)
    (vertexEquiv_localLeft left right root) (vertexEquiv_localRight left right root) u v

end WeightedMIS.ComputedComponents
