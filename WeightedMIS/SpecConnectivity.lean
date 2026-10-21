module

public import WeightedMIS.SpecFlags
public import WeightedMIS.RibbonCellular

/-!
# Connectivity of a statement-level closed-surface map

Statement connectivity (reflexive-transitive closure of adjacency) yields the
internal walk connectivity. With at least one edge, every vertex carries a
flag, so the internal cellular embedding of the map is available.
-/

@[expose] public section

namespace WeightedMIS.Spec

namespace Map

variable (A : Map) (hA : A.IsClosedSurface)

/-- Adjacency chains are genuine endpoint walks. -/
theorem walk_of_reflTransGen {u v : Fin A.vertices} (h : Relation.ReflTransGen A.Adjacent u v) :
    ∃ n, Incidence.Walk A.left A.right u v n := by
  induction h with
  | refl => exact ⟨0, .nil _⟩
  | tail _ hbc ih =>
      obtain ⟨n, p⟩ := ih
      obtain ⟨e, ⟨hl, hr⟩ | ⟨hl, hr⟩⟩ := hbc
      · subst hr
        exact ⟨n + 1, .forward e hl.symm p⟩
      · subst hl
        exact ⟨n + 1, .backward e hr.symm p⟩

include hA in
/-- The map's graph is connected in the internal sense. -/
theorem connected : Incidence.Connected A.left A.right :=
  fun u v => A.walk_of_reflTransGen (hA.connected u v)

include hA in
/-- Every vertex of a closed-surface map carries a flag. -/
theorem vertex_present (v : Fin A.vertices) :
    ∃ x : EmbeddingFaces.Flag (Fin A.edges), x.vertex A.left A.right = v := by
  let e0 : Fin A.edges := ⟨0, hA.has_edge⟩
  have h := hA.connected (A.left e0) v
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨b, _, e, ⟨_, hr⟩ | ⟨hl, _⟩⟩
  · exact ⟨⟨e0, false, false⟩, h.symm⟩
  · exact ⟨⟨e, false, true⟩, hr⟩
  · exact ⟨⟨e, false, false⟩, hl⟩

include hA in
theorem nonempty_edges : Nonempty (Fin A.edges) := ⟨⟨0, hA.has_edge⟩⟩

/-- The internal cellular embedding traced from the corner pairing of a
closed-surface map. Its face type is the internal set of ribbon circles. -/
noncomputable def cellular :
    EmbeddingFaces.CellularEmbedding A.left A.right (A.ribbon hA).FaceIndex :=
  (A.ribbon hA).toCellularEmbedding (A.ribbon_vertexLinks hA) (A.vertex_present hA)
    (A.nonempty_edges hA)

theorem cellular_sides : (A.cellular hA).sides = (A.ribbon hA).sidePairing := rfl

end Map

end WeightedMIS.Spec
