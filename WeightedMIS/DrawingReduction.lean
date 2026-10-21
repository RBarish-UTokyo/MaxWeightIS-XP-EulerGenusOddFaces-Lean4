module

public import WeightedMIS.DrawingEmbeddedReduction
public import WeightedMIS.DrawingComponents
public import WeightedMIS.OriginalReduction

/-!
# Mathematical reduction for disconnected and noncellular drawings

The graph itself has the retained edges and original vertices, including
isolates and loops. An auxiliary connected cellular decomposition witnesses
its ambient surface and actual complementary-region grouping. Only the
original drawing's total region-boundary parities enter the exponent.
The actual finite-edge preprocessing uses the original retained graph.
-/

@[expose] public section

namespace WeightedMIS.DrawingReduction

open scoped BigOperators
open EmbeddingFaces EmbeddedReduction Incidence DrawingComponents Persistence
open InducedComponents (Vertex edgeLeft edgeRight)

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1600000

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E] [DecidableEq F]
    {left right : E → V}

variable (M : CellularEmbedding left right F) (g : E → Prop) [DecidablePred g] (keep : V → Prop) [DecidablePred keep] (w : V → ℚ)

/-- Search certificates for an actual residual component, with codimension
bounded by the original embedding and its sharper orientable alternative. -/
def ComponentRecovery (q : Part left right g keep) : Prop :=
  ∃ hne : Nonempty {e : E // componentKeep left right g keep q e},
    coordinateCount (M.cappedDeletion (componentKeep left right g keep q) hne) ≤
        Parameters.exponent M.eulerGenus (M.sides.oddRegionCount g) ∧
      (∀ _O : M.sides.Orientation,
        coordinateCount (M.cappedDeletion (componentKeep left right g keep q) hne) ≤
          Parameters.orientableExponent M.eulerGenus (M.sides.oddRegionCount g)) ∧
      Recovery (M.cappedDeletion (componentKeep left right g keep q) hne) (fun v => w v.val)

/-- Every nonbipartite actual all-half residual component receives a genuine
search certificate; no residual matrix, optimizer, or genus bound is supplied. -/
theorem nonbipartite_component_recovery (hc : Connected left right)
    (ho : Optimal (EdgeTransport.Adj (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep))
      (fun v : Vertex keep => w v.val) (fun _ => 1 / 2))
    (q : Part left right g keep)
    (hnb : ¬Bipartite (componentLeft (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep) q)
      (componentRight (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep) q)) :
    ComponentRecovery M g keep w q := by
  classical
  have hne := nonempty_edges_of_nonbipartite hnb
  let hn := componentKeep_nonempty left right g keep q hne
  let ev := componentVertexEquiv left right g keep q hne
  have hopt := ComponentAssembly.component_half_optimal (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep)
    (fun v : Vertex keep => w v.val) ho q
  have ha := GraphRelabeling.half_optimal_pullback ev _ _
    (component_adj left right g keep q hne) (fun v : PartVertex left right g keep q => w v.val.val) hopt
  have hconn := DrawingComponents.component_connected left right g keep q hne
  have hnot := component_nonbipartite left right g keep q hne hnb
  refine ⟨hn, drawing_coordinateCount_le M g _ hn (componentKeep_sub left right g keep q) hc hconn hnot, ?_, ?_⟩
  · intro O
    exact drawing_coordinateCount_le_orientable M g _ hn (componentKeep_sub left right g keep q) hc hconn hnot O
  · exact exists_recovery (M.cappedDeletion _ hn) hconn hnot (fun v => w v.val) ha

/-- Each actual residual component has a maximum, using its bipartite color
classes or its constructed embedded search certificate as appropriate. -/
theorem component_maximum
    (ho : Optimal (EdgeTransport.Adj (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep))
      (fun v : Vertex keep => w v.val) (fun _ => 1 / 2))
    (cert : ∀ q : Part left right g keep,
      ¬Bipartite (componentLeft (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep) q)
        (componentRight (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep) q) →
      ComponentRecovery M g keep w q)
    (q : Part left right g keep) :
    ∃ I : Finset (PartVertex left right g keep q),
      Independent (EdgeTransport.Adj (componentLeft (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep) q)
        (componentRight (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep) q)) I ∧
      ∀ J, Independent (EdgeTransport.Adj
        (componentLeft (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep) q)
        (componentRight (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep) q)) J →
        weight (fun v : PartVertex left right g keep q => w v.val.val) J ≤
          weight (fun v : PartVertex left right g keep q => w v.val.val) I := by
  classical
  by_cases hb : Bipartite (componentLeft (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep) q)
      (componentRight (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep) q)
  · obtain ⟨color, hcolor⟩ := hb
    have hc' : ∀ u v, EdgeTransport.Adj
        (componentLeft (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep) q)
        (componentRight (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep) q) u v → color u ≠ color v := by
      rintro u v ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact hcolor e
      · exact (hcolor e).symm
    have hopt := ComponentAssembly.component_half_optimal
      (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep)
      (fun v : Vertex keep => w v.val) ho q
    have h := BipartiteRecovery.colorClass_maximum
      (EdgeTransport.Adj (componentLeft (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep) q)
        (componentRight (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep) q))
      (fun v : PartVertex left right g keep q => w v.val.val) color hc'
      hopt false
    exact ⟨_, h.1, h.2.2⟩
  · obtain ⟨hn, _, _, hr⟩ := cert q hb
    obtain ⟨I, hi, hm⟩ := OriginalReduction.recovery_maximum (M.cappedDeletion _ hn) (fun v => w v.val) hr
    let hne := nonempty_edges_of_nonbipartite hb
    let ev := componentVertexEquiv left right g keep q hne
    have h := GraphRelabeling.maximum_map ev _ _ (component_adj left right g keep q hne)
      (fun v : PartVertex left right g keep q => w v.val.val) I hi hm
    exact ⟨_, h⟩

/-- The actual all-half induced residual has a maximum obtained by combining
its component solutions, including any isolated vertices. -/
theorem induced_half_maximum (hc : Connected left right)
    (ho : Optimal (EdgeTransport.Adj (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep))
      (fun v : Vertex keep => w v.val) (fun _ => 1 / 2)) :
    (∀ q : Part left right g keep,
      ¬Bipartite (componentLeft (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep) q)
        (componentRight (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep) q) →
      ComponentRecovery M g keep w q) ∧
    ∃ J : Finset (Vertex keep), Independent (fun u v : Vertex keep => EdgeTransport.Adj (graphLeft left g) (graphRight right g) u.val v.val) J ∧
      ∀ K, Independent (fun u v : Vertex keep => EdgeTransport.Adj (graphLeft left g) (graphRight right g) u.val v.val) K →
        weight (fun v : Vertex keep => w v.val) K ≤ weight (fun v : Vertex keep => w v.val) J := by
  classical
  have cert := nonbipartite_component_recovery M g keep w hc ho
  refine ⟨cert, ?_⟩
  choose I hI hm using component_maximum M g keep w ho cert
  have hI' : ∀ q, Independent (fun u v : PartVertex left right g keep q =>
      EdgeTransport.Adj (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep) u.val v.val) (I q) := by
    intro q
    simpa only [Independent, ComponentAssembly.component_adj_iff] using hI q
  have hm' : ∀ q J, Independent (fun u v : PartVertex left right g keep q =>
      EdgeTransport.Adj (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep) u.val v.val) J →
      weight (fun v : PartVertex left right g keep q => w v.val.val) J ≤
        weight (fun v : PartVertex left right g keep q => w v.val.val) (I q) := by
    intro q J hJ
    exact hm q J (by simpa only [Independent, ComponentAssembly.component_adj_iff] using hJ)
  have h := ComponentAssembly.assemble_maximum
    (EdgeTransport.Adj (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep))
    (componentOf (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep))
    (ComponentAssembly.component_closed _ _) (fun v : Vertex keep => w v.val) I hI' hm'
  refine ⟨ComponentAssembly.assemble (componentOf (edgeLeft (graphLeft left g) (graphRight right g) keep) (edgeRight (graphLeft left g) (graphRight right g) keep)) I, ?_⟩
  simpa only [Independent, InducedComponents.adj_iff] using h

/-- Starting with the original embedded weighted graph, the actual max-flow
preprocessing, component reductions, persistence, and pruning yield an original
maximum and the original-parameter search certificates for every hard residual. -/
theorem drawing_weighted_reduction (hc : Connected left right)
    (nodes : List V) (complete : ∀ v, v ∈ nodes) :
    let z := OriginalReduction.preprocessingPoint (left := graphLeft left g) (right := graphRight right g) w nodes
    (∀ q : Part left right g (fun v => z v = 1 / 2),
      ¬Bipartite (componentLeft (edgeLeft (graphLeft left g) (graphRight right g) (fun v => z v = 1 / 2))
          (edgeRight (graphLeft left g) (graphRight right g) (fun v => z v = 1 / 2)) q)
        (componentRight (edgeLeft (graphLeft left g) (graphRight right g) (fun v => z v = 1 / 2))
          (edgeRight (graphLeft left g) (graphRight right g) (fun v => z v = 1 / 2)) q) →
      ComponentRecovery M g (fun v => z v = 1 / 2) (NegativeWeights.nonnegative w) q) ∧
    ∃ I : Finset V, Independent (EdgeTransport.Adj (graphLeft left g) (graphRight right g)) I ∧
      ∀ J, Independent (EdgeTransport.Adj (graphLeft left g) (graphRight right g)) J → weight w J ≤ weight w I := by
  classical
  let z := OriginalReduction.preprocessingPoint (left := graphLeft left g) (right := graphRight right g) w nodes
  have hz := OriginalReduction.preprocessingPoint_correct (left := graphLeft left g) (right := graphRight right g) w nodes complete
  have hr := InducedReduction.residual_optimal (EdgeTransport.Adj (graphLeft left g) (graphRight right g))
    (NegativeWeights.nonnegative w) z hz.2 hz.1
  have hr' : Optimal (EdgeTransport.Adj (edgeLeft (graphLeft left g) (graphRight right g) (fun v => z v = 1 / 2))
      (edgeRight (graphLeft left g) (graphRight right g) (fun v => z v = 1 / 2)))
      (fun v : Vertex (fun v => z v = 1 / 2) => NegativeWeights.nonnegative w v.val) (fun _ => 1 / 2) := by
    simpa only [Optimal, Feasible, InducedComponents.adj_iff] using hr
  obtain ⟨cert, J, hJ, hm⟩ := induced_half_maximum M g (fun v => z v = 1 / 2)
    (NegativeWeights.nonnegative w) hc hr'
  have h := InducedReduction.residual_maximum (EdgeTransport.Adj (graphLeft left g) (graphRight right g))
    (NegativeWeights.nonnegative w) z hz.2 hz.1 J hJ hm
  have hp := NegativeWeights.optimum_of_truncated (EdgeTransport.Adj (graphLeft left g) (graphRight right g)) w _ h.1 h.2.2
  exact ⟨cert, _, hp⟩

end WeightedMIS.DrawingReduction
