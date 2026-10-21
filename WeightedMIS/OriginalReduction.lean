module

public import WeightedMIS.DeletedEmbeddedReduction
public import WeightedMIS.InducedComponents
public import WeightedMIS.EndpointRelabeling
public import WeightedMIS.GraphRelabeling
public import WeightedMIS.ComponentAssembly
public import WeightedMIS.BipartiteRecovery
public import WeightedMIS.MaxFlowPreprocessing
public import WeightedMIS.NegativeWeights

/-!
# Mathematical assembly from the original weighted embedded graph

The concrete maximum-flow preprocessing supplies the half-integral optimum.
The actual induced residual graph is partitioned by edge-walk components.
Bipartite components use their color classes; nonbipartite components use the
constructed capped embedding and bounded-signature search. Persistence and
negative-weight pruning recover a maximum for the original rational weights.
The parameter certificates refer to the original cellular embedding.
-/

@[expose] public section

namespace WeightedMIS.OriginalReduction

open scoped BigOperators
open EmbeddingFaces EmbeddedReduction Incidence InducedComponents Persistence

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 1600000

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E] [DecidableEq F]
    {left right : E → V}

theorem independent_iff (I : Finset V) :
    Slack.Independent left right I ↔ Independent (EdgeTransport.Adj left right) I := by
  constructor
  · intro h u v huv hu hv
    obtain ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := huv
    · exact h e ⟨hu, hv⟩
    · exact h e ⟨hv, hu⟩
  · intro h e he
    exact h (left e) (right e) ⟨e, Or.inl ⟨rfl, rfl⟩⟩ he.1 he.2

/-- The finite search certificate supplies an actual endpoint-graph maximum. -/
theorem recovery_maximum (M : CellularEmbedding left right F) (w : V → ℚ) (h : Recovery M w) :
    ∃ I : Finset V, Independent (EdgeTransport.Adj left right) I ∧
      ∀ J, Independent (EdgeTransport.Adj left right) J → weight w J ≤ weight w I := by
  obtain ⟨C, W, cost, _, _, _, _, _, root, π, _, path, _, _, x, _, _, hi, hm, _⟩ := h
  refine ⟨Slack.threshold x, independent_iff _ |>.mp hi, ?_⟩
  intro J hJ
  simpa only [InducedReduction.weight_eq_sum] using hm J ((independent_iff J).mpr hJ)

variable (M : CellularEmbedding left right F) (keep : V → Prop) [DecidablePred keep] (w : V → ℚ)

/-- Search certificates for an actual residual component, with codimension
bounded by the original embedding and its sharper orientable alternative. -/
def ComponentRecovery (q : Part left right keep) : Prop :=
  ∃ hne : Nonempty {e : E // componentKeep left right keep q e},
    coordinateCount (M.cappedDeletion (componentKeep left right keep q) hne) ≤
        Parameters.exponent M.eulerGenus (oddFaceCount M) ∧
      (∀ _O : M.sides.Orientation,
        coordinateCount (M.cappedDeletion (componentKeep left right keep q) hne) ≤
          Parameters.orientableExponent M.eulerGenus (oddFaceCount M)) ∧
      Recovery (M.cappedDeletion (componentKeep left right keep q) hne) (fun v => w v.val)

/-- Every nonbipartite actual all-half residual component receives a genuine
search certificate; no residual matrix, optimizer, or genus bound is supplied. -/
theorem nonbipartite_component_recovery (hc : Connected left right)
    (ho : Optimal (EdgeTransport.Adj (edgeLeft left right keep) (edgeRight left right keep))
      (fun v : Vertex keep => w v.val) (fun _ => 1 / 2))
    (q : Part left right keep)
    (hnb : ¬Bipartite (componentLeft (edgeLeft left right keep) (edgeRight left right keep) q)
      (componentRight (edgeLeft left right keep) (edgeRight left right keep) q)) :
    ComponentRecovery M keep w q := by
  classical
  have hne := nonempty_edges_of_nonbipartite hnb
  let hn := componentKeep_nonempty left right keep q hne
  let ev := activeComponentEquiv left right keep q hne
  have hopt := ComponentAssembly.component_half_optimal (edgeLeft left right keep) (edgeRight left right keep)
    (fun v : Vertex keep => w v.val) ho q
  have ha := GraphRelabeling.half_optimal_pullback ev _ _
    (activeComponent_adj left right keep q hne) (fun v : PartVertex left right keep q => w v.val.val) hopt
  have hconn := activeComponent_connected left right keep q hne
  have hnot := activeComponent_nonbipartite left right keep q hne hnb
  refine ⟨hn, deleted_coordinateCount_le M _ hn hc hconn hnot, ?_, ?_⟩
  · intro O
    exact deleted_coordinateCount_le_orientable M _ hn hc hconn hnot O
  · exact exists_recovery (M.cappedDeletion _ hn) hconn hnot (fun v => w v.val) ha

/-- Each actual residual component has a maximum, using its bipartite color
classes or its constructed embedded search certificate as appropriate. -/
theorem component_maximum
    (ho : Optimal (EdgeTransport.Adj (edgeLeft left right keep) (edgeRight left right keep))
      (fun v : Vertex keep => w v.val) (fun _ => 1 / 2))
    (cert : ∀ q : Part left right keep,
      ¬Bipartite (componentLeft (edgeLeft left right keep) (edgeRight left right keep) q)
        (componentRight (edgeLeft left right keep) (edgeRight left right keep) q) →
      ComponentRecovery M keep w q)
    (q : Part left right keep) :
    ∃ I : Finset (PartVertex left right keep q),
      Independent (EdgeTransport.Adj (componentLeft (edgeLeft left right keep) (edgeRight left right keep) q)
        (componentRight (edgeLeft left right keep) (edgeRight left right keep) q)) I ∧
      ∀ J, Independent (EdgeTransport.Adj
        (componentLeft (edgeLeft left right keep) (edgeRight left right keep) q)
        (componentRight (edgeLeft left right keep) (edgeRight left right keep) q)) J →
        weight (fun v : PartVertex left right keep q => w v.val.val) J ≤
          weight (fun v : PartVertex left right keep q => w v.val.val) I := by
  classical
  by_cases hb : Bipartite (componentLeft (edgeLeft left right keep) (edgeRight left right keep) q)
      (componentRight (edgeLeft left right keep) (edgeRight left right keep) q)
  · obtain ⟨color, hcolor⟩ := hb
    have hc' : ∀ u v, EdgeTransport.Adj
        (componentLeft (edgeLeft left right keep) (edgeRight left right keep) q)
        (componentRight (edgeLeft left right keep) (edgeRight left right keep) q) u v → color u ≠ color v := by
      rintro u v ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact hcolor e
      · exact (hcolor e).symm
    have hopt := ComponentAssembly.component_half_optimal
      (edgeLeft left right keep) (edgeRight left right keep)
      (fun v : Vertex keep => w v.val) ho q
    have h := BipartiteRecovery.colorClass_maximum
      (EdgeTransport.Adj (componentLeft (edgeLeft left right keep) (edgeRight left right keep) q)
        (componentRight (edgeLeft left right keep) (edgeRight left right keep) q))
      (fun v : PartVertex left right keep q => w v.val.val) color hc'
      hopt false
    exact ⟨_, h.1, h.2.2⟩
  · obtain ⟨hn, _, _, hr⟩ := cert q hb
    obtain ⟨I, hi, hm⟩ := recovery_maximum (M.cappedDeletion _ hn) (fun v => w v.val) hr
    let hne := nonempty_edges_of_nonbipartite hb
    let ev := activeComponentEquiv left right keep q hne
    have h := GraphRelabeling.maximum_map ev _ _ (activeComponent_adj left right keep q hne)
      (fun v : PartVertex left right keep q => w v.val.val) I hi hm
    exact ⟨_, h⟩

/-- The actual all-half induced residual has a maximum obtained by combining
its component solutions, including any isolated vertices. -/
theorem induced_half_maximum (hc : Connected left right)
    (ho : Optimal (EdgeTransport.Adj (edgeLeft left right keep) (edgeRight left right keep))
      (fun v : Vertex keep => w v.val) (fun _ => 1 / 2)) :
    (∀ q : Part left right keep,
      ¬Bipartite (componentLeft (edgeLeft left right keep) (edgeRight left right keep) q)
        (componentRight (edgeLeft left right keep) (edgeRight left right keep) q) →
      ComponentRecovery M keep w q) ∧
    ∃ J : Finset (Vertex keep), Independent (fun u v : Vertex keep => EdgeTransport.Adj left right u.val v.val) J ∧
      ∀ K, Independent (fun u v : Vertex keep => EdgeTransport.Adj left right u.val v.val) K →
        weight (fun v : Vertex keep => w v.val) K ≤ weight (fun v : Vertex keep => w v.val) J := by
  classical
  have cert := nonbipartite_component_recovery M keep w hc ho
  refine ⟨cert, ?_⟩
  choose I hI hm using component_maximum M keep w ho cert
  have hI' : ∀ q, Independent (fun u v : PartVertex left right keep q =>
      EdgeTransport.Adj (edgeLeft left right keep) (edgeRight left right keep) u.val v.val) (I q) := by
    intro q
    simpa only [Independent, ComponentAssembly.component_adj_iff] using hI q
  have hm' : ∀ q J, Independent (fun u v : PartVertex left right keep q =>
      EdgeTransport.Adj (edgeLeft left right keep) (edgeRight left right keep) u.val v.val) J →
      weight (fun v : PartVertex left right keep q => w v.val.val) J ≤
        weight (fun v : PartVertex left right keep q => w v.val.val) (I q) := by
    intro q J hJ
    exact hm q J (by simpa only [Independent, ComponentAssembly.component_adj_iff] using hJ)
  have h := ComponentAssembly.assemble_maximum
    (EdgeTransport.Adj (edgeLeft left right keep) (edgeRight left right keep))
    (componentOf (edgeLeft left right keep) (edgeRight left right keep))
    (ComponentAssembly.component_closed _ _) (fun v : Vertex keep => w v.val) I hI' hm'
  refine ⟨ComponentAssembly.assemble (componentOf (edgeLeft left right keep) (edgeRight left right keep)) I, ?_⟩
  simpa only [Independent, InducedComponents.adj_iff] using h

/-- The concrete preprocessing vector for arbitrary original rational weights. -/
def preprocessingPoint (nodes : List V) : V → ℚ :=
  letI := endpointAdjDecidable (leftV := left) (rightV := right)
  MaxFlowPreprocessing.lpPoint (EdgeTransport.Adj left right) nodes (NegativeWeights.nonnegative w)

/-- The actual finite-edge adjacency decision and max-flow preprocessing
return a genuine half-integral optimum of the truncated-weight relaxation. -/
theorem preprocessingPoint_correct (nodes : List V) (complete : ∀ v, v ∈ nodes) :
    HalfIntegral (preprocessingPoint (left := left) (right := right) w nodes) ∧
      Optimal (EdgeTransport.Adj left right) (NegativeWeights.nonnegative w)
        (preprocessingPoint (left := left) (right := right) w nodes) := by
  exact @MaxFlowPreprocessing.lpPoint_correct V _ _ (EdgeTransport.Adj left right)
    (endpointAdjDecidable (leftV := left) (rightV := right))
    (EdgeTransport.adj_symmetric left right) nodes complete (NegativeWeights.nonnegative w)
    (NegativeWeights.nonnegative_nonnegative w)

/-- Starting with the original embedded weighted graph, the actual max-flow
preprocessing, component reductions, persistence, and pruning yield an original
maximum and the original-parameter search certificates for every hard residual. -/
theorem original_weighted_reduction (hc : Connected left right)
    (nodes : List V) (complete : ∀ v, v ∈ nodes) :
    let z := preprocessingPoint (left := left) (right := right) w nodes
    (∀ q : Part left right (fun v => z v = 1 / 2),
      ¬Bipartite (componentLeft (edgeLeft left right (fun v => z v = 1 / 2))
          (edgeRight left right (fun v => z v = 1 / 2)) q)
        (componentRight (edgeLeft left right (fun v => z v = 1 / 2))
          (edgeRight left right (fun v => z v = 1 / 2)) q) →
      ComponentRecovery M (fun v => z v = 1 / 2) (NegativeWeights.nonnegative w) q) ∧
    ∃ I : Finset V, Independent (EdgeTransport.Adj left right) I ∧
      ∀ J, Independent (EdgeTransport.Adj left right) J → weight w J ≤ weight w I := by
  classical
  let z := preprocessingPoint (left := left) (right := right) w nodes
  have hz := preprocessingPoint_correct (left := left) (right := right) w nodes complete
  have hr := InducedReduction.residual_optimal (EdgeTransport.Adj left right)
    (NegativeWeights.nonnegative w) z hz.2 hz.1
  have hr' : Optimal (EdgeTransport.Adj (edgeLeft left right (fun v => z v = 1 / 2))
      (edgeRight left right (fun v => z v = 1 / 2)))
      (fun v : Vertex (fun v => z v = 1 / 2) => NegativeWeights.nonnegative w v.val) (fun _ => 1 / 2) := by
    simpa only [Optimal, Feasible, InducedComponents.adj_iff] using hr
  obtain ⟨cert, J, hJ, hm⟩ := induced_half_maximum M (fun v => z v = 1 / 2)
    (NegativeWeights.nonnegative w) hc hr'
  have h := InducedReduction.residual_maximum (EdgeTransport.Adj left right)
    (NegativeWeights.nonnegative w) z hz.2 hz.1 J hJ hm
  have hp := NegativeWeights.optimum_of_truncated (EdgeTransport.Adj left right) w _ h.1 h.2.2
  exact ⟨cert, _, hp⟩

end WeightedMIS.OriginalReduction
