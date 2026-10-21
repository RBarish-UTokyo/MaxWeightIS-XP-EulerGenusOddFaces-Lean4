module

public import WeightedMIS.ComputedEmbeddedMatrices
public import WeightedMIS.ComputedOddRow
public import WeightedMIS.ComputedPathRecovery
public import WeightedMIS.SparseSearchLabeledWeights

/-!
# Executable search and recovery for a connected hard component

All data used by the output function are computed: facial columns, bounded
kernel-complement rows, the parity row, integral transport costs, the sparse
search trace, its edge-occurrence vector, and the integer threshold set.
The minimum-path and integer-existence theorems certify this output but do
not select any of its data.
-/

@[expose] public section

namespace WeightedMIS.ExecutableReduction

open EmbeddingFaces SidePairing Expanded Walks

variable {n m r d : ℕ} {left right : Fin m → Fin n}

/-- Original edge labels of the concrete sparse-search result. -/
def searchLabels (C : Fin m → Column (Fin r)) (W : Fin m → Fin d → ℤ)
    (π : Fin m → ZMod 2) (radius : ℕ) (cost : Fin m → ℕ) : List (Fin m) :=
  let graph := SparseSearchGraph.Labeled.graph id C W π radius cost
  let result := EfficientSearch.solve graph (SparseSearchGraph.nodeKey (start radius))
  match (EfficientSearch.recover result (SparseSearchGraph.nodeKey (finish radius))).1 with
  | none => []
  | some (_, trace) => SparseSearchGraph.Labeled.traceLabels id trace

/-- The returned labels belong to an actual minimum path for the computed
rational edge costs. Failure is excluded by a genuine witness path. -/
theorem searchLabels_minimum (left right : Fin m → Fin n)
    (weights : Fin n → ℚ) (hw : ∀ v, 0 ≤ weights v)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) weights (fun _ => 1 / 2))
    (C : Fin m → Column (Fin r)) (W : Fin m → Fin d → ℤ)
    (π : Fin m → ZMod 2) (radius : ℕ)
    (reachable : Nonempty (Path C W π radius (start radius) (finish radius))) :
    ∃ p : Path C W π radius (start radius) (finish radius),
      p.labels = searchLabels C W π radius
        (IntegerEdgeCosts.integerCost left right (List.finRange m) (List.finRange n) weights) ∧
      ∀ q : Path C W π radius (start radius) (finish radius),
        p.cost (EdgeAllocation.computedCost left right (List.finRange m) (List.finRange n) weights) ≤
          q.cost (EdgeAllocation.computedCost left right (List.finRange m) (List.finRange n) weights) := by
  obtain ⟨distance, trace, p, hout, hl, _hc, hmin⟩ :=
    SparseSearchGraph.Labeled.solve_computedCost_minimum id id (fun _ => rfl)
      left right (List.finRange m) (List.finRange n) (fun v => List.mem_finRange v)
      weights hw ho C W π radius (start radius) (finish radius) reachable
  refine ⟨p, ?_, hmin⟩
  simpa only [searchLabels, hout] using hl

/-- The computed integer odd row in the canonical numeric vertex/edge orders. -/
def parityRow (root : Fin n) : Fin m → ℤ :=
  ComputedOddRow.oddRow left right (List.finRange m) (List.finRange n) root

/-- Compute the actual sparse-search labels for the given ribbon graph. -/
def hardLabels (R : Ribbon left right) (weights : Fin n → ℚ) (root : Fin n) : List (Fin m) :=
  searchLabels (R.computedColumn (Flag.canonicalOrder m))
    (ComputedEmbeddedMatrices.globalColumn R) (fun e => (parityRow (left := left) (right := right) root e : ZMod 2)) (Fintype.card (Fin m))
    (IntegerEdgeCosts.integerCost left right (List.finRange m) (List.finRange n) weights)

/-- The deterministic independent-set output for a connected nonbipartite
all-half component. The function is total; correctness supplies its conditions. -/
def hardSolve (R : Ribbon left right) (weights : Fin n → ℚ) (root : Fin n) : Finset (Fin n) :=
  let π := parityRow (left := left) (right := right) root
  let labels := hardLabels R weights root
  let y := fun e => (projection labels e : ℤ)
  Slack.threshold (ComputedRecovery.recover left right (List.finRange m) (List.finRange n) root π y)

/-- The actual computed output is independent and maximum for the original
component weights; no matrices, parity row, edge costs, or minimum path are inputs. -/
theorem hardSolve_correct (R : Ribbon left right) (weights : Fin n → ℚ) (root : Fin n)
    (hc : Incidence.Connected left right) (hnb : ¬Incidence.Bipartite left right)
    (hw : ∀ v, 0 ≤ weights v)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) weights (fun _ => 1 / 2)) :
    Persistence.Independent (EdgeTransport.Adj left right) (hardSolve R weights root) ∧
      ∀ J, Persistence.Independent (EdgeTransport.Adj left right) J →
        Persistence.weight weights J ≤ Persistence.weight weights (hardSolve R weights root) := by
  let C := R.computedColumn (Flag.canonicalOrder m)
  let W := ComputedEmbeddedMatrices.globalColumn R
  let π := parityRow (left := left) (right := right) root
  let cost := EdgeAllocation.computedCost left right (List.finRange m) (List.finRange n) weights
  have hmat := ComputedEmbeddedMatrices.computed_matrices_spec R hc hnb
  have hπ : IntegerSlacks.OddRow left right root π :=
    ComputedOddRow.oddRow_correct left right (List.finRange m) (fun e => List.mem_finRange e)
      (List.finRange n) (fun v => List.mem_finRange v) root hc hnb
  have hcost := EdgeAllocation.computedCost_correct left right (List.finRange m)
    (fun e => List.mem_finRange e) (List.finRange n) (fun v => List.mem_finRange v) weights hw ho
  have hempty : Slack.Independent left right (∅ : Finset (Fin n)) := by intro e; simp
  obtain ⟨witness, _hw, _hc⟩ := Reduction.independent_set_has_path left right root hc C W
    hmat.2 hmat.1 π hπ cost ∅ hempty
  have hreach : Nonempty (Reduction.SearchPath C W π) := ⟨witness⟩
  obtain ⟨p, hl, hmin⟩ := searchLabels_minimum left right weights hw ho C W
    (fun e => (π e : ZMod 2)) (Fintype.card (Fin m)) hreach
  have hlabels : p.labels = hardLabels R weights root := hl
  have hrec := ComputedRecovery.minimum_path_maximum left right (List.finRange m)
    (fun e => List.mem_finRange e) (List.finRange n) (fun v => List.mem_finRange v) root hc
    C W hmat.2 hmat.1 π hπ cost hcost.1 weights hcost.2 p hmin
  simpa only [hlabels, hardSolve] using hrec

end WeightedMIS.ExecutableReduction
