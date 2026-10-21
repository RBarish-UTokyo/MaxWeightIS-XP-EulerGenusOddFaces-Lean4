module

public import WeightedMIS.ExecutableReduction
public import WeightedMIS.ExecutableParity

/-!
# An executable solver for every connected all-half component

The actual parity search selects either the sparse embedded search or the
computed bipartite color class. The canonical first vertex is the root. The
empty indexed graph returns the empty set, so the solver is total.
-/

@[expose] public section

namespace WeightedMIS.ExecutableReduction

open EmbeddingFaces

variable {n m : ℕ} {left right : Fin m → Fin n}

/-- Actual parity detection chooses the algorithm used on a nonempty component. -/
def halfSolve (R : Ribbon left right) (weights : Fin n → ℚ) (root : Fin n) : Finset (Fin n) :=
  if (root, true) ∈ (ComputedOddRow.paritySearch left right (List.finRange m) (List.finRange n) root).seen then
    hardSolve R weights root
  else
    BipartiteRecovery.colorClass
      (BipartiteRecovery.coloring left right (List.finRange m) (List.finRange n) root) false

/-- Both actual branch outputs are maximum independent sets. -/
theorem halfSolve_correct (R : Ribbon left right) (weights : Fin n → ℚ) (root : Fin n)
    (hc : Incidence.Connected left right) (hw : ∀ v, 0 ≤ weights v)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) weights (fun _ => 1 / 2)) :
    Persistence.Independent (EdgeTransport.Adj left right) (halfSolve R weights root) ∧
      ∀ J, Persistence.Independent (EdgeTransport.Adj left right) J →
        Persistence.weight weights J ≤ Persistence.weight weights (halfSolve R weights root) := by
  unfold halfSolve
  split_ifs with hseen
  · exact hardSolve_correct R weights root hc
      (ComputedOddRow.nonbipartite_of_seen left right (List.finRange m) (List.finRange n)
        (fun v => List.mem_finRange v) root hseen) hw ho
  · exact BipartiteRecovery.searched_color_maximum left right (List.finRange m)
      (fun e => List.mem_finRange e) (List.finRange n) (fun v => List.mem_finRange v) root hc hseen weights ho

/-- A total solver with the canonical numeric root, including the empty graph. -/
def connectedSolve (R : Ribbon left right) (weights : Fin n → ℚ) : Finset (Fin n) :=
  if hn : 0 < n then halfSolve R weights ⟨0, hn⟩ else ∅

/-- The canonical-root solver returns a maximum for every connected all-half
input, including isolated vertices and the empty graph. -/
theorem connectedSolve_correct (R : Ribbon left right) (weights : Fin n → ℚ)
    (hc : Incidence.Connected left right) (hw : ∀ v, 0 ≤ weights v)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) weights (fun _ => 1 / 2)) :
    Persistence.Independent (EdgeTransport.Adj left right) (connectedSolve R weights) ∧
      ∀ J, Persistence.Independent (EdgeTransport.Adj left right) J →
        Persistence.weight weights J ≤ Persistence.weight weights (connectedSolve R weights) := by
  unfold connectedSolve
  split_ifs with hn
  · exact halfSolve_correct R weights ⟨0, hn⟩ hc hw ho
  · have hz : n = 0 := by omega
    subst n
    constructor
    · intro u; exact Fin.elim0 u
    · intro J _
      have he : J = ∅ := by ext v; exact Fin.elim0 v
      rw [he]

end WeightedMIS.ExecutableReduction
