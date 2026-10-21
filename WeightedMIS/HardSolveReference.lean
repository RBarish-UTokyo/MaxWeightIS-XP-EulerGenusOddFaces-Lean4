module

public import WeightedMIS.ExecutableReduction
public import WeightedMIS.RegisterPotentialRoute
public import WeightedMIS.SearchHistogramProjection

/-!
# Reference form of the hard-component output

`ExecutableReduction.hardSolve` thresholds the integer potential recovered
from the projected search labels. This file restates it through an explicit
threshold-from-counts reference, proves that the root numerator is even under
the hypotheses of `hardSolve_correct`, bounds the total label count by the
sparse adjacency size, and identifies potential propagation on reverse stored
routes with `GraphSearch.propagate` on forward vertex routes.
-/

@[expose] public section

namespace WeightedMIS.HardSolveReference

open scoped BigOperators
open WeightedMIS.EfficientSearch WeightedMIS.SparseSearchGraph WeightedMIS.Expanded
open WeightedMIS.Walks WeightedMIS.ExecutableReduction

/-! ## Threshold from counts -/

section Threshold

variable {n m : ℕ}

/-- Vertices with value at least one, in increasing numeric order. -/
def thresholdList (x : Fin n → ℤ) : List (Fin n) :=
  (List.finRange n).filter (fun v => decide (1 ≤ x v))

theorem mem_thresholdList (x : Fin n → ℤ) (v : Fin n) :
    v ∈ thresholdList x ↔ 1 ≤ x v := by
  simp [thresholdList]

theorem threshold_eq_toFinset (x : Fin n → ℤ) :
    Slack.threshold x = (thresholdList x).toFinset := by
  ext v
  simp [Slack.threshold, mem_thresholdList]

/-- The recovery and threshold for given parity row and edge counts. -/
def thresholdFrom (left right : Fin m → Fin n) (root : Fin n) (π y : Fin m → ℤ) :
    Finset (Fin n) :=
  Slack.threshold (ComputedRecovery.recover left right (List.finRange m) (List.finRange n) root π y)

/-- The numerator halved by the root-value computation. -/
def rootNumerator (π y : Fin m → ℤ) : ℤ := 1 - ∑ e, π e * y e

theorem rootValue_eq_div (π y : Fin m → ℤ) :
    ComputedRecovery.rootValue π y = rootNumerator π y / 2 := rfl

end Threshold

section Hard

variable {n m : ℕ} {left right : Fin m → Fin n}

/-- Original-edge counts of the actual search labels. -/
def hardCounts (R : EmbeddingFaces.Ribbon left right) (weights : Fin n → ℚ) (root : Fin n) :
    Fin m → ℤ :=
  fun e => (projection (hardLabels R weights root) e : ℤ)

theorem hardSolve_eq (R : EmbeddingFaces.Ribbon left right) (weights : Fin n → ℚ) (root : Fin n) :
    hardSolve R weights root =
      thresholdFrom left right root (parityRow (left := left) (right := right) root)
        (hardCounts R weights root) := rfl

/-- Under the correctness hypotheses, the edge counts are the slacks of an
integer vertex vector. -/
theorem hardCounts_realized (R : EmbeddingFaces.Ribbon left right) (weights : Fin n → ℚ)
    (root : Fin n) (hc : Incidence.Connected left right) (hnb : ¬Incidence.Bipartite left right)
    (hw : ∀ v, 0 ≤ weights v)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) weights (fun _ => 1 / 2)) :
    ∃ x : Fin n → ℤ, ∀ e, x (left e) + x (right e) = 1 - hardCounts R weights root e := by
  let C := R.computedColumn (EmbeddingFaces.Flag.canonicalOrder m)
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
  obtain ⟨x, _hf, hs, _⟩ := Reduction.minimum_path_recovers left right root hc C W hmat.2 hmat.1
    π hπ cost hcost.1 p hmin
  refine ⟨x, fun e => ?_⟩
  have h := hs e
  rw [hlabels] at h
  unfold Slack.slack at h
  change x (left e) + x (right e) = 1 - (projection (hardLabels R weights root) e : ℤ)
  omega

/-- Any realizing vector makes the root numerator exactly twice its root value. -/
theorem rootNumerator_eq_two_mul (root : Fin n) (π y : Fin m → ℤ)
    (hπ : IntegerSlacks.OddRow left right root π) (x : Fin n → ℤ)
    (hx : ∀ e, x (left e) + x (right e) = 1 - y e) :
    rootNumerator π y = 2 * x root := by
  have hq := hπ (fun v => (x v : ℚ))
  have he : (∑ e, π e * (x (left e) + x (right e))) = 2 * x root := by
    exact_mod_cast hq
  simp_rw [hx, mul_sub, mul_one] at he
  rw [Finset.sum_sub_distrib, IntegerSlacks.odd_row_sum left right root π hπ] at he
  unfold rootNumerator
  omega

/-- The root numerator of the actual hard-component data is even, and it is
twice the computed root value. -/
theorem hardLabels_even (R : EmbeddingFaces.Ribbon left right) (weights : Fin n → ℚ)
    (root : Fin n) (hc : Incidence.Connected left right) (hnb : ¬Incidence.Bipartite left right)
    (hw : ∀ v, 0 ≤ weights v)
    (ho : Persistence.Optimal (EdgeTransport.Adj left right) weights (fun _ => 1 / 2)) :
    rootNumerator (parityRow (left := left) (right := right) root) (hardCounts R weights root) =
      2 * ComputedRecovery.rootValue (parityRow (left := left) (right := right) root)
        (hardCounts R weights root) := by
  obtain ⟨x, hx⟩ := hardCounts_realized R weights root hc hnb hw ho
  have hπ : IntegerSlacks.OddRow left right root (parityRow (left := left) (right := right) root) :=
    ComputedOddRow.oddRow_correct left right (List.finRange m) (fun e => List.mem_finRange e)
      (List.finRange n) (fun v => List.mem_finRange v) root hc hnb
  have h := rootNumerator_eq_two_mul root _ _ hπ x hx
  rw [rootValue_eq_div, h]
  omega

end Hard

/-! ## Total label count -/

section Counts

variable {r m d : ℕ}

theorem projection_sum_eq_length (l : List (Fin m)) : ∑ e, projection l e = l.length := by
  have h := sum_mul_projection (R := ℕ) l (fun _ => 1)
  simpa using h

theorem recover_some {Label : Type*} {vbits cbits : ℕ} {result : Result Label vbits cbits}
    {target : Bits vbits} {distance : Bits cbits} {trace : Trace Label vbits cbits}
    (h : (recover result target).1 = some (distance, trace)) :
    ∃ path, (target, (distance, path)) ∈ result.settled.elements ∧ trace = path.reverse := by
  unfold recover at h
  cases hl : (Radix.lookup target result.settled).1 with
  | nil => simp [hl] at h
  | cons x xs =>
    obtain ⟨distance0, path⟩ := x
    simp only [hl, Option.some.injEq, Prod.mk.injEq, reverseCount_value, List.append_nil] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨path, (Radix.mem_lookup _ _ _).mp ?_, rfl⟩
    rw [hl]
    exact List.mem_cons_self

/-- The search labels are no more numerous than the sparse adjacency entries
plus one. -/
theorem searchLabels_length_le (C : Fin m → Column (Fin r)) (W : Fin m → Fin d → ℤ)
    (π : Fin m → ZMod 2) (radius : ℕ) (cost : Fin m → ℕ) :
    (searchLabels C W π radius cost).length ≤ entryBound r m d radius + 1 := by
  unfold searchLabels
  dsimp only
  cases h : (recover (solve (Labeled.graph id C W π radius cost) (nodeKey (start radius)))
      (nodeKey (finish radius))).1 with
  | none => simp
  | some x =>
    obtain ⟨distance, trace⟩ := x
    obtain ⟨path, hm, rfl⟩ := recover_some h
    have hd := solve_stored_depth (Labeled.graph id C W π radius cost) (nodeKey (start radius)) _ hm
    have hg := Labeled.graph_size_le id C W π radius cost
    have hf : (Labeled.traceLabels id path.reverse).length ≤ path.reverse.length :=
      List.length_filterMap_le _ _
    simp only [List.length_reverse] at hf
    change path.length < _ at hd
    simp only
    omega

theorem projection_sum_le (C : Fin m → Column (Fin r)) (W : Fin m → Fin d → ℤ)
    (π : Fin m → ZMod 2) (radius : ℕ) (cost : Fin m → ℕ) :
    ∑ e, projection (searchLabels C W π radius cost) e ≤ entryBound r m d radius + 1 := by
  rw [projection_sum_eq_length]
  exact searchLabels_length_le C W π radius cost

theorem projection_le (C : Fin m → Column (Fin r)) (W : Fin m → Fin d → ℤ)
    (π : Fin m → ZMod 2) (radius : ℕ) (cost : Fin m → ℕ) (e : Fin m) :
    projection (searchLabels C W π radius cost) e ≤ entryBound r m d radius + 1 :=
  (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)).trans
    (projection_sum_le C W π radius cost)

end Counts

/-! ## Reverse stored routes -/

section Routes

variable {V E : Type*} [Fintype V] [DecidableEq V] {vb b : ℕ}

theorem propagate_append (l₁ l₂ : List (ResidualWords.Arc vb b)) (initial : ℤ) :
    RegisterPotentialRoute.propagate (l₁ ++ l₂) initial =
      RegisterPotentialRoute.propagate l₁ (RegisterPotentialRoute.propagate l₂ initial) := by
  induction l₁ with
  | nil => rfl
  | cons a rest ih => simp only [List.cons_append, RegisterPotentialRoute.propagate, ih]

/-- An arc stores the count of the first original edge joining a route pair. -/
def Carries (left right : E → V) (edges : List E) (y : E → ℤ)
    (arc : ResidualWords.Arc vb b) (pair : V × V) : Prop :=
  ∃ e, GraphSearch.edgeBetween left right edges pair.1 pair.2 = some e ∧
    (arc.capacity.value : ℤ) = y e

omit [Fintype V] in
/-- Recursion on a reverse arc list, head edge last, equals forward
propagation on the corresponding vertex route. -/
theorem propagate_reverse (left right : E → V) (edges : List E) (y : E → ℤ)
    (arcs : List (ResidualWords.Arc vb b)) (route : List (V × V))
    (h : List.Forall₂ (Carries left right edges y) arcs.reverse route) (initial : ℤ) :
    RegisterPotentialRoute.propagate arcs initial =
      GraphSearch.propagate left right edges y route initial := by
  rw [← List.reverse_reverse arcs]
  generalize arcs.reverse = forward at h
  induction h generalizing initial with
  | nil => rfl
  | @cons arc pair restArcs restRoute hc _ ih =>
    obtain ⟨e, he, hcap⟩ := hc
    rw [List.reverse_cons, propagate_append]
    simp only [RegisterPotentialRoute.propagate, GraphSearch.propagate, GraphSearch.edgeSum, he,
      hcap]
    rw [ih]

omit [Fintype V] in
/-- A map-form instance: encode each forward route pair as an arc, then store
the encoded list in reverse. -/
theorem propagate_map_reverse (left right : E → V) (edges : List E) (y : E → ℤ)
    (encode : V × V → ResidualWords.Arc vb b) (route : List (V × V))
    (h : ∀ a ∈ route, Carries left right edges y (encode a) a) (initial : ℤ) :
    RegisterPotentialRoute.propagate (route.map encode).reverse initial =
      GraphSearch.propagate left right edges y route initial := by
  apply propagate_reverse
  rw [List.reverse_reverse, List.forall₂_map_left_iff]
  induction route with
  | nil => exact .nil
  | cons a rest ih =>
    exact .cons (h a List.mem_cons_self) (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- Reverse stored routes of the actual route table propagate the computed
root value to the executable recovery value. -/
theorem propagate_recover (left right : E → V) (edges : List E) (nodes : List V) (root : V)
    [Fintype E] (π y : E → ℤ) (v : V) (arcs : List (ResidualWords.Arc vb b))
    (h : List.Forall₂ (Carries left right edges y) arcs.reverse
      ((GraphSearch.search left right edges nodes root).route v)) :
    RegisterPotentialRoute.propagate arcs (ComputedRecovery.rootValue π y) =
      ComputedRecovery.recover left right edges nodes root π y v := by
  rw [propagate_reverse left right edges y arcs _ h]
  rfl

end Routes

end WeightedMIS.HardSolveReference
