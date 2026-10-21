module

public import WeightedMIS.ExecutableReduction
public import WeightedMIS.EfficientSearchRelabel
public import WeightedMIS.EfficientSearchHistogram

/-!
# Histograms of stored labels are original-edge projections

The compiled search runs on the sparse graph whose labels are stored pointers
`η label`. Its returned reverse path is the relabelled reverse path of the
search on the graph labelled by `Option (Fin m)` itself, which defines
`ExecutableReduction.searchLabels`. Counting the binary keys of the stored
labels on that path therefore gives exactly the projection of the search
labels onto each original edge, provided distinct labels have distinct keys.
-/

@[expose] public section

namespace WeightedMIS.SearchHistogramProjection

open WeightedMIS.EfficientSearch WeightedMIS.SparseSearchGraph WeightedMIS.Expanded
open WeightedMIS.Walks

variable {m r d : ℕ}

/-- Canonical label keys: an original edge is keyed by its index and the
connector label by `m`. -/
def edgeKey (G : ℕ) : Option (Fin m) → Bits G
  | some e => encodeBits G e.val
  | none => encodeBits G m

theorem edgeKey_injective {G : ℕ} (hm : m < 2 ^ G) : Function.Injective (@edgeKey m G) := by
  intro a b h
  have hv := congrArg Bits.value h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      simp only [edgeKey, encodeBits_value _ _ hm,
        encodeBits_value _ _ (b.isLt.trans hm)] at hv
      exact absurd hv.symm (Nat.ne_of_lt b.isLt)
  | some a =>
    cases b with
    | none =>
      simp only [edgeKey, encodeBits_value _ _ hm,
        encodeBits_value _ _ (a.isLt.trans hm)] at hv
      exact absurd hv (Nat.ne_of_lt a.isLt)
    | some b =>
      simp only [edgeKey, encodeBits_value _ _ (a.isLt.trans hm),
        encodeBits_value _ _ (b.isLt.trans hm)] at hv
      exact congrArg some (Fin.ext hv)

/-- Counting keyed labels along a reverse path counts its original-edge labels. -/
theorem count_keys {G vb cb : ℕ} (key : Option (Fin m) → Bits G) (hkey : Function.Injective key)
    (path : Trace (Option (Fin m)) vb cb) (e : Fin m) :
    (path.map (fun x => key x.2.label)).count (key (some e)) =
      projection (Labeled.traceLabels id path.reverse) e := by
  unfold projection Labeled.traceLabels
  rw [List.filterMap_reverse, List.count_reverse]
  induction path with
  | nil => rfl
  | cons x rest ih =>
    rw [List.map_cons, List.count_cons, ih, List.filterMap_cons]
    cases hx : x.2.label with
    | none =>
      have hne : (key none == key (some e)) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun h => by simpa using hkey h
      simp [hne]
    | some a =>
      by_cases hae : a = e
      · subst hae
        simp
      · have hne : (key (some a) == key (some e)) = false := by
          rw [beq_eq_false_iff_ne]
          exact fun h => hae (Option.some.inj (hkey h))
        simp [hne, hae]

/-- The search labels are the labels of the settled reverse path. -/
theorem searchLabels_eq {C : Fin m → Column (Fin r)} {W : Fin m → Fin d → ℤ}
    {π : Fin m → ZMod 2} {radius : ℕ} {cost : Fin m → ℕ}
    {distance : Bits (costWidth r d radius cost)}
    {path : Trace (Option (Fin m)) (vertexWidth r d radius) (costWidth r d radius cost)}
    (hlookup : lookupResult (solve (Labeled.graph id C W π radius cost)
      (nodeKey (start radius))) (nodeKey (finish radius)) = some (distance, path)) :
    ExecutableReduction.searchLabels C W π radius cost = Labeled.traceLabels id path.reverse := by
  unfold ExecutableReduction.searchLabels
  dsimp only
  rw [recover_lookup _ _ _ _ hlookup]

/-- A lookup on the pointer-labelled graph is the relabelled lookup on the
graph labelled by original edges. -/
theorem lookup_labeled {Label : Type*} (η : Option (Fin m) → Label)
    {C : Fin m → Column (Fin r)} {W : Fin m → Fin d → ℤ}
    {π : Fin m → ZMod 2} {radius : ℕ} {cost : Fin m → ℕ}
    {source target : Bits (vertexWidth r d radius)}
    {distance : Bits (costWidth r d radius cost)}
    {path : Trace Label (vertexWidth r d radius) (costWidth r d radius cost)}
    (hlookup : lookupResult (solve (Labeled.graph η C W π radius cost) source) target =
      some (distance, path)) :
    ∃ path0, lookupResult (solve (Labeled.graph id C W π radius cost) source) target =
      some (distance, path0) ∧ path = traceRelabel η path0 := by
  rw [Labeled.graph_eq_relabel_id, solve_lookup_relabel] at hlookup
  cases h : lookupResult (solve (Labeled.graph id C W π radius cost) source) target with
  | none => simp [h] at hlookup
  | some x =>
    obtain ⟨distance0, path0⟩ := x
    simp only [h, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hlookup
    obtain ⟨rfl, rfl⟩ := hlookup
    exact ⟨path0, rfl, rfl⟩

/-- The stored-label histogram of the path returned on the pointer-labelled
graph equals the projection of `ExecutableReduction.searchLabels` onto each
original edge. -/
theorem histogram_projection {G : ℕ} (η : Option (Fin m) → Ptr) (encode : Ptr → Bits G)
    (hη : ∀ l, encode (η l) = edgeKey G l) (hm : m < 2 ^ G)
    {C : Fin m → Column (Fin r)} {W : Fin m → Fin d → ℤ}
    {π : Fin m → ZMod 2} {radius : ℕ} {cost : Fin m → ℕ}
    {distance : Bits (costWidth r d radius cost)}
    {path : Trace Ptr (vertexWidth r d radius) (costWidth r d radius cost)}
    (hlookup : lookupResult (solve (Labeled.graph η C W π radius cost)
      (nodeKey (start radius))) (nodeKey (finish radius)) = some (distance, path))
    (e : Fin m) :
    (path.map (fun x => encode x.2.label)).count (edgeKey G (some e)) =
      projection (ExecutableReduction.searchLabels C W π radius cost) e := by
  obtain ⟨path0, h0, rfl⟩ := lookup_labeled η hlookup
  rw [searchLabels_eq h0, ← count_keys (edgeKey G) (edgeKey_injective hm) path0 e]
  simp only [traceRelabel, List.map_map]
  congr 2
  funext x
  simp [rawRelabel, hη]

/-- The same identity for a stored histogram table with the exact counts. -/
theorem table_projection {G nb : ℕ} (η : Option (Fin m) → Ptr) (encode : Ptr → Bits G)
    (hη : ∀ l, encode (η l) = edgeKey G l) (hm : m < 2 ^ G)
    {C : Fin m → Column (Fin r)} {W : Fin m → Fin d → ℤ}
    {π : Fin m → ZMod 2} {radius : ℕ} {cost : Fin m → ℕ}
    {distance : Bits (costWidth r d radius cost)}
    {path : Trace Ptr (vertexWidth r d radius) (costWidth r d radius cost)}
    (hlookup : lookupResult (solve (Labeled.graph η C W π radius cost)
      (nodeKey (start radius))) (nodeKey (finish radius)) = some (distance, path))
    {table : Histogram.Table G nb}
    (hcounts : ∀ key, (Histogram.count key table).value =
      (path.map (fun e => encode e.2.label)).count key)
    (e : Fin m) :
    (Histogram.count (edgeKey G (some e)) table).value =
      projection (ExecutableReduction.searchLabels C W π radius cost) e := by
  rw [hcounts, histogram_projection η encode hη hm hlookup e]

end WeightedMIS.SearchHistogramProjection
