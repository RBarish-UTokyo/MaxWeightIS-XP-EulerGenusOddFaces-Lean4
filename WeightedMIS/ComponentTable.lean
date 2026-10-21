module

public import WeightedMIS.RibbonTableRestrict
public import WeightedMIS.ComputedComponentRibbon

/-!
# Ribbon tables of computed components

The vertex words of a component are the positions whose words occur in the
reached list, its edge words are the records whose left endpoint word is a
component vertex, and the component ribbon table is the key-based restriction
of the original table renumbered by those lists. Local weights are selected by
the component vertex words. Each statement is an exact equality with the
executable component construction.
-/

@[expose] public section

namespace WeightedMIS.ComponentTable

open WeightedMIS.EfficientSearch WeightedMIS.RibbonTable

/-- Words of `0, ..., k - 1` that occur in `S`, in increasing order. -/
def memberWords (W k : ℕ) (S : List (Bits W)) : List (Bits W) :=
  (rangeWords W k).filter (fun w => decide (w ∈ S))

/-- Words of the records whose left endpoint word occurs in `vs`. -/
def componentEdgeWords {W : ℕ} (T : List (EdgeRec W)) (vs : List (Bits W)) : List (Bits W) :=
  T.filterMap (fun r => if r.left ∈ vs then some r.key else none)

/-- Increasing member words of a label list are the words of the filtered labels. -/
theorem memberWords_map {W k : ℕ} (hk : k < 2 ^ W) (S : List (Fin k)) :
    memberWords W k (S.map (fun v => word W v.val)) =
      ((List.finRange k).filter (fun v => decide (v ∈ S))).map (fun v => word W v.val) := by
  have hr : rangeWords W k = (List.finRange k).map (fun v => word W v.val) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp
  rw [memberWords, hr, List.filter_map]
  congr 1
  apply List.filter_congr
  intro v _
  exact decide_eq_decide.mpr (mem_map_word hk S v)

variable {n m : ℕ} (left right : Fin m → Fin n) (root : Fin n)

/-- Component vertex words are the range words occurring in any list of the
reached vertices. -/
theorem vertices_encode (W : ℕ) (hn : n < 2 ^ W) (S : List (Fin n))
    (hS : ∀ v, v ∈ S ↔ v ∈ (ComputedComponents.routes left right root).seen) :
    (ComputedComponents.vertices left right root).map (fun v => word W v.val) =
      memberWords W n (S.map (fun v => word W v.val)) := by
  rw [memberWords_map hn, ComputedComponents.vertices]
  congr 1
  apply List.filter_congr
  intro v _
  exact decide_eq_decide.mpr (hS v).symm

/-- Component edge words are the records whose left endpoint is a component vertex. -/
theorem edges_encode (W : ℕ) (hn : n < 2 ^ W) (R : EmbeddingFaces.Ribbon left right) :
    (ComputedComponents.edges left right root).map (fun e => word W e.val) =
      componentEdgeWords (encodeRibbon W R)
        ((ComputedComponents.vertices left right root).map (fun v => word W v.val)) := by
  rw [componentEdgeWords, encodeRibbon, List.filterMap_map, ComputedComponents.edges,
    ← filterMap_ite_eq (fun e => left e ∈ (ComputedComponents.routes left right root).seen)
      (fun e => word W e.val)]
  apply List.filterMap_congr
  intro e _
  simp only [Function.comp_apply, encodeEdge, mem_map_word hn, ComputedComponents.vertices,
    List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]

/-- The table of the computed component ribbon is the restricted, renumbered
table of the original ribbon. -/
theorem encode_componentRibbon (W : ℕ) (hn : n < 2 ^ W) (hm : m < 2 ^ W)
    (R : EmbeddingFaces.Ribbon left right) :
    encodeRibbon W (ComputedComponents.componentRibbon left right root R) =
      restrictTable W (encodeRibbon W R)
        ((ComputedComponents.edges left right root).map (fun e => word W e.val))
        ((ComputedComponents.vertices left right root).map (fun v => word W v.val)) :=
  restrict_relabel_encode R (fun e => e ∈ ComputedComponents.edges left right root)
    (ComputedComponents.edges left right root) (ComputedComponents.vertices left right root)
    (ComputedComponents.retainedEdgeEquiv left right root) (fun _ => rfl)
    (fun v => (ComputedComponents.vertexEquiv left right root v).val)
    (Subtype.val_injective.comp (ComputedComponents.vertexEquiv left right root).injective)
    (fun _ => rfl)
    (ComputedComponents.localLeft left right root) (ComputedComponents.localRight left right root)
    (fun e => congrArg Subtype.val (ComputedComponents.vertexEquiv_localLeft left right root e))
    (fun e => congrArg Subtype.val (ComputedComponents.vertexEquiv_localRight left right root e))
    W hn hm

/-- Local component weights are the weights selected by the component vertex words. -/
theorem weights_encode {α : Type*} (W : ℕ) (hn : n < 2 ^ W) (w : Fin n → α) :
    List.ofFn (fun v => w (ComputedComponents.vertexEquiv left right root v).val) =
      selectBy ((ComputedComponents.vertices left right root).map (fun v => word W v.val))
        (List.ofFn w) :=
  ofFn_get_eq_selectBy hn (fun v => v ∈ (ComputedComponents.routes left right root).seen) w

end WeightedMIS.ComponentTable
