module

public import WeightedMIS.RibbonTableRestrict
public import WeightedMIS.ComputedInduced

/-!
# Ribbon tables of computed induced graphs

Retained vertices are listed by a Boolean mask, retained edges by testing both
stored endpoint words, and the induced ribbon table is the key-based
restriction of the original table renumbered by those lists. Each statement is
an exact equality with the executable induced-graph construction.
-/

@[expose] public section

namespace WeightedMIS.InducedTable

open WeightedMIS.EfficientSearch WeightedMIS.RibbonTable

/-- Words of the positions whose mask bit is set, in increasing order. -/
def maskWords (W : ℕ) (mask : List Bool) : List (Bits W) :=
  ((rangeWords W mask.length).zip mask).filterMap (fun p => if p.2 then some p.1 else none)

/-- Words of the records whose two endpoint words both occur in `vs`. -/
def inducedEdgeWords {W : ℕ} (T : List (EdgeRec W)) (vs : List (Bits W)) : List (Bits W) :=
  T.filterMap (fun r => if r.left ∈ vs ∧ r.right ∈ vs then some r.key else none)

variable {n m : ℕ} (left right : Fin m → Fin n) (keep : Fin n → Prop) [DecidablePred keep]

/-- The retained vertex words are the positions of the retention mask. -/
theorem vertices_encode (W : ℕ) :
    (ComputedInduced.vertices keep).map (fun v => word W v.val) =
      maskWords W (List.ofFn (fun v => decide (keep v))) := by
  have hz : (rangeWords W (List.ofFn (fun v => decide (keep v))).length).zip
      (List.ofFn (fun v => decide (keep v))) =
      (List.finRange n).map (fun v => (word W v.val, decide (keep v))) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp [List.getElem_zip]
  rw [maskWords, hz, List.filterMap_map, ComputedInduced.vertices,
    ← filterMap_ite_eq keep (fun v => word W v.val)]
  apply List.filterMap_congr
  intro v _
  by_cases h : keep v <;> simp [h]

/-- The retained edge words are the records with both endpoints retained. -/
theorem edges_encode (W : ℕ) (hn : n < 2 ^ W) (R : EmbeddingFaces.Ribbon left right) :
    (ComputedInduced.edges left right keep).map (fun e => word W e.val) =
      inducedEdgeWords (encodeRibbon W R)
        ((ComputedInduced.vertices keep).map (fun v => word W v.val)) := by
  rw [inducedEdgeWords, encodeRibbon, List.filterMap_map, ComputedInduced.edges,
    ← filterMap_ite_eq (ComputedInduced.edgeKeep left right keep) (fun e => word W e.val)]
  apply List.filterMap_congr
  intro e _
  simp only [Function.comp_apply, encodeEdge, mem_map_word hn, ComputedInduced.mem_vertices]
  by_cases h : ComputedInduced.edgeKeep left right keep e
  · have h' : keep (left e) ∧ keep (right e) := h
    rw [ite_eq_left h', ite_eq_left h]
  · have h' : ¬(keep (left e) ∧ keep (right e)) := h
    rw [ite_eq_right h', ite_eq_right h]

/-- The table of the computed induced ribbon is the restricted, renumbered
table of the original ribbon. -/
theorem encode_ribbon (W : ℕ) (hn : n < 2 ^ W) (hm : m < 2 ^ W)
    (R : EmbeddingFaces.Ribbon left right) :
    encodeRibbon W (ComputedInduced.ribbon left right keep R) =
      restrictTable W (encodeRibbon W R)
        ((ComputedInduced.edges left right keep).map (fun e => word W e.val))
        ((ComputedInduced.vertices keep).map (fun v => word W v.val)) :=
  restrict_relabel_encode R (ComputedInduced.edgeKeep left right keep)
    (ComputedInduced.edges left right keep) (ComputedInduced.vertices keep)
    (ComputedInduced.edgeEquiv left right keep) (fun _ => rfl)
    (fun v => (ComputedInduced.vertexEquiv keep v).val)
    (Subtype.val_injective.comp (ComputedInduced.vertexEquiv keep).injective) (fun _ => rfl)
    (ComputedInduced.localLeft left right keep) (ComputedInduced.localRight left right keep)
    (ComputedInduced.vertexEquiv_localLeft left right keep)
    (ComputedInduced.vertexEquiv_localRight left right keep) W hn hm

/-- The stored local endpoints of the induced table are the computed local endpoints. -/
theorem localLeft_encode (W : ℕ) (hn : n < 2 ^ W) (hm : m < 2 ^ W)
    (R : EmbeddingFaces.Ribbon left right) :
    (restrictTable W (encodeRibbon W R)
        ((ComputedInduced.edges left right keep).map (fun e => word W e.val))
        ((ComputedInduced.vertices keep).map (fun v => word W v.val))).map EdgeRec.left =
      (List.finRange (ComputedInduced.edges left right keep).length).map
        (fun e => word W (ComputedInduced.localLeft left right keep e).val) := by
  rw [← encode_ribbon left right keep W hn hm R, encodeRibbon, List.map_map]
  rfl

theorem localRight_encode (W : ℕ) (hn : n < 2 ^ W) (hm : m < 2 ^ W)
    (R : EmbeddingFaces.Ribbon left right) :
    (restrictTable W (encodeRibbon W R)
        ((ComputedInduced.edges left right keep).map (fun e => word W e.val))
        ((ComputedInduced.vertices keep).map (fun v => word W v.val))).map EdgeRec.right =
      (List.finRange (ComputedInduced.edges left right keep).length).map
        (fun e => word W (ComputedInduced.localRight left right keep e).val) := by
  rw [← encode_ribbon left right keep W hn hm R, encodeRibbon, List.map_map]
  rfl

/-- Local induced weights are the weights selected by the retained vertex words. -/
theorem weights_encode {α : Type*} (W : ℕ) (hn : n < 2 ^ W) (w : Fin n → α) :
    List.ofFn (fun v => w (ComputedInduced.vertexEquiv keep v).val) =
      selectBy ((ComputedInduced.vertices keep).map (fun v => word W v.val)) (List.ofFn w) :=
  ofFn_get_eq_selectBy hn keep w

end WeightedMIS.InducedTable
