module

public import WeightedMIS.RibbonTable
public import WeightedMIS.ComputedRestriction
public import WeightedMIS.RibbonRelabeling

/-!
# Key-based restriction and renumbering of ribbon tables

Retaining a list of edges splices corners by the bounded first-return scan:
the restricted partner of a flag is the other side of the first retained flag
reached by repeatedly turning through a corner and crossing the edge. Retained
edges and vertices are renumbered by their positions in the supplied lists,
using association-list lookup. For a ribbon table this computes exactly the
table of the executable restriction followed by numeric relabelling.
-/

@[expose] public section

namespace WeightedMIS.RibbonTable

open WeightedMIS.EfficientSearch

/-! ## Encoded operations -/

/-- Bounded first-return scan on flag keys: turn through a corner, cross the
edge, and stop at the first key whose edge passes `keep`. -/
def scanKey {W : ℕ} (T : List (EdgeRec W)) (keep : Bits W → Bool) :
    ℕ → Bits (W + 2) → Bits (W + 2)
  | 0, x => x
  | fuel + 1, x =>
    let y := acrossKey (cornerKey T x)
    if keep (edgePart y) then y else scanKey T keep fuel y

/-- Association-list lookup with a default value. -/
def assoc {α β : Type*} [DecidableEq α] (d : β) : List (α × β) → α → β
  | [], _ => d
  | p :: rest, k => if p.1 = k then p.2 else assoc d rest k

/-- Renumber the edge word of a flag key through an association list. -/
def relabelKey {W : ℕ} (ez : List (Bits W × Bits W)) (k : Bits (W + 2)) : Bits (W + 2) :=
  mkKey (sideBit k) (endBit k) (assoc (edgePart k) ez (edgePart k))

/-- Restricted, renumbered corner partner of a key. -/
def restrictCorner {W : ℕ} (T : List (EdgeRec W)) (ks : List (Bits W)) (k : Bits (W + 2)) :
    Bits (W + 2) :=
  relabelKey (ks.zip (rangeWords W ks.length))
    (acrossKey (scanKey T (fun g => decide (g ∈ ks)) (4 * T.length) k))

/-- The record of the retained edge `g`, renumbered to `i`. -/
def restrictRecord {W : ℕ} (T : List (EdgeRec W)) (ks vs : List (Bits W)) (g i : Bits W) :
    EdgeRec W :=
  let vz := vs.zip (rangeWords W vs.length)
  match findRecord T g with
  | some r =>
    ⟨i, assoc r.left vz r.left, assoc r.right vz r.right,
      restrictCorner T ks (mkKey false false g), restrictCorner T ks (mkKey false true g),
      restrictCorner T ks (mkKey true false g), restrictCorner T ks (mkKey true true g)⟩
  | none =>
    ⟨i, i, i,
      restrictCorner T ks (mkKey false false g), restrictCorner T ks (mkKey false true g),
      restrictCorner T ks (mkKey true false g), restrictCorner T ks (mkKey true true g)⟩

/-- Restrict a table to the edge words `ks` (in this order) and renumber the
vertex words by their positions in `vs`. -/
def restrictTable (W : ℕ) (T : List (EdgeRec W)) (ks vs : List (Bits W)) : List (EdgeRec W) :=
  (ks.zip (rangeWords W ks.length)).map (fun p => restrictRecord T ks vs p.1 p.2)

@[simp] theorem restrictTable_length (W : ℕ) (T : List (EdgeRec W)) (ks vs : List (Bits W)) :
    (restrictTable W T ks vs).length = ks.length := by
  simp [restrictTable]

/-- Entries of `ws` at the positions whose words occur in `ks`. -/
def selectBy {α : Type*} {W : ℕ} (ks : List (Bits W)) (ws : List α) : List α :=
  ((rangeWords W ws.length).zip ws).filterMap (fun p => if p.1 ∈ ks then some p.2 else none)

/-! ## Association lists -/

theorem assoc_zip {α β : Type*} [DecidableEq α] (d : β) {xs : List α} (ys : List β)
    (hxs : xs.Nodup) (i : ℕ) (hi : i < xs.length) (hy : i < ys.length) :
    assoc d (xs.zip ys) xs[i] = ys[i] := by
  induction xs generalizing ys i with
  | nil => simp at hi
  | cons a xs ih =>
    cases ys with
    | nil => simp at hy
    | cons b ys =>
      rw [List.zip_cons_cons]
      cases i with
      | zero => simp [assoc]
      | succ j =>
        have hj : j < xs.length := by simpa using hi
        have hne : a ≠ xs[j] := by
          intro h
          exact (List.nodup_cons.mp hxs).1 (h ▸ List.getElem_mem hj)
        simp only [assoc, List.getElem_cons_succ, hne, ↓reduceIte]
        exact ih ys (List.nodup_cons.mp hxs).2 j (by simpa using hi) (by simpa using hy)

variable {n m : ℕ}

/-- Renumbering a word of a listed label gives the word of its position. -/
theorem assoc_word {W : ℕ} (hk : m < 2 ^ W) {l : List (Fin m)} (hl : l.Nodup) (d : Bits W)
    (i : Fin l.length) :
    assoc d ((l.map (fun e => word W e.val)).zip (rangeWords W (l.map (fun e => word W e.val)).length))
      (word W (l.get i).val) = word W i.val := by
  have h := assoc_zip d (rangeWords W (l.map (fun e => word W e.val)).length)
    (nodup_map_word hk hl) i.val (by simp) (by simp)
  simpa using h

/-- Renumbering a flag key whose edge is listed gives the key of the local flag. -/
theorem relabelKey_flagKey {W : ℕ} (hm : m < 2 ^ W) {es : List (Fin m)} (hes : es.Nodup)
    (y : EmbeddingFaces.Flag (Fin es.length)) :
    relabelKey ((es.map (fun e => word W e.val)).zip
        (rangeWords W (es.map (fun e => word W e.val)).length))
      (flagKey W (⟨es.get y.edge, y.side, y.endpoint⟩ : EmbeddingFaces.Flag (Fin m))) =
      flagKey W y := by
  simp only [relabelKey, sideBit_flagKey, endBit_flagKey, edgePart_flagKey]
  rw [assoc_word hm hes]
  rfl

/-! ## The first-return scan on keys -/

/-- The key scan follows exactly the executable first-return scan. -/
theorem scanKey_encode (W : ℕ) (hm : m < 2 ^ W) {left right : Fin m → Fin n}
    (R : EmbeddingFaces.Ribbon left right) (keep : Fin m → Prop) [DecidablePred keep]
    (keepB : Bits W → Bool) (hkeep : ∀ e : Fin m, keepB (word W e.val) = decide (keep e))
    (fuel : ℕ) (x : EmbeddingFaces.Flag (Fin m)) :
    scanKey (encodeRibbon W R) keepB fuel (flagKey W x) =
      flagKey W (PermutationDeletion.scan (R.corner.trans EmbeddingFaces.SidePairing.across)
        (fun y => keep y.edge) fuel x) := by
  induction fuel generalizing x with
  | zero => rfl
  | succ fuel ih =>
    simp only [scanKey, PermutationDeletion.scan, cornerKey_encode W hm, acrossKey_flagKey,
      edgePart_flagKey, hkeep, Equiv.trans_apply]
    by_cases h : keep (EmbeddingFaces.SidePairing.across (R.corner x)).edge
    · simp [h]
    · simp [h, ih]

/-! ## The relabelled computed restriction -/

/-- The flag of the original graph named by a relabelled retained flag. -/
def globalFlag {D E : Type*} {keep : E → Prop} (ee : D ≃ {e // keep e})
    (x : EmbeddingFaces.Flag D) : EmbeddingFaces.Flag E :=
  ⟨(ee x.edge).val, x.side, x.endpoint⟩

section Corner

variable {V U D E : Type*} [Fintype E] {left right : E → V} (R : EmbeddingFaces.Ribbon left right)
    (keep : E → Prop) [DecidablePred keep] (ee : D ≃ {e // keep e}) (f : U → V)
    (hf : Function.Injective f) (leftU rightU : D → U)
    (hl : ∀ e, f (leftU e) = left (ee e).val) (hr : ∀ e, f (rightU e) = right (ee e).val)

/-- Pointwise corner of the relabelled computed restriction: cross the edge at
the first retained flag found by the bounded scan. -/
theorem relabel_restrict_corner (x : EmbeddingFaces.Flag D) :
    globalFlag ee (((R.computedRestrict keep).relabel ee f hf leftU rightU hl hr).corner x) =
      EmbeddingFaces.SidePairing.across
        (PermutationDeletion.scan (R.corner.trans EmbeddingFaces.SidePairing.across)
          (fun y => keep y.edge) (Fintype.card (EmbeddingFaces.Flag E)) (globalFlag ee x)) := by
  rcases x with ⟨d, s, t⟩
  let w := PermutationDeletion.computedReturnMap (R.corner.trans EmbeddingFaces.SidePairing.across)
    (fun y => keep y.edge) ⟨⟨(ee d).val, s, t⟩, (ee d).property⟩
  have hy : ((R.computedRestrict keep).relabel ee f hf leftU rightU hl hr).corner ⟨d, s, t⟩ =
      ⟨ee.symm ⟨w.val.edge, w.property⟩, !w.val.side, w.val.endpoint⟩ := rfl
  rw [hy]
  simp only [globalFlag, Equiv.apply_symm_apply]
  rfl

end Corner

/-! ## The restricted table -/

section Table

variable {left right : Fin m → Fin n} (R : EmbeddingFaces.Ribbon left right)
    (keep : Fin m → Prop) [DecidablePred keep] (es : List (Fin m)) (vs : List (Fin n))
    (ee : Fin es.length ≃ {e // keep e}) (hee : ∀ i, (ee i).val = es.get i)
    (f : Fin vs.length → Fin n) (hf : Function.Injective f) (hfv : ∀ v, f v = vs.get v)
    (leftU rightU : Fin es.length → Fin vs.length)
    (hl : ∀ e, f (leftU e) = left (ee e).val) (hr : ∀ e, f (rightU e) = right (ee e).val)

omit [DecidablePred keep] in
include hee in
theorem nodup_of_equiv : es.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro i j h
  rw [← hee, ← hee] at h
  exact ee.injective (Subtype.ext h)

include hf hfv in
theorem nodup_of_injective : vs.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro i j h
  rw [← hfv, ← hfv] at h
  exact hf h

omit [DecidablePred keep] in
include hee in
theorem mem_of_equiv (e : Fin m) : e ∈ es ↔ keep e := by
  constructor
  · intro h
    obtain ⟨i, rfl⟩ := List.get_of_mem h
    rw [← hee]
    exact (ee i).property
  · intro h
    rw [← Subtype.coe_mk e h, ← ee.apply_symm_apply ⟨e, h⟩, hee]
    exact List.get_mem _ _

include hee in
/-- The restricted corner of every local flag key is the stored relabelled corner. -/
theorem restrictCorner_encode (W : ℕ) (hm : m < 2 ^ W) (x : EmbeddingFaces.Flag (Fin es.length)) :
    restrictCorner (encodeRibbon W R) (es.map (fun e => word W e.val))
        (flagKey W (⟨es.get x.edge, x.side, x.endpoint⟩ : EmbeddingFaces.Flag (Fin m))) =
      flagKey W (((R.computedRestrict keep).relabel ee f hf leftU rightU hl hr).corner x) := by
  have hes := nodup_of_equiv keep es ee hee
  have hkeep : ∀ e : Fin m, decide (word W e.val ∈ es.map (fun e => word W e.val)) =
      decide (keep e) := by
    intro e
    simp only [mem_map_word hm, mem_of_equiv keep es ee hee]
  have hg : (⟨es.get x.edge, x.side, x.endpoint⟩ : EmbeddingFaces.Flag (Fin m)) =
      globalFlag ee x := by
    simp only [globalFlag, hee]
  have hcard : 4 * (encodeRibbon W R).length = Fintype.card (EmbeddingFaces.Flag (Fin m)) := by
    simp
  rw [restrictCorner, scanKey_encode W hm R keep _ hkeep, hcard, acrossKey_flagKey, hg,
    ← relabel_restrict_corner R keep ee f hf leftU rightU hl hr x]
  set y := ((R.computedRestrict keep).relabel ee f hf leftU rightU hl hr).corner x
  have hy : globalFlag ee y = ⟨es.get y.edge, y.side, y.endpoint⟩ := by
    simp only [globalFlag, hee]
  rw [hy, relabelKey_flagKey hm hes]

include hee hfv in
/-- Restricting and renumbering the table of a ribbon gives exactly the table
of the relabelled executable restriction. -/
theorem restrict_relabel_encode (W : ℕ) (hn : n < 2 ^ W) (hm : m < 2 ^ W) :
    encodeRibbon W ((R.computedRestrict keep).relabel ee f hf leftU rightU hl hr) =
      restrictTable W (encodeRibbon W R) (es.map (fun e => word W e.val))
        (vs.map (fun v => word W v.val)) := by
  have hvs := nodup_of_injective vs f hf hfv
  apply List.ext_getElem
  · simp
  intro i h1 h2
  have hi : i < es.length := by simpa using h1
  rw [encodeRibbon_getElem]
  simp only [restrictTable, List.getElem_map, List.getElem_zip, rangeWords_getElem]
  simp only [restrictRecord, findRecord_encode W hm]
  have hleft : left es[i] = vs.get (leftU ⟨i, hi⟩) := by
    rw [← hfv, hl, hee]; rfl
  have hright : right es[i] = vs.get (rightU ⟨i, hi⟩) := by
    rw [← hfv, hr, hee]; rfl
  have hc : ∀ s t, restrictCorner (encodeRibbon W R) (es.map (fun e => word W e.val))
      (mkKey s t (word W es[i].val)) =
      flagKey W (((R.computedRestrict keep).relabel ee f hf leftU rightU hl hr).corner
        ⟨⟨i, hi⟩, s, t⟩) := by
    intro s t
    exact restrictCorner_encode R keep es vs ee hee f hf leftU rightU hl hr W hm
      ⟨⟨i, hi⟩, s, t⟩
  simp only [encodeEdge, hc, EdgeRec.mk.injEq, true_and, and_true]
  constructor
  · rw [hleft, assoc_word hn hvs]
  · rw [hright, assoc_word hn hvs]

end Table

/-! ## Selecting entries by retained labels -/

theorem filterMap_ite_eq {α β : Type*} (S : α → Prop) [DecidablePred S] (w : α → β) (l : List α) :
    l.filterMap (fun v => if S v then some (w v) else none) = (l.filter (fun v => decide (S v))).map w := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : S a <;> simp [h, ih]

/-- Selecting by the words of a filtered label list keeps exactly the entries
of the retained labels, in increasing order. -/
theorem selectBy_eq {α : Type*} {W k : ℕ} (hk : k < 2 ^ W) (S : Fin k → Prop) [DecidablePred S]
    (w : Fin k → α) :
    selectBy (((List.finRange k).filter (fun v => decide (S v))).map (fun v => word W v.val))
        (List.ofFn w) = ((List.finRange k).filter (fun v => decide (S v))).map w := by
  have hz : (rangeWords W (List.ofFn w).length).zip (List.ofFn w) =
      (List.finRange k).map (fun v => (word W v.val, w v)) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp [List.getElem_zip]
  rw [selectBy, hz, List.filterMap_map]
  have hmem : ∀ v : Fin k, (word W v.val ∈ ((List.finRange k).filter (fun v => decide (S v))).map
      (fun v => word W v.val)) ↔ S v := by
    intro v
    rw [mem_map_word hk]
    simp
  simp only [Function.comp_def, hmem]
  exact filterMap_ite_eq S w _

/-- Weights read through a label list are the selected weight entries. -/
theorem ofFn_get_eq_selectBy {α : Type*} {W k : ℕ} (hk : k < 2 ^ W) (S : Fin k → Prop)
    [DecidablePred S] (w : Fin k → α) :
    List.ofFn (fun v : Fin ((List.finRange k).filter (fun v => decide (S v))).length =>
        w (((List.finRange k).filter (fun v => decide (S v))).get v)) =
      selectBy (((List.finRange k).filter (fun v => decide (S v))).map (fun v => word W v.val))
        (List.ofFn w) := by
  rw [selectBy_eq hk]
  conv_rhs => rw [← List.ofFn_get ((List.finRange k).filter (fun v => decide (S v)))]
  rw [List.map_ofFn]
  rfl

end WeightedMIS.RibbonTable
