module

public import WeightedMIS.SparseSearchGraph
public import WeightedMIS.EnumeratedEmbedding
public import WeightedMIS.EfficientSearchPointerTrie

/-!
# Key-based tables of corner matchings

A flag of an edge with numeric ID `e` is stored as the word
`side :: endpoint :: word e` of width `W + 2`. A ribbon is stored as one
acyclic record per edge: its own word, its two endpoint words, and the four
corner partners of its flags, in the order `00, 01, 10, 11` of the flag bits.
Corner lookup is a search for the record of the flag's edge part followed by
selection with the two flag bits. The flag keys in canonical order are read
off the records in four passes.
-/

@[expose] public section

namespace WeightedMIS.RibbonTable

open WeightedMIS.EfficientSearch WeightedMIS.EfficientSearch.Pointer
open WeightedMIS.PointerMemory WeightedMIS.EmbeddingFaces

/-! ## Words and flag keys -/

/-- Fixed-width big-endian word of a natural number. -/
def word (W i : ℕ) : Bits W := SparseSearchGraph.encodeBits W i

/-- The words of `0, ..., k - 1` in increasing order. -/
def rangeWords (W k : ℕ) : List (Bits W) := (List.range k).map (word W)

@[simp] theorem rangeWords_length (W k : ℕ) : (rangeWords W k).length = k := by
  simp [rangeWords]

@[simp] theorem rangeWords_getElem (W k i : ℕ) (hi : i < (rangeWords W k).length) :
    (rangeWords W k)[i] = word W i := by
  simp [rangeWords]

theorem word_value {W i : ℕ} (h : i < 2 ^ W) : (word W i).value = i :=
  SparseSearchGraph.encodeBits_value W i h

theorem word_inj {W i j : ℕ} (hi : i < 2 ^ W) (hj : j < 2 ^ W) :
    word W i = word W j ↔ i = j :=
  ⟨SparseSearchGraph.encodeBits_injective hi hj, fun h => h ▸ rfl⟩

/-- Words of finite labels below `2 ^ W` are injective. -/
theorem word_fin_inj {W k : ℕ} (hk : k < 2 ^ W) {a b : Fin k} :
    word W a.val = word W b.val ↔ a = b := by
  rw [word_inj (a.isLt.trans hk) (b.isLt.trans hk), Fin.val_inj]

/-- A list of distinct finite labels has distinct words. -/
theorem nodup_map_word {W k : ℕ} (hk : k < 2 ^ W) {l : List (Fin k)} (hl : l.Nodup) :
    (l.map (fun a => word W a.val)).Nodup :=
  hl.map_on (fun _ _ _ _ h => (word_fin_inj hk).mp h)

theorem mem_map_word {W k : ℕ} (hk : k < 2 ^ W) (l : List (Fin k)) (a : Fin k) :
    word W a.val ∈ l.map (fun b => word W b.val) ↔ a ∈ l := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨b, hb, he⟩
    rwa [← (word_fin_inj hk).mp he]
  · exact fun h => ⟨a, h, rfl⟩

/-- Fixed-width words are determined by their natural values. -/
theorem value_injective {n : ℕ} : Function.Injective (@Bits.value n) := by
  intro a b h
  induction n with
  | zero => cases a; cases b; rfl
  | succ n ih =>
    cases a with
    | cons x xs =>
      cases b with
      | cons y ys =>
        have hx := Bits.value_lt xs
        have hy := Bits.value_lt ys
        cases x <;> cases y <;> simp only [Bits.value, Bool.false_eq_true, ↓reduceIte, zero_add] at h
        · exact congrArg (Bits.cons false) (ih h)
        · omega
        · omega
        · exact congrArg (Bits.cons true) (ih (by omega))

/-- Key of a flag: side bit, endpoint bit, then the edge word. -/
def flagKey (W : ℕ) {m : ℕ} (x : EmbeddingFaces.Flag (Fin m)) : Bits (W + 2) :=
  .cons x.side (.cons x.endpoint (word W x.edge.val))

/-- The first (side) bit of a flag key. -/
def sideBit {W : ℕ} : Bits (W + 2) → Bool
  | .cons s _ => s

/-- The second (endpoint) bit of a flag key. -/
def endBit {W : ℕ} : Bits (W + 2) → Bool
  | .cons _ (.cons t _) => t

/-- The edge word of a flag key. -/
def edgePart {W : ℕ} : Bits (W + 2) → Bits W
  | .cons _ (.cons _ w) => w

/-- Flip the side bit. -/
def acrossKey {W : ℕ} : Bits (W + 2) → Bits (W + 2)
  | .cons s rest => .cons (!s) rest

/-- Flip the endpoint bit. -/
def alongKey {W : ℕ} : Bits (W + 2) → Bits (W + 2)
  | .cons s (.cons t w) => .cons s (.cons (!t) w)

/-- Assemble a key from its two bits and its edge word. -/
def mkKey {W : ℕ} (s t : Bool) (w : Bits W) : Bits (W + 2) := .cons s (.cons t w)

theorem eta_key {W : ℕ} (k : Bits (W + 2)) : mkKey (sideBit k) (endBit k) (edgePart k) = k := by
  rcases k with _ | ⟨s, _ | ⟨t, w⟩⟩
  rfl

@[simp] theorem sideBit_mkKey {W : ℕ} (s t : Bool) (w : Bits W) : sideBit (mkKey s t w) = s := rfl
@[simp] theorem endBit_mkKey {W : ℕ} (s t : Bool) (w : Bits W) : endBit (mkKey s t w) = t := rfl
@[simp] theorem edgePart_mkKey {W : ℕ} (s t : Bool) (w : Bits W) : edgePart (mkKey s t w) = w := rfl

theorem flagKey_eq_mkKey {W m : ℕ} (x : EmbeddingFaces.Flag (Fin m)) :
    flagKey W x = mkKey x.side x.endpoint (word W x.edge.val) := rfl

@[simp] theorem sideBit_flagKey {W m : ℕ} (x : EmbeddingFaces.Flag (Fin m)) :
    sideBit (flagKey W x) = x.side := rfl
@[simp] theorem endBit_flagKey {W m : ℕ} (x : EmbeddingFaces.Flag (Fin m)) :
    endBit (flagKey W x) = x.endpoint := rfl
@[simp] theorem edgePart_flagKey {W m : ℕ} (x : EmbeddingFaces.Flag (Fin m)) :
    edgePart (flagKey W x) = word W x.edge.val := rfl

@[simp] theorem acrossKey_flagKey {W m : ℕ} (x : EmbeddingFaces.Flag (Fin m)) :
    acrossKey (flagKey W x) = flagKey W (SidePairing.across x) := rfl

@[simp] theorem alongKey_flagKey {W m : ℕ} (x : EmbeddingFaces.Flag (Fin m)) :
    alongKey (flagKey W x) = flagKey W (SidePairing.along x) := rfl

/-- Flag keys determine flags when edge IDs fit in the width. -/
theorem flagKey_injective {W m : ℕ} (hm : m < 2 ^ W) :
    Function.Injective (flagKey W (m := m)) := by
  rintro ⟨e, s, t⟩ ⟨e', s', t'⟩ h
  simp only [flagKey, Bits.cons.injEq] at h
  obtain ⟨rfl, rfl, hw⟩ := h
  rw [(word_fin_inj hm).mp hw]

/-- Flag-key values are injective as natural numbers. -/
theorem flagKey_value_injective {W m : ℕ} (hm : m < 2 ^ W) {x y : EmbeddingFaces.Flag (Fin m)}
    (h : (flagKey W x).value = (flagKey W y).value) : x = y :=
  flagKey_injective hm (value_injective h)

/-! ## Edge records -/

/-- One stored edge: its word, endpoint words, and the four corner keys
`c_st = flagKey (corner ⟨e, s, t⟩)`. -/
structure EdgeRec (W : ℕ) where
  key : Bits W
  left : Bits W
  right : Bits W
  c00 : Bits (W + 2)
  c01 : Bits (W + 2)
  c10 : Bits (W + 2)
  c11 : Bits (W + 2)

/-- Select a corner key with the two flag bits. -/
def EdgeRec.select {W : ℕ} (r : EdgeRec W) : Bool → Bool → Bits (W + 2)
  | false, false => r.c00
  | false, true => r.c01
  | true, false => r.c10
  | true, true => r.c11

variable {n m : ℕ}

/-- The record of one edge under a corner map. -/
def encodeEdge (W : ℕ) (left right : Fin m → Fin n)
    (corner : EmbeddingFaces.Flag (Fin m) → EmbeddingFaces.Flag (Fin m)) (e : Fin m) : EdgeRec W where
  key := word W e.val
  left := word W (left e).val
  right := word W (right e).val
  c00 := flagKey W (corner ⟨e, false, false⟩)
  c01 := flagKey W (corner ⟨e, false, true⟩)
  c10 := flagKey W (corner ⟨e, true, false⟩)
  c11 := flagKey W (corner ⟨e, true, true⟩)

@[simp] theorem encodeEdge_select (W : ℕ) (left right : Fin m → Fin n)
    (corner : EmbeddingFaces.Flag (Fin m) → EmbeddingFaces.Flag (Fin m)) (e : Fin m) (s t : Bool) :
    (encodeEdge W left right corner e).select s t = flagKey W (corner ⟨e, s, t⟩) := by
  cases s <;> cases t <;> rfl

/-- The table of a ribbon: one record per edge in increasing edge order. -/
def encodeRibbon (W : ℕ) {left right : Fin m → Fin n} (R : Ribbon left right) :
    List (EdgeRec W) :=
  (List.finRange m).map (encodeEdge W left right R.corner)

@[simp] theorem encodeRibbon_length (W : ℕ) {left right : Fin m → Fin n} (R : Ribbon left right) :
    (encodeRibbon W R).length = m := by simp [encodeRibbon]

@[simp] theorem encodeRibbon_getElem (W : ℕ) {left right : Fin m → Fin n}
    (R : Ribbon left right) (i : ℕ) (h : i < (encodeRibbon W R).length) :
    (encodeRibbon W R)[i] = encodeEdge W left right R.corner ⟨i, by simpa using h⟩ := by
  simp [encodeRibbon]

/-- The first record with a given edge word. -/
def findRecord {W : ℕ} (T : List (EdgeRec W)) (g : Bits W) : Option (EdgeRec W) :=
  T.find? (fun r => decide (r.key = g))

/-- Corner lookup by key; an unknown key is returned unchanged. -/
def cornerKey {W : ℕ} (T : List (EdgeRec W)) (x : Bits (W + 2)) : Bits (W + 2) :=
  match findRecord T (edgePart x) with
  | some r => r.select (sideBit x) (endBit x)
  | none => x

/-- `find?` returns the unique element satisfying a predicate characterising it. -/
theorem find?_eq_of_unique {α : Type*} (p : α → Bool) {l : List α} {x : α} (hx : x ∈ l)
    (hp : ∀ a ∈ l, p a = true ↔ a = x) : l.find? p = some x := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    by_cases ha : p a = true
    · rw [List.find?_cons_of_pos ha, (hp a (by simp)).mp ha]
    · rw [List.find?_cons_of_neg ha]
      have hax : a ≠ x := fun h => ha ((hp a (by simp)).mpr h)
      exact ih (by simpa [Ne.symm hax] using hx) (fun b hb => hp b (by simp [hb]))

theorem findRecord_encode (W : ℕ) (hm : m < 2 ^ W) {left right : Fin m → Fin n}
    (R : Ribbon left right) (e : Fin m) :
    findRecord (encodeRibbon W R) (word W e.val) = some (encodeEdge W left right R.corner e) := by
  apply find?_eq_of_unique
  · exact List.mem_map.mpr ⟨e, List.mem_finRange e, rfl⟩
  · intro r hr
    obtain ⟨e', -, rfl⟩ := List.mem_map.mp hr
    simp only [encodeEdge, decide_eq_true_eq, word_fin_inj hm]
    constructor
    · rintro rfl; rfl
    · intro h
      exact (word_fin_inj hm).mp (congrArg EdgeRec.key h)

/-- Key lookup in the table computes exactly the stored corner matching. -/
theorem cornerKey_encode (W : ℕ) (hm : m < 2 ^ W) {left right : Fin m → Fin n}
    (R : Ribbon left right) (x : EmbeddingFaces.Flag (Fin m)) :
    cornerKey (encodeRibbon W R) (flagKey W x) = flagKey W (R.corner x) := by
  rcases x with ⟨e, s, t⟩
  simp only [cornerKey, edgePart_flagKey, findRecord_encode W hm, sideBit_flagKey,
    endBit_flagKey, encodeEdge_select]

/-! ## Canonical flag keys -/

/-- Flag keys of every record, in the four-pass order `00, 01, 10, 11`. -/
def canonicalKeys {W : ℕ} (T : List (EdgeRec W)) : List (Bits (W + 2)) :=
  T.map (fun r => mkKey false false r.key) ++ T.map (fun r => mkKey false true r.key) ++
    T.map (fun r => mkKey true false r.key) ++ T.map (fun r => mkKey true true r.key)

/-- The stored flags are listed exactly in the canonical executable order. -/
theorem canonicalKeys_encode (W : ℕ) {left right : Fin m → Fin n} (R : Ribbon left right) :
    canonicalKeys (encodeRibbon W R) = (EmbeddingFaces.Flag.canonicalOrder m).map (flagKey W) := by
  simp only [canonicalKeys, encodeRibbon, EmbeddingFaces.Flag.canonicalOrder,
    EmbeddingFaces.Flag.listOrder, List.map_append, List.map_map]
  rfl

/-! ## Heap layout -/

/-- One record as six pair cells:
`p ↦ (key, a)`, `a ↦ (left, b)`, `b ↦ (right, c)`, `c ↦ (q0, q1)`,
`q0 ↦ (c00, c01)`, `q1 ↦ (c10, c11)`. -/
def EdgeRecAt {W : ℕ} (h : Heap) (p : Ptr) (r : EdgeRec W) : Prop :=
  ∃ kp a lp b rp c q0 q1 c00p c01p c10p c11p,
    h[p]? = some (.pair kp a) ∧ BitsAt h kp r.key ∧
    h[a]? = some (.pair lp b) ∧ BitsAt h lp r.left ∧
    h[b]? = some (.pair rp c) ∧ BitsAt h rp r.right ∧
    h[c]? = some (.pair q0 q1) ∧
    h[q0]? = some (.pair c00p c01p) ∧ BitsAt h c00p r.c00 ∧ BitsAt h c01p r.c01 ∧
    h[q1]? = some (.pair c10p c11p) ∧ BitsAt h c10p r.c10 ∧ BitsAt h c11p r.c11

/-- A list of records. -/
def RecordsAt {W : ℕ} (h : Heap) (p : Ptr) (rs : List (EdgeRec W)) : Prop :=
  ListRep EdgeRecAt h p rs

theorem EdgeRecAt.allocated {W : ℕ} {h : Heap} {p : Ptr} {r : EdgeRec W}
    (hr : EdgeRecAt h p r) : p < h.length := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc, _⟩ := hr
  exact List.getElem?_eq_some_iff.mp hc |>.1

theorem EdgeRecAt.mono {W : ℕ} {h h' : Heap} (he : Extends h h')
    {p : Ptr} {r : EdgeRec W} (hr : EdgeRecAt h p r) : EdgeRecAt h' p r := by
  obtain ⟨kp, a, lp, b, rp, c, q0, q1, c00p, c01p, c10p, c11p,
    hp, hk, ha, hl, hb, hr, hc, hq0, h00, h01, hq1, h10, h11⟩ := hr
  exact ⟨kp, a, lp, b, rp, c, q0, q1, c00p, c01p, c10p, c11p,
    he.lookup hp, hk.mono he, he.lookup ha, hl.mono he, he.lookup hb, hr.mono he,
    he.lookup hc, he.lookup hq0, h00.mono he, h01.mono he, he.lookup hq1, h10.mono he,
    h11.mono he⟩

theorem RecordsAt.allocated {W : ℕ} {h : Heap} {p : Ptr} {rs : List (EdgeRec W)}
    (hr : RecordsAt h p rs) : p < h.length := ListRep.allocated hr

theorem RecordsAt.mono {W : ℕ} {h h' : Heap} (he : Extends h h')
    {p : Ptr} {rs : List (EdgeRec W)} (hr : RecordsAt h p rs) : RecordsAt h' p rs :=
  ListRep.mono he (fun _ _ h => h.mono he) hr

theorem RecordsAt.nil {W : ℕ} {h : Heap} {p : Ptr} (hc : h[p]? = some .nil) :
    RecordsAt h p ([] : List (EdgeRec W)) := ⟨[], .nil hc, .nil⟩

theorem RecordsAt.cons {W : ℕ} {h : Heap} {p head tail : Ptr}
    {r : EdgeRec W} {rs : List (EdgeRec W)}
    (hc : h[p]? = some (.cons head tail)) (hh : EdgeRecAt h head r)
    (ht : RecordsAt h tail rs) : RecordsAt h p (r :: rs) := by
  obtain ⟨ps, hp, hw⟩ := ht
  exact ⟨head :: ps, .cons hc hp, .cons hh hw⟩

theorem RecordsAt.nil_iff {W : ℕ} {h : Heap} {p : Ptr} :
    RecordsAt h p ([] : List (EdgeRec W)) ↔ h[p]? = some .nil := by
  constructor
  · rintro ⟨ps, hp, hw⟩
    cases hw
    cases hp with
    | nil hc => exact hc
  · exact RecordsAt.nil

theorem RecordsAt.cons_iff {W : ℕ} {h : Heap} {p : Ptr}
    {r : EdgeRec W} {rs : List (EdgeRec W)} :
    RecordsAt h p (r :: rs) ↔ ∃ head tail, h[p]? = some (.cons head tail) ∧
      EdgeRecAt h head r ∧ RecordsAt h tail rs := by
  constructor
  · rintro ⟨ps, hp, hw⟩
    cases hw with
    | cons head rest =>
      cases hp with
      | cons hc ht => exact ⟨_, _, hc, head, _, ht, rest⟩
  · rintro ⟨head, tail, hc, hh, ht⟩
    exact RecordsAt.cons hc hh ht

end WeightedMIS.RibbonTable
