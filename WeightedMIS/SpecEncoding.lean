module

public import WeightedMIS.SpecEncodingWriters
public import WeightedMIS.GraphReachEncoded
public import WeightedMIS.RegisterMachineBounds

/-!
# The encoded input and output in internal representations

The heap `(encode D w).1` is valid, its root `(encode D w).2` is allocated,
and the root record is `(vertices, (edges, weights))` where

* `vertices` is the word list `rangeWords W |V|` (`ExpandedWords.WordsAt`);
* `edges` is the record table `encodeRibbon W R` (`RibbonTable.RecordsAt`) of
  every internal corner system `R` whose corner map is `D.corner` read through
  `Spec.Flag.equiv`;
* `weights` is a row of canonical stored rationals with values `w v`
  (`RegisterRationalRow.RowAt`),

with `W = indexWidth D`, and every vertex and edge index below `2 ^ W`. The
heap has an explicit number of cells, bounded by
`100 · N ^ 2 · (L + 1)`. Conversely, an internal word list of a vertex set is
an output list in the sense of `Spec.NumbersAt`.
-/

@[expose] public section

namespace WeightedMIS.SpecEncoding

open WeightedMIS.Spec WeightedMIS.PointerMemory WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.RegisterMachine

/-! ## Widths -/

theorem vertices_lt (D : Drawing) : D.vertices < 2 ^ indexWidth D :=
  lt_of_le_of_lt (Nat.le_add_right _ _) (Nat.lt_size_self _)

theorem edges_lt (D : Drawing) : D.edges < 2 ^ indexWidth D :=
  lt_of_le_of_lt (Nat.le_add_left _ _) (Nat.lt_size_self _)

theorem indexWidth_le (D : Drawing) : indexWidth D ≤ D.vertices + D.edges :=
  Nat.size_le.mpr Nat.lt_two_pow_self

theorem weightWidth_le {n : ℕ} (w : Fin n → ℚ) : weightWidth w ≤ weightLength w := by
  apply Finset.sup_le
  intro v _
  calc max (w v).num.natAbs.size (w v).den.size
      ≤ (w v).num.natAbs.size + (w v).den.size := max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    _ ≤ weightLength w :=
      Finset.single_le_sum (f := fun v => (w v).num.natAbs.size + (w v).den.size)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)

theorem weight_fits {n : ℕ} (w : Fin n → ℚ) (v : Fin n) : RatFits (weightWidth w) (w v) := by
  have hv := Finset.le_sup (f := fun v => max (w v).num.natAbs.size (w v).den.size)
    (Finset.mem_univ v)
  exact ⟨Nat.size_le.mp (le_trans (le_max_left _ _) hv),
    Nat.size_le.mp (le_trans (le_max_right _ _) hv)⟩

/-- The stored weight row: canonical words of width `weightWidth w`. -/
def weightRow {n : ℕ} (w : Fin n → ℚ) : List (BinaryRational.Word (weightWidth w)) :=
  (List.finRange n).map fun v => ratWord (weightWidth w) (w v)

theorem weightRow_value {n : ℕ} (w : Fin n → ℚ) (v : Fin n) :
    (ratWord (weightWidth w) (w v)).value = w v := ratWord_value (weight_fits w v)

theorem weightRow_canonical {n : ℕ} (w : Fin n → ℚ) (v : Fin n) :
    BinaryRational.Canonical (ratWord (weightWidth w) (w v)) := ratWord_canonical (weight_fits w v)

/-! ## The three lists -/

theorem initial_valid : Valid ([.nil] : Heap) := by
  refine ⟨rfl, ?_⟩
  intro p c hp q hq
  rcases p with _ | p
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
    subst hp
    simp [Cell.references] at hq
  · simp at hp

theorem putVertices_spec (D : Drawing) :
    Writes (putList (fun v => putBits (bitsOf (indexWidth D) v)) (List.range D.vertices))
      (fun h p => ExpandedWords.WordsAt h p (RibbonTable.rangeWords (indexWidth D) D.vertices))
      (D.vertices * (indexWidth D + 1)) := by
  have := putList_spec (R := fun h p (x : Bits (indexWidth D)) => BitsAt h p x)
    (f := RibbonTable.word (indexWidth D)) (fun b => bitsAt_mono b) (List.range D.vertices)
    (fun x hx => putBits_word ((List.mem_range.mp hx).trans (vertices_lt D)))
  exact (this.weaken fun _ _ x => x).size (by simp)

/-- The edge-record table of the drawing's own corner map. -/
def edgeTable (D : Drawing) : List (RibbonTable.EdgeRec (indexWidth D)) :=
  (List.finRange D.edges).map (RibbonTable.encodeEdge (indexWidth D) D.left D.right (cornerMap D))

/-- Every internal ribbon carrying the drawing's corners has the stored table. -/
theorem encodeRibbon_eq (D : Drawing) {R : EmbeddingFaces.Ribbon D.left D.right}
    (hR : ∀ y, R.corner y = Spec.Flag.equiv _ (D.corner ((Spec.Flag.equiv _).symm y))) :
    RibbonTable.encodeRibbon (indexWidth D) R = edgeTable D := by
  have hc : (fun y => R.corner y) = cornerMap D := funext hR
  simp only [RibbonTable.encodeRibbon, edgeTable]
  rw [show (⇑R.corner) = cornerMap D from hc]

theorem putEdges_spec (D : Drawing) :
    Writes (putList (putEdge D (indexWidth D)) (List.finRange D.edges))
      (fun h p => RibbonTable.RecordsAt h p (edgeTable D))
      (D.edges * (edgeCells (indexWidth D) + 1)) := by
  have := putList_spec (R := RibbonTable.EdgeRecAt)
    (f := RibbonTable.encodeEdge (indexWidth D) D.left D.right (cornerMap D))
    (fun r => fun _ _ he _ hr => hr.mono he) (List.finRange D.edges)
    (fun e _ => putEdge_spec D (edges_lt D) (vertices_lt D) e)
  exact (this.weaken fun _ _ x => x).size (by simp)

theorem putWeights_spec {n : ℕ} (w : Fin n → ℚ) :
    Writes (putList (putRat (weightWidth w)) (List.ofFn w))
      (fun h p => RegisterRationalRow.RowAt h p (weightRow w))
      (n * (2 * weightWidth w + 3)) := by
  have := putList_spec (R := fun h p (q : BinaryRational.Word (weightWidth w)) => StoredRational.At h p q)
    (f := ratWord (weightWidth w)) (fun q => fun _ _ he _ hq => hq.mono he) (List.ofFn w)
    (fun x hx => by
      obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hx
      exact putRat_word (weight_fits w v))
  refine (this.weaken ?_).size (by simp)
  intro h p hp
  simp only [List.ofFn_eq_map, List.map_map] at hp
  exact hp

/-! ## The root record -/

/-- The number of cells of the encoded input heap. -/
def encodeCells (D : Drawing) (w : Fin D.vertices → ℚ) : ℕ :=
  1 + (D.vertices * (indexWidth D + 1) +
    (D.edges * (edgeCells (indexWidth D) + 1) + D.vertices * (2 * weightWidth w + 3) + 1) + 1)

/-- **The encoded input.** The heap is valid, the root is allocated, and the
root record holds the vertex words, the edge-record table of the drawing's
corner map, and the canonical weight row. -/
theorem encode_spec (D : Drawing) (w : Fin D.vertices → ℚ) :
    Valid (encode D w).1 ∧ (encode D w).2 < (encode D w).1.length ∧
      (encode D w).1.length = encodeCells D w ∧
      ∃ vp rest tp wp, (encode D w).1[(encode D w).2]? = some (.pair vp rest) ∧
        (encode D w).1[rest]? = some (.pair tp wp) ∧
        ExpandedWords.WordsAt (encode D w).1 vp
          (RibbonTable.rangeWords (indexWidth D) D.vertices) ∧
        RibbonTable.RecordsAt (encode D w).1 tp (edgeTable D) ∧
        RegisterRationalRow.RowAt (encode D w).1 wp (weightRow w) := by
  have hrest := putPair_spec (putEdges_spec D) (putWeights_spec w)
    (fun _ _ he _ hr => hr.mono he) (fun _ _ he _ hr => hr.mono he)
  have hroot := putPair_spec (putVertices_spec D) hrest
    (fun _ _ he _ hr => hr.mono he)
    (pair_mono (fun _ _ he _ hr => hr.mono he) (fun _ _ he _ hr => hr.mono he))
  obtain ⟨-, hv, ⟨vp, rest, hc, hvp, tp, wp, hc', htp, hwp⟩, ha, hl⟩ := hroot _ initial_valid
  refine ⟨hv, ha, ?_, vp, rest, tp, wp, hc, hc', hvp, htp, hwp⟩
  unfold encode
  rw [hl]
  simp [encodeCells]

/-- The root record with the table of any internal ribbon carrying the
drawing's corners (for example `Drawing.ribbon hA W`). -/
theorem encode_root (D : Drawing) (w : Fin D.vertices → ℚ)
    {R : EmbeddingFaces.Ribbon D.left D.right}
    (hR : ∀ y, R.corner y = Spec.Flag.equiv _ (D.corner ((Spec.Flag.equiv _).symm y))) :
    ∃ vp rest tp wp, (encode D w).1[(encode D w).2]? = some (.pair vp rest) ∧
      (encode D w).1[rest]? = some (.pair tp wp) ∧
      ExpandedWords.WordsAt (encode D w).1 vp
        (RibbonTable.rangeWords (indexWidth D) D.vertices) ∧
      RibbonTable.RecordsAt (encode D w).1 tp (RibbonTable.encodeRibbon (indexWidth D) R) ∧
      RegisterRationalRow.RowAt (encode D w).1 wp
        ((List.finRange D.vertices).map fun v => ratWord (weightWidth w) (w v)) := by
  obtain ⟨-, -, -, h⟩ := encode_spec D w
  rwa [encodeRibbon_eq D hR]

/-- The vertex word list of `RibbonTable` is the one of `GraphReachEncoded`. -/
theorem rangeWords_eq (W n : ℕ) :
    GraphReachEncoded.rangeWords W n = RibbonTable.rangeWords W n := by
  rw [GraphReachEncoded.rangeWords_eq_range]
  rfl

theorem encode_valid (D : Drawing) (w : Fin D.vertices → ℚ) : Valid (encode D w).1 :=
  (encode_spec D w).1

theorem encode_root_lt (D : Drawing) (w : Fin D.vertices → ℚ) :
    (encode D w).2 < (encode D w).1.length :=
  (encode_spec D w).2.1

/-- The initial register bank of a run on the encoded input is bounded by the heap. -/
theorem encode_args_bounded (D : Drawing) (w : Fin D.vertices → ℚ) :
    ValuesBound (encode D w).1.length [.pointer (encode D w).2] := by
  intro v hv
  simp only [List.mem_singleton] at hv
  subst hv
  simpa [Value.Bounded, Value.word, Word.Bounded] using encode_root_lt D w

theorem encode_registers_bounded (D : Drawing) (w : Fin D.vertices → ℚ) :
    RegistersBound (encode D w).1.length (initialRegisters [.pointer (encode D w).2]) :=
  initialRegisters_bounded (lt_of_le_of_lt (Nat.zero_le _) (encode_root_lt D w))
    (encode_args_bounded D w)

/-! ## Size of the input heap -/

theorem encode_length (D : Drawing) (w : Fin D.vertices → ℚ) :
    (encode D w).1.length = encodeCells D w := (encode_spec D w).2.2.1

/-- The input heap has at most `100 · N ^ 2 · (L + 1)` cells. -/
theorem encode_length_le (D : Drawing) (w : Fin D.vertices → ℚ) :
    (encode D w).1.length ≤ 100 * D.size ^ 2 * (weightLength w + 1) := by
  rw [encode_length]
  have hW := indexWidth_le D
  have hw := weightWidth_le w
  simp only [encodeCells, edgeCells, Drawing.size]
  generalize indexWidth D = W at hW ⊢
  generalize weightWidth w = a at hw ⊢
  generalize weightLength w = L at hw ⊢
  obtain ⟨N, hN⟩ : ∃ N, D.vertices + D.edges + 1 = N := ⟨_, rfl⟩
  rw [hN]
  have hn : D.vertices < N := by omega
  have hm : D.edges < N := by omega
  have hWN : W + 1 ≤ N := by omega
  have h1 : D.vertices * (W + 1) ≤ N ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul hn.le hWN
  have h2 : D.edges * (7 * W + 14 + 1) ≤ 22 * N ^ 2 := by
    have : 7 * W + 14 + 1 ≤ 22 * N := by omega
    calc D.edges * (7 * W + 14 + 1) ≤ N * (22 * N) := Nat.mul_le_mul hm.le this
      _ = 22 * N ^ 2 := by ring
  have h3 : D.vertices * (2 * a + 3) ≤ 3 * N ^ 2 * (L + 1) := by
    have hN1 : 1 ≤ N := by omega
    calc D.vertices * (2 * a + 3) ≤ N * (3 * (L + 1)) := Nat.mul_le_mul hn.le (by omega)
      _ ≤ N * N * (3 * (L + 1)) := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ hN1)
      _ = 3 * N ^ 2 * (L + 1) := by ring
  have h4 : N ^ 2 ≤ N ^ 2 * (L + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h5 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h6 : 100 * N ^ 2 * (L + 1) = 100 * (N ^ 2 * (L + 1)) := by ring
  have h7 : 3 * N ^ 2 * (L + 1) = 3 * (N ^ 2 * (L + 1)) := by ring
  omega

/-! ## Output words -/

theorem bitsValue_foldl (a : ℕ) (bs : List Bool) :
    bs.foldl (fun a b => 2 * a + if b then 1 else 0) a = a * 2 ^ bs.length + bitsValue bs := by
  induction bs generalizing a with
  | nil => simp [bitsValue]
  | cons b bs ih =>
    simp only [bitsValue, List.foldl_cons, List.length_cons] at ih ⊢
    rw [ih, ih (2 * 0 + _)]
    ring

theorem bitsValue_cons (b : Bool) (bs : List Bool) :
    bitsValue (b :: bs) = (if b then 2 ^ bs.length else 0) + bitsValue bs := by
  have := bitsValue_foldl (2 * 0 + if b then 1 else 0) bs
  simp only [bitsValue, List.foldl_cons] at this ⊢
  rw [this]
  cases b <;> simp

theorem bitsList_length {n : ℕ} (b : Bits n) : (bitsList b).length = n := by
  induction b with
  | nil => rfl
  | cons x t ih => simp [bitsList, ih]

theorem bitsValue_bitsList {n : ℕ} (b : Bits n) : bitsValue (bitsList b) = b.value := by
  induction b with
  | nil => rfl
  | @cons n x t ih => rw [bitsList, bitsValue_cons, ih, bitsList_length]; rfl

theorem wordAt_of_bitsAt {h : Heap} {n : ℕ} {p : Ptr} {b : Bits n} (hb : BitsAt h p b) :
    WordAt h p (bitsList b) := by
  induction hb with
  | nil hc => exact .nil hc
  | cons hc _ ih => exact .cons hc ih

/-- A stored word list denotes the list of its values. -/
theorem numbersAt_of_wordsAt {h : Heap} {n : ℕ} {q : Ptr} {ws : List (Bits n)}
    (hw : ExpandedWords.WordsAt h q ws) : NumbersAt h q (ws.map Bits.value) := by
  obtain ⟨ps, hl, hr⟩ := hw
  induction hl generalizing ws with
  | nil hc => cases hr; exact .nil hc
  | cons hc _ ih =>
    cases hr with
    | cons hb hrest =>
      have := NumbersAt.cons hc (wordAt_of_bitsAt hb) (ih hrest)
      rwa [bitsValue_bitsList] at this

/-- Words of numbers below `2 ^ W` denote those numbers. -/
theorem numbersAt_of_words {h : Heap} {W : ℕ} {q : Ptr} {l : List ℕ} (hl : ∀ x ∈ l, x < 2 ^ W)
    (hw : ExpandedWords.WordsAt h q (l.map (RibbonTable.word W))) : NumbersAt h q l := by
  have := numbersAt_of_wordsAt hw
  rwa [List.map_map, List.map_congr_left (f := Bits.value ∘ RibbonTable.word W) (g := id)
    (fun x hx => RibbonTable.word_value (hl x hx)), List.map_id] at this

/-- The stored word list of a vertex set denotes exactly that set. -/
theorem numbersAt_setWords {h : Heap} {W k : ℕ} (hk : k < 2 ^ W) {q : Ptr} {S : Finset (Fin k)}
    (hw : ExpandedWords.WordsAt h q (GraphReachEncoded.setWords W S)) :
    ∃ l, NumbersAt h q l ∧ ∀ v : Fin k, v ∈ S ↔ v.val ∈ l := by
  refine ⟨((List.finRange k).filter (· ∈ S)).map Fin.val, numbersAt_of_words (W := W) ?_ ?_, ?_⟩
  · intro x hx
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
    exact v.isLt.trans hk
  · rw [List.map_map]
    exact hw
  · intro v
    simp [Fin.val_inj]

/-- A run returning the stored word list of `I` outputs `I`. -/
theorem outputs_of_setWords (D : Drawing) {r : Run (List Value)} {p : Ptr}
    {I : Finset (Fin D.vertices)} (hv : r.value = [.pointer p])
    (hw : ExpandedWords.WordsAt r.heap p (GraphReachEncoded.setWords (indexWidth D) I)) :
    Outputs D r I := by
  obtain ⟨l, hl, hm⟩ := numbersAt_setWords (vertices_lt D) hw
  exact ⟨p, l, hv, hl, hm⟩

end WeightedMIS.SpecEncoding
