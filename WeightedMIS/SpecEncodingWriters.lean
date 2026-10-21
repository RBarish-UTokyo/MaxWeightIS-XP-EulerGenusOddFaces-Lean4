module

public import WeightedMIS.SpecMachine
public import WeightedMIS.SpecFlags
public import WeightedMIS.RibbonTable
public import WeightedMIS.ExpandedWords
public import WeightedMIS.RegisterRationalRow

/-!
# Heap writers of the statement-level input encoding

Each writer of `WeightedMIS.Spec` (`putCell`, `putBits`, `putPair`, `putList`,
`putEdge`, `putRat`) appends a fixed number of cells to a valid heap, keeps
the heap valid, never changes old cells, and returns an allocated pointer to
the internal representation of the written value: `BitsAt` for words,
`EdgeRecAt` for edge records, `StoredRational.At` for rationals, and
`ListRep` for lists. The statement word `bitsOf W k` is the internal word
`SparseSearchGraph.encodeBits W (k % 2 ^ W)`.
-/

@[expose] public section

namespace WeightedMIS.SpecEncoding

open WeightedMIS.Spec WeightedMIS.PointerMemory WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer

/-- `put` appends exactly `k` cells to every valid heap, keeps it valid, and
returns an allocated pointer satisfying `R` in the new heap. -/
def Writes (put : Heap → Heap × Ptr) (R : Heap → Ptr → Prop) (k : ℕ) : Prop :=
  ∀ h, Valid h → Extends h (put h).1 ∧ Valid (put h).1 ∧ R (put h).1 (put h).2 ∧
    (put h).2 < (put h).1.length ∧ (put h).1.length = h.length + k

/-- A representation predicate that survives heap extension. -/
def Mono (R : Heap → Ptr → Prop) : Prop := ∀ h h' : Heap, Extends h h' → ∀ p, R h p → R h' p

theorem Writes.weaken {put : Heap → Heap × Ptr} {R S : Heap → Ptr → Prop} {k : ℕ}
    (hw : Writes put R k) (hRS : ∀ h p, R h p → S h p) : Writes put S k := by
  intro h hh
  obtain ⟨e, v, r, a, l⟩ := hw h hh
  exact ⟨e, v, hRS _ _ r, a, l⟩

theorem Writes.size {put : Heap → Heap × Ptr} {R : Heap → Ptr → Prop} {k k' : ℕ}
    (hw : Writes put R k) (hk : k = k') : Writes put R k' := hk ▸ hw

/-! ## Single cells -/

theorem null_lt {h : Heap} (hh : Valid h) : 0 < h.length :=
  List.getElem?_eq_some_iff.mp hh.1 |>.1

theorem putCell_spec {h : Heap} (hh : Valid h) {c : Cell} (hc : c.Fits h.length) :
    Extends h (putCell c h).1 ∧ Valid (putCell c h).1 ∧
      (putCell c h).1[(putCell c h).2]? = some c ∧
      (putCell c h).2 < (putCell c h).1.length ∧ (putCell c h).1.length = h.length + 1 := by
  have hs := safe_allocate h hh c hc
  refine ⟨hs.1, hs.2.1, ?_, ?_, ?_⟩ <;> simp [putCell]

/-! ## Binary words -/

theorem bitsOf_length (W k : ℕ) : (bitsOf W k).length = W := by
  induction W with
  | zero => rfl
  | succ W ih => simp [bitsOf, ih]

/-- The statement word of `k` is the internal word of `k mod 2 ^ W`. -/
theorem encodeBits_mod_succ (W k : ℕ) :
    SparseSearchGraph.encodeBits (W + 1) (k % 2 ^ (W + 1)) =
      .cons (k.testBit W) (SparseSearchGraph.encodeBits W (k % 2 ^ W)) := by
  have hmod : k % 2 ^ (W + 1) % 2 ^ W = k % 2 ^ W :=
    Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (Nat.le_succ W))
  have hbit : decide (2 ^ W ≤ k % 2 ^ (W + 1)) = k.testBit W := by
    rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
    have hlt : k % 2 ^ W < 2 ^ W := Nat.mod_lt _ (by positivity)
    rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ W) with h0 | h1
    · rw [h0]; simp; omega
    · rw [h1]; simp
  simp only [SparseSearchGraph.encodeBits, hmod, hbit]

theorem putBits_bitsOf (W k : ℕ) :
    Writes (putBits (bitsOf W k))
      (fun h p => BitsAt h p (SparseSearchGraph.encodeBits W (k % 2 ^ W))) W := by
  induction W with
  | zero =>
    intro h hh
    refine ⟨.refl h, hh, ?_, null_lt hh, by simp [putBits, bitsOf]⟩
    simp only [bitsOf, putBits]
    exact .nil hh.1
  | succ W ih =>
    intro h hh
    obtain ⟨e, v, r, a, l⟩ := ih h hh
    obtain ⟨e', v', c, a', l'⟩ := putCell_spec v (c := .bit (k.testBit W) (putBits (bitsOf W k) h).2)
      (by intro q hq; simp only [Cell.references, List.mem_singleton] at hq; exact hq ▸ a)
    simp only [bitsOf, putBits]
    refine ⟨e.trans e', v', ?_, a', by omega⟩
    rw [encodeBits_mod_succ]
    exact .cons c (r.mono e')

/-- Writing `bitsOf W k` for `k < 2 ^ W` stores the internal word `word W k`. -/
theorem putBits_word {W k : ℕ} (hk : k < 2 ^ W) :
    Writes (putBits (bitsOf W k)) (fun h p => BitsAt h p (RibbonTable.word W k)) W := by
  have := putBits_bitsOf W k
  rwa [Nat.mod_eq_of_lt hk] at this

/-- `bitsOf` agrees with `encodeBits` bit by bit (as lists). -/
def bitsList : {n : ℕ} → Bits n → List Bool
  | _, .nil => []
  | _, .cons b t => b :: bitsList t

theorem bitsList_encodeBits (W k : ℕ) :
    bitsList (SparseSearchGraph.encodeBits W (k % 2 ^ W)) = bitsOf W k := by
  induction W with
  | zero => rfl
  | succ W ih => rw [encodeBits_mod_succ]; simp [bitsList, bitsOf, ih]

theorem bitsList_word {W k : ℕ} (hk : k < 2 ^ W) : bitsList (RibbonTable.word W k) = bitsOf W k := by
  have := bitsList_encodeBits W k
  rwa [Nat.mod_eq_of_lt hk] at this

/-! ## Pairs and lists -/

theorem putPair_spec {a b : Heap → Heap × Ptr} {Ra Rb : Heap → Ptr → Prop} {ka kb : ℕ}
    (ha : Writes a Ra ka) (hb : Writes b Rb kb) (hm : Mono Ra) (hmb : Mono Rb) :
    Writes (putPair a b) (fun h p => ∃ x y, h[p]? = some (.pair x y) ∧ Ra h x ∧ Rb h y)
      (ka + kb + 1) := by
  intro h hh
  obtain ⟨e1, v1, r1, a1, l1⟩ := ha h hh
  obtain ⟨e2, v2, r2, a2, l2⟩ := hb _ v1
  obtain ⟨e3, v3, c3, a3, l3⟩ := putCell_spec v2 (c := .pair (a h).2 (b (a h).1).2) (by
    intro q hq
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact lt_of_lt_of_le a1 e2.length_le
    · exact a2)
  refine ⟨e1.trans (e2.trans e3), v3, ⟨_, _, c3, hm _ _ (e2.trans e3) _ r1, hmb _ _ e3 _ r2⟩, a3, ?_⟩
  simp only [putPair] at l3 ⊢
  omega

theorem putList_spec {α β : Type} {put : α → Heap → Heap × Ptr} {R : Heap → Ptr → β → Prop}
    {f : α → β} {k : ℕ} (hm : ∀ b, Mono (fun h p => R h p b)) (xs : List α)
    (hput : ∀ x ∈ xs, Writes (put x) (fun h p => R h p (f x)) k) :
    Writes (putList put xs) (fun h p => ListRep R h p (xs.map f)) (xs.length * (k + 1)) := by
  induction xs with
  | nil =>
    intro h hh
    refine ⟨.refl h, hh, ⟨[], .nil hh.1, .nil⟩, null_lt hh, by simp [putList]⟩
  | cons x xs ih =>
    intro h hh
    obtain ⟨e1, v1, ⟨ps, hl, hr⟩, a1, l1⟩ := ih (fun y hy => hput y (by simp [hy])) h hh
    obtain ⟨e2, v2, r2, a2, l2⟩ := hput x (by simp) _ v1
    obtain ⟨e3, v3, c3, a3, l3⟩ := putCell_spec v2
      (c := .cons (put x (putList put xs h).1).2 (putList put xs h).2) (by
        intro q hq
        simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact a2
        · exact lt_of_lt_of_le a1 e2.length_le)
    simp only [putList, List.map_cons, List.length_cons] at l3 ⊢
    refine ⟨e1.trans (e2.trans e3), v3, ⟨_ :: ps, .cons c3 (hl.mono (e2.trans e3)),
      .cons (hm _ _ _ e3 _ r2) (hr.imp fun _ _ hq => hm _ _ _ (e2.trans e3) _ hq)⟩, a3, ?_⟩
    rw [l3, l2, l1]
    ring

/-! ## Monotonicity of the representations used -/

theorem bitsAt_mono {n : ℕ} (b : Bits n) : Mono (fun h p => BitsAt h p b) :=
  fun _ _ he _ hb => hb.mono he

theorem pair_mono {Ra Rb : Heap → Ptr → Prop} (ha : Mono Ra) (hb : Mono Rb) :
    Mono (fun h p => ∃ x y, h[p]? = some (.pair x y) ∧ Ra h x ∧ Rb h y) := by
  rintro h h' he p ⟨x, y, c, rx, ry⟩
  exact ⟨x, y, he.lookup c, ha _ _ he _ rx, hb _ _ he _ ry⟩

/-! ## Flag keys and edge records -/

theorem putBits_flagKey {W m : ℕ} (hm : m < 2 ^ W) (x : Spec.Flag (Fin m)) :
    Writes (putBits (flagBits W x))
      (fun h p => BitsAt h p (RibbonTable.flagKey W (Spec.Flag.equiv _ x))) (W + 2) := by
  intro h hh
  have hw := putBits_word (W := W) (k := x.edge.val) (x.edge.isLt.trans hm) h hh
  obtain ⟨e1, v1, r1, a1, l1⟩ := hw
  obtain ⟨e2, v2, c2, a2, l2⟩ := putCell_spec v1
    (c := .bit x.endpoint (putBits (bitsOf W x.edge.val) h).2)
    (by intro q hq; simp only [Cell.references, List.mem_singleton] at hq; exact hq ▸ a1)
  obtain ⟨e3, v3, c3, a3, l3⟩ := putCell_spec v2
    (c := .bit x.side (putCell (.bit x.endpoint (putBits (bitsOf W x.edge.val) h).2)
      (putBits (bitsOf W x.edge.val) h).1).2)
    (by intro q hq; simp only [Cell.references, List.mem_singleton] at hq; exact hq ▸ a2)
  simp only [flagBits, putBits]
  refine ⟨e1.trans (e2.trans e3), v3, ?_, a3, by omega⟩
  exact .cons c3 (.cons (e3.lookup c2) ((r1.mono e2).mono e3))

/-- The number of cells of one edge record. -/
def edgeCells (W : ℕ) : ℕ := 7 * W + 14

/-- The drawing's corner map on internal flags. -/
def cornerMap (D : Drawing) (y : EmbeddingFaces.Flag (Fin D.edges)) :
    EmbeddingFaces.Flag (Fin D.edges) :=
  Spec.Flag.equiv _ (D.corner ((Spec.Flag.equiv _).symm y))

theorem putEdge_spec (D : Drawing) {W : ℕ} (hm : D.edges < 2 ^ W) (hn : D.vertices < 2 ^ W)
    (e : Fin D.edges) :
    Writes (putEdge D W e)
      (fun h p => RibbonTable.EdgeRecAt h p (RibbonTable.encodeEdge W D.left D.right (cornerMap D) e))
      (edgeCells W) := by
  have hc : ∀ s t, Writes (putBits (flagBits W (D.corner ⟨e, s, t⟩)))
      (fun h p => BitsAt h p (RibbonTable.flagKey W (cornerMap D ⟨e, s, t⟩))) (W + 2) :=
    fun s t => putBits_flagKey hm _
  have b2 : ∀ {x y : Bits (W + 2)}, Mono (fun h p => ∃ u v, h[p]? = some (.pair u v) ∧
      BitsAt h u x ∧ BitsAt h v y) := pair_mono (bitsAt_mono _) (bitsAt_mono _)
  have hq0 := putPair_spec (hc false false) (hc false true) (bitsAt_mono _) (bitsAt_mono _)
  have hq1 := putPair_spec (hc true false) (hc true true) (bitsAt_mono _) (bitsAt_mono _)
  have hc4 := putPair_spec hq0 hq1 b2 b2
  have hr := putPair_spec (putBits_word ((D.right e).isLt.trans hn)) hc4 (bitsAt_mono _)
    (pair_mono b2 b2)
  have hl := putPair_spec (putBits_word ((D.left e).isLt.trans hn)) hr (bitsAt_mono _)
    (pair_mono (bitsAt_mono _) (pair_mono b2 b2))
  have hk := putPair_spec (putBits_word (e.isLt.trans hm)) hl (bitsAt_mono _)
    (pair_mono (bitsAt_mono _) (pair_mono (bitsAt_mono _) (pair_mono b2 b2)))
  refine (hk.weaken ?_).size (by simp only [edgeCells]; ring)
  rintro h p ⟨kp, a, c1, k1, lp, b, c2, k2, rp, c, c3, k3, q0, q1, c4,
    ⟨c00p, c01p, c5, k00, k01⟩, ⟨c10p, c11p, c6, k10, k11⟩⟩
  exact ⟨kp, a, lp, b, rp, c, q0, q1, c00p, c01p, c10p, c11p,
    c1, k1, c2, k2, c3, k3, c4, c5, k00, k01, c6, k10, k11⟩

/-! ## Rationals -/

/-- The stored word of a rational in lowest terms at a given width. -/
def ratWord (width : ℕ) (q : ℚ) : BinaryRational.Word width :=
  ⟨decide (q.num < 0), SparseSearchGraph.encodeBits width q.num.natAbs,
    SparseSearchGraph.encodeBits width q.den⟩

/-- A rational fits a width when its absolute numerator and denominator do. -/
def RatFits (width : ℕ) (q : ℚ) : Prop := q.num.natAbs < 2 ^ width ∧ q.den < 2 ^ width

theorem ratWord_value {width : ℕ} {q : ℚ} (hq : RatFits width q) : (ratWord width q).value = q := by
  unfold BinaryRational.Word.value BinaryRational.Word.numerator ratWord
  simp only [SparseSearchGraph.encodeBits_value _ _ hq.1, SparseSearchGraph.encodeBits_value _ _ hq.2]
  have hnum : (if decide (q.num < 0) = true then -(q.num.natAbs : ℤ) else (q.num.natAbs : ℤ)) = q.num := by
    rw [Int.natCast_natAbs]
    by_cases h : q.num < 0
    · simp [h, abs_of_neg h]
    · simp [h, abs_of_nonneg (not_lt.mp h)]
  rw [hnum]
  exact Rat.num_div_den q

theorem ratWord_canonical {width : ℕ} {q : ℚ} (hq : RatFits width q) :
    BinaryRational.Canonical (ratWord width q) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [ratWord, SparseSearchGraph.encodeBits_value _ _ hq.2, q.den_pos]
  · rw [ratWord_value hq]; simp [ratWord, SparseSearchGraph.encodeBits_value _ _ hq.1]
  · rw [ratWord_value hq]; simp [ratWord, SparseSearchGraph.encodeBits_value _ _ hq.2]

theorem putRat_spec (width : ℕ) (q : ℚ) :
    Writes (putRat width q)
      (fun h p => StoredRational.At h p
        (⟨decide (q.num < 0), SparseSearchGraph.encodeBits width (q.num.natAbs % 2 ^ width),
          SparseSearchGraph.encodeBits width (q.den % 2 ^ width)⟩ : BinaryRational.Word width))
      (2 * width + 2) := by
  have hsign : Writes
      (fun h => putCell (.bit (decide (q.num < 0)) (putBits (bitsOf width q.num.natAbs) h).2)
        (putBits (bitsOf width q.num.natAbs) h).1)
      (fun h p => ∃ np, h[p]? = some (.bit (decide (q.num < 0)) np) ∧
        BitsAt h np (SparseSearchGraph.encodeBits width (q.num.natAbs % 2 ^ width))) (width + 1) := by
    intro h hh
    dsimp only
    obtain ⟨e1, v1, r1, a1, l1⟩ := putBits_bitsOf width q.num.natAbs h hh
    obtain ⟨e2, v2, c2, a2, l2⟩ := putCell_spec v1
      (c := .bit (decide (q.num < 0)) (putBits (bitsOf width q.num.natAbs) h).2)
      (by intro x hx; simp only [Cell.references, List.mem_singleton] at hx; exact hx ▸ a1)
    exact ⟨e1.trans e2, v2, ⟨_, c2, r1.mono e2⟩, a2, by omega⟩
  have hsm : Mono (fun h p => ∃ np, h[p]? = some (.bit (decide (q.num < 0)) np) ∧
      BitsAt h np (SparseSearchGraph.encodeBits width (q.num.natAbs % 2 ^ width))) := by
    rintro h h' he p ⟨np, c, b⟩
    exact ⟨np, he.lookup c, b.mono he⟩
  have hp := putPair_spec hsign (putBits_bitsOf width q.den) hsm (bitsAt_mono _)
  refine (hp.weaken ?_).size (by ring)
  rintro h p ⟨sp, dp, c, ⟨np, cs, bn⟩, bd⟩
  exact ⟨sp, np, dp, c, cs, bn, bd⟩

theorem putRat_word {width : ℕ} {q : ℚ} (hq : RatFits width q) :
    Writes (putRat width q) (fun h p => StoredRational.At h p (ratWord width q)) (2 * width + 2) := by
  have := putRat_spec width q
  rwa [Nat.mod_eq_of_lt hq.1, Nat.mod_eq_of_lt hq.2] at this

end WeightedMIS.SpecEncoding
