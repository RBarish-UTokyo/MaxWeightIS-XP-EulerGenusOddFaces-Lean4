module

public import WeightedMIS.RegisterIncidenceRows
public import WeightedMIS.RegisterListFind
public import WeightedMIS.RegisterListZip

/-!
# First-edge scan over edge-count records

An edge-count record is a `pair` cell holding an edge record
`.pair leftWord rightWord` and an unsigned count word. The record list is
built by zipping the stored edge list with the stored count list. A fixed
predicate procedure compares the two queried vertex words with both endpoint
words, in both orientations, using the binary comparator; the list search
combinator returns the first matching record.

On the records of a graph with vertex words `word W v`, the first matching
record is exactly the record of `GraphSearch.edgeBetween` on
`List.finRange m`.
-/

@[expose] public section

namespace WeightedMIS.RegisterFirstEdge

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords
open WeightedMIS.GraphReachEncoded
open WeightedMIS.RegisterIncidenceRows (EdgeAt eqb eqb_word)

variable {W B : ℕ}

/-! ## Heap helpers -/

theorem allocate_fits {h : Heap} (hh : Valid h) {c : Cell} (hc : c.Fits h.length) :
    Extends h (h ++ [c]) ∧ Valid (h ++ [c]) ∧ (h ++ [c])[h.length]? = some c := by
  have hs := safe_allocate h hh c hc
  exact ⟨by simpa [Program.allocate] using hs.1, by simpa [Program.allocate] using hs.2.1,
    by simp⟩

theorem pair_fits {h : Heap} {a b : Ptr} (ha : a < h.length) (hb : b < h.length) :
    (Cell.pair a b).Fits h.length := by
  intro q hq
  simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ha
  · exact hb

theorem cons_fits {h : Heap} {a b : Ptr} (ha : a < h.length) (hb : b < h.length) :
    (Cell.cons a b).Fits h.length := by
  intro q hq
  simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ha
  · exact hb

theorem bit_fits {h : Heap} {b : Bool} {a : Ptr} (ha : a < h.length) :
    (Cell.bit b a).Fits h.length := by
  intro q hq
  simp only [Cell.references, List.mem_singleton] at hq
  exact hq ▸ ha

theorem lt_of_ext {h h' : Heap} (he : Extends h h') {b : Ptr} (hb : b < h.length) :
    b < h'.length :=
  lt_of_lt_of_le hb he.length_le

/-! ## Records and the matching predicate -/

/-- An edge with its count. -/
abbrev Record (W B : ℕ) := (Bits W × Bits W) × Bits B

/-- A record `.pair edgeRecord countWord`. -/
def RecordAt (h : Heap) (p : Ptr) (r : Record W B) : Prop :=
  ∃ ep cp, h[p]? = some (.pair ep cp) ∧ EdgeAt h ep r.1 ∧ BitsAt h cp r.2

theorem RecordAt.mono {h h' : Heap} (he : Extends h h') {p : Ptr} {r : Record W B}
    (hr : RecordAt h p r) : RecordAt h' p r := by
  obtain ⟨ep, cp, c, hep, hcp⟩ := hr
  exact ⟨ep, cp, he.lookup c, hep.mono he, hcp.mono he⟩

theorem RecordAt.allocated {h : Heap} {p : Ptr} {r : Record W B} (hr : RecordAt h p r) :
    p < h.length := by
  obtain ⟨_, _, c, -⟩ := hr
  exact (List.getElem?_eq_some_iff.mp c).1

abbrev RecordsAt (h : Heap) (p : Ptr) (rs : List (Record W B)) : Prop := ListRep RecordAt h p rs

theorem RecordsAt.mono {h h' : Heap} (he : Extends h h') {p : Ptr} {rs : List (Record W B)}
    (hr : RecordsAt h p rs) : RecordsAt h' p rs :=
  ListRep.mono he (fun _ _ hx => hx.mono he) hr

/-- A query `.pair firstWord secondWord`. -/
def QueryAt (h : Heap) (p : Ptr) (q : Bits W × Bits W) : Prop :=
  ∃ up vp, h[p]? = some (.pair up vp) ∧ BitsAt h up q.1 ∧ BitsAt h vp q.2

theorem QueryAt.mono {h h' : Heap} (he : Extends h h') {p : Ptr} {q : Bits W × Bits W}
    (hq : QueryAt h p q) : QueryAt h' p q := by
  obtain ⟨up, vp, c, hu, hv⟩ := hq
  exact ⟨up, vp, he.lookup c, hu.mono he, hv.mono he⟩

/-- The second orientation test. -/
def other (u v : Bits W) (e : Bits W × Bits W) : Bool :=
  if eqb e.1 v then eqb e.2 u else false

/-- The edge joins the two queried words, in either orientation. -/
def matchW (u v : Bits W) (e : Bits W × Bits W) : Bool :=
  if eqb e.1 u then (if eqb e.2 v then true else other u v e) else other u v e

/-- The search predicate on records. -/
def pred (q : Bits W × Bits W) (r : Record W B) : Bool := matchW q.1 q.2 r.1

theorem matchW_eq (u v : Bits W) (e : Bits W × Bits W) :
    matchW u v e = ((eqb e.1 u && eqb e.2 v) || (eqb e.1 v && eqb e.2 u)) := by
  unfold matchW other
  cases eqb e.1 u <;> cases eqb e.2 v <;> cases eqb e.1 v <;> cases eqb e.2 u <;> rfl

/-- The records of a graph with counts, in edge order. -/
def records (W : ℕ) {n m : ℕ} (left right : Fin m → Fin n) (yw : Fin m → Bits B) :
    List (Record W B) :=
  (List.finRange m).map fun e => ((word W (left e).val, word W (right e).val), yw e)

theorem zip_map_same {α β γ : Type*} (l : List α) (f : α → β) (g : α → γ) :
    List.zipWith (fun a b => (a, b)) (l.map f) (l.map g) = l.map fun x => (f x, g x) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem records_eq_zip {n m : ℕ} (left right : Fin m → Fin n) (yw : Fin m → Bits B) :
    List.zipWith (fun a b => (a, b)) (edgeWords W left right) ((List.finRange m).map yw) =
      records W left right yw := by
  unfold edgeWords records
  exact zip_map_same _ _ _

/-- The first matching record is the record of the first joining edge. -/
theorem find_records {n m : ℕ} (hn : n < 2 ^ W) (left right : Fin m → Fin n)
    (yw : Fin m → Bits B) (u v : Fin n) :
    (records W left right yw).find? (pred (word W u.val, word W v.val)) =
      (GraphSearch.edgeBetween left right (List.finRange m) u v).map
        (fun e => ((word W (left e).val, word W (right e).val), yw e)) := by
  unfold records GraphSearch.edgeBetween
  rw [List.find?_map]
  congr 1
  apply congrArg (fun p => (List.finRange m).find? p)
  funext e
  simp only [Function.comp_apply, pred, matchW_eq, eqb_word hn]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]

/-! ## Procedures -/

variable {p : ℕ}

/-- Arguments: edge record, count word, unused data. -/
def recordItemBody : Command p :=
  .allocate 3 (.pair (.register 0) (.register 1)) (.ret [.register 3])

/-- Second orientation, with endpoints in registers 4,5 and query words in 6,7. -/
def otherBody (cmp : Fin p) : Command p :=
  .call cmp [.register 4, .register 7] [12, 13]
    (.branch (.register 13)
      (.call cmp [.register 5, .register 6] [14, 8] (.ret [.register 8]))
      (.ret [.flag false]))

/-- Arguments: record, query. Result: the matching flag. -/
def matchBody (cmp : Fin p) : Command p :=
  .load (.register 0) 2 3 15 { CompiledTrie.failCases with
    pair := .load (.register 2) 4 5 15 { CompiledTrie.failCases with
      pair := .load (.register 1) 6 7 15 { CompiledTrie.failCases with
        pair := .call cmp [.register 4, .register 6] [8, 9]
          (.branch (.register 9)
            (.call cmp [.register 5, .register 7] [10, 11]
              (.branch (.register 11) (.ret [.flag true]) (otherBody cmp)))
            (otherBody cmp)) } } }

def matchBudget (W : ℕ) : ℕ := 150 * W + 200

def findBudget (W M : ℕ) : ℕ := (matchBudget W + 30) * M + 15

theorem recordItem_compiled (code : Code p) (item : Fin p) (hitem : code item = recordItemBody)
    {h : Heap} (hh : Valid h) {ap bp dp : Ptr} {e : Bits W × Bits W} {c : Bits B}
    (ha : EdgeAt h ap e) (hb : BitsAt h bp c) :
    ∃ out q, Extends h out ∧ Valid out ∧ RecordAt out q (e, c) ∧
      Within code h (initialRegisters [.pointer ap, .pointer bp, .pointer dp])
        (code item) [.pointer q] out 11 := by
  have hal : ap < h.length := by
    obtain ⟨_, _, cell, -⟩ := ha
    exact (List.getElem?_eq_some_iff.mp cell).1
  obtain ⟨ex, v1, c1⟩ := allocate_fits hh
    (pair_fits hal hb.allocated)
  refine ⟨_, h.length, ex, v1, ⟨ap, bp, c1, ha.mono ex, hb.mono ex⟩, ?_⟩
  let regs := initialRegisters [Value.pointer ap, .pointer bp, .pointer dp]
  have last := Within.ret code (h ++ [.pair ap bp]) (Function.update regs 3 (.pointer h.length))
    [.register 3]
  have al := Within.allocate (regs := regs) (dst := 3) (h := h)
    (expr := .pair (.register 0) (.register 1)) (c := .pair ap bp)
    (by simp [CellExpr.eval, Atom.eval, regs, initialRegisters, Value.asPointer])
    (by simpa [values, Atom.eval] using last)
  rw [hitem]
  exact al.mono (by simp [CellExpr.args])

theorem eqFlag (a b : Bits W) :
    decide ((Bits.compare a b).1 = .eq) = eqb a b := rfl

theorem other_within (code : Code p) (cmp : Fin p)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    {h : Heap} {regs : Registers} {lp rp up vp : Ptr} {l r u v : Bits W}
    (h4 : regs 4 = .pointer lp) (h5 : regs 5 = .pointer rp) (h6 : regs 6 = .pointer up)
    (h7 : regs 7 = .pointer vp) (hl : BitsAt h lp l) (hr : BitsAt h rp r)
    (hu : BitsAt h up u) (hv : BitsAt h vp v) :
    Within code h regs (otherBody cmp) [.flag (other u v (l, r))] h (72 * W + 70) := by
  have c1 := RegisterComparator.compiled code cmp hcmp hl hv
  have c2 := RegisterComparator.compiled code cmp hcmp hr hu
  let r1 := bindResults regs [12, 13] (RegisterComparator.flags (Bits.compare l v).1)
  have a1 : values regs [.register 4, .register 7] = [.pointer lp, .pointer vp] := by
    simp [values, Atom.eval, h4, h7]
  by_cases he : eqb l v = true
  · let r2 := bindResults r1 [14, 8] (RegisterComparator.flags (Bits.compare r u).1)
    have last : Within code h r2 (.ret [.register 8]) [.flag (eqb r u)] h 3 := by
      simpa [r2, bindResults, values, Atom.eval, RegisterComparator.flags, eqFlag] using
        Within.ret code h r2 [.register 8]
    have a2 : values r1 [.register 5, .register 6] = [.pointer rp, .pointer up] := by
      simp [r1, bindResults, values, Atom.eval, h5, h6, RegisterComparator.flags]
    have k2 := Within.call (procedure := cmp) (regs := r1)
      (arguments := [.register 5, .register 6]) (results := [14, 8])
      (by simpa only [a2] using c2) last
    have b1 := Within.branch (b := true) (test := .register 13) (regs := r1)
      (no := .ret [.flag false])
      (by simp [r1, bindResults, Atom.eval, RegisterComparator.flags, eqFlag, he]) k2
    have k1 := Within.call (procedure := cmp) (regs := regs)
      (arguments := [.register 4, .register 7]) (results := [12, 13])
      (by simpa only [a1] using c1) b1
    have ho : other u v (l, r) = eqb r u := by simp [other, he]
    rw [ho]
    exact k1.mono (by simp; omega)
  · have hf : eqb l v = false := by simpa using he
    have last : Within code h r1 (.ret [.flag false]) [.flag false] h 3 := by
      simpa [values, Atom.eval] using Within.ret code h r1 [.flag false]
    have b1 := Within.branch (b := false) (test := .register 13) (regs := r1)
      (yes := .call cmp [.register 5, .register 6] [14, 8] (.ret [.register 8]))
      (by simp [r1, bindResults, Atom.eval, RegisterComparator.flags, eqFlag, hf]) last
    have k1 := Within.call (procedure := cmp) (regs := regs)
      (arguments := [.register 4, .register 7]) (results := [12, 13])
      (by simpa only [a1] using c1) b1
    have ho : other u v (l, r) = false := by simp [other, hf]
    rw [ho]
    exact k1.mono (by simp; omega)

theorem match_compiled (code : Code p) (self cmp : Fin p) (hself : code self = matchBody cmp)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    {h : Heap} {rp qp : Ptr} {rec : Record W B} {q : Bits W × Bits W}
    (hrec : RecordAt h rp rec) (hq : QueryAt h qp q) :
    Within code h (initialRegisters [.pointer rp, .pointer qp]) (code self)
      [.flag (pred q rec)] h (matchBudget W) := by
  obtain ⟨ep, cp, cell, ⟨lp, rrp, ecell, hl, hr⟩, -⟩ := hrec
  obtain ⟨up, vp, qcell, hu, hv⟩ := hq
  let regs := initialRegisters [Value.pointer rp, .pointer qp]
  let s1 := loadRegisters regs 2 3 15 (.pair ep cp)
  let s2 := loadRegisters s1 4 5 15 (.pair lp rrp)
  let s3 := loadRegisters s2 6 7 15 (.pair up vp)
  let r1 := bindResults s3 [8, 9] (RegisterComparator.flags (Bits.compare rec.1.1 q.1).1)
  have c1 := RegisterComparator.compiled code cmp hcmp hl hu
  have c2 := RegisterComparator.compiled code cmp hcmp hr hv
  have a1 : values s3 [.register 4, .register 6] = [.pointer lp, .pointer up] := by
    simp [s3, s2, s1, regs, loadRegisters, decoded, values, Atom.eval]
  have o4 : ∀ rs : Registers, rs = r1 ∨ rs = bindResults r1 [10, 11]
      (RegisterComparator.flags (Bits.compare rec.1.2 q.2).1) →
      Within code h rs (otherBody cmp) [.flag (other q.1 q.2 rec.1)] h (72 * W + 70) := by
    intro rs hrs
    have hw := other_within (W := W) code cmp hcmp (regs := rs) (lp := lp) (rp := rrp) (up := up)
      (vp := vp) (l := rec.1.1) (r := rec.1.2) (u := q.1) (v := q.2)
      (by rcases hrs with rfl | rfl <;>
        simp [r1, s3, s2, s1, bindResults, loadRegisters, decoded, RegisterComparator.flags])
      (by rcases hrs with rfl | rfl <;>
        simp [r1, s3, s2, s1, bindResults, loadRegisters, decoded, RegisterComparator.flags])
      (by rcases hrs with rfl | rfl <;>
        simp [r1, s3, s2, s1, bindResults, loadRegisters, decoded, RegisterComparator.flags])
      (by rcases hrs with rfl | rfl <;>
        simp [r1, s3, s2, s1, bindResults, loadRegisters, decoded, RegisterComparator.flags])
      hl hr hu hv
    simpa using hw
  have inner : Within code h r1
      (.branch (.register 9)
        (.call cmp [.register 5, .register 7] [10, 11]
          (.branch (.register 11) (.ret [.flag true]) (otherBody cmp)))
        (otherBody cmp)) [.flag (pred q rec)] h (36 * W + 30 + 3 + 72 * W + 70 + 3) := by
    by_cases he1 : eqb rec.1.1 q.1 = true
    · let r2 := bindResults r1 [10, 11] (RegisterComparator.flags (Bits.compare rec.1.2 q.2).1)
      have a2 : values r1 [.register 5, .register 7] = [.pointer rrp, .pointer vp] := by
        simp [r1, s3, s2, s1, bindResults, loadRegisters, decoded, values, Atom.eval,
          RegisterComparator.flags]
      have tail : Within code h r2 (.branch (.register 11) (.ret [.flag true]) (otherBody cmp))
          [.flag (pred q rec)] h (3 + (72 * W + 70)) := by
        by_cases he2 : eqb rec.1.2 q.2 = true
        · have last : Within code h r2 (.ret [.flag true]) [.flag true] h 3 := by
            simpa [values, Atom.eval] using Within.ret code h r2 [.flag true]
          have b := Within.branch (b := true) (test := .register 11) (regs := r2)
            (no := otherBody cmp)
            (by simp [r2, bindResults, Atom.eval, RegisterComparator.flags, eqFlag, he2]) last
          have hp : pred q rec = true := by simp [pred, matchW, he1, he2]
          rw [hp]
          exact b.mono (by omega)
        · have hf : eqb rec.1.2 q.2 = false := by simpa using he2
          have b := Within.branch (b := false) (test := .register 11) (regs := r2)
            (yes := .ret [.flag true])
            (by simp [r2, bindResults, Atom.eval, RegisterComparator.flags, eqFlag, hf])
            (o4 r2 (Or.inr rfl))
          have hp : pred q rec = other q.1 q.2 rec.1 := by simp [pred, matchW, he1, hf]
          rw [hp]
          exact b
      have k := Within.call (procedure := cmp) (regs := r1)
        (arguments := [.register 5, .register 7]) (results := [10, 11])
        (by simpa only [a2] using c2) tail
      have b := Within.branch (b := true) (test := .register 9) (regs := r1)
        (no := otherBody cmp)
        (by simp [r1, bindResults, Atom.eval, RegisterComparator.flags, eqFlag, he1]) k
      exact b.mono (by simp; omega)
    · have hf : eqb rec.1.1 q.1 = false := by simpa using he1
      have b := Within.branch (b := false) (test := .register 9) (regs := r1)
        (yes := .call cmp [.register 5, .register 7] [10, 11]
          (.branch (.register 11) (.ret [.flag true]) (otherBody cmp)))
        (by simp [r1, bindResults, Atom.eval, RegisterComparator.flags, eqFlag, hf])
        (o4 r1 (Or.inl rfl))
      have hp : pred q rec = other q.1 q.2 rec.1 := by simp [pred, matchW, hf]
      rw [hp]
      exact b.mono (by omega)
  have k1 := Within.call (procedure := cmp) (regs := s3)
    (arguments := [.register 4, .register 6]) (results := [8, 9])
    (by simpa only [a1] using c1) inner
  have l3 := Within.load (regs := s2) (address := .register 1) (first := 6) (second := 7)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .call cmp [.register 4, .register 6] [8, 9]
        (.branch (.register 9)
          (.call cmp [.register 5, .register 7] [10, 11]
            (.branch (.register 11) (.ret [.flag true]) (otherBody cmp)))
          (otherBody cmp)) })
    (by simp [s2, s1, regs, loadRegisters, decoded, initialRegisters, Atom.eval]) qcell k1
  have l2 := Within.load (regs := s1) (address := .register 2) (first := 4) (second := 5)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .load (.register 1) 6 7 15 { CompiledTrie.failCases with
        pair := .call cmp [.register 4, .register 6] [8, 9]
          (.branch (.register 9)
            (.call cmp [.register 5, .register 7] [10, 11]
              (.branch (.register 11) (.ret [.flag true]) (otherBody cmp)))
            (otherBody cmp)) } })
    (by simp [s1, loadRegisters, decoded, Atom.eval]) ecell l3
  have l1 := Within.load (regs := regs) (address := .register 0) (first := 2) (second := 3)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .load (.register 2) 4 5 15 { CompiledTrie.failCases with
        pair := .load (.register 1) 6 7 15 { CompiledTrie.failCases with
          pair := .call cmp [.register 4, .register 6] [8, 9]
            (.branch (.register 9)
              (.call cmp [.register 5, .register 7] [10, 11]
                (.branch (.register 11) (.ret [.flag true]) (otherBody cmp)))
              (otherBody cmp)) } } })
    (by simp [regs, initialRegisters, Atom.eval]) cell l2
  rw [hself]
  exact l1.mono (by simp [matchBudget]; omega)

/-! ## Record construction and first-edge search -/

structure Procedures (p : ℕ) where
  cmp : Fin p
  recordItem : Fin p
  zip : Fin p
  matchItem : Fin p
  find : Fin p

def Procedures.Matches (d : Procedures p) (code : Code p) : Prop :=
  code d.cmp = RegisterComparator.comparatorBody d.cmp ∧
  code d.recordItem = recordItemBody ∧
  code d.zip = RegisterListZip.body d.zip d.recordItem ∧
  code d.matchItem = matchBody d.cmp ∧
  code d.find = RegisterListFind.body d.find d.matchItem

/-- Zipping the stored edge list with the stored count list. -/
theorem records_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {n m : ℕ} (left right : Fin m → Fin n) (yw : Fin m → Bits B)
    {h : Heap} (hh : Valid h) {ep yp : Ptr}
    (he : ListRep EdgeAt h ep (edgeWords W left right))
    (hy : WordsAt h yp ((List.finRange m).map yw)) :
    ∃ out q, Extends h out ∧ Valid out ∧ RecordsAt out q (records W left right yw) ∧
      Within code h (initialRegisters [.pointer ep, .pointer yp, .pointer 0]) (code d.zip)
        [.pointer q] out (56 * m + 23) := by
  obtain ⟨-, hitem, hzip, -, -⟩ := hm
  obtain ⟨out, q, hx, hv, hq, run⟩ := RegisterListZip.compiled_const code d.zip d.recordItem hzip
    EdgeAt (fun h p (c : Bits B) => BitsAt h p c) (fun _ _ (_ : Unit) => True) RecordAt
    (fun he _ _ hx => hx.mono he) (fun he _ _ hx => hx.mono he) (fun _ _ _ _ => trivial)
    (fun he _ _ hx => hx.mono he) (fun _ hx => hx.allocated) (fun _ a b => (a, b)) 11
    (dataPtr := 0) (data := ()) hh he hy trivial
    (fun hv _ _ _ _ _ ha hb _ => recordItem_compiled code d.recordItem hitem hv ha hb)
  refine ⟨out, q, hx, hv, ?_, run.mono ?_⟩
  · rw [← records_eq_zip]
    exact hq
  · simp [edgeWords]

/-- First matching record: the flag says whether one exists; the pointer is the
shared address of the first matching record. -/
theorem find_compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {h : Heap} (hh : Valid h) {rp qp : Ptr} {rs : List (Record W B)} {q : Bits W × Bits W}
    (hr : RecordsAt h rp rs) (hq : QueryAt h qp q) :
    ∃ out r, Extends h out ∧ Valid out ∧
      (∀ x, rs.find? (pred q) = some x → RecordAt out r x) ∧
      Within code h (initialRegisters [.pointer rp, .pointer qp]) (code d.find)
        [.flag (rs.find? (pred q)).isSome, .pointer r] out (findBudget W rs.length) := by
  obtain ⟨hcmp, -, -, hmatch, hfind⟩ := hm
  obtain ⟨out, r, hx, hv, hfound, -, run⟩ := RegisterListFind.compiled_const code d.find
    d.matchItem hfind RecordAt QueryAt (fun he _ _ hx => hx.mono he) (fun he _ _ hx => hx.mono he)
    pred (matchBudget W) hh hr hq
    (fun hv _ _ _ hx hq' =>
      ⟨_, .refl _, hv, match_compiled code d.matchItem d.cmp hmatch hcmp hx hq'⟩)
  exact ⟨out, r, hx, hv, hfound, run⟩

end WeightedMIS.RegisterFirstEdge
