module

public import WeightedMIS.RegisterKeyFaceEnumeration
public import WeightedMIS.FaceRowSemantics
public import WeightedMIS.SignedWords
public import WeightedMIS.RegisterSignedAdd
public import WeightedMIS.RegisterListMap

/-!
# Signed rows of stored key cycles

The entry procedure folds a stored key cycle from the right: the entry of the
empty cycle is zero; otherwise the entry of the tail is negated, and one is
added when the edge word of the head key equals the queried edge word. The
row procedure maps the entry over the stored table records, and the rows
procedure maps the row over a list of cycles. The results refine `entryW`,
`rowW` and `rowsW`.
-/

@[expose] public section

namespace WeightedMIS.RegisterFaceRow

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords WeightedMIS.RibbonTable
open WeightedMIS.RegisterFlagKeys WeightedMIS.RegisterKeyTrace WeightedMIS.FaceRowSemantics
open WeightedMIS.RegisterPotentialStep WeightedMIS.SignedWords
open WeightedMIS.RegisterKeyFaceEnumeration

variable {p : ℕ}

/-- The two constants of the signed entries: `pair one zero`. -/
def ConstsAt {b : ℕ} (one zero : Bits b) (h : Heap) (ptr : Ptr) : Prop :=
  ∃ op zp, h[ptr]? = some (.pair op zp) ∧ BitsAt h op one ∧ BitsAt h zp zero

theorem ConstsAt.mono {b : ℕ} {one zero : Bits b} {h h' : Heap} (he : Extends h h') {ptr : Ptr}
    (hc : ConstsAt one zero h ptr) : ConstsAt one zero h' ptr := by
  obtain ⟨op, zp, hp, ho, hz⟩ := hc
  exact ⟨op, zp, he.lookup hp, ho.mono he, hz.mono he⟩

/-- Allocate a signed word cell. -/
def signedRet (sign : Atom) (mag : Register) : Command p :=
  .allocate 10 (.bit sign (.register mag)) (.ret [.register 10])

/-- Arguments 0 = key cycle, 1 = edge word, 2 = constants; the result is the
signed alternating count of the edge on the cycle. -/
def entryBody (self edge cmp sadd : Fin p) : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    nil := .load (.register 2) 5 6 15 { CompiledTrie.failCases with
      pair := .allocate 7 (.bit (.flag false) (.register 6)) (.ret [.register 7]) }
    cons := .call self [.register 4, .register 1, .register 2] [5]
      (.load (.register 5) 6 7 8 { CompiledTrie.failCases with
        bit := .call edge [.register 3] [9]
          (.call cmp [.register 9, .register 1] [10, 11]
            (.branch (.register 11)
              (.load (.register 2) 12 13 15 { CompiledTrie.failCases with
                pair := .branch (.register 8)
                  (.call sadd [.flag false, .register 12, .flag false, .register 6] [14, 15]
                    (signedRet (.register 14) 15))
                  (.call sadd [.flag false, .register 12, .flag true, .register 6] [14, 15]
                    (signedRet (.register 14) 15)) })
              (.branch (.register 8) (signedRet (.flag false) 6) (signedRet (.flag true) 6)))) }) }

/-- Arithmetic procedures used by the entry. -/
structure Arith (p : ℕ) where
  sadd : Fin p
  add : Fin p
  cmp : Fin p
  sub : Fin p
  complement : Fin p

def Arith.Matches (ids : Arith p) (code : Code p) : Prop :=
  code ids.sadd = RegisterSignedAdd.signedAddBody ids.add ids.cmp ids.sub ∧
  code ids.add = RegisterAdder.adderBody ids.add ∧
  code ids.cmp = RegisterComparator.comparatorBody ids.cmp ∧
  code ids.sub = RegisterSubtractor.subtractorBody ids.complement ids.add ∧
  code ids.complement = RegisterComplement.complementBody ids.complement

def entryBudget (W b L : ℕ) : ℕ := (36 * W + 180 * b + 250) * L + 31

theorem alloc_signed {b : ℕ} {h : Heap} (hh : Valid h) (s : Bool) {mp : Ptr} {mag : Bits b}
    (hm : BitsAt h mp mag) :
    Extends h (h ++ [.bit s mp]) ∧ Valid (h ++ [.bit s mp]) ∧
      SignedAt (h ++ [.bit s mp]) h.length (s, mag) := by
  have hs := safe_allocate h hh (.bit s mp) (by
    intro q hq
    simp only [Cell.references, List.mem_singleton] at hq
    exact hq ▸ hm.allocated)
  have he : Extends h (h ++ [.bit s mp]) := hs.1
  refine ⟨he, hs.2.1, mp, ?_, hm.mono he⟩
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem signedRet_within (code : Code p) {b : ℕ} {h : Heap} (hh : Valid h) {regs : Registers}
    {sign : Atom} {mag : Register} {s : Bool} {mp : Ptr} {m : Bits b}
    (hs : sign.eval regs = .flag s) (hmr : regs mag = .pointer mp) (hm : BitsAt h mp m) :
    ∃ out q, Extends h out ∧ Valid out ∧ SignedAt out q (s, m) ∧
      Within code h regs (signedRet sign mag) [.pointer q] out 11 := by
  obtain ⟨e, v, sa⟩ := alloc_signed hh s hm
  refine ⟨_, _, e, v, sa, ?_⟩
  refine (Within.allocate (c := Cell.bit s mp)
    (by rw [CellExpr.eval, hs]; simp [Atom.eval, hmr, Value.asFlag, Value.asPointer])
    (ret_values (by simp [values, Atom.eval]) le_rfl)).mono ?_
  simp [CellExpr.args]

theorem entry_compiled (code : Code p) (self edge : Fin p) (ar : Arith p)
    (hself : code self = entryBody self edge ar.cmp ar.sadd) (hedge : code edge = edgePartBody)
    (har : ar.Matches code) {W b : ℕ} (one zero : Bits b) (e : Bits W) :
    ∀ (c : List (Bits (W + 2))) {h : Heap}, Valid h → ∀ {cp ep kp : Ptr},
      WordsAt h cp c → BitsAt h ep e → ConstsAt one zero h kp →
      ∃ out q, Extends h out ∧ Valid out ∧ SignedAt out q (entryW one zero e c) ∧
        Within code h (initialRegisters [.pointer cp, .pointer ep, .pointer kp]) (code self)
          [.pointer q] out (entryBudget W b c.length) := by
  obtain ⟨hsadd, hadd, hcmp, hsub, hcomp⟩ := har
  intro c
  induction c with
  | nil =>
    intro h hh cp ep kp hc he hk
    have cell := WordsAt.nil_iff.mp hc
    obtain ⟨op, zp, hkp, ho, hz⟩ := hk
    obtain ⟨e1, v1, s1⟩ := alloc_signed hh false hz
    refine ⟨_, _, e1, v1, s1, ?_⟩
    rw [hself]
    apply Within.mono (a := 31) _ (by simp [entryBudget])
    apply Within.load (budget := 21) (pointer := cp) (c := Cell.nil)
    · simp [Atom.eval, initialRegisters]
    · exact cell
    apply Within.load (budget := 11) (pointer := kp) (c := Cell.pair op zp)
    · simp [Atom.eval, loadRegisters, decoded, initialRegisters]
    · exact hkp
    apply Within.allocate (budget := 3) (c := Cell.bit false zp)
    · simp [CellExpr.eval, Atom.eval, loadRegisters, decoded, Value.asFlag, Value.asPointer]
    exact ret_values (by simp [values, Atom.eval]) le_rfl
  | cons k c ih =>
    intro h hh cp ep kp hc he hk
    obtain ⟨xp, rest, cell, hx, hrest⟩ := WordsAt.cons_iff.mp hc
    obtain ⟨m1, vp, e1, v1, s1, w1⟩ := ih hh hrest he hk
    rcases hvc : entryW one zero e c with ⟨vs, vmag⟩
    rw [hvc] at s1
    obtain ⟨mp, hvp, hmag⟩ := s1
    obtain ⟨wp, hw, w2⟩ := edgePart_compiled code edge hedge (hx.mono e1)
    have w3 := RegisterComparator.compiled code ar.cmp hcmp hw (he.mono e1)
    obtain ⟨op, zp, hkp, ho, hz⟩ := hk.mono e1
    let regs := initialRegisters [Value.pointer cp, .pointer ep, .pointer kp]
    let r1 := loadRegisters regs 3 4 15 (.cons xp rest)
    let r2 := bindResults r1 [5] [.pointer vp]
    let r3 := loadRegisters r2 6 7 8 (.bit vs mp)
    let r4 := bindResults r3 [9] [.pointer wp]
    let r5 := bindResults r4 [10, 11] (RegisterComparator.flags (Bits.compare (edgePart k) e).1)
    have h8 : r5 8 = .flag vs := by
      simp [r5, r4, r3, bindResults, loadRegisters, decoded, RegisterComparator.flags]
    have h6 : r5 6 = .pointer mp := by
      simp [r5, r4, r3, bindResults, loadRegisters, decoded, RegisterComparator.flags]
    have h11 : r5 11 = .flag (decide (edgePart k = e)) := by
      simp [r5, bindResults, RegisterComparator.flags, RegisterKeyTrace.compare_eq_decide]
    have hb : 36 * W + 180 * b + 250 + entryBudget W b c.length = entryBudget W b (c.length + 1) := by
      simp [entryBudget]; ring
    -- the tail after the comparison
    have tail : ∃ out q, Extends m1 out ∧ Valid out ∧ SignedAt out q (entryW one zero e (k :: c)) ∧
        Within code m1 r5
          (.branch (.register 11)
            (.load (.register 2) 12 13 15 { CompiledTrie.failCases with
              pair := .branch (.register 8)
                (.call ar.sadd [.flag false, .register 12, .flag false, .register 6] [14, 15]
                  (signedRet (.register 14) 15))
                (.call ar.sadd [.flag false, .register 12, .flag true, .register 6] [14, 15]
                  (signedRet (.register 14) 15)) })
            (.branch (.register 8) (signedRet (.flag false) 6) (signedRet (.flag true) 6)))
          [.pointer q] out (180 * b + 160) := by
      by_cases hke : edgePart k = e
      · have hres : entryW one zero e (k :: c) =
            (BinaryRational.signedAdd false (!vs) one vmag).1 := by
          simp [entryW, hke, hvc]
        obtain ⟨m2, rp, e2, v2, b2, w4⟩ := RegisterSignedAdd.compiled code ar.cmp ar.sub
          ar.complement ar.add hcmp hsub hcomp hadd v1 ho hmag false (!vs)
        let r6 := loadRegisters r5 12 13 15 (.pair op zp)
        have hrun : ∃ out q, Extends m1 out ∧ Valid out ∧
              SignedAt out q (BinaryRational.signedAdd false (!vs) one vmag).1 ∧
              Within code m1 r6
                (.call ar.sadd [.flag false, .register 12, .flag (!vs), .register 6] [14, 15]
                  (signedRet (.register 14) 15)) [.pointer q] out (180 * b + 140) := by
          obtain ⟨m3, q3, e3, v3, s3, w5⟩ := signedRet_within code v2
            (regs := bindResults r6 [14, 15]
              [.flag (BinaryRational.signedAdd false (!vs) one vmag).1.1, .pointer rp])
            (sign := .register 14) (mag := 15)
            (s := (BinaryRational.signedAdd false (!vs) one vmag).1.1)
            (by simp [Atom.eval, bindResults]) (by simp [bindResults]) b2
          refine ⟨m3, q3, e2.trans e3, v3, s3, ?_⟩
          refine (call_of (args := [.flag false, .pointer op, .flag (!vs), .pointer mp])
            (by simp [values, Atom.eval, r6, h6, loadRegisters, decoded]) (by
              rw [hsadd]; exact w4) w5).mono ?_
          simp
          omega
        obtain ⟨out, q, ex, vx, sx, wx⟩ := hrun
        refine ⟨out, q, ex, vx, by rw [hres]; exact sx, ?_⟩
        cases vs
        · refine (Within.branch (b := true) (by simp [Atom.eval, h11, hke])
            (Within.load (pointer := kp) (c := Cell.pair op zp)
              (by simp [Atom.eval, r5, r4, r3, r2, r1, regs, bindResults, loadRegisters, decoded,
                initialRegisters, RegisterComparator.flags]) hkp
              (Within.branch (b := false) (by simp [Atom.eval, r6, loadRegisters, decoded, h8])
                wx))).mono ?_
          omega
        · refine (Within.branch (b := true) (by simp [Atom.eval, h11, hke])
            (Within.load (pointer := kp) (c := Cell.pair op zp)
              (by simp [Atom.eval, r5, r4, r3, r2, r1, regs, bindResults, loadRegisters, decoded,
                initialRegisters, RegisterComparator.flags]) hkp
              (Within.branch (b := true) (by simp [Atom.eval, r6, loadRegisters, decoded, h8])
                wx))).mono ?_
          omega
      · have hres : entryW one zero e (k :: c) = (!vs, vmag) := by simp [entryW, hke, hvc]
        cases vs
        · obtain ⟨out, q, ex, vx, sx, wx⟩ := signedRet_within code v1 (regs := r5)
            (sign := .flag true) (mag := 6) (s := true) (by simp [Atom.eval]) h6 hmag
          refine ⟨out, q, ex, vx, by rw [hres]; exact sx, ?_⟩
          refine (Within.branch (b := false) (by simp [Atom.eval, h11, hke])
            (Within.branch (b := false) (by simp [Atom.eval, h8]) wx)).mono ?_
          omega
        · obtain ⟨out, q, ex, vx, sx, wx⟩ := signedRet_within code v1 (regs := r5)
            (sign := .flag false) (mag := 6) (s := false) (by simp [Atom.eval]) h6 hmag
          refine ⟨out, q, ex, vx, by rw [hres]; exact sx, ?_⟩
          refine (Within.branch (b := false) (by simp [Atom.eval, h11, hke])
            (Within.branch (b := true) (by simp [Atom.eval, h8]) wx)).mono ?_
          omega
    obtain ⟨out, q, ex, vx, sx, wx⟩ := tail
    refine ⟨out, q, e1.trans ex, vx, sx, ?_⟩
    rw [hself]
    refine (Within.load (pointer := cp) (c := Cell.cons xp rest)
      (by simp [Atom.eval, initialRegisters]) cell
      (call_of (by simp [values, Atom.eval, loadRegisters, decoded, initialRegisters]) w1
        (Within.load (pointer := vp) (c := Cell.bit vs mp)
          (by simp [Atom.eval, bindResults]) hvp
          (call_of (by simp [values, Atom.eval, r3, r2, r1, regs, bindResults, loadRegisters,
            decoded]) w2
            (call_of (by simp [values, Atom.eval, r3, r2, r1, regs, bindResults, loadRegisters,
              decoded, initialRegisters]) w3 wx))))).mono ?_
    simp only [List.length_cons, List.length_nil]
    rw [← hb]
    omega

/-! ## Rows -/

/-- Data of one row: `pair cycle constants`. -/
def RowDataAt {W b : ℕ} (one zero : Bits b) (h : Heap) (ptr : Ptr) (c : List (Bits (W + 2))) :
    Prop :=
  ∃ cp kp, h[ptr]? = some (.pair cp kp) ∧ WordsAt h cp c ∧ ConstsAt one zero h kp

theorem RowDataAt.mono {W b : ℕ} {one zero : Bits b} {h h' : Heap} (he : Extends h h') {ptr : Ptr}
    {c : List (Bits (W + 2))} (hd : RowDataAt one zero h ptr c) : RowDataAt one zero h' ptr c := by
  obtain ⟨cp, kp, hp, hc, hk⟩ := hd
  exact ⟨cp, kp, he.lookup hp, hc.mono he, hk.mono he⟩

/-- Arguments 0 = record, 1 = row data; the result is the entry of the record's edge. -/
def rowItemBody (entry : Fin p) : Command p :=
  .load (.register 0) 2 3 15 { CompiledTrie.failCases with
    pair := .load (.register 1) 4 5 15 { CompiledTrie.failCases with
      pair := .call entry [.register 4, .register 2, .register 5] [6] (.ret [.register 6]) } }

theorem rowItem_compiled (code : Code p) (self entry edge : Fin p) (ar : Arith p)
    (hself : code self = rowItemBody entry)
    (hentry : code entry = entryBody entry edge ar.cmp ar.sadd) (hedge : code edge = edgePartBody)
    (har : ar.Matches code) {W b : ℕ} (one zero : Bits b) {h : Heap} (hh : Valid h)
    {rp dp : Ptr} {r : EdgeRec W} {c : List (Bits (W + 2))}
    (hr : EdgeRecAt h rp r) (hd : RowDataAt one zero h dp c) :
    ∃ out q, Extends h out ∧ Valid out ∧ SignedAt out q (entryW one zero r.key c) ∧
      Within code h (initialRegisters [.pointer rp, .pointer dp]) (code self) [.pointer q] out
        (entryBudget W b c.length + 30) := by
  obtain ⟨kp, a, _, _, _, _, _, _, _, _, _, _, hp, hk, -⟩ := hr
  obtain ⟨cp, cnp, hdp, hc, hcn⟩ := hd
  obtain ⟨out, q, e1, v1, s1, w1⟩ := entry_compiled code entry edge ar hentry hedge har one zero
    r.key c hh hc hk hcn
  refine ⟨out, q, e1, v1, s1, ?_⟩
  rw [hself]
  refine (Within.load (pointer := rp) (c := Cell.pair kp a) (by simp [Atom.eval, initialRegisters])
    hp (Within.load (pointer := dp) (c := Cell.pair cp cnp)
      (by simp [Atom.eval, loadRegisters, decoded, initialRegisters]) hdp
      (call_of (by simp [values, Atom.eval, loadRegisters, decoded]) w1
        (ret_values (by simp [values, Atom.eval, bindResults]) le_rfl)))).mono ?_
  simp
  omega

def rowBudget (W b L m : ℕ) : ℕ := (entryBudget W b L + 65) * m + 13

theorem row_compiled (code : Code p) (self item entry edge : Fin p) (ar : Arith p)
    (hself : code self = RegisterListMap.body self item) (hitem : code item = rowItemBody entry)
    (hentry : code entry = entryBody entry edge ar.cmp ar.sadd) (hedge : code edge = edgePartBody)
    (har : ar.Matches code) {W b : ℕ} (one zero : Bits b) {h : Heap} (hh : Valid h)
    {tp dp : Ptr} {T : List (EdgeRec W)} {c : List (Bits (W + 2))}
    (hT : RecordsAt h tp T) (hd : RowDataAt one zero h dp c) :
    ∃ out q, Extends h out ∧ Valid out ∧ SignedWords.ListAt out q (rowW one zero T c) ∧
      Within code h (initialRegisters [.pointer tp, .pointer dp]) (code self) [.pointer q] out
        (rowBudget W b c.length T.length) := by
  obtain ⟨out, q, e, v, hq, w⟩ := RegisterListMap.compiled_const code self item hself
    EdgeRecAt (RowDataAt one zero) SignedAt (fun he _ _ hr => hr.mono he)
    (fun he _ _ hd => hd.mono he) (fun he _ _ hs => hs.mono he)
    (fun _ hs => hs.allocated) (fun c r => entryW one zero r.key c) (entryBudget W b c.length + 30)
    hh hT hd (fun {_} hv {_} {_} _ hr hd' => rowItem_compiled code item entry edge ar hitem hentry hedge har
      one zero hv hr hd')
  refine ⟨out, q, e, v, hq, w.mono ?_⟩
  simp [rowBudget]

end WeightedMIS.RegisterFaceRow
