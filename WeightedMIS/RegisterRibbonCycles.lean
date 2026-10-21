module

public import WeightedMIS.RegisterKeyFaceEnumeration
public import WeightedMIS.RegisterRecordLookup

/-!
# Even facial cycles of a stored ribbon table

The rotation step turns a flag key along its edge and looks up the stored
corner key. The canonical key list is produced by four flat-map passes over
the records, one for each pair of flag bits. The first-unseen scan of the
canonical keys with first-return cycles of fuel `4 m` then returns exactly the
key images of the even facial cycles of the canonical enumeration.
-/

@[expose] public section

namespace WeightedMIS.RegisterRibbonCycles

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords WeightedMIS.FlagKeyFaces
open WeightedMIS.RegisterFlagKeys WeightedMIS.RegisterKeyTrace WeightedMIS.RibbonTable
open WeightedMIS.RegisterKeyFaceEnumeration WeightedMIS.EmbeddingFaces WeightedMIS.FiniteCycleEnumeration

variable {p : ℕ}

/-! ## Rotation step -/

/-- Arguments 0 = key, 1 = table; the result is the rotation key. -/
def rotBody (along corner : Fin p) : Command p :=
  .call along [.register 0] [2] (.call corner [.register 1, .register 2] [3] (.ret [.register 3]))

def rotBudget (W m : ℕ) : ℕ := RegisterRecordLookup.cornerBudget W m + 53

theorem rot_step (code : Code p) (rot along : Fin p) (lookup : RegisterRecordLookup.Procedures p)
    (hrot : code rot = rotBody along lookup.corner) (halong : code along = alongBody)
    (hl : lookup.Matches code) {W : ℕ} (T : List (EdgeRec W)) :
    StepSpec code rot (rotK T) (fun _ => True) (fun h p (T : List (EdgeRec W)) => RecordsAt h p T)
      T (rotBudget W T.length) := by
  intro h hh xp dp x _ hx hT
  obtain ⟨m1, a, e1, v1, b1, w1⟩ := along_compiled code along halong hh hx
  obtain ⟨m2, q, e2, v2, b2, w2⟩ :=
    RegisterRecordLookup.corner_compiled lookup code hl v1 (hT.mono e1) b1
  refine ⟨m2, q, e1.trans e2, v2, b2, ?_⟩
  rw [hrot]
  refine (call_of (by simp [values, Atom.eval, initialRegisters]) w1
    (call_of (by simp [values, Atom.eval, bindResults, initialRegisters]) w2
      (ret_values (by simp [values, Atom.eval, bindResults]) le_rfl))).mono ?_
  simp [rotBudget]
  omega

/-! ## Canonical keys -/

/-- Two flag bits stored as a two-bit word. -/
def BitPairAt (h : Heap) (dp : Ptr) (st : Bool × Bool) : Prop :=
  BitsAt h dp (.cons st.1 (.cons st.2 .nil) : Bits 2)

/-- Arguments 0 = record, 1 = flag bits, 2 = tail; prepends the flag key. -/
def keyItemBody : Command p :=
  .load (.register 1) 3 4 5 { CompiledTrie.failCases with
    bit := .load (.register 3) 6 7 8 { CompiledTrie.failCases with
      bit := .load (.register 0) 9 10 15 { CompiledTrie.failCases with
        pair := .allocate 11 (.bit (.register 8) (.register 9))
          (.allocate 12 (.bit (.register 5) (.register 11))
            (.allocate 13 (.cons (.register 12) (.register 2)) (.ret [.register 13]))) } } }

/-- Argument 0 = table; the result is `canonicalKeys`. -/
def keysBody (flat : Fin p) : Command p :=
  .allocate 1 (.bit (.flag true) .null)
    (.allocate 2 (.bit (.flag false) .null)
      (.allocate 3 (.bit (.flag true) (.register 1))
        (.allocate 4 (.bit (.flag true) (.register 2))
          (.allocate 5 (.bit (.flag false) (.register 1))
            (.allocate 6 (.bit (.flag false) (.register 2))
              (.call flat [.register 0, .register 3, .null] [7]
                (.call flat [.register 0, .register 4, .register 7] [7]
                  (.call flat [.register 0, .register 5, .register 7] [7]
                    (.call flat [.register 0, .register 6, .register 7] [7]
                      (.ret [.register 7]))))))))))

theorem keyItem_compiled (code : Code p) (self : Fin p) (hself : code self = keyItemBody)
    {W : ℕ} {h : Heap} (hh : Valid h) {rp dp acc : Ptr} {r : EdgeRec W} {st : Bool × Bool}
    {tail : List (Bits (W + 2))} (hr : EdgeRecAt h rp r) (hd : BitPairAt h dp st)
    (ht : WordsAt h acc tail) :
    ∃ out q, Extends h out ∧ Valid out ∧ WordsAt out q ([mkKey st.1 st.2 r.key] ++ tail) ∧
      Within code h (initialRegisters [.pointer rp, .pointer dp, .pointer acc]) (code self)
        [.pointer q] out 57 := by
  rcases st with ⟨s, t⟩
  unfold BitPairAt at hd
  cases hd with
  | @cons _ q1 _ _ _ c1 h1 =>
  cases h1 with
  | @cons _ z _ _ _ c2 _ =>
  obtain ⟨kp, a, _, _, _, _, _, _, _, _, _, _, hp, hk, -⟩ := hr
  obtain ⟨e1, v1, b1⟩ := alloc_bit hh t hk
  obtain ⟨e2, v2, b2⟩ := alloc_bit v1 s b1
  obtain ⟨e3, v3, b3⟩ := alloc_wordCons v2 b2 ((ht.mono e1).mono e2)
  refine ⟨_, _, e1.trans (e2.trans e3), v3, b3, ?_⟩
  rw [hself]
  apply Within.load (budget := 47) (pointer := dp) (c := Cell.bit s q1)
  · simp [Atom.eval, initialRegisters]
  · exact c1
  apply Within.load (budget := 37) (pointer := q1) (c := Cell.bit t z)
  · simp [Atom.eval, loadRegisters, decoded]
  · exact c2
  apply Within.load (budget := 27) (pointer := rp) (c := Cell.pair kp a)
  · simp [Atom.eval, loadRegisters, decoded, initialRegisters]
  · exact hp
  apply Within.allocate (budget := 19) (c := Cell.bit t kp)
  · simp [CellExpr.eval, Atom.eval, loadRegisters, decoded, Value.asFlag, Value.asPointer]
  apply Within.allocate (budget := 11) (c := Cell.bit s h.length)
  · simp [CellExpr.eval, Atom.eval, loadRegisters, decoded, Value.asFlag, Value.asPointer]
  apply Within.allocate (budget := 3) (c := Cell.cons (h ++ [Cell.bit t kp]).length acc)
  · simp [CellExpr.eval, Atom.eval, loadRegisters, decoded, Value.asPointer, initialRegisters]
  exact ret_values (by simp [values, Atom.eval]) le_rfl

theorem keyFlat_compiled (code : Code p) (self item : Fin p)
    (hself : code self = RegisterListFlatMap.body self item) (hitem : code item = keyItemBody)
    {W : ℕ} {h : Heap} (hh : Valid h) {tp dp acc : Ptr} {T : List (EdgeRec W)} {st : Bool × Bool}
    {tail : List (Bits (W + 2))} (hT : RecordsAt h tp T) (hd : BitPairAt h dp st)
    (ht : WordsAt h acc tail) :
    ∃ out q, Extends h out ∧ Valid out ∧
      WordsAt out q (T.map (fun r => mkKey st.1 st.2 r.key) ++ tail) ∧
      Within code h (initialRegisters [.pointer tp, .pointer dp, .pointer acc]) (code self)
        [.pointer q] out (84 * T.length + 13) := by
  obtain ⟨out, q, he, ho, hq, hw⟩ := RegisterListFlatMap.compiled code self item hself
    EdgeRecAt BitPairAt (fun h p l => WordsAt h p l) (fun he _ _ hr => hr.mono he)
    (fun he _ _ hb => BitsAt.mono he hb)
    (fun st r => [mkKey st.1 st.2 r.key]) 57
    (fun {_} hv {_ _ _} {_ _ _} hr hd ht => keyItem_compiled code item hitem hv hr hd ht)
    hh hT hd ht
  have hfm : ∀ l : List (EdgeRec W), l.flatMap (fun r => [mkKey st.1 st.2 r.key]) =
      l.map (fun r => mkKey st.1 st.2 r.key) := by
    intro l; induction l <;> simp [*]
  refine ⟨out, q, he, ho, ?_, hw.mono (by ring_nf; omega)⟩
  simpa [hfm] using hq

def keysBudget (m : ℕ) : ℕ := 4 * (84 * m + 13) + 90

theorem keys_compiled (code : Code p) (self flat item : Fin p)
    (hself : code self = keysBody flat) (hflat : code flat = RegisterListFlatMap.body flat item)
    (hitem : code item = keyItemBody)
    {W : ℕ} {h : Heap} (hh : Valid h) {tp : Ptr} {T : List (EdgeRec W)} (hT : RecordsAt h tp T) :
    ∃ out q, Extends h out ∧ Valid out ∧ WordsAt out q (canonicalKeys T) ∧
      Within code h (initialRegisters [.pointer tp]) (code self) [.pointer q] out
        (keysBudget T.length) := by
  have hz : BitsAt h 0 (.nil : Bits 0) := .nil hh.1
  obtain ⟨e1, v1, b1⟩ := alloc_bit hh true hz
  obtain ⟨e2, v2, b2⟩ := alloc_bit v1 false (hz.mono e1)
  obtain ⟨e3, v3, b3⟩ := alloc_bit v2 true (b1.mono e2)
  obtain ⟨e4, v4, b4⟩ := alloc_bit v3 true ((b2.mono e3))
  obtain ⟨e5, v5, b5⟩ := alloc_bit v4 false ((b1.mono e2).mono e3 |>.mono e4)
  obtain ⟨e6, v6, b6⟩ := alloc_bit v5 false ((b2.mono e3).mono e4 |>.mono e5)
  have d11 : BitPairAt _ _ (true, true) := ((b3.mono e4).mono e5).mono e6
  have d10 : BitPairAt _ _ (true, false) := (b4.mono e5).mono e6
  have d01 : BitPairAt _ _ (false, true) := b5.mono e6
  have d00 : BitPairAt _ _ (false, false) := b6
  have e06 := e1.trans (e2.trans (e3.trans (e4.trans (e5.trans e6))))
  obtain ⟨m1, q1, f1, u1, k1, w1⟩ := keyFlat_compiled code flat item hflat hitem v6 (hT.mono e06)
    d11 (RegisterListCommon.listRep_null v6 : WordsAt _ 0 ([] : List (Bits (W + 2))))
  obtain ⟨m2, q2, f2, u2, k2, w2⟩ := keyFlat_compiled code flat item hflat hitem u1
    ((hT.mono e06).mono f1) (d10.mono f1) k1
  obtain ⟨m3, q3, f3, u3, k3, w3⟩ := keyFlat_compiled code flat item hflat hitem u2
    (((hT.mono e06).mono f1).mono f2) ((d01.mono f1).mono f2) k2
  obtain ⟨m4, q4, f4, u4, k4, w4⟩ := keyFlat_compiled code flat item hflat hitem u3
    ((((hT.mono e06).mono f1).mono f2).mono f3) (((d00.mono f1).mono f2).mono f3) k3
  refine ⟨m4, q4, e06.trans (f1.trans (f2.trans (f3.trans f4))), u4, ?_, ?_⟩
  · simpa [canonicalKeys, List.append_assoc] using k4
  rw [hself]
  refine (Within.allocate (c := Cell.bit true 0)
    (by simp [CellExpr.eval, Atom.eval, Value.asFlag, Value.asPointer])
    (Within.allocate (c := Cell.bit false 0)
      (by simp [CellExpr.eval, Atom.eval, Value.asFlag, Value.asPointer])
      (Within.allocate (c := Cell.bit true h.length)
        (by simp [CellExpr.eval, Atom.eval, Value.asFlag, Value.asPointer])
        (Within.allocate (c := Cell.bit true (h ++ [Cell.bit true 0]).length)
          (by simp [CellExpr.eval, Atom.eval, Value.asFlag, Value.asPointer])
          (Within.allocate (c := Cell.bit false h.length)
            (by simp [CellExpr.eval, Atom.eval, Value.asFlag, Value.asPointer])
            (Within.allocate (c := Cell.bit false (h ++ [Cell.bit true 0]).length)
              (by simp [CellExpr.eval, Atom.eval, Value.asFlag, Value.asPointer])
              (call_of (by simp [values, Atom.eval, initialRegisters]) w1
                (call_of (by simp [values, Atom.eval, bindResults, initialRegisters]) w2
                  (call_of (by simp [values, Atom.eval, bindResults, initialRegisters]) w3
                    (call_of (by simp [values, Atom.eval, bindResults, initialRegisters]) w4
                      (ret_values (by simp [values, Atom.eval, bindResults]) le_rfl))))))))))).mono ?_
  simp [keysBudget, CellExpr.args]
  omega

/-! ## Even facial cycles -/

/-- Argument 0 = table; the result lists the even facial key cycles. -/
def cyclesBody (keys scan : Fin p) : Command p :=
  .call keys [.register 0] [1] (.call scan [.register 1, .null, .register 0] [2] (.ret [.register 2]))

structure Procedures (p : ℕ) where
  top : Fin p
  keys : Fin p
  keyFlat : Fin p
  keyItem : Fin p
  rot : Fin p
  enum : RegisterKeyFaceEnumeration.Procedures p
  lookup : RegisterRecordLookup.Procedures p

def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  code ids.top = cyclesBody ids.keys ids.enum.scan ∧
  code ids.keys = keysBody ids.keyFlat ∧
  code ids.keyFlat = RegisterListFlatMap.body ids.keyFlat ids.keyItem ∧
  code ids.keyItem = keyItemBody ∧
  code ids.rot = rotBody ids.enum.along ids.lookup.corner ∧
  ids.enum.next = ids.rot ∧
  ids.enum.Matches code ∧
  ids.lookup.Matches code

def cyclesBudget (W m : ℕ) : ℕ :=
  keysBudget m + scanBudget (W + 2) (rotBudget W m) (4 * m) (2 * (4 * m + 1) * (4 * m)) (4 * m) + 13

/-- The fixed procedures return the key images of the even facial cycles of
the canonical enumeration of a stored ribbon. -/
theorem cycles_compiled (ids : Procedures p) (code : Code p) (hm : ids.Matches code)
    {W n m : ℕ} {left right : Fin m → Fin n} (R : Ribbon left right) (hW : m < 2 ^ W)
    {h : Heap} (hh : Valid h) {tp : Ptr} (hT : RecordsAt h tp (encodeRibbon W R)) :
    ∃ out q, Extends h out ∧ Valid out ∧
      CyclesAt out q ((evenRoots R (Flag.canonicalOrder m)).map
        (fun x => (cycleList R.rotation x).map (flagKey W))) ∧
      Within code h (initialRegisters [.pointer tp]) (code ids.top) [.pointer q] out
        (cyclesBudget W m) := by
  obtain ⟨htop, hkeys, hflat, hitem, hrot, hnext, henum, hlookup⟩ := hm
  obtain ⟨m1, q1, e1, v1, k1, w1⟩ := keys_compiled code ids.keys ids.keyFlat ids.keyItem
    hkeys hflat hitem hh hT
  have step : StepSpec code ids.enum.next (rotK (encodeRibbon W R)) (fun _ => True)
      (fun h p (T : List (EdgeRec W)) => RecordsAt h p T) (encodeRibbon W R) (rotBudget W m) := by
    have hs : StepSpec code ids.rot (rotK (encodeRibbon W R)) (fun _ => True)
        (fun h p (T : List (EdgeRec W)) => RecordsAt h p T) (encodeRibbon W R)
        (rotBudget W (encodeRibbon W R).length) :=
      rot_step code ids.rot ids.enum.along ids.lookup hrot henum.2.2.2.2.2.2.2 hlookup
        (encodeRibbon W R)
    rw [encodeRibbon_length, ← hnext] at hs
    exact @hs
  rw [canonicalKeys_encode] at k1
  have hret : ∀ x ∈ (Flag.canonicalOrder m).map (flagKey W),
      True ∧ Returns (rotK (encodeRibbon W R)) x (4 * m) (rotK (encodeRibbon W R) x) := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
    exact ⟨trivial, returns_encode hW R (4 * m) le_rfl y⟩
  obtain ⟨m2, q2, e2, v2, c2, w2⟩ := scan_compiled ids.enum code henum (rotK (encodeRibbon W R))
    (fun _ => True) (fun _ _ => trivial) (fun h p (T : List (EdgeRec W)) => RecordsAt h p T)
    (fun he _ _ hr => hr.mono he) (encodeRibbon W R) _ step (4 * m) (2 * (4 * m + 1) * (4 * m))
    ((Flag.canonicalOrder m).map (flagKey W)) v1 k1
    (RegisterListCommon.listRep_null v1 : WordsAt m1 0 ([] : List (Bits (W + 2))))
    (hT.mono e1) hret (by simp)
  refine ⟨m2, q2, e1.trans e2, v2, ?_, ?_⟩
  · have hk := keyEvenCycles_encode hW R (4 * m) le_rfl
    rw [keyEvenCycles, canonicalKeys_encode] at hk
    rw [← hk]
    exact c2
  rw [htop]
  refine (call_of (by simp [values, Atom.eval, initialRegisters]) w1
    (call_of (by simp [values, Atom.eval, bindResults, initialRegisters]) w2
      (ret_values (by simp [values, Atom.eval, bindResults]) le_rfl))).mono ?_
  simp [cyclesBudget]
  omega

end WeightedMIS.RegisterRibbonCycles
