module

public import WeightedMIS.RegisterListCommon

/-!
# An order-preserving linked-list zip combinator

The command body traverses two lists of actual cons cells in lockstep. For
a pair of heads it first zips the tails recursively, then calls one fixed
item procedure on both heads and a data pointer, and finally allocates one
`cons` cell for the returned address. The traversal stops at the end of the
shorter list. The theorem refines `List.zipWith`.
-/

@[expose] public section

namespace WeightedMIS.RegisterListZip

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.Pointer

variable {p : ℕ}

/-- Arguments 0=first list, 1=second list, 2=data; the result is the zipped list. -/
def body (self item : Fin p) : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    nil := .ret [.null]
    cons := .load (.register 1) 5 6 15 { CompiledTrie.failCases with
      nil := .ret [.null]
      cons := .call self [.register 4, .register 6, .register 2] [7]
        (.call item [.register 3, .register 5, .register 2] [8]
          (.allocate 9 (.cons (.register 8) (.register 7)) (.ret [.register 9]))) } }

/-- Zip with a pair-dependent item cost. -/
theorem compiled {α β γ δ : Type*} (code : Code p) (self item : Fin p)
    (hself : code self = body self item)
    (LeftAt : Heap → Ptr → α → Prop) (RightAt : Heap → Ptr → β → Prop)
    (DataAt : Heap → Ptr → γ → Prop) (OutputAt : Heap → Ptr → δ → Prop)
    (leftMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, LeftAt h ptr x → LeftAt h' ptr x)
    (rightMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr y, RightAt h ptr y → RightAt h' ptr y)
    (dataMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr d, DataAt h ptr d → DataAt h' ptr d)
    (outputMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr z, OutputAt h ptr z → OutputAt h' ptr z)
    (outputAllocated : ∀ {h : Heap} {ptr : Ptr} {z : δ}, Valid h → OutputAt h ptr z →
      ptr < h.length)
    (f : γ → α → β → δ) (itemBudget : α → β → ℕ)
    {h : Heap} (hh : Valid h) {listA listB dataPtr : Ptr} {as : List α} {bs : List β} {data : γ}
    (ha : ListRep LeftAt h listA as) (hb : ListRep RightAt h listB bs)
    (hd : DataAt h dataPtr data)
    (itemCompiled : ∀ {h : Heap}, Valid h → ∀ {ap bp : Ptr} {a : α} {b : β},
      (a, b) ∈ as.zip bs → LeftAt h ap a → RightAt h bp b → DataAt h dataPtr data →
      ∃ out q, Extends h out ∧ Valid out ∧ OutputAt out q (f data a b) ∧
        Within code h (initialRegisters [.pointer ap, .pointer bp, .pointer dataPtr])
          (code item) [.pointer q] out (itemBudget a b)) :
    ∃ out q, Extends h out ∧ Valid out ∧
      ListRep OutputAt out q (List.zipWith (f data) as bs) ∧
      Within code h (initialRegisters [.pointer listA, .pointer listB, .pointer dataPtr])
        (code self) [.pointer q] out
        ((List.zipWith itemBudget as bs).sum + 45 * min as.length bs.length + 23) := by
  induction as generalizing h listA bs listB with
  | nil =>
    obtain ⟨pointers, hlist, hrel⟩ := ha
    cases hrel
    cases hlist with
    | nil cell =>
      refine ⟨h, 0, .refl h, hh, by simpa using RegisterListCommon.listRep_null hh, ?_⟩
      rw [hself]
      unfold body
      refine Within.mono (a := 13) ?_ (by simp)
      apply Within.load (budget := 3) (pointer := listA) (c := .nil)
      · simp [Atom.eval, initialRegisters]
      · exact cell
      · simpa [values, Atom.eval, Cases.select] using
          Within.ret code h (loadRegisters (initialRegisters
            [.pointer listA, .pointer listB, .pointer dataPtr]) 3 4 15 .nil) [.null]
  | cons x as ih =>
    obtain ⟨pointers, hlist, hrel⟩ := ha
    cases hrel with
    | @cons ap _ ps _ hx hxs =>
    cases hlist with
    | @cons _ _ restA _ cellA hrestA =>
    let regs := initialRegisters [Value.pointer listA, .pointer listB, .pointer dataPtr]
    let rs := loadRegisters regs 3 4 15 (.cons ap restA)
    obtain ⟨qointers, hlistB, hrelB⟩ := hb
    cases hrelB with
    | nil =>
      cases hlistB with
      | nil cellB =>
        refine ⟨h, 0, .refl h, hh, by simpa using RegisterListCommon.listRep_null hh, ?_⟩
        have inner := Within.load (address := .register 1) (first := 5) (second := 6) (bit := 15)
          (regs := rs) (c := .nil)
          (branches := {CompiledTrie.failCases with
            nil := .ret [.null]
            cons := .call self [.register 4, .register 6, .register 2] [7]
              (.call item [.register 3, .register 5, .register 2] [8]
                (.allocate 9 (.cons (.register 8) (.register 7)) (.ret [.register 9])))})
          (by simp [Atom.eval, rs, regs, loadRegisters, initialRegisters]) cellB
          (by simpa [values, Atom.eval, Cases.select] using
            Within.ret code h (loadRegisters rs 5 6 15 .nil) [.null])
        have loaded := Within.load (address := .register 0) (first := 3) (second := 4) (bit := 15)
          (branches := {CompiledTrie.failCases with
            nil := .ret [.null]
            cons := .load (.register 1) 5 6 15 { CompiledTrie.failCases with
              nil := .ret [.null]
              cons := .call self [.register 4, .register 6, .register 2] [7]
                (.call item [.register 3, .register 5, .register 2] [8]
                  (.allocate 9 (.cons (.register 8) (.register 7)) (.ret [.register 9]))) }})
          (by simp [Atom.eval, regs, initialRegisters]) cellA inner
        simpa only [hself, body] using loaded.mono (by simp)
    | @cons bp y qs bs hy hys =>
      cases hlistB with
      | @cons _ _ restB _ cellB hrestB =>
      obtain ⟨mid, mp, hem, hm, hmp, hc⟩ := ih hh ⟨ps, hrestA, hxs⟩ ⟨qs, hrestB, hys⟩ hd
        (fun hv _ _ _ _ hmem ha' hb' hd' =>
          itemCompiled hv (List.mem_cons_of_mem _ hmem) ha' hb' hd')
      obtain ⟨out, q, heout, ho, hq, hi⟩ := itemCompiled hm (by simp)
        (leftMono hem ap x hx) (rightMono hem bp y hy) (dataMono hem dataPtr data hd)
      obtain ⟨hefin, hfin, hrep⟩ := RegisterListCommon.allocate_consRep outputMono ho hq
        (outputAllocated ho hq) (ListRep.mono heout (outputMono heout) hmp)
      refine ⟨out ++ [.cons q mp], out.length, hem.trans (heout.trans hefin), hfin,
        by simpa using hrep, ?_⟩
      let rs2 := loadRegisters rs 5 6 15 (.cons bp restB)
      let rt := bindResults rs2 [7] [.pointer mp]
      let ru := bindResults rt [8] [.pointer q]
      have fin := RegisterListCommon.within_consRet code out (regs := ru) (dst := 9)
        (head := 8) (tail := 7) (a := q) (t := mp)
        (by simp [ru, bindResults]) (by simp [ru, rt, bindResults])
      have iargs : values rt [.register 3, .register 5, .register 2] =
          [.pointer ap, .pointer bp, .pointer dataPtr] := by
        simp [values, Atom.eval, rt, rs2, rs, regs, bindResults, loadRegisters, decoded,
          initialRegisters]
      have icall := Within.call (procedure := item)
        (arguments := [.register 3, .register 5, .register 2]) (results := [8]) (regs := rt)
        (by simpa only [iargs] using hi) fin
      have sargs : values rs2 [.register 4, .register 6, .register 2] =
          [.pointer restA, .pointer restB, .pointer dataPtr] := by
        simp [values, Atom.eval, rs2, rs, regs, loadRegisters, decoded, initialRegisters]
      have scall := Within.call (procedure := self)
        (arguments := [.register 4, .register 6, .register 2]) (results := [7]) (regs := rs2)
        (by simpa only [sargs] using hc) icall
      have inner := Within.load (address := .register 1) (first := 5) (second := 6) (bit := 15)
        (regs := rs)
        (branches := {CompiledTrie.failCases with
          nil := .ret [.null]
          cons := .call self [.register 4, .register 6, .register 2] [7]
            (.call item [.register 3, .register 5, .register 2] [8]
              (.allocate 9 (.cons (.register 8) (.register 7)) (.ret [.register 9])))})
        (by simp [Atom.eval, rs, regs, loadRegisters, initialRegisters]) cellB scall
      have loaded := Within.load (address := .register 0) (first := 3) (second := 4) (bit := 15)
        (branches := {CompiledTrie.failCases with
          nil := .ret [.null]
          cons := .load (.register 1) 5 6 15 { CompiledTrie.failCases with
            nil := .ret [.null]
            cons := .call self [.register 4, .register 6, .register 2] [7]
              (.call item [.register 3, .register 5, .register 2] [8]
                (.allocate 9 (.cons (.register 8) (.register 7)) (.ret [.register 9]))) }})
        (by simp [Atom.eval, regs, initialRegisters]) cellA inner
      simpa only [hself, body] using
        loaded.mono (b := (List.zipWith itemBudget (x :: as) (y :: bs)).sum +
          45 * min (x :: as).length (y :: bs).length + 23)
          (by simp [Nat.succ_min_succ]; omega)

/-- Zip with a uniform item cost. -/
theorem compiled_const {α β γ δ : Type*} (code : Code p) (self item : Fin p)
    (hself : code self = body self item)
    (LeftAt : Heap → Ptr → α → Prop) (RightAt : Heap → Ptr → β → Prop)
    (DataAt : Heap → Ptr → γ → Prop) (OutputAt : Heap → Ptr → δ → Prop)
    (leftMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, LeftAt h ptr x → LeftAt h' ptr x)
    (rightMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr y, RightAt h ptr y → RightAt h' ptr y)
    (dataMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr d, DataAt h ptr d → DataAt h' ptr d)
    (outputMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr z, OutputAt h ptr z → OutputAt h' ptr z)
    (outputAllocated : ∀ {h : Heap} {ptr : Ptr} {z : δ}, Valid h → OutputAt h ptr z →
      ptr < h.length)
    (f : γ → α → β → δ) (itemBudget : ℕ)
    {h : Heap} (hh : Valid h) {listA listB dataPtr : Ptr} {as : List α} {bs : List β} {data : γ}
    (ha : ListRep LeftAt h listA as) (hb : ListRep RightAt h listB bs)
    (hd : DataAt h dataPtr data)
    (itemCompiled : ∀ {h : Heap}, Valid h → ∀ {ap bp : Ptr} {a : α} {b : β},
      (a, b) ∈ as.zip bs → LeftAt h ap a → RightAt h bp b → DataAt h dataPtr data →
      ∃ out q, Extends h out ∧ Valid out ∧ OutputAt out q (f data a b) ∧
        Within code h (initialRegisters [.pointer ap, .pointer bp, .pointer dataPtr])
          (code item) [.pointer q] out itemBudget) :
    ∃ out q, Extends h out ∧ Valid out ∧
      ListRep OutputAt out q (List.zipWith (f data) as bs) ∧
      Within code h (initialRegisters [.pointer listA, .pointer listB, .pointer dataPtr])
        (code self) [.pointer q] out ((itemBudget + 45) * min as.length bs.length + 23) := by
  obtain ⟨out, q, he, ho, hq, hw⟩ := compiled code self item hself LeftAt RightAt DataAt
    OutputAt leftMono rightMono dataMono outputMono outputAllocated f (fun _ _ => itemBudget)
    hh ha hb hd itemCompiled
  refine ⟨out, q, he, ho, hq, hw.mono ?_⟩
  have hsum : ∀ (as : List α) (bs : List β),
      (List.zipWith (fun _ _ => itemBudget) as bs).sum = itemBudget * min as.length bs.length := by
    intro as bs
    induction as generalizing bs with
    | nil => simp
    | cons a as ih =>
      cases bs with
      | nil => simp
      | cons b bs => simp [ih, Nat.succ_min_succ]; ring
  rw [hsum]
  ring_nf
  omega

end WeightedMIS.RegisterListZip
