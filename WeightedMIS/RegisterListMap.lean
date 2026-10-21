module

public import WeightedMIS.RegisterListCommon

/-!
# An order-preserving linked-list map combinator

The command body traverses actual cons cells, first mapping the tail
recursively, then calling one fixed item procedure on the head with a data
pointer, and finally allocating one `cons` cell for the returned address.
The theorem refines `List.map`.
-/

@[expose] public section

namespace WeightedMIS.RegisterListMap

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.Pointer

variable {p : ℕ}

/-- Arguments 0=list, 1=data; the result is the mapped list. -/
def body (self item : Fin p) : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    nil := .ret [.null]
    cons := .call self [.register 4, .register 1] [5]
      (.call item [.register 3, .register 1] [6]
        (.allocate 7 (.cons (.register 6) (.register 5)) (.ret [.register 7]))) }

/-- Map with an item-dependent cost. -/
theorem compiled {α β γ : Type*} (code : Code p) (self item : Fin p)
    (hself : code self = body self item)
    (InputAt : Heap → Ptr → α → Prop) (DataAt : Heap → Ptr → γ → Prop)
    (OutputAt : Heap → Ptr → β → Prop)
    (inputMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, InputAt h ptr x → InputAt h' ptr x)
    (dataMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, DataAt h ptr x → DataAt h' ptr x)
    (outputMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr y, OutputAt h ptr y → OutputAt h' ptr y)
    (outputAllocated : ∀ {h : Heap} {ptr : Ptr} {y : β}, Valid h → OutputAt h ptr y →
      ptr < h.length)
    (f : γ → α → β) (itemBudget : α → ℕ)
    {h : Heap} (hh : Valid h) {list dataPtr : Ptr} {xs : List α} {data : γ}
    (hl : ListRep InputAt h list xs) (hd : DataAt h dataPtr data)
    (itemCompiled : ∀ {h : Heap}, Valid h → ∀ {xp : Ptr} {x : α}, x ∈ xs →
      InputAt h xp x → DataAt h dataPtr data →
      ∃ out q, Extends h out ∧ Valid out ∧ OutputAt out q (f data x) ∧
        Within code h (initialRegisters [.pointer xp, .pointer dataPtr])
          (code item) [.pointer q] out (itemBudget x)) :
    ∃ out q, Extends h out ∧ Valid out ∧ ListRep OutputAt out q (xs.map (f data)) ∧
      Within code h (initialRegisters [.pointer list, .pointer dataPtr])
        (code self) [.pointer q] out ((xs.map itemBudget).sum + 35 * xs.length + 13) := by
  induction xs generalizing h list with
  | nil =>
    obtain ⟨pointers, hlist, hrel⟩ := hl
    cases hrel
    cases hlist with
    | nil cell =>
      refine ⟨h, 0, .refl h, hh, RegisterListCommon.listRep_null hh, ?_⟩
      rw [hself]
      unfold body
      apply Within.load (budget := 3) (pointer := list) (c := .nil)
      · simp [Atom.eval, initialRegisters]
      · exact cell
      · simpa [values, Atom.eval, Cases.select] using
          Within.ret code h
            (loadRegisters (initialRegisters [.pointer list, .pointer dataPtr]) 3 4 15 .nil)
            [.null]
  | cons x xs ih =>
    obtain ⟨pointers, hlist, hrel⟩ := hl
    cases hrel with
    | @cons xp _ ps _ hx hxs =>
    cases hlist with
    | @cons _ _ rest _ cell hrest =>
    obtain ⟨mid, mp, hem, hm, hmp, hc⟩ := ih hh ⟨ps, hrest, hxs⟩ hd
      (fun hv _ _ hmem hx' hd' => itemCompiled hv (List.mem_cons_of_mem x hmem) hx' hd')
    obtain ⟨out, q, heout, ho, hq, hi⟩ := itemCompiled hm List.mem_cons_self
      (inputMono hem xp x hx) (dataMono hem dataPtr data hd)
    obtain ⟨hefin, hfin, hrep⟩ := RegisterListCommon.allocate_consRep outputMono ho hq
      (outputAllocated ho hq) (ListRep.mono heout (outputMono heout) hmp)
    refine ⟨out ++ [.cons q mp], out.length, hem.trans (heout.trans hefin), hfin,
      by simpa using hrep, ?_⟩
    let regs := initialRegisters [Value.pointer list, .pointer dataPtr]
    let rs := loadRegisters regs 3 4 15 (.cons xp rest)
    let rt := bindResults rs [5] [.pointer mp]
    let ru := bindResults rt [6] [.pointer q]
    have fin := RegisterListCommon.within_consRet code out (regs := ru) (dst := 7)
      (head := 6) (tail := 5) (a := q) (t := mp)
      (by simp [ru, bindResults]) (by simp [ru, rt, bindResults])
    have iargs : values rt [.register 3, .register 1] = [.pointer xp, .pointer dataPtr] := by
      simp [values, Atom.eval, rt, rs, regs, bindResults, loadRegisters, decoded, initialRegisters]
    have icall := Within.call (procedure := item)
      (arguments := [.register 3, .register 1]) (results := [6]) (regs := rt)
      (by simpa only [iargs] using hi) fin
    have sargs : values rs [.register 4, .register 1] = [.pointer rest, .pointer dataPtr] := by
      simp [values, Atom.eval, rs, regs, loadRegisters, decoded, initialRegisters]
    have scall := Within.call (procedure := self)
      (arguments := [.register 4, .register 1]) (results := [5]) (regs := rs)
      (by simpa only [sargs] using hc) icall
    have loaded := Within.load (address := .register 0) (first := 3) (second := 4) (bit := 15)
      (branches := {CompiledTrie.failCases with
        nil := .ret [.null]
        cons := .call self [.register 4, .register 1] [5]
          (.call item [.register 3, .register 1] [6]
            (.allocate 7 (.cons (.register 6) (.register 5)) (.ret [.register 7])))})
      (by simp [Atom.eval, regs, initialRegisters]) cell scall
    simpa only [hself, body] using
      loaded.mono (b := ((x :: xs).map itemBudget).sum + 35 * (x :: xs).length + 13)
        (by simp; omega)

/-- Map with a uniform item cost. -/
theorem compiled_const {α β γ : Type*} (code : Code p) (self item : Fin p)
    (hself : code self = body self item)
    (InputAt : Heap → Ptr → α → Prop) (DataAt : Heap → Ptr → γ → Prop)
    (OutputAt : Heap → Ptr → β → Prop)
    (inputMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, InputAt h ptr x → InputAt h' ptr x)
    (dataMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, DataAt h ptr x → DataAt h' ptr x)
    (outputMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr y, OutputAt h ptr y → OutputAt h' ptr y)
    (outputAllocated : ∀ {h : Heap} {ptr : Ptr} {y : β}, Valid h → OutputAt h ptr y →
      ptr < h.length)
    (f : γ → α → β) (itemBudget : ℕ)
    {h : Heap} (hh : Valid h) {list dataPtr : Ptr} {xs : List α} {data : γ}
    (hl : ListRep InputAt h list xs) (hd : DataAt h dataPtr data)
    (itemCompiled : ∀ {h : Heap}, Valid h → ∀ {xp : Ptr} {x : α}, x ∈ xs →
      InputAt h xp x → DataAt h dataPtr data →
      ∃ out q, Extends h out ∧ Valid out ∧ OutputAt out q (f data x) ∧
        Within code h (initialRegisters [.pointer xp, .pointer dataPtr])
          (code item) [.pointer q] out itemBudget) :
    ∃ out q, Extends h out ∧ Valid out ∧ ListRep OutputAt out q (xs.map (f data)) ∧
      Within code h (initialRegisters [.pointer list, .pointer dataPtr])
        (code self) [.pointer q] out ((itemBudget + 35) * xs.length + 13) := by
  obtain ⟨out, q, he, ho, hq, hw⟩ := compiled code self item hself InputAt DataAt OutputAt
    inputMono dataMono outputMono outputAllocated f (fun _ => itemBudget) hh hl hd itemCompiled
  refine ⟨out, q, he, ho, hq, hw.mono ?_⟩
  rw [RegisterListCommon.sum_map_const]
  ring_nf
  omega

end WeightedMIS.RegisterListMap
