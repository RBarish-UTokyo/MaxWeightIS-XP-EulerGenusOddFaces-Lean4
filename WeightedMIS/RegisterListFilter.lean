module

public import WeightedMIS.RegisterListCommon

/-!
# An order-preserving linked-list filter combinator

The command body traverses actual cons cells, first filtering the tail
recursively, then calling one fixed predicate procedure on the head with a
data pointer. A kept item costs one `cons` allocation that shares the item's
address; item values are never copied. The theorem refines `List.filter`.
-/

@[expose] public section

namespace WeightedMIS.RegisterListFilter

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.Pointer

variable {p : ℕ}

/-- Arguments 0=list, 1=data; the result is the list of kept items. -/
def body (self item : Fin p) : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    nil := .ret [.null]
    cons := .call self [.register 4, .register 1] [5]
      (.call item [.register 3, .register 1] [6]
        (.branch (.register 6)
          (.allocate 7 (.cons (.register 3) (.register 5)) (.ret [.register 7]))
          (.ret [.register 5]))) }

/-- Filter with an item-dependent predicate cost. -/
theorem compiled {α γ : Type*} (code : Code p) (self item : Fin p)
    (hself : code self = body self item)
    (InputAt : Heap → Ptr → α → Prop) (DataAt : Heap → Ptr → γ → Prop)
    (inputMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, InputAt h ptr x → InputAt h' ptr x)
    (dataMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, DataAt h ptr x → DataAt h' ptr x)
    (pred : γ → α → Bool) (itemBudget : α → ℕ)
    {h : Heap} (hh : Valid h) {list dataPtr : Ptr} {xs : List α} {data : γ}
    (hl : ListRep InputAt h list xs) (hd : DataAt h dataPtr data)
    (itemCompiled : ∀ {h : Heap}, Valid h → ∀ {xp : Ptr} {x : α}, x ∈ xs →
      InputAt h xp x → DataAt h dataPtr data →
      ∃ out, Extends h out ∧ Valid out ∧
        Within code h (initialRegisters [.pointer xp, .pointer dataPtr])
          (code item) [.flag (pred data x)] out (itemBudget x)) :
    ∃ out q, Extends h out ∧ Valid out ∧ ListRep InputAt out q (xs.filter (pred data)) ∧
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
    obtain ⟨out, heout, ho, hi⟩ := itemCompiled hm List.mem_cons_self
      (inputMono hem xp x hx) (dataMono hem dataPtr data hd)
    have hall := hem.trans heout
    have hmpo := ListRep.mono heout (inputMono heout) hmp
    let regs := initialRegisters [Value.pointer list, .pointer dataPtr]
    let rs := loadRegisters regs 3 4 15 (.cons xp rest)
    let rt := bindResults rs [5] [.pointer mp]
    let ru := bindResults rt [6] [.flag (pred data x)]
    have iargs : values rt [.register 3, .register 1] = [.pointer xp, .pointer dataPtr] := by
      simp [values, Atom.eval, rt, rs, regs, bindResults, loadRegisters, decoded, initialRegisters]
    have sargs : values rs [.register 4, .register 1] = [.pointer rest, .pointer dataPtr] := by
      simp [values, Atom.eval, rs, regs, loadRegisters, decoded, initialRegisters]
    have hlen : xp < out.length := lt_of_lt_of_le
      (RegisterListCommon.ListAt.head_allocated hh cell) hall.length_le
    -- The shared tail of both branches: load, recursive call, predicate call.
    have finish : ∀ {final : Heap} {res : Value} {rb : ℕ},
        Within code out ru (.branch (.register 6)
          (.allocate 7 (.cons (.register 3) (.register 5)) (.ret [.register 7]))
          (.ret [.register 5])) [res] final rb →
        rb ≤ 14 →
        Within code h regs (code self) [res] final
          (((x :: xs).map itemBudget).sum + 35 * (x :: xs).length + 13) := by
      intro final res rb hb hrb
      have icall := Within.call (procedure := item)
        (arguments := [.register 3, .register 1]) (results := [6]) (regs := rt)
        (by simpa only [iargs] using hi) hb
      have scall := Within.call (procedure := self)
        (arguments := [.register 4, .register 1]) (results := [5]) (regs := rs)
        (by simpa only [sargs] using hc) icall
      have loaded := Within.load (address := .register 0) (first := 3) (second := 4) (bit := 15)
        (branches := {CompiledTrie.failCases with
          nil := .ret [.null]
          cons := .call self [.register 4, .register 1] [5]
            (.call item [.register 3, .register 1] [6]
              (.branch (.register 6)
                (.allocate 7 (.cons (.register 3) (.register 5)) (.ret [.register 7]))
                (.ret [.register 5])))})
        (by simp [Atom.eval, regs, initialRegisters]) cell scall
      simpa only [hself, body] using
        loaded.mono (b := ((x :: xs).map itemBudget).sum + 35 * (x :: xs).length + 13)
          (by simp; omega)
    by_cases hp : pred data x = true
    · obtain ⟨hefin, hfin, hrep⟩ := RegisterListCommon.allocate_consRep inputMono ho
        (inputMono hall xp x hx) hlen hmpo
      refine ⟨out ++ [.cons xp mp], out.length, hall.trans hefin, hfin,
        by simpa [List.filter_cons, hp] using hrep, ?_⟩
      refine finish (rb := 3 + 11) ?_ (by omega)
      refine Within.branch (regs := ru) (test := .register 6) (b := true)
        (by simp [Atom.eval, ru, bindResults, hp]) ?_
      simpa using RegisterListCommon.within_consRet code out (regs := ru) (dst := 7)
        (head := 3) (tail := 5) (a := xp) (t := mp)
        (by simp [ru, rt, rs, bindResults, loadRegisters, decoded])
        (by simp [ru, rt, bindResults])
    · have hpf : pred data x = false := by simpa using hp
      refine ⟨out, mp, hall, ho, by simpa [List.filter_cons, hpf] using hmpo, ?_⟩
      refine finish (rb := 3 + 3) ?_ (by omega)
      refine Within.branch (regs := ru) (test := .register 6) (b := false)
        (by simp [Atom.eval, ru, bindResults, hpf]) ?_
      simpa [values, Atom.eval, ru, rt, bindResults] using
        Within.ret code out ru [.register 5]

/-- Filter with a uniform predicate cost. -/
theorem compiled_const {α γ : Type*} (code : Code p) (self item : Fin p)
    (hself : code self = body self item)
    (InputAt : Heap → Ptr → α → Prop) (DataAt : Heap → Ptr → γ → Prop)
    (inputMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, InputAt h ptr x → InputAt h' ptr x)
    (dataMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, DataAt h ptr x → DataAt h' ptr x)
    (pred : γ → α → Bool) (itemBudget : ℕ)
    {h : Heap} (hh : Valid h) {list dataPtr : Ptr} {xs : List α} {data : γ}
    (hl : ListRep InputAt h list xs) (hd : DataAt h dataPtr data)
    (itemCompiled : ∀ {h : Heap}, Valid h → ∀ {xp : Ptr} {x : α}, x ∈ xs →
      InputAt h xp x → DataAt h dataPtr data →
      ∃ out, Extends h out ∧ Valid out ∧
        Within code h (initialRegisters [.pointer xp, .pointer dataPtr])
          (code item) [.flag (pred data x)] out itemBudget) :
    ∃ out q, Extends h out ∧ Valid out ∧ ListRep InputAt out q (xs.filter (pred data)) ∧
      Within code h (initialRegisters [.pointer list, .pointer dataPtr])
        (code self) [.pointer q] out ((itemBudget + 35) * xs.length + 13) := by
  obtain ⟨out, q, he, ho, hq, hw⟩ := compiled code self item hself InputAt DataAt
    inputMono dataMono pred (fun _ => itemBudget) hh hl hd itemCompiled
  refine ⟨out, q, he, ho, hq, hw.mono ?_⟩
  rw [RegisterListCommon.sum_map_const]
  ring_nf
  omega

end WeightedMIS.RegisterListFilter
