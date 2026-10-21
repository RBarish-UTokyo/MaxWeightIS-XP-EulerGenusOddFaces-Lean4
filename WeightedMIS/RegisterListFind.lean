module

public import WeightedMIS.RegisterListCommon

/-!
# A linked-list search combinator

The command body traverses actual cons cells and calls one fixed predicate
procedure per item, with the item and a data pointer as arguments. The
traversal stops at the first item whose predicate procedure returns `true`
and returns that item's shared address; it returns `false` and the null
address when no item qualifies. The theorem refines `List.find?`.
-/

@[expose] public section

namespace WeightedMIS.RegisterListFind

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.Pointer

variable {p : ℕ}

/-- Arguments 0=list, 1=data; results are the found flag and the item address. -/
def body (self item : Fin p) : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    nil := .ret [.flag false, .null]
    cons := .call item [.register 3, .register 1] [5]
      (.branch (.register 5)
        (.ret [.flag true, .register 3])
        (.call self [.register 4, .register 1] [6, 7] (.ret [.register 6, .register 7]))) }

/-- Search with an item-dependent predicate cost. The predicate procedure may
extend the heap and may use that the inspected item belongs to the list. -/
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
    ∃ out q, Extends h out ∧ Valid out ∧
      (∀ x, xs.find? (pred data) = some x → InputAt out q x) ∧
      (xs.find? (pred data) = none → q = 0) ∧
      Within code h (initialRegisters [.pointer list, .pointer dataPtr])
        (code self) [.flag (xs.find? (pred data)).isSome, .pointer q] out
        ((xs.map itemBudget).sum + 30 * xs.length + 15) := by
  induction xs generalizing h list with
  | nil =>
    obtain ⟨pointers, hlist, hrel⟩ := hl
    cases hrel
    cases hlist with
    | nil cell =>
      refine ⟨h, 0, .refl h, hh, by simp, by simp, ?_⟩
      rw [hself]
      unfold body
      apply Within.load (budget := 5) (pointer := list) (c := .nil)
      · simp [Atom.eval, initialRegisters]
      · exact cell
      · simpa [values, Atom.eval, Cases.select] using
          Within.ret code h
            (loadRegisters (initialRegisters [.pointer list, .pointer dataPtr]) 3 4 15 .nil)
            [.flag false, .null]
  | cons x xs ih =>
    obtain ⟨pointers, hlist, hrel⟩ := hl
    cases hrel with
    | @cons xp _ ps _ hx hxs =>
    cases hlist with
    | @cons _ _ rest _ cell hrest =>
    obtain ⟨mid, hem, hm, hi⟩ := itemCompiled hh List.mem_cons_self hx hd
    let regs := initialRegisters [Value.pointer list, .pointer dataPtr]
    let rs := loadRegisters regs 3 4 15 (.cons xp rest)
    have iargs : values rs [.register 3, .register 1] = [.pointer xp, .pointer dataPtr] := by
      simp [values, Atom.eval, rs, regs, loadRegisters, decoded, initialRegisters]
    by_cases hp : pred data x = true
    · have hfind : (x :: xs).find? (pred data) = some x := by simp [hp]
      refine ⟨mid, xp, hem, hm, ?_, by simp [hfind], ?_⟩
      · intro y hy
        rw [hfind] at hy
        cases hy
        exact inputMono hem xp x hx
      · rw [hfind]
        let rt := bindResults rs [5] [.flag true]
        have ret : Within code mid rt (.ret [.flag true, .register 3])
            [.flag true, .pointer xp] mid 5 := by
          simpa [values, Atom.eval, rt, rs, bindResults, loadRegisters, decoded] using
            Within.ret code mid rt [.flag true, .register 3]
        have br := Within.branch (b := true) (test := .register 5) (regs := rt)
          (no := .call self [.register 4, .register 1] [6, 7] (.ret [.register 6, .register 7]))
          (by simp [Atom.eval, rt, bindResults]) (by simpa using ret)
        have icall := Within.call (procedure := item)
          (arguments := [.register 3, .register 1]) (results := [5]) (regs := rs)
          (by simpa only [iargs, hp] using hi) br
        have loaded := Within.load (address := .register 0) (first := 3) (second := 4) (bit := 15)
          (branches := {CompiledTrie.failCases with
            nil := .ret [.flag false, .null]
            cons := .call item [.register 3, .register 1] [5]
              (.branch (.register 5)
                (.ret [.flag true, .register 3])
                (.call self [.register 4, .register 1] [6, 7]
                  (.ret [.register 6, .register 7])))})
          (by simp [Atom.eval, regs, initialRegisters]) cell icall
        simpa only [hself, body, Option.isSome_some] using
          loaded.mono (b := ((x :: xs).map itemBudget).sum + 30 * (x :: xs).length + 15)
            (by simp; omega)
    · have hpf : pred data x = false := by simpa using hp
      have hfind : (x :: xs).find? (pred data) = xs.find? (pred data) := by simp [hpf]
      obtain ⟨out, q, heout, ho, hfound, hnone, hc⟩ := ih (h := mid) hm
        ⟨ps, hrest.mono hem, hxs.imp (inputMono hem)⟩ (dataMono hem dataPtr data hd)
        (fun hv _ _ hmem hx' hd' => itemCompiled hv (List.mem_cons_of_mem x hmem) hx' hd')
      refine ⟨out, q, hem.trans heout, ho, by simpa [hfind] using hfound,
        by simpa [hfind] using hnone, ?_⟩
      rw [hfind]
      let rt := bindResults rs [5] [.flag false]
      let ru := bindResults rt [6, 7] [.flag (xs.find? (pred data)).isSome, .pointer q]
      have ret : Within code out ru (.ret [.register 6, .register 7])
          [.flag (xs.find? (pred data)).isSome, .pointer q] out 5 := by
        simpa [values, Atom.eval, ru, bindResults] using
          Within.ret code out ru [.register 6, .register 7]
      have sargs : values rt [.register 4, .register 1] = [.pointer rest, .pointer dataPtr] := by
        simp [values, Atom.eval, rt, rs, regs, bindResults, loadRegisters, decoded,
          initialRegisters]
      have scall := Within.call (procedure := self)
        (arguments := [.register 4, .register 1]) (results := [6, 7]) (regs := rt)
        (by simpa only [sargs] using hc) ret
      have br := Within.branch (b := false) (test := .register 5) (regs := rt)
        (yes := .ret [.flag true, .register 3])
        (by simp [Atom.eval, rt, bindResults]) (by simpa using scall)
      have icall := Within.call (procedure := item)
        (arguments := [.register 3, .register 1]) (results := [5]) (regs := rs)
        (by simpa only [iargs, hpf] using hi) br
      have loaded := Within.load (address := .register 0) (first := 3) (second := 4) (bit := 15)
        (branches := {CompiledTrie.failCases with
          nil := .ret [.flag false, .null]
          cons := .call item [.register 3, .register 1] [5]
            (.branch (.register 5)
              (.ret [.flag true, .register 3])
              (.call self [.register 4, .register 1] [6, 7]
                (.ret [.register 6, .register 7])))})
        (by simp [Atom.eval, regs, initialRegisters]) cell icall
      simpa only [hself, body] using
        loaded.mono (b := ((x :: xs).map itemBudget).sum + 30 * (x :: xs).length + 15)
          (by simp; omega)

/-- Search with a uniform predicate cost. -/
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
    ∃ out q, Extends h out ∧ Valid out ∧
      (∀ x, xs.find? (pred data) = some x → InputAt out q x) ∧
      (xs.find? (pred data) = none → q = 0) ∧
      Within code h (initialRegisters [.pointer list, .pointer dataPtr])
        (code self) [.flag (xs.find? (pred data)).isSome, .pointer q] out
        ((itemBudget + 30) * xs.length + 15) := by
  obtain ⟨out, q, he, ho, hf, hn, hw⟩ := compiled code self item hself InputAt DataAt
    inputMono dataMono pred (fun _ => itemBudget) hh hl hd itemCompiled
  refine ⟨out, q, he, ho, hf, hn, hw.mono ?_⟩
  rw [RegisterListCommon.sum_map_const]
  ring_nf
  omega

end WeightedMIS.RegisterListFind
