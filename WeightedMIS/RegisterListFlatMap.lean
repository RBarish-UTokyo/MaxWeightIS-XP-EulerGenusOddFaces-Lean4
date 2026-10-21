module

public import WeightedMIS.CompiledTrie
public import WeightedMIS.EfficientSearchCodeBounds
public import WeightedMIS.EfficientSearchPointerTrie

/-!
# A finite linked-list flat-map combinator

The command body traverses actual cons cells and calls one fixed procedure
identifier per item. It shares the output accumulator and never copies a
previously produced list. The theorem composes an independently compiled
item procedure; no host function is part of the command syntax.
-/

@[expose] public section

namespace WeightedMIS.RegisterListFlatMap

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.Pointer

variable {p : ℕ}

def body (self item : Fin p) : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    nil := .ret [.register 2]
    cons := .call self [.register 4, .register 1, .register 2] [5]
      (.call item [.register 3, .register 1, .register 5] [6] (.ret [.register 6])) }

theorem compiled {α β γ : Type*} (code : Code p) (self item : Fin p)
    (hself : code self = body self item)
    (InputAt : Heap → Ptr → α → Prop) (DataAt : Heap → Ptr → γ → Prop)
    (OutputAt : Heap → Ptr → List β → Prop)
    (inputMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, InputAt h ptr x → InputAt h' ptr x)
    (dataMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, DataAt h ptr x → DataAt h' ptr x)
    (f : γ → α → List β) (itemBudget : ℕ)
    (itemCompiled : ∀ {h : Heap}, Valid h → ∀ {xp dp acc : Ptr} {x : α} {data : γ} {tail : List β},
      InputAt h xp x → DataAt h dp data → OutputAt h acc tail →
      ∃ out q, Extends h out ∧ Valid out ∧ OutputAt out q (f data x ++ tail) ∧
        Within code h (initialRegisters [.pointer xp, .pointer dp, .pointer acc])
          (code item) [.pointer q] out itemBudget)
    {h : Heap} (hh : Valid h) {list dataPtr acc : Ptr} {xs : List α} {data : γ} {tail : List β}
    (hl : ListRep InputAt h list xs) (hd : DataAt h dataPtr data) (ha : OutputAt h acc tail) :
    ∃ out q, Extends h out ∧ Valid out ∧ OutputAt out q (xs.flatMap (f data) ++ tail) ∧
      Within code h (initialRegisters [.pointer list, .pointer dataPtr, .pointer acc])
        (code self) [.pointer q] out ((itemBudget + 27) * xs.length + 13) := by
  obtain ⟨pointers, hlist, hrel⟩ := hl
  induction hlist generalizing xs with
  | @nil list cell =>
    cases hrel
    refine ⟨h, acc, .refl h, hh, by simpa using ha, ?_⟩
    rw [hself]
    unfold body
    apply Within.load (budget := 3) (pointer := list) (c := .nil)
    · simp [Atom.eval, initialRegisters]
    · exact cell
    · simpa [values, Atom.eval, loadRegisters, decoded, initialRegisters, Cases.select] using
        Within.ret code h
          (loadRegisters (initialRegisters [.pointer list, .pointer dataPtr, .pointer acc]) 3 4 15 .nil)
          [.register 2]
  | @cons list xp rest pointers cell hlrest ih =>
    cases hrel with
    | @cons _ x _ xs hx hxs =>
      obtain ⟨mid, midPtr, he, hm, ht, hc⟩ := ih hxs
      obtain ⟨out, q, heout, ho, hq, hi⟩ := itemCompiled hm
        (inputMono he xp x hx) (dataMono he dataPtr data hd) ht
      refine ⟨out, q, he.trans heout, ho, ?_, ?_⟩
      · simpa [List.flatMap_cons, List.append_assoc] using hq
      · let regs := initialRegisters [Value.pointer list, .pointer dataPtr, .pointer acc]
        let rs := loadRegisters regs 3 4 15 (.cons xp rest)
        let rt := bindResults rs [5] [.pointer midPtr]
        let ru := bindResults rt [6] [.pointer q]
        have ret : Within code out ru (.ret [.register 6]) [.pointer q] out 3 := by
          simpa [values, Atom.eval, ru, bindResults] using Within.ret code out ru [.register 6]
        have iargs : values rt [.register 3, .register 1, .register 5] =
            [.pointer xp, .pointer dataPtr, .pointer midPtr] := by
          simp [values, Atom.eval, rt, rs, regs, bindResults, loadRegisters, decoded, initialRegisters]
        have icall := Within.call (procedure := item)
          (arguments := [.register 3, .register 1, .register 5]) (results := [6]) (regs := rt)
          (by simpa only [iargs] using hi) ret
        have sargs : values rs [.register 4, .register 1, .register 2] =
            [.pointer rest, .pointer dataPtr, .pointer acc] := by
          simp [values, Atom.eval, rs, regs, loadRegisters, decoded, initialRegisters]
        have scall := Within.call (procedure := self)
          (arguments := [.register 4, .register 1, .register 2]) (results := [5]) (regs := rs)
          (by simpa only [sargs] using hc) icall
        have loaded := Within.load (address := .register 0) (first := 3) (second := 4) (bit := 15)
          (branches := {CompiledTrie.failCases with
            nil := .ret [.register 2]
            cons := .call self [.register 4, .register 1, .register 2] [5]
              (.call item [.register 3, .register 1, .register 5] [6] (.ret [.register 6]))})
          (by simp [Atom.eval, regs, initialRegisters]) cell scall
        simpa only [hself, body] using
          loaded.mono (b := (itemBudget + 27) * (x :: xs).length + 13) (by simp [Nat.mul_add]; omega)

end WeightedMIS.RegisterListFlatMap
