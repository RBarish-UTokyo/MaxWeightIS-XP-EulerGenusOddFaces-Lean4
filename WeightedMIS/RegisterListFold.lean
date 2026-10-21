module

public import WeightedMIS.RegisterListCommon

/-!
# A linked-list left-fold combinator

The command body traverses actual cons cells from the front and calls one
fixed step procedure per item with the item, a data pointer, and the current
state pointer; the returned state pointer is passed to the next item. The
theorem refines `List.foldl`. The step hypothesis is indexed by the position
of the item, so a caller can maintain an invariant of the processed prefix.
-/

@[expose] public section

namespace WeightedMIS.RegisterListFold

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch.Pointer

variable {p : ℕ}

/-- Arguments 0=list, 1=data, 2=state; the result is the final state. -/
def body (self item : Fin p) : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    nil := .ret [.register 2]
    cons := .call item [.register 3, .register 1, .register 2] [5]
      (.call self [.register 4, .register 1, .register 5] [6] (.ret [.register 6])) }

/-- Left fold with an item-dependent step cost. -/
theorem compiled {α γ σ : Type*} (code : Code p) (self item : Fin p)
    (hself : code self = body self item)
    (InputAt : Heap → Ptr → α → Prop) (DataAt : Heap → Ptr → γ → Prop)
    (StateAt : Heap → Ptr → σ → Prop)
    (inputMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, InputAt h ptr x → InputAt h' ptr x)
    (dataMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, DataAt h ptr x → DataAt h' ptr x)
    (step : γ → σ → α → σ) (itemBudget : α → ℕ)
    {h : Heap} (hh : Valid h) {list dataPtr state : Ptr} {xs : List α} {data : γ} {s0 : σ}
    (hl : ListRep InputAt h list xs) (hd : DataAt h dataPtr data) (hs : StateAt h state s0)
    (itemCompiled : ∀ pre x post, xs = pre ++ x :: post →
      ∀ {h : Heap}, Valid h → ∀ {xp sp : Ptr},
        InputAt h xp x → DataAt h dataPtr data → StateAt h sp (pre.foldl (step data) s0) →
        ∃ out sp', Extends h out ∧ Valid out ∧
          StateAt out sp' (step data (pre.foldl (step data) s0) x) ∧
          Within code h (initialRegisters [.pointer xp, .pointer dataPtr, .pointer sp])
            (code item) [.pointer sp'] out (itemBudget x)) :
    ∃ out q, Extends h out ∧ Valid out ∧ StateAt out q (xs.foldl (step data) s0) ∧
      Within code h (initialRegisters [.pointer list, .pointer dataPtr, .pointer state])
        (code self) [.pointer q] out ((xs.map itemBudget).sum + 30 * xs.length + 15) := by
  induction xs generalizing h list state s0 with
  | nil =>
    obtain ⟨pointers, hlist, hrel⟩ := hl
    cases hrel
    cases hlist with
    | nil cell =>
      refine ⟨h, state, .refl h, hh, by simpa using hs, ?_⟩
      rw [hself]
      unfold body
      refine Within.mono (a := 13) ?_ (by simp)
      apply Within.load (budget := 3) (pointer := list) (c := .nil)
      · simp [Atom.eval, initialRegisters]
      · exact cell
      · simpa [values, Atom.eval, loadRegisters, decoded, initialRegisters, Cases.select] using
          Within.ret code h (loadRegisters (initialRegisters
            [.pointer list, .pointer dataPtr, .pointer state]) 3 4 15 .nil) [.register 2]
  | cons x xs ih =>
    obtain ⟨pointers, hlist, hrel⟩ := hl
    cases hrel with
    | @cons xp _ ps _ hx hxs =>
    cases hlist with
    | @cons _ _ rest _ cell hrest =>
    obtain ⟨mid, sp, hem, hm, hsp, hi⟩ := itemCompiled [] x xs rfl hh hx hd (by simpa using hs)
    obtain ⟨out, q, heout, ho, hq, hc⟩ := ih (h := mid) (state := sp)
      (s0 := step data s0 x) hm ⟨ps, hrest.mono hem, hxs.imp (inputMono hem)⟩
      (dataMono hem dataPtr data hd) (by simpa using hsp)
      (fun pre y post hsplit _ hv _ _ hy hd' hst => by
        simpa using itemCompiled (x :: pre) y post (by simp [hsplit]) hv hy hd'
          (by simpa using hst))
    refine ⟨out, q, hem.trans heout, ho, by simpa using hq, ?_⟩
    let regs := initialRegisters [Value.pointer list, .pointer dataPtr, .pointer state]
    let rs := loadRegisters regs 3 4 15 (.cons xp rest)
    let rt := bindResults rs [5] [.pointer sp]
    let ru := bindResults rt [6] [.pointer q]
    have ret : Within code out ru (.ret [.register 6]) [.pointer q] out 3 := by
      simpa [values, Atom.eval, ru, bindResults] using Within.ret code out ru [.register 6]
    have sargs : values rt [.register 4, .register 1, .register 5] =
        [.pointer rest, .pointer dataPtr, .pointer sp] := by
      simp [values, Atom.eval, rt, rs, regs, bindResults, loadRegisters, decoded, initialRegisters]
    have scall := Within.call (procedure := self)
      (arguments := [.register 4, .register 1, .register 5]) (results := [6]) (regs := rt)
      (by simpa only [sargs] using hc) ret
    have iargs : values rs [.register 3, .register 1, .register 2] =
        [.pointer xp, .pointer dataPtr, .pointer state] := by
      simp [values, Atom.eval, rs, regs, loadRegisters, decoded, initialRegisters]
    have icall := Within.call (procedure := item)
      (arguments := [.register 3, .register 1, .register 2]) (results := [5]) (regs := rs)
      (by simpa only [iargs] using hi) scall
    have loaded := Within.load (address := .register 0) (first := 3) (second := 4) (bit := 15)
      (branches := {CompiledTrie.failCases with
        nil := .ret [.register 2]
        cons := .call item [.register 3, .register 1, .register 2] [5]
          (.call self [.register 4, .register 1, .register 5] [6] (.ret [.register 6]))})
      (by simp [Atom.eval, regs, initialRegisters]) cell icall
    simpa only [hself, body] using
      loaded.mono (b := ((x :: xs).map itemBudget).sum + 30 * (x :: xs).length + 15)
        (by simp; omega)

/-- Left fold with a uniform step cost. -/
theorem compiled_const {α γ σ : Type*} (code : Code p) (self item : Fin p)
    (hself : code self = body self item)
    (InputAt : Heap → Ptr → α → Prop) (DataAt : Heap → Ptr → γ → Prop)
    (StateAt : Heap → Ptr → σ → Prop)
    (inputMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, InputAt h ptr x → InputAt h' ptr x)
    (dataMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, DataAt h ptr x → DataAt h' ptr x)
    (step : γ → σ → α → σ) (itemBudget : ℕ)
    {h : Heap} (hh : Valid h) {list dataPtr state : Ptr} {xs : List α} {data : γ} {s0 : σ}
    (hl : ListRep InputAt h list xs) (hd : DataAt h dataPtr data) (hs : StateAt h state s0)
    (itemCompiled : ∀ pre x post, xs = pre ++ x :: post →
      ∀ {h : Heap}, Valid h → ∀ {xp sp : Ptr},
        InputAt h xp x → DataAt h dataPtr data → StateAt h sp (pre.foldl (step data) s0) →
        ∃ out sp', Extends h out ∧ Valid out ∧
          StateAt out sp' (step data (pre.foldl (step data) s0) x) ∧
          Within code h (initialRegisters [.pointer xp, .pointer dataPtr, .pointer sp])
            (code item) [.pointer sp'] out itemBudget) :
    ∃ out q, Extends h out ∧ Valid out ∧ StateAt out q (xs.foldl (step data) s0) ∧
      Within code h (initialRegisters [.pointer list, .pointer dataPtr, .pointer state])
        (code self) [.pointer q] out ((itemBudget + 30) * xs.length + 15) := by
  obtain ⟨out, q, he, ho, hq, hw⟩ := compiled code self item hself InputAt DataAt StateAt
    inputMono dataMono step (fun _ => itemBudget) hh hl hd hs itemCompiled
  refine ⟨out, q, he, ho, hq, hw.mono ?_⟩
  rw [RegisterListCommon.sum_map_const]
  ring_nf
  omega

end WeightedMIS.RegisterListFold
