module

public import WeightedMIS.CompiledTemplateEmit

/-! # Finite signed-column template conversion and its constant event bound -/

@[expose] public section

namespace WeightedMIS.CompiledTemplates

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch WeightedMIS.CompiledTrie WeightedMIS.Walks

variable {p : ℕ} {Row Metadata : Type*} {width : ℕ}
    {key : State Row → Bits width} {metaAt : Heap → Ptr → Metadata → Prop}

/-- Every actual signed column emits exactly its actual one-or-two arcs. -/
theorem column_compiled (code : Code p) (stub emit : Fin p)
    (stubCode : code stub = stubBody) (emitCode : code emit = emitBody)
    (mono : ∀ {h h' ptr a}, Extends h h' → metaAt h ptr a → metaAt h' ptr a)
    {h : Heap} (hh : Valid h) {cp mp hub tail : Ptr} {c : Column Row} {metadata : Metadata}
    {as : List (Template Row Metadata)}
    (hc : ColumnAt key h cp c) (hm : metaAt h mp metadata) (hmalloc : mp < h.length)
    (hubAt : BitsAt h hub (key none)) (tailAt : TemplatesAt key metaAt h tail as) :
    ∃ out final, Within code h (initialRegisters [.pointer cp, .pointer mp, .pointer hub,
        .pointer tail]) (columnBody stub emit) [.pointer out] final 147 ∧
      Valid final ∧ Extends h final ∧
      TemplatesAt key metaAt final out (templates c metadata ++ as) := by
  cases hc with
  | zero cell =>
    obtain ⟨out, final, emitted, valid, ext, result⟩ := emit_compiled (metaAt := metaAt) code mono hh
      (a := ⟨none, none, metadata⟩) hubAt hubAt hm hmalloc tailAt
    let r0 := initialRegisters [Value.pointer cp, .pointer mp, .pointer hub, .pointer tail]
    let r1 := loadRegisters r0 4 10 15 .nil
    let r2 := bindResults r1 [9] [Value.pointer out]
    have last : Within code final r2 (.ret [.register 9]) [.pointer out] final 3 := by
      simpa [values, Atom.eval, r2, bindResults] using Within.ret code final r2 [.register 9]
    have call := Within.call (procedure := emit) (regs := r1)
      (arguments := [.register 2, .register 2, .register 1, .register 3]) (results := [9])
      (by simpa [emitCode, values, Atom.eval, r1, r0, loadRegisters, decoded, initialRegisters]
        using emitted) last
    have loaded := Within.load (address := .register 0) (first := 4) (second := 10) (bit := 15)
      (branches := {failCases with
        nil := .call emit [.register 2, .register 2, .register 1, .register 3] [9] (.ret [.register 9])
        bucket := oneBody stub emit
        pair := twoBody stub emit})
      (by simp [Atom.eval, r0, initialRegisters]) cell call
    exact ⟨out, final, loaded.mono (by decide), valid, ext, by simpa [templates] using result⟩
  | @one sp s cell stubAt =>
    obtain ⟨opp, own, readStub, oppAt, ownAt⟩ := stub_within code
      (regs := initialRegisters [.pointer sp]) (by simp [initialRegisters]) stubAt
    obtain ⟨midPtr, mid, reverse, midValid, midExt, midAt⟩ := emit_compiled (metaAt := metaAt) code mono hh
      (a := ⟨some (opposite s), none, metadata⟩) oppAt hubAt hm hmalloc tailAt
    obtain ⟨out, final, forward, valid, finalExt, result⟩ := emit_compiled (metaAt := metaAt) code mono midValid
      (a := ⟨none, some s, metadata⟩) (hubAt.mono midExt) (ownAt.mono midExt)
      (mono midExt hm) (lt_of_lt_of_le hmalloc midExt.length_le) midAt
    let r0 := initialRegisters [Value.pointer cp, .pointer mp, .pointer hub, .pointer tail]
    let r1 := loadRegisters r0 4 10 15 (.bucket sp)
    let r2 := bindResults r1 [5, 6] [Value.pointer opp, .pointer own]
    let r3 := bindResults r2 [9] [Value.pointer midPtr]
    let r4 := bindResults r3 [9] [Value.pointer out]
    have last : Within code final r4 (.ret [.register 9]) [.pointer out] final 3 := by
      simpa [values, Atom.eval, r4, bindResults] using Within.ret code final r4 [.register 9]
    have fcall := Within.call (procedure := emit) (regs := r3)
      (arguments := [.register 2, .register 6, .register 1, .register 9]) (results := [9])
      (by simpa [emitCode, values, Atom.eval, r3, r2, r1, r0, bindResults,
        loadRegisters, decoded, initialRegisters] using forward) last
    have rcall := Within.call (procedure := emit) (regs := r2)
      (arguments := [.register 5, .register 2, .register 1, .register 3]) (results := [9])
      (by simpa [emitCode, values, Atom.eval, r2, r1, r0, bindResults,
        loadRegisters, decoded, initialRegisters] using reverse) fcall
    have scall := Within.call (procedure := stub) (regs := r1)
      (arguments := [.register 4]) (results := [5, 6])
      (by simpa [stubCode, values, Atom.eval, r1, loadRegisters, decoded] using readStub) rcall
    have loaded := Within.load (address := .register 0) (first := 4) (second := 10) (bit := 15)
      (branches := {failCases with
        nil := .call emit [.register 2, .register 2, .register 1, .register 3] [9] (.ret [.register 9])
        bucket := oneBody stub emit
        pair := twoBody stub emit})
      (by simp [Atom.eval, r0, initialRegisters]) cell scall
    exact ⟨out, final, loaded.mono (by decide), valid, midExt.trans finalExt,
      by simpa [templates] using result⟩
  | @two sp tp s t cell first second =>
    obtain ⟨oppS, ownS, readS, oppSAt, ownSAt⟩ := stub_within code
      (regs := initialRegisters [.pointer sp]) (by simp [initialRegisters]) first
    obtain ⟨oppT, ownT, readT, oppTAt, ownTAt⟩ := stub_within code
      (regs := initialRegisters [.pointer tp]) (by simp [initialRegisters]) second
    obtain ⟨midPtr, mid, reverse, midValid, midExt, midAt⟩ := emit_compiled (metaAt := metaAt) code mono hh
      (a := ⟨some (opposite t), some s, metadata⟩) oppTAt ownSAt hm hmalloc tailAt
    obtain ⟨out, final, forward, valid, finalExt, result⟩ := emit_compiled (metaAt := metaAt) code mono midValid
      (a := ⟨some (opposite s), some t, metadata⟩) (oppSAt.mono midExt) (ownTAt.mono midExt)
      (mono midExt hm) (lt_of_lt_of_le hmalloc midExt.length_le) midAt
    let r0 := initialRegisters [Value.pointer cp, .pointer mp, .pointer hub, .pointer tail]
    let r1 := loadRegisters r0 4 10 15 (.pair sp tp)
    let r2 := bindResults r1 [5, 6] [Value.pointer oppS, .pointer ownS]
    let r3 := bindResults r2 [7, 8] [Value.pointer oppT, .pointer ownT]
    let r4 := bindResults r3 [9] [Value.pointer midPtr]
    let r5 := bindResults r4 [9] [Value.pointer out]
    have last : Within code final r5 (.ret [.register 9]) [.pointer out] final 3 := by
      simpa [values, Atom.eval, r5, bindResults] using Within.ret code final r5 [.register 9]
    have fcall := Within.call (procedure := emit) (regs := r4)
      (arguments := [.register 5, .register 8, .register 1, .register 9]) (results := [9])
      (by simpa [emitCode, values, Atom.eval, r4, r3, r2, r1, r0, bindResults,
        loadRegisters, decoded, initialRegisters] using forward) last
    have rcall := Within.call (procedure := emit) (regs := r3)
      (arguments := [.register 7, .register 6, .register 1, .register 3]) (results := [9])
      (by simpa [emitCode, values, Atom.eval, r3, r2, r1, r0, bindResults,
        loadRegisters, decoded, initialRegisters] using reverse) fcall
    have tcall := Within.call (procedure := stub) (regs := r2)
      (arguments := [.register 10]) (results := [7, 8])
      (by simpa [stubCode, values, Atom.eval, r2, r1, bindResults,
        loadRegisters, decoded] using readT) rcall
    have scall := Within.call (procedure := stub) (regs := r1)
      (arguments := [.register 4]) (results := [5, 6])
      (by simpa [stubCode, values, Atom.eval, r1, loadRegisters, decoded] using readS) tcall
    have loaded := Within.load (address := .register 0) (first := 4) (second := 10) (bit := 15)
      (branches := {failCases with
        nil := .call emit [.register 2, .register 2, .register 1, .register 3] [9] (.ret [.register 9])
        bucket := oneBody stub emit
        pair := twoBody stub emit})
      (by simp [Atom.eval, r0, initialRegisters]) cell scall
    exact ⟨out, final, loaded.mono (by decide), valid, midExt.trans finalExt,
      by simpa [templates] using result⟩

end WeightedMIS.CompiledTemplates
