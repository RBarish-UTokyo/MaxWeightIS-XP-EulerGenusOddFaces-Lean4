module

public import WeightedMIS.CompiledTemplateColumn

/-!
# Linear-event compilation of all signed-column templates

The input is an actual immutable list of stored signed columns and metadata.
The finite recursive procedure emits their actual arcs in original edge order.
-/

@[expose] public section

namespace WeightedMIS.CompiledTemplates

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch WeightedMIS.CompiledTrie WeightedMIS.Walks

variable {p : ℕ} {Row Metadata : Type*} {width : ℕ}
    {key : State Row → Bits width} {metaAt : Heap → Ptr → Metadata → Prop}

/-- The exact source/target/metadata records for the supplied signed columns. -/
def allTemplates (entries : List (Column Row × Metadata)) : List (Template Row Metadata) :=
  entries.flatMap (fun e => templates e.1 e.2)

theorem allTemplates_length_le (entries : List (Column Row × Metadata)) :
    (allTemplates entries).length ≤ 2 * entries.length := by
  induction entries with
  | nil => simp [allTemplates]
  | cons entry entries ih =>
    have := templates_length_le_two entry.1 entry.2
    simp only [allTemplates, List.flatMap_cons, List.length_append, List.length_cons] at *
    omega

/-- The exact executable preprocessor, retaining an arbitrary represented tail. -/
theorem list_compiled_aux (code : Code p) (self column stub emit : Fin p)
    (listCode : code self = listBody self column)
    (columnCode : code column = columnBody stub emit)
    (stubCode : code stub = stubBody) (emitCode : code emit = emitBody)
    (mono : ∀ {h h' ptr a}, Extends h h' → metaAt h ptr a → metaAt h' ptr a)
    {h : Heap} (hh : Valid h) {input hub tail : Ptr} {pointers : List Ptr}
    {entries : List (Column Row × Metadata)} {as : List (Template Row Metadata)}
    (listAt : ListAt h input pointers) (entriesAt : List.Forall₂ (EdgeAt key metaAt h) pointers entries)
    (hubAt : BitsAt h hub (key none)) (tailAt : TemplatesAt key metaAt h tail as) :
    ∃ out final, Within code h (initialRegisters [.pointer input, .pointer hub, .pointer tail])
      (code self) [.pointer out] final (186 * entries.length + 13) ∧
      Valid final ∧ Extends h final ∧
      TemplatesAt key metaAt final out (allTemplates entries ++ as) := by
  induction listAt generalizing entries with
  | @nil input cell =>
    cases entriesAt
    let r0 := initialRegisters [Value.pointer input, .pointer hub, .pointer tail]
    let r1 := loadRegisters r0 3 4 5 .nil
    have last : Within code h r1 (.ret [.register 2]) [.pointer tail] h 3 := by
      simpa [values, Atom.eval, r1, r0, loadRegisters, decoded, initialRegisters] using
        Within.ret code h r1 [.register 2]
    have loaded := Within.load (address := .register 0) (first := 3) (second := 4) (bit := 5)
      (branches := {failCases with
        nil := .ret [.register 2]
        cons := .load (.register 3) 6 7 8 {
          failCases with
          pair := .call self [.register 4, .register 1, .register 2] [9]
            (.call column [.register 6, .register 7, .register 1, .register 9] [10] (.ret [.register 10]))
        }})
      (by simp [Atom.eval, r0, initialRegisters]) cell last
    refine ⟨tail, h, ?_, hh, Extends.refl h, ?_⟩
    · simpa [listCode, listBody] using loaded
    · simpa [allTemplates] using tailAt
  | @cons input ep inputTail pointers cell rest ih =>
    cases entriesAt with
    | @cons _ entry _ entries record records =>
      obtain ⟨cp, mp, recordCell, columnAt, metadataAt⟩ := record
      have hmalloc : mp < h.length := hh.2 ep (.pair cp mp) recordCell mp (by simp [Cell.references])
      obtain ⟨midPtr, mid, child, midValid, midExt, midAt⟩ := ih records
      obtain ⟨out, final, converted, valid, finalExt, result⟩ := column_compiled (metaAt := metaAt) code stub emit
        stubCode emitCode mono midValid (columnAt.mono midExt) (mono midExt metadataAt)
        (lt_of_lt_of_le hmalloc midExt.length_le) (hubAt.mono midExt) midAt
      let r0 := initialRegisters [Value.pointer input, .pointer hub, .pointer tail]
      let r1 := loadRegisters r0 3 4 5 (.cons ep inputTail)
      let r2 := loadRegisters r1 6 7 8 (.pair cp mp)
      let r3 := bindResults r2 [9] [Value.pointer midPtr]
      let r4 := bindResults r3 [10] [Value.pointer out]
      have last : Within code final r4 (.ret [.register 10]) [.pointer out] final 3 := by
        simpa [values, Atom.eval, r4, bindResults] using Within.ret code final r4 [.register 10]
      have ccall := Within.call (procedure := column) (regs := r3)
        (arguments := [.register 6, .register 7, .register 1, .register 9]) (results := [10])
        (by simpa [columnCode, values, Atom.eval, r3, r2, r1, r0, bindResults,
          loadRegisters, decoded, initialRegisters] using converted) last
      have scall := Within.call (procedure := self) (regs := r2)
        (arguments := [.register 4, .register 1, .register 2]) (results := [9])
        (by simpa [values, Atom.eval, r2, r1, r0, loadRegisters, decoded, initialRegisters]
          using child) ccall
      have recordLoad := Within.load (address := .register 3) (first := 6) (second := 7) (bit := 8)
        (branches := {failCases with
          pair := .call self [.register 4, .register 1, .register 2] [9]
            (.call column [.register 6, .register 7, .register 1, .register 9] [10] (.ret [.register 10]))})
        (by simp [Atom.eval, r1, loadRegisters, decoded]) recordCell scall
      have listLoad := Within.load (address := .register 0) (first := 3) (second := 4) (bit := 5)
        (branches := {failCases with
          nil := .ret [.register 2]
          cons := .load (.register 3) 6 7 8 {
            failCases with
            pair := .call self [.register 4, .register 1, .register 2] [9]
              (.call column [.register 6, .register 7, .register 1, .register 9] [10] (.ret [.register 10]))
          }})
        (by simp [Atom.eval, r0, initialRegisters]) cell recordLoad
      refine ⟨out, final, ?_, valid, midExt.trans finalExt, ?_⟩
      · rw [listCode]
        exact listLoad.mono (by simp [List.length_cons]; omega)
      · simpa [allTemplates, List.append_assoc] using result

/-- From the empty output tail, the finite program emits all and only the
actual signed arcs, at most twice the number of original input edges. -/
theorem list_compiled (code : Code p) (self column stub emit : Fin p)
    (listCode : code self = listBody self column)
    (columnCode : code column = columnBody stub emit)
    (stubCode : code stub = stubBody) (emitCode : code emit = emitBody)
    (mono : ∀ {h h' ptr a}, Extends h h' → metaAt h ptr a → metaAt h' ptr a)
    {h : Heap} (hh : Valid h) {input hub : Ptr} {pointers : List Ptr}
    {entries : List (Column Row × Metadata)}
    (listAt : ListAt h input pointers) (entriesAt : List.Forall₂ (EdgeAt key metaAt h) pointers entries)
    (hubAt : BitsAt h hub (key none)) :
    ∃ out final, Within code h (initialRegisters [.pointer input, .pointer hub, .pointer 0])
      (code self) [.pointer out] final (186 * entries.length + 13) ∧
      Valid final ∧ Extends h final ∧ TemplatesAt key metaAt final out (allTemplates entries) := by
  simpa using list_compiled_aux (metaAt := metaAt) code self column stub emit listCode columnCode stubCode emitCode
    mono hh listAt entriesAt hubAt (as := []) ⟨[], .nil hh.1, .nil⟩

end WeightedMIS.CompiledTemplates
