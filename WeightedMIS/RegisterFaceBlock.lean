module

public import WeightedMIS.RegisterPermutationMirror
public import WeightedMIS.RibbonEnumeration

/-! # A finite program enumerating both orientations of an actual face -/

@[expose] public section

namespace WeightedMIS.RegisterFaceBlock

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.FiniteCycleEnumeration
open WeightedMIS.RegisterPermutationMirror

variable {p : ℕ}

/-- Arguments 0=fuel list, 1=root flag, 2=shared output tail. -/
def blockBody (ordinary mirrored : Fin p) : Command p :=
  .call mirrored [.register 0, .register 1, .register 2] [3]
    (.call ordinary [.register 0, .register 1, .register 3] [4] (.ret [.register 4]))

/-- The two actual pointer traversals produce exactly the facial membership
block used by the deterministic first-unseen scan. -/
theorem compiled {α : Type*} (code : Code p) (ordinary mirrored : Fin p)
    (hordinary : code ordinary = RegisterPermutationTrace.traceBody ordinary)
    (hmirrored : code mirrored = RegisterPermutationMirror.traceBody mirrored)
    (next : Equiv.Perm α) (mirror : α → α) (pointer : α → Ptr)
    {h : Heap} (hh : Valid h) (graph : FlagLinksAt next mirror pointer h)
    {fuel tail : Ptr} {fuelItems tailItems : List Ptr}
    (fuelAt : ListAt h fuel fuelItems) (tailAt : ListAt h tail tailItems) (x : α) :
    ∃ out final, Within code h (initialRegisters [.pointer fuel, .pointer (pointer x), .pointer tail])
      (blockBody ordinary mirrored) [.pointer out] final (86 * fuelItems.length + 43) ∧
      Valid final ∧ Extends h final ∧
      ListAt final out ((bothTrace next mirror fuelItems.length x).map pointer ++ tailItems) := by
  obtain ⟨midPtr, mid, reverse, midValid, midExt, midAt⟩ :=
    RegisterPermutationMirror.compiled code mirrored hmirrored next mirror pointer hh graph fuelAt tailAt x
  obtain ⟨out, final, forward, valid, finalExt, result⟩ :=
    RegisterPermutationTrace.compiled code ordinary hordinary next pointer midValid
      (graph.successors.mono midExt) (fuelAt.mono midExt) midAt x
  let regs := initialRegisters [Value.pointer fuel, .pointer (pointer x), .pointer tail]
  let r1 := bindResults regs [3] [Value.pointer midPtr]
  let r2 := bindResults r1 [4] [Value.pointer out]
  have last : Within code final r2 (.ret [.register 4]) [.pointer out] final 3 := by
    simpa [values, Atom.eval, r2, bindResults] using Within.ret code final r2 [.register 4]
  have first := Within.call (procedure := ordinary) (regs := r1)
    (arguments := [.register 0, .register 1, .register 3]) (results := [4])
    (by simpa [values, Atom.eval, r1, regs, bindResults, initialRegisters] using forward) last
  have second := Within.call (procedure := mirrored) (regs := regs)
    (arguments := [.register 0, .register 1, .register 2]) (results := [3])
    (by simpa [values, Atom.eval, regs, initialRegisters] using reverse) first
  refine ⟨out, final, second.mono (by simp only [List.length_cons, List.length_nil]; omega),
    valid, midExt.trans finalExt, ?_⟩
  simpa [bothTrace, List.map_append, List.map_map, List.append_assoc] using result

/-- A concrete three-procedure table contains both tracers and their wrapper. -/
def program : Code 3 :=
  ![RegisterPermutationTrace.traceBody 0, RegisterPermutationMirror.traceBody 1, blockBody 0 1]

end WeightedMIS.RegisterFaceBlock

namespace WeightedMIS.EmbeddingFaces.Ribbon

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.FiniteCycleEnumeration
open WeightedMIS.RegisterPermutationMirror
open WeightedMIS.EmbeddingFaces.SidePairing

/-- The finite flag records contain the actual rotation and endpoint reversal
of the supplied ribbon, so tracing executes actual facial permutations. -/
def FlagLinksAt {V E : Type*} {left right : E → V} (R : Ribbon left right)
    (pointer : Flag E → Ptr) (h : Heap) : Prop :=
  RegisterPermutationMirror.FlagLinksAt R.rotation along pointer h

/-- The fixed machine emits an actual complete facial-membership block;
its membership predicate is precisely equality of actual facial circles. -/
theorem compiled_face_block {V E : Type*} [Fintype E] [DecidableEq E]
    {left right : E → V} (R : Ribbon left right) (pointer : Flag E → Ptr)
    (hinj : Function.Injective pointer) {h : Heap} (hh : Valid h) (graph : R.FlagLinksAt pointer h)
    {fuel : Ptr} {fuelItems : List Ptr} (fuelAt : ListAt h fuel fuelItems)
    (hlen : fuelItems.length = Fintype.card (Flag E)) (x : Flag E) :
    ∃ out final block, Within RegisterFaceBlock.program h
        (initialRegisters [.pointer fuel, .pointer (pointer x), .pointer 0])
        (RegisterFaceBlock.program 2) [.pointer out] final (86 * Fintype.card (Flag E) + 43) ∧
      Valid final ∧ Extends h final ∧ ListAt final out block ∧
      block.length = 2 * Fintype.card (Flag E) ∧
      (∀ y, pointer y ∈ block ↔ R.SameFace x y) := by
  obtain ⟨out, final, run, valid, ext, result⟩ := RegisterFaceBlock.compiled
    RegisterFaceBlock.program 0 1 rfl rfl R.rotation along pointer hh graph fuelAt (.nil hh.1) x
  rw [hlen] at run result
  refine ⟨out, final, (bothTrace R.rotation along (Fintype.card (Flag E)) x).map pointer,
    run, valid, ext, ?_, ?_, ?_⟩
  · simpa using result
  · simp [bothTrace_length]
  · intro y
    rw [List.mem_map]
    constructor
    · rintro ⟨z, hz, he⟩
      have hzy := hinj he
      subst z
      exact (mem_bothTrace_iff R.rotation along along_along x y).mp hz
    · intro hy
      exact ⟨y, (mem_bothTrace_iff R.rotation along along_along x y).mpr hy, rfl⟩

end WeightedMIS.EmbeddingFaces.Ribbon
