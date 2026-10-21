module

public import WeightedMIS.EfficientSearchCodeSolve
public import WeightedMIS.CompiledLookup
public import WeightedMIS.CompiledInsert
public import WeightedMIS.CompiledPop
public import WeightedMIS.RegisterAdder
public import WeightedMIS.RegisterMachineFrames

/-!
# One closed sparse-search program

The same twelve-procedure code table runs for every finite input graph. Vertex
and cost widths are represented by linked binary words, so no graph-dependent
command or oracle is part of the table.
-/

@[expose] public section

namespace WeightedMIS.EfficientSearch.Program

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch.RegisterCode

/-- Fixed procedure identifiers: lookup, insertion, pop, addition, record
creation, pair inspection, empty lookup, push, relax, settle, search, entry. -/
def code : Code 12 := fun i => match i.val with
  | 0 => WeightedMIS.CompiledTrie.lookupBody 0
  | 1 => WeightedMIS.CompiledTrie.insertBody 1
  | 2 => WeightedMIS.CompiledTrie.popBody 2
  | 3 => WeightedMIS.RegisterAdder.adderBody 3
  | 4 => extendBody
  | 5 => readPairBody
  | 6 => lookupEmptyBody 0
  | 7 => pushBody 3 4 1
  | 8 => relaxBody 7 8
  | 9 => freshBody 1 0 8
  | 10 => searchBody 2 5 6 9 10
  | _ => solveBody 1 10

theorem lookup_compiled {h : Heap} {key tree : Ptr} {result : Run (Option Ptr)}
    (he : LookupEval h key tree result) :
    Within code h (initialRegisters [.pointer key, .pointer tree]) (code 0)
      (pointerOutput result.value) result.heap (100 * result.trace.length) := by
  obtain ⟨out, hv, hc⟩ := WeightedMIS.CompiledTrie.compile_lookup (code := code) (self := 0)
    rfl he (initialRegisters [.pointer key, .pointer tree])
    (by simp [initialRegisters]) (by simp [initialRegisters])
  rw [hv]
  exact hc.mono (by omega)

theorem insert_compiled {h : Heap} {key a tree : Ptr} {result : Run (Option Ptr)}
    (he : InsertEval h key a tree result) :
    Within code h (initialRegisters [.pointer key, .pointer a, .pointer tree]) (code 1)
      (pointerOutput result.value) result.heap (100 * result.trace.length) := by
  obtain ⟨out, hv, hc⟩ := WeightedMIS.CompiledTrie.compile_insert (code := code) (self := 1)
    rfl he (initialRegisters [.pointer key, .pointer a, .pointer tree])
    (by simp [initialRegisters]) (by simp [initialRegisters]) (by simp [initialRegisters])
  rw [hv]
  exact hc.mono (by omega)

theorem add_compiled {h : Heap} {ap bp : Ptr} {carry : Bool} {result : Run (Ptr × Bool)}
    (he : AddEval h ap bp carry result) :
    Within code h (initialRegisters [.pointer ap, .pointer bp, .flag carry]) (code 3)
      [.pointer result.value.1, .flag result.value.2] result.heap (10 * result.trace.length) :=
  WeightedMIS.RegisterAdder.compiled code 3 rfl he

theorem read_compiled {h : Heap} {pointer : Ptr} {result : Run (Option (Ptr × Ptr))}
    (he : Pointer.ReadPairEval h pointer result) :
    Within code h (initialRegisters [.pointer pointer]) (code 5)
      (pairOutput result.value) result.heap 15 := readPairEval_compile code he

theorem known_compiled {h : Heap} {key tree : Ptr} {result : Run (Option Bool)}
    (he : Pointer.LookupEmptyEval h key tree result) :
    Within code h (initialRegisters [.pointer key, .pointer tree]) (code 6)
      (flagOutput result.value) result.heap (100 * result.trace.length) :=
  lookupEmptyEval_compile code lookup_compiled he

theorem push_compiled {h : Heap} {vertex path distance arc queue : Ptr}
    {result : Run (Option (Ptr × Bool))} (he : Pointer.PushEdgeEval h vertex path distance arc queue result) :
    Within code h (initialRegisters [.pointer vertex, .pointer path, .pointer distance,
      .pointer arc, .pointer queue]) (code 7)
      (queueOutput result.value) result.heap (100 * result.trace.length) :=
  pushEval_compile (code := code) (add := 3) (extend := 4) (insert := 1) (push := 7) rfl rfl add_compiled insert_compiled he

theorem relax_compiled {h : Heap} {vertex path distance edges queue : Ptr}
    {result : Run (Option (Ptr × Bool))} (he : Pointer.RelaxEval h vertex path distance edges queue result) :
    Within code h (initialRegisters [.pointer vertex, .pointer path, .pointer distance,
      .pointer edges, .pointer queue]) (code 8)
      (queueOutput result.value) result.heap (100 * result.trace.length) :=
  relaxEval_compile (code := code) (push := 7) (self := 8) rfl push_compiled he

theorem fresh_compiled {h : Heap} {graph vertex path distance queue settled : Ptr}
    {result : Run (Option Pointer.FreshValue)} (he : Pointer.FreshEval h graph vertex path distance queue settled result) :
    Within code h (initialRegisters [.pointer graph, .pointer vertex, .pointer path,
      .pointer distance, .pointer queue, .pointer settled]) (code 9)
      (freshOutput result.value) result.heap (100 * result.trace.length) :=
  freshEval_compile (code := code) (insert := 1) (lookup := 0) (relax := 8) (fresh := 9) rfl insert_compiled lookup_compiled relax_compiled he

theorem pop_compiled {h : Heap} {tree : Ptr} {result : Run PopValue}
    (he : PopEval h tree result) (hh : Valid h) :
    Within code h (initialRegisters [.pointer tree]) (code 2)
      (popOutput tree result.value) result.heap (100 * result.trace.length) :=
  WeightedMIS.CompiledTrie.compile_pop (code := code) (self := 2) rfl he hh
    (initialRegisters [.pointer tree]) (by simp [initialRegisters])

theorem search_compiled {h : Heap} {graph queue settled : Ptr}
    {result : Run (Option Pointer.SearchRecord)} (he : Pointer.SearchEval h graph queue settled result) :
    Within code h (initialRegisters [.pointer graph, .pointer queue, .pointer settled]) (code 10)
      (searchOutput result.value) result.heap (100 * result.trace.length) :=
  searchEval_compile (code := code) (pop := 2) (read := 5) (lookupEmpty := 6) (fresh := 9) (self := 10)
    rfl pop_compiled read_compiled known_compiled fresh_compiled he

theorem solve_compiled {h : Heap} {graph source zeroKey : Ptr}
    {result : Run (Option Pointer.SearchRecord)} (he : Pointer.SolveEval h graph source zeroKey result) :
    Within code h (initialRegisters [.pointer graph, .pointer source, .pointer zeroKey]) (code 11)
      (searchOutput result.value) result.heap (100 * result.trace.length) :=
  solveEval_compile (code := code) (insert := 1) (search := 10) (entry := 11) rfl
    insert_compiled search_compiled he

end WeightedMIS.EfficientSearch.Program
