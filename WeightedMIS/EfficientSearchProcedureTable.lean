module

public import WeightedMIS.EfficientSearchProgram

/-!
# Linking sparse search into a larger finite program

The interface below fixes every search dependency by an equality with its
concrete command syntax. It permits a single larger program to contain graph
construction, search, and output recovery without introducing algorithmic
or runtime assumptions.
-/

@[expose] public section

namespace WeightedMIS.EfficientSearch.Linked

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch.RegisterCode

structure Procedures (p : ℕ) where
  lookup : Fin p
  insert : Fin p
  pop : Fin p
  add : Fin p
  extend : Fin p
  read : Fin p
  known : Fin p
  push : Fin p
  relax : Fin p
  fresh : Fin p
  search : Fin p
  solve : Fin p

structure Procedures.Matches {p : ℕ} (d : Procedures p) (code : Code p) : Prop where
  lookup : code d.lookup = WeightedMIS.CompiledTrie.lookupBody d.lookup
  insert : code d.insert = WeightedMIS.CompiledTrie.insertBody d.insert
  pop : code d.pop = WeightedMIS.CompiledTrie.popBody d.pop
  add : code d.add = WeightedMIS.RegisterAdder.adderBody d.add
  extend : code d.extend = extendBody
  read : code d.read = readPairBody
  known : code d.known = lookupEmptyBody d.lookup
  push : code d.push = pushBody d.add d.extend d.insert
  relax : code d.relax = relaxBody d.push d.relax
  fresh : code d.fresh = freshBody d.insert d.lookup d.relax
  search : code d.search = searchBody d.pop d.read d.known d.fresh d.search
  solve : code d.solve = solveBody d.insert d.search

variable {p : ℕ} (code : Code p) (d : Procedures p) (hm : d.Matches code)

include hm

theorem lookup_compiled {h : Heap} {key tree : Ptr} {result : Run (Option Ptr)}
    (he : LookupEval h key tree result) :
    Within code h (initialRegisters [.pointer key, .pointer tree]) (code d.lookup)
      (pointerOutput result.value) result.heap (100 * result.trace.length) := by
  obtain ⟨out, hv, hc⟩ := WeightedMIS.CompiledTrie.compile_lookup hm.lookup he
    (initialRegisters [.pointer key, .pointer tree])
    (by simp [initialRegisters]) (by simp [initialRegisters])
  rw [hv, hm.lookup]
  exact hc.mono (by omega)

theorem insert_compiled {h : Heap} {key a tree : Ptr} {result : Run (Option Ptr)}
    (he : InsertEval h key a tree result) :
    Within code h (initialRegisters [.pointer key, .pointer a, .pointer tree]) (code d.insert)
      (pointerOutput result.value) result.heap (100 * result.trace.length) := by
  obtain ⟨out, hv, hc⟩ := WeightedMIS.CompiledTrie.compile_insert hm.insert he
    (initialRegisters [.pointer key, .pointer a, .pointer tree])
    (by simp [initialRegisters]) (by simp [initialRegisters]) (by simp [initialRegisters])
  rw [hv, hm.insert]
  exact hc.mono (by omega)

theorem add_compiled {h : Heap} {ap bp : Ptr} {carry : Bool} {result : Run (Ptr × Bool)}
    (he : AddEval h ap bp carry result) :
    Within code h (initialRegisters [.pointer ap, .pointer bp, .flag carry]) (code d.add)
      [.pointer result.value.1, .flag result.value.2] result.heap (10 * result.trace.length) :=
  WeightedMIS.RegisterAdder.compiled code d.add hm.add he

theorem read_compiled {h : Heap} {pointer : Ptr} {result : Run (Option (Ptr × Ptr))}
    (he : Pointer.ReadPairEval h pointer result) :
    Within code h (initialRegisters [.pointer pointer]) (code d.read)
      (pairOutput result.value) result.heap 15 := by
  rw [hm.read]
  exact readPairEval_compile code he

theorem known_compiled {h : Heap} {key tree : Ptr} {result : Run (Option Bool)}
    (he : Pointer.LookupEmptyEval h key tree result) :
    Within code h (initialRegisters [.pointer key, .pointer tree]) (code d.known)
      (flagOutput result.value) result.heap (100 * result.trace.length) := by
  rw [hm.known]
  exact lookupEmptyEval_compile code (lookup_compiled code d hm) he

theorem push_compiled {h : Heap} {vertex path distance arc queue : Ptr}
    {result : Run (Option (Ptr × Bool))} (he : Pointer.PushEdgeEval h vertex path distance arc queue result) :
    Within code h (initialRegisters [.pointer vertex, .pointer path, .pointer distance,
      .pointer arc, .pointer queue]) (code d.push)
      (queueOutput result.value) result.heap (100 * result.trace.length) :=
  pushEval_compile (code := code) (add := d.add) (extend := d.extend) (insert := d.insert) (push := d.push)
    hm.push hm.extend (add_compiled code d hm) (insert_compiled code d hm) he

theorem relax_compiled {h : Heap} {vertex path distance edges queue : Ptr}
    {result : Run (Option (Ptr × Bool))} (he : Pointer.RelaxEval h vertex path distance edges queue result) :
    Within code h (initialRegisters [.pointer vertex, .pointer path, .pointer distance,
      .pointer edges, .pointer queue]) (code d.relax)
      (queueOutput result.value) result.heap (100 * result.trace.length) :=
  relaxEval_compile (code := code) (push := d.push) (self := d.relax)
    hm.relax (push_compiled code d hm) he

theorem fresh_compiled {h : Heap} {graph vertex path distance queue settled : Ptr}
    {result : Run (Option Pointer.FreshValue)} (he : Pointer.FreshEval h graph vertex path distance queue settled result) :
    Within code h (initialRegisters [.pointer graph, .pointer vertex, .pointer path,
      .pointer distance, .pointer queue, .pointer settled]) (code d.fresh)
      (freshOutput result.value) result.heap (100 * result.trace.length) :=
  freshEval_compile (code := code) (insert := d.insert) (lookup := d.lookup) (relax := d.relax) (fresh := d.fresh)
    hm.fresh (insert_compiled code d hm) (lookup_compiled code d hm) (relax_compiled code d hm) he

theorem pop_compiled {h : Heap} {tree : Ptr} {result : Run PopValue}
    (he : PopEval h tree result) (hh : Valid h) :
    Within code h (initialRegisters [.pointer tree]) (code d.pop)
      (popOutput tree result.value) result.heap (100 * result.trace.length) := by
  rw [hm.pop]
  exact WeightedMIS.CompiledTrie.compile_pop hm.pop he hh
    (initialRegisters [.pointer tree]) (by simp [initialRegisters])

theorem search_compiled {h : Heap} {graph queue settled : Ptr}
    {result : Run (Option Pointer.SearchRecord)} (he : Pointer.SearchEval h graph queue settled result) :
    Within code h (initialRegisters [.pointer graph, .pointer queue, .pointer settled]) (code d.search)
      (searchOutput result.value) result.heap (100 * result.trace.length) :=
  searchEval_compile (code := code) (pop := d.pop) (read := d.read) (lookupEmpty := d.known)
    (fresh := d.fresh) (self := d.search) hm.search
    (pop_compiled code d hm) (read_compiled code d hm) (known_compiled code d hm) (fresh_compiled code d hm) he

/-- Every dependency has been discharged against its closed finite body. -/
theorem solve_compiled {h : Heap} {graph source zeroKey : Ptr}
    {result : Run (Option Pointer.SearchRecord)} (he : Pointer.SolveEval h graph source zeroKey result) :
    Within code h (initialRegisters [.pointer graph, .pointer source, .pointer zeroKey]) (code d.solve)
      (searchOutput result.value) result.heap (100 * result.trace.length) :=
  solveEval_compile (code := code) (insert := d.insert) (search := d.search) (entry := d.solve)
    hm.solve (insert_compiled code d hm) (search_compiled code d hm) he

end WeightedMIS.EfficientSearch.Linked
