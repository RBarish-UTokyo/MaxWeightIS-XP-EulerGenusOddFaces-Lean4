module

public import WeightedMIS.RegisterMachineMeta

/-!
# Frames attached to actual interpreter calls

This operational relation refines the fixed-code interpreter by retaining its
call structure. Every call saves the actual sixteen caller registers, and the
continuation follows restoration of that exact bank. Hence flattening calls
into uncharged heap code cannot satisfy the relation.
-/

@[expose] public section

namespace WeightedMIS.RegisterMachine

open WeightedMIS.PointerMemory

/-- Exposing call frames does not change a single interpreted instruction. -/
theorem FramedExec.erase {p : ℕ} {code : Code p} {h : Heap} {regs : Registers}
    {command : Command p} {result : Run (List Value)} {tree : CallTree}
    (he : FramedExec code h regs command result tree) : Exec code h regs command result := by
  induction he with
  | ret => exact .ret _ _ _
  | copy rest ih => exact .copy ih
  | allocate evaluated rest ih => exact .allocate evaluated ih
  | load evaluated loaded rest ih => exact .load evaluated loaded ih
  | branch evaluated rest ih => exact .branch evaluated ih
  | call body rest ihbody ihrest => exact .call ihbody ihrest

/-- Every actual finite-code evaluation has its exact call-frame refinement. -/
theorem Exec.framed {p : ℕ} {code : Code p} {h : Heap} {regs : Registers}
    {command : Command p} {result : Run (List Value)} (he : Exec code h regs command result) :
    ∃ tree, FramedExec code h regs command result tree := by
  induction he with
  | ret => exact ⟨_, .ret _ _ _⟩
  | copy rest ih => obtain ⟨tree, ht⟩ := ih; exact ⟨_, .copy ht⟩
  | allocate evaluated rest ih => obtain ⟨tree, ht⟩ := ih; exact ⟨_, .allocate evaluated ht⟩
  | load evaluated loaded rest ih => obtain ⟨tree, ht⟩ := ih; exact ⟨_, .load evaluated loaded ht⟩
  | branch evaluated rest ih => obtain ⟨tree, ht⟩ := ih; exact ⟨_, .branch evaluated ht⟩
  | call body rest ihbody ihrest =>
      obtain ⟨bt, hb⟩ := ihbody
      obtain ⟨rt, hr⟩ := ihrest
      exact ⟨_, .call hb hr⟩

/-- Fixed code and input determine the call-frame tree as well as the result.
The concrete saved-bank structure is not an existential optimization choice. -/
theorem FramedExec.deterministic {p : ℕ} {code : Code p} {h : Heap} {regs : Registers}
    {command : Command p} {first second : Run (List Value)} {firstTree secondTree : CallTree}
    (hf : FramedExec code h regs command first firstTree)
    (hs : FramedExec code h regs command second secondTree) :
    first = second ∧ firstTree = secondTree := by
  induction hf generalizing second secondTree with
  | ret => cases hs; exact ⟨rfl, rfl⟩
  | copy rest ih =>
      cases hs with
      | copy rest' => obtain ⟨rfl, rfl⟩ := ih rest'; exact ⟨rfl, rfl⟩
  | allocate evaluated rest ih =>
      cases hs with
      | allocate evaluated' rest' =>
          cases Option.some.inj (evaluated.symm.trans evaluated')
          obtain ⟨rfl, rfl⟩ := ih rest'
          exact ⟨rfl, rfl⟩
  | load evaluated loaded rest ih =>
      cases hs with
      | load evaluated' loaded' rest' =>
          cases Value.pointer.inj (evaluated.symm.trans evaluated')
          cases Option.some.inj (loaded.symm.trans loaded')
          obtain ⟨rfl, rfl⟩ := ih rest'
          exact ⟨rfl, rfl⟩
  | branch evaluated rest ih =>
      cases hs with
      | branch evaluated' rest' =>
          cases Value.flag.inj (evaluated.symm.trans evaluated')
          obtain ⟨rfl, rfl⟩ := ih rest'
          exact ⟨rfl, rfl⟩
  | call body rest ihbody ihrest =>
      cases hs with
      | call body' rest' =>
          obtain ⟨rfl, rfl⟩ := ihbody body'
          obtain ⟨rfl, rfl⟩ := ihrest rest'
          exact ⟨rfl, rfl⟩

/-- Frame erasure preserves the exact charged heap-event trace. -/
theorem FramedExec.memoryTrace {p : ℕ} {code : Code p} {h : Heap} {regs : Registers}
    {command : Command p} {result : Run (List Value)} {tree : CallTree}
    (he : FramedExec code h regs command result tree) : tree.memoryTrace = result.trace := by
  induction he with
  | ret => rfl
  | copy rest ih => simp only [CallTree.memoryTrace, withEvents, ih]
  | allocate evaluated rest ih => simp only [CallTree.memoryTrace, withEvents, ih]
  | load evaluated loaded rest ih => simp only [CallTree.memoryTrace, withEvents, ih]
  | branch evaluated rest ih => simp only [CallTree.memoryTrace, withEvents, ih]
  | call body rest ihbody ihrest =>
      simp only [CallTree.memoryTrace, withEvents, sequenceRuns, ihbody, ihrest]

/-- Every actual call contributes at least its own control event. -/
theorem FramedExec.calls_le {p : ℕ} {code : Code p} {h : Heap} {regs : Registers}
    {command : Command p} {result : Run (List Value)} {tree : CallTree}
    (he : FramedExec code h regs command result tree) : tree.calls ≤ result.trace.length := by
  induction he with
  | ret => simp [CallTree.calls]
  | copy rest ih => simp only [CallTree.calls, withEvents, List.length_append, List.length_cons]; omega
  | allocate evaluated rest ih =>
      simp only [CallTree.calls, withEvents, List.length_append, List.length_cons]; omega
  | load evaluated loaded rest ih =>
      simp only [CallTree.calls, withEvents, List.length_append, List.length_cons]; omega
  | branch evaluated rest ih =>
      simp only [CallTree.calls, withEvents, List.length_append, List.length_cons]; omega
  | call body rest ihbody ihrest =>
      simp only [CallTree.calls, withEvents, sequenceRuns, List.length_append, List.length_cons]; omega

/-- Increasing the available heap bound preserves every concrete saved word. -/
theorem callTree_bounded_mono {tree : CallTree} {a b slots : ℕ}
    (ht : tree.Bounded a slots) (hab : a ≤ b) : tree.Bounded b slots := by
  induction tree with
  | code => trivial
  | seq x y ihx ihy => exact ⟨ihx ht.1, ihy ht.2⟩
  | call frame body ih =>
      refine ⟨ht.1, ?_, ih ht.2.2⟩
      intro w hw
      have hv := ht.2.1 w hw
      cases w with
      | pointer p => exact lt_of_lt_of_le hv hab
      | flag => trivial

/-- Every saved bank has exactly sixteen actual allocated pointer/bit words. -/
theorem FramedExec.bounded {p : ℕ} {code : Code p} {h : Heap} {regs : Registers}
    {command : Command p} {result : Run (List Value)} {tree : CallTree}
    (he : FramedExec code h regs command result tree) :
    Valid h → RegistersBound h.length regs → tree.Bounded result.heap.length 16 := by
  induction he with
  | ret => intro _ _; trivial
  | @copy h regs dst src next result tree rest ih =>
      intro hh hr
      exact ⟨trivial, ih hh (update_bounded hr dst (src.bounded hr (null_allocated hh)))⟩
  | @allocate h regs dst expr c next result tree evaluated rest ih =>
      intro hh hr
      have ha := safe_allocate h hh c (CellExpr.fits hr (null_allocated hh) evaluated)
      have hp : (Value.pointer h.length).Bounded (h ++ [c]).length := by
        simp [Value.Bounded, Value.word, Word.Bounded]
      exact ⟨trivial, ih ha.2.1 (update_bounded (registersBound_mono hr ha.1.length_le) dst hp)⟩
  | @load h regs address addr c first second bit branches result tree evaluated loaded rest ih =>
      intro hh hr
      exact ⟨trivial, ih hh (loadRegisters_bounded hr (null_allocated hh)
        (hh.2 addr c loaded) first second bit)⟩
  | branch evaluated rest ih => intro hh hr; exact ⟨trivial, ih hh hr⟩
  | @call h regs procedure arguments results next callee continuation bodyTree restTree body rest ihbody ihrest =>
      intro hh hr
      have hv := values_bounded hr (null_allocated hh) arguments
      have hi := initialRegisters_bounded (null_allocated hh) hv
      obtain ⟨hc, hcv⟩ := body.erase.safe hh hi
      have hrest := bindResults_bounded (rs := results) (registersBound_mono hr hc.1.length_le) hcv
      have hs := (rest.erase.safe hc.2.1 hrest).1
      refine ⟨trivial, ⟨?_, ihrest hc.2.1 hrest⟩⟩
      exact ⟨by simp, savedRegisters_bounded (registersBound_mono hr
        (hc.1.trans hs.1).length_le), callTree_bounded_mono (ihbody hh hi) hs.1.length_le⟩

/-- The real interpreter frames satisfy the trace, width, address, and call
count invariants required by the symbol-stack cost theorem. -/
theorem FramedExec.stackRealizes {p : ℕ} {code : Code p} {h : Heap} {regs : Registers}
    {command : Command p} {result : Run (List Value)} {tree : CallTree}
    (he : FramedExec code h regs command result tree)
    (hh : Valid h) (hr : RegistersBound h.length regs) :
    StackRealizes result.heap.length 16 result.trace tree :=
  ⟨he.memoryTrace, he.bounded hh hr, he.calls_le⟩

/-- Concrete framed execution is a physical symbol-stack execution restoring
exactly the supplied caller stack. -/
theorem FramedExec.stack_exec {p : ℕ} {code : Code p} {h : Heap} {regs : Registers}
    {command : Command p} {result : Run (List Value)} {tree : CallTree}
    (he : FramedExec code h regs command result tree) (stack : SymbolStack) :
    StackExec h stack tree.compile result.heap stack := by
  apply tree.exec
  rw [he.memoryTrace]
  exact he.erase.heap_exec

/-- Heap accesses and all actual sixteen-word caller saves/restores fit one
logarithmic overhead per interpreted event. -/
theorem FramedExec.bitCost_le {p : ℕ} {code : Code p} {h : Heap} {regs : Registers}
    {command : Command p} {result : Run (List Value)} {tree : CallTree}
    (he : FramedExec code h regs command result tree)
    (hh : Valid h) (hr : RegistersBound h.length regs) :
    stackBitCost tree.compile ≤ result.trace.length *
      (102 + 35 * (h.length + result.trace.length).size) := by
  have hs := (he.erase.safe hh hr).1
  have ht : TraceBound tree.memoryTrace result.heap.length := by
    rw [he.memoryTrace]
    exact hs.2.2.1
  have hc : tree.calls ≤ tree.memoryTrace.length := by
    rw [he.memoryTrace]
    exact he.calls_le
  have hb := tree.bitCost_le result.heap.length 16 ht (he.bounded hh hr) hc
  rw [he.memoryTrace] at hb
  have hsize := Nat.size_le_size hs.2.2.2
  nlinarith [Nat.mul_le_mul_left result.trace.length (Nat.mul_le_mul_left 35 hsize)]

/-- Every interpreted result admits its actual framed execution and concrete
bit-stack simulation with a logarithmic address-width overhead. -/
theorem Exec.exists_stack_execution {p : ℕ} {code : Code p} {h : Heap} {regs : Registers}
    {command : Command p} {result : Run (List Value)}
    (he : Exec code h regs command result) (hh : Valid h) (hr : RegistersBound h.length regs) :
    ∃ tree, FramedExec code h regs command result tree ∧
      StackRealizes result.heap.length 16 result.trace tree ∧
      (∀ stack, StackExec h stack tree.compile result.heap stack) ∧
      stackBitCost tree.compile ≤ result.trace.length *
        (102 + 35 * (h.length + result.trace.length).size) := by
  obtain ⟨tree, hf⟩ := he.framed
  exact ⟨tree, hf, hf.stackRealizes hh hr, hf.stack_exec, hf.bitCost_le hh hr⟩

/-- An upper bound on interpreted events also bounds the full concrete
stack simulation, including the logarithmic width of all allocated addresses. -/
theorem FramedExec.bitCost_le_of_length_le {p : ℕ} {code : Code p} {h : Heap} {regs : Registers}
    {command : Command p} {result : Run (List Value)} {tree : CallTree} {steps : ℕ}
    (he : FramedExec code h regs command result tree)
    (hh : Valid h) (hr : RegistersBound h.length regs) (hlen : result.trace.length ≤ steps) :
    stackBitCost tree.compile ≤ steps * (102 + 35 * (h.length + steps).size) := by
  apply le_trans (he.bitCost_le hh hr)
  apply Nat.mul_le_mul hlen
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 35
    (Nat.size_le_size (Nat.add_le_add_left hlen h.length))) 102

/-- Entry-point executions have the same concrete stack simulation from
bounded input words; clients need not reason about initial register filling. -/
theorem Executes.exists_stack_execution {p : ℕ} {code : Code p} {entry : Fin p}
    {h : Heap} {arguments : List Value} {result : Run (List Value)} {steps : ℕ}
    (he : Executes code entry h arguments result) (hh : Valid h)
    (ha : ValuesBound h.length arguments) (hlen : result.trace.length ≤ steps) :
    ∃ tree, FramedExec code h (initialRegisters arguments) (code entry) result tree ∧
      StackRealizes result.heap.length 16 result.trace tree ∧
      (∀ stack, StackExec h stack tree.compile result.heap stack) ∧
      stackBitCost tree.compile ≤ steps * (102 + 35 * (h.length + steps).size) := by
  have hr := initialRegisters_bounded (null_allocated hh) ha
  obtain ⟨tree, hf⟩ := he.framed
  exact ⟨tree, hf, hf.stackRealizes hh hr, hf.stack_exec, hf.bitCost_le_of_length_le hh hr hlen⟩

end WeightedMIS.RegisterMachine
