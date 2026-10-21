module

public import WeightedMIS.PointerExecution

/-!
# Explicit bit-stack simulation of recursive pointer calls

A call saves concrete register words on a symbol stack and restores exactly
the same symbols after the callee returns. Words are copied one bit at a time,
with delimiters. Stack operations use the current tape head, not an unbounded
natural-number stack index. `CallTree` is a finite evaluation derivation, not a
runtime syntax tree or fuel counter. Heap events retain their specified
logarithmic-cost random-access semantics; stack events are individual symbol
reads/writes. Calls and returns each also execute one finite-control tick.
-/

@[expose] public section

namespace WeightedMIS.PointerMemory

def Word.Bounded (bound : ℕ) : Word → Prop
  | .pointer p => p < bound
  | .flag _ => True

theorem Word.symbols_length_le (bound : ℕ) (w : Word) (hw : w.Bounded bound) :
    w.symbols.length ≤ bound.size + 3 := by
  cases w with
  | pointer p =>
    have hp := Nat.size_le_size (Nat.le_of_lt hw)
    simp only [symbols, List.length_cons, List.length_append, List.length_map,
      List.length_nil, Nat.size_eq_bits_len]
    omega
  | flag b => simp [symbols]

theorem frameSymbols_length_le (frame : List Word) (bound : ℕ)
    (h : ∀ w ∈ frame, w.Bounded bound) :
    (frameSymbols frame).length ≤ frame.length * (bound.size + 3) := by
  induction frame with
  | nil => simp [frameSymbols]
  | cons w ws ih =>
    have hw := w.symbols_length_le bound (h w List.mem_cons_self)
    have ht := ih (fun v hv => h v (List.mem_cons_of_mem w hv))
    simp only [frameSymbols, List.flatMap_cons, List.length_append, List.length_cons] at *
    nlinarith

abbrev SymbolStack := List (Option Bool)

inductive StackStep : Heap → SymbolStack → StackInstruction → Heap → SymbolStack → Prop
  | heap {h h' : Heap} {e : Event} (stack : SymbolStack) (step : HeapStep h e h') :
      StackStep h stack (.heap e) h' stack
  | push (h : Heap) (stack : SymbolStack) (s : Option Bool) :
      StackStep h stack (.push s) h (s :: stack)
  | pop (h : Heap) (stack : SymbolStack) (s : Option Bool) :
      StackStep h (s :: stack) (.pop s) h stack
  | tick (h : Heap) (stack : SymbolStack) : StackStep h stack .tick h stack

inductive StackExec : Heap → SymbolStack → List StackInstruction → Heap → SymbolStack → Prop
  | nil (h : Heap) (stack : SymbolStack) : StackExec h stack [] h stack
  | cons {h h' h'' : Heap} {s s' s'' : SymbolStack} {i : StackInstruction} {is : List StackInstruction}
      (head : StackStep h s i h' s') (tail : StackExec h' s' is h'' s'') :
      StackExec h s (i :: is) h'' s''

theorem StackExec.append {h h' h'' : Heap} {s s' s'' : SymbolStack} {xs ys : List StackInstruction}
    (hx : StackExec h s xs h' s') (hy : StackExec h' s' ys h'' s'') :
    StackExec h s (xs ++ ys) h'' s'' := by
  induction hx with
  | nil => exact hy
  | cons he ht ih => exact .cons he (ih hy)

theorem HeapExec.on_stack {h h' : Heap} {events : List Event}
    (he : HeapExec h events h') (stack : SymbolStack) :
    StackExec h stack (events.map StackInstruction.heap) h' stack := by
  induction he with
  | nil => exact .nil _ _
  | cons head tail ih => exact .cons (.heap _ head) ih

theorem pushSymbols_exec (h : Heap) (stack symbols : SymbolStack) :
    StackExec h stack (symbols.reverse.map StackInstruction.push) h (symbols ++ stack) := by
  induction symbols with
  | nil => exact .nil _ _
  | cons s ss ih =>
    simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.cons_append] using ih.append (.cons (.push h (ss ++ stack) s) (.nil _ _))

theorem popSymbols_exec (h : Heap) (stack symbols : SymbolStack) :
    StackExec h (symbols ++ stack) (symbols.map StackInstruction.pop) h stack := by
  induction symbols with
  | nil => exact .nil _ _
  | cons s ss ih => exact .cons (.pop _ _ _) ih

def CallTree.calls : CallTree → ℕ
  | .code _ => 0
  | .seq a b => a.calls + b.calls
  | .call _ body => body.calls + 1

def CallTree.savedSymbols : CallTree → ℕ
  | .code _ => 0
  | .seq a b => a.savedSymbols + b.savedSymbols
  | .call frame body => body.savedSymbols + (frameSymbols frame).length

/-- An operational simulation, not a cost assignment: the expanded sequence
executes on the heap and physical symbol stack, and restores the caller stack. -/
theorem CallTree.exec (tree : CallTree) {h h' : Heap}
    (he : HeapExec h tree.memoryTrace h') (stack : SymbolStack) :
    StackExec h stack tree.compile h' stack := by
  induction tree generalizing h h' stack with
  | code events => exact he.on_stack stack
  | seq a b iha ihb =>
    obtain ⟨mid, ha, hb⟩ := HeapExec.append_iff.mp he
    exact (iha ha stack).append (ihb hb stack)
  | call frame body ih =>
    have first := (StackExec.cons (.tick h stack) (.nil h stack)).append
      (pushSymbols_exec h stack (frameSymbols frame))
    have middle := ih he (frameSymbols frame ++ stack)
    have last := (popSymbols_exec h' stack (frameSymbols frame)).append
      (.cons (.tick h' stack) (.nil h' stack))
    simpa only [CallTree.compile, List.append_assoc] using (first.append middle).append last

@[simp] theorem stackBitCost_append (xs ys : List StackInstruction) :
    stackBitCost (xs ++ ys) = stackBitCost xs + stackBitCost ys := by
  simp [stackBitCost]

theorem CallTree.compile_cost (tree : CallTree) :
    stackBitCost tree.compile = bitCost tree.memoryTrace + 2 * tree.savedSymbols + 2 * tree.calls := by
  induction tree with
  | code events => simp [CallTree.compile, CallTree.memoryTrace, CallTree.savedSymbols,
      CallTree.calls, stackBitCost, bitCost, List.map_map, Function.comp_def, StackInstruction.bitCost]
  | seq a b iha ihb =>
    simp only [CallTree.compile, stackBitCost_append, CallTree.memoryTrace, CallTree.savedSymbols,
      CallTree.calls, bitCost, List.map_append, List.sum_append] at *
    omega
  | call frame body ih =>
    simp only [CallTree.compile, stackBitCost_append, CallTree.memoryTrace, CallTree.savedSymbols,
      CallTree.calls]
    have hp : stackBitCost ((frameSymbols frame).reverse.map StackInstruction.push) =
        (frameSymbols frame).length := by simp [stackBitCost, List.map_map, Function.comp_def, StackInstruction.bitCost]
    have hr : stackBitCost ((frameSymbols frame).map StackInstruction.pop) =
        (frameSymbols frame).length := by simp [stackBitCost, List.map_map, Function.comp_def, StackInstruction.bitCost]
    rw [hp, hr, ih]
    simp [stackBitCost, StackInstruction.bitCost]
    omega

def CallTree.Bounded (bound slots : ℕ) : CallTree → Prop
  | .code _ => True
  | .seq a b => a.Bounded bound slots ∧ b.Bounded bound slots
  | .call frame body => frame.length ≤ slots ∧ (∀ w ∈ frame, w.Bounded bound) ∧ body.Bounded bound slots

theorem CallTree.savedSymbols_le (tree : CallTree) (bound slots : ℕ)
    (hb : tree.Bounded bound slots) :
    tree.savedSymbols ≤ tree.calls * slots * (bound.size + 3) := by
  induction tree with
  | code => simp [CallTree.savedSymbols, CallTree.calls]
  | seq a b iha ihb =>
    have ha := iha hb.1
    have hb' := ihb hb.2
    simp only [CallTree.savedSymbols, CallTree.calls]
    nlinarith
  | call frame body ih =>
    have ht := ih hb.2.2
    have hf := frameSymbols_length_le frame bound hb.2.1
    have hm := Nat.mul_le_mul_right (bound.size + 3) hb.1
    simp only [CallTree.savedSymbols, CallTree.calls]
    nlinarith

/-- The final logarithmic factor pays actual RAM accesses and actual symbol
copies of all saved/restored register words. No natural-number fuel is charged
as a unit instruction. -/
theorem CallTree.bitCost_le (tree : CallTree) (bound slots : ℕ)
    (ht : TraceBound tree.memoryTrace bound) (hb : tree.Bounded bound slots)
    (hc : tree.calls ≤ tree.memoryTrace.length) :
    stackBitCost tree.compile ≤ tree.memoryTrace.length *
      (6 + 3 * bound.size + 2 * slots * (bound.size + 3)) := by
  have hm := WeightedMIS.PointerMemory.bitCost_le tree.memoryTrace bound ht
  have hs := tree.savedSymbols_le bound slots hb
  have hscale := Nat.mul_le_mul_right (slots * (bound.size + 3)) hc
  rw [tree.compile_cost]
  nlinarith

end WeightedMIS.PointerMemory
