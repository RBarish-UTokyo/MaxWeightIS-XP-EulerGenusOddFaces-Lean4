module

public import WeightedMIS.CompiledTrie
public import WeightedMIS.EfficientSearchCodeBounds

/-! # Finite sequences of pair-field reads -/

@[expose] public section

namespace WeightedMIS.RegisterPairReads

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine

abbrev Fields := Register × Register × Register

/-- A syntax macro: every list entry expands to one concrete tagged load. -/
def readPairs {p : ℕ} : List Fields → Command p → Command p
  | [], next => next
  | (address, first, second) :: rest, next =>
      .load (.register address) first second 15 { CompiledTrie.failCases with pair := readPairs rest next }

inductive Reads (h : Heap) : Registers → List Fields → Registers → Prop
  | nil (regs : Registers) : Reads h regs [] regs
  | cons {regs final : Registers} {address first second : Register} {rest : List Fields}
      {ptr left right : Ptr} (eval : regs address = .pointer ptr)
      (cell : h[ptr]? = some (.pair left right))
      (tail : Reads h (loadRegisters regs first second 15 (.pair left right)) rest final) :
      Reads h regs ((address, first, second) :: rest) final

theorem Reads.within {p : ℕ} {code : Code p} {h final : Heap} {regs loaded : Registers}
    {fields : List Fields} {next : Command p} {outputs : List Value} {budget : ℕ}
    (hr : Reads h regs fields loaded) (cont : Within code h loaded next outputs final budget) :
    Within code h regs (readPairs fields next) outputs final (10 * fields.length + budget) := by
  induction hr with
  | nil regs => simpa [readPairs] using cont
  | @cons regs loaded address first second rest ptr left right eval cell tail ih =>
    have ht := Within.load (address := .register address) (first := first) (second := second) (bit := 15)
      (branches := {CompiledTrie.failCases with pair := readPairs rest next})
      (show (.register address : Atom).eval regs = .pointer ptr from eval) cell (ih cont)
    simpa [readPairs, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht

end WeightedMIS.RegisterPairReads
