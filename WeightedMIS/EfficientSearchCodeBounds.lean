module

public import WeightedMIS.RegisterMachine

/-! # Compositional event bounds for closed register programs -/

@[expose] public section

namespace WeightedMIS.RegisterMachine

open WeightedMIS.PointerMemory

def Within {p : ℕ} (code : Code p) (heap : Heap) (regs : Registers)
    (command : Command p) (outputs : List Value) (finalHeap : Heap) (budget : ℕ) : Prop :=
  ∃ events, Exec code heap regs command ⟨outputs, finalHeap, events⟩ ∧ events.length ≤ budget

@[simp] theorem Value.moves_length (v : Value) : v.moves.length = 2 := by cases v <;> rfl

@[simp] theorem moves_length (vs : List Value) : (moves vs).length = 2 * vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [moves, List.flatMap_cons, List.length_append,
      Value.moves_length, List.length_cons] at *; omega

@[simp] theorem values_length (regs : Registers) (args : List Atom) :
    (values regs args).length = args.length := by simp [values]

@[simp] theorem decodedMoves_length (c : Cell) : (decodedMoves c).length = 6 := by
  simp [decodedMoves]

theorem Within.mono {p : ℕ} {code : Code p} {h h' : Heap} {regs : Registers}
    {cmd : Command p} {outputs : List Value} {a b : ℕ}
    (he : Within code h regs cmd outputs h' a) (hab : a ≤ b) :
    Within code h regs cmd outputs h' b := by
  obtain ⟨events, hx, hc⟩ := he
  exact ⟨events, hx, hc.trans hab⟩

theorem Within.ret {p : ℕ} (code : Code p) (h : Heap) (regs : Registers) (outputs : List Atom) :
    Within code h regs (.ret outputs) (values regs outputs) h (1 + 2 * outputs.length) := by
  refine ⟨_, Exec.ret h regs outputs, ?_⟩
  simp

theorem Within.copy {p : ℕ} {code : Code p} {h h' : Heap} {regs : Registers}
    {dst : Register} {src : Atom} {next : Command p} {outputs : List Value} {budget : ℕ}
    (rest : Within code h (Function.update regs dst (src.eval regs)) next outputs h' budget) :
    Within code h regs (.copy dst src next) outputs h' (3 + budget) := by
  obtain ⟨events, he, hc⟩ := rest
  refine ⟨_, Exec.copy he, ?_⟩
  simp only [List.length_append, List.length_cons, Value.moves_length]
  omega

theorem Within.allocate {p : ℕ} {code : Code p} {h h' : Heap} {regs : Registers}
    {dst : Register} {expr : CellExpr} {c : Cell} {next : Command p}
    {outputs : List Value} {budget : ℕ}
    (evaluated : expr.eval regs = some c)
    (rest : Within code (h ++ [c]) (Function.update regs dst (.pointer h.length)) next outputs h' budget) :
    Within code h regs (.allocate dst expr next) outputs h'
      (4 + 2 * expr.args.length + budget) := by
  obtain ⟨events, he, hc⟩ := rest
  refine ⟨_, Exec.allocate evaluated he, ?_⟩
  simp only [List.length_append, List.length_cons, List.length_nil,
    moves_length, values_length, Value.moves_length]
  omega

theorem Within.load {p : ℕ} {code : Code p} {h h' : Heap} {regs : Registers}
    {address : Atom} {pointer : Ptr} {c : Cell} {first second bit : Register}
    {branches : Cases (Command p)} {outputs : List Value} {budget : ℕ}
    (evaluated : address.eval regs = .pointer pointer) (loaded : h[pointer]? = some c)
    (rest : Within code h (loadRegisters regs first second bit c)
      (branches.select c) outputs h' budget) :
    Within code h regs (.load address first second bit branches) outputs h' (10 + budget) := by
  obtain ⟨events, he, hc⟩ := rest
  refine ⟨_, Exec.load evaluated loaded he, ?_⟩
  simp only [List.length_append, List.length_cons, List.length_nil,
    Value.moves_length, decodedMoves_length]
  omega

theorem Within.branch {p : ℕ} {code : Code p} {h h' : Heap} {regs : Registers}
    {test : Atom} {b : Bool} {yes no : Command p} {outputs : List Value} {budget : ℕ}
    (evaluated : test.eval regs = .flag b)
    (rest : Within code h regs (if b then yes else no) outputs h' budget) :
    Within code h regs (.branch test yes no) outputs h' (3 + budget) := by
  obtain ⟨events, he, hc⟩ := rest
  refine ⟨_, Exec.branch evaluated he, ?_⟩
  simp only [List.length_append, List.length_cons, Value.moves_length]
  omega

theorem Within.call {p : ℕ} {code : Code p} {h mid final : Heap} {regs : Registers}
    {procedure : Fin p} {arguments : List Atom} {results : List Register} {next : Command p}
    {returned outputs : List Value} {calleeBudget restBudget : ℕ}
    (body : Within code h (initialRegisters (values regs arguments)) (code procedure)
      returned mid calleeBudget)
    (rest : Within code mid (bindResults regs results returned) next outputs final restBudget) :
    Within code h regs (.call procedure arguments results next) outputs final
      (1 + 2 * arguments.length + calleeBudget + restBudget) := by
  obtain ⟨first, he, hc⟩ := body
  obtain ⟨last, hrest, hrc⟩ := rest
  refine ⟨_, Exec.call he hrest, ?_⟩
  simp only [sequenceRuns, List.length_append, List.length_cons,
    moves_length, values_length]
  omega

end WeightedMIS.RegisterMachine
