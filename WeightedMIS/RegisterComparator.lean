module

public import WeightedMIS.RegisterAdder
public import WeightedMIS.EfficientSearchArithmeticMore

/-!
# Closed register code for binary comparison

The finite procedure reads the two head bits and returns immediately when they
differ; equal heads cause a recursive call on the stored tails. Its two output
flags encode strictly-less and equal. No arithmetic oracle or width parameter
occurs in the command syntax.
-/

@[expose] public section

namespace WeightedMIS.RegisterComparator

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch

variable {p : ℕ}

def flags (o : Ordering) : List Value :=
  [.flag (decide (o = .lt)), .flag (decide (o = .eq))]

def terminal (o : Ordering) : Command p :=
  .ret [.flag (decide (o = .lt)), .flag (decide (o = .eq))]

def recurse (self : Fin p) : Command p :=
  .call self [.register 3, .register 5] [7, 8] (.ret [.register 7, .register 8])

def afterLoads (self : Fin p) : Command p :=
  .branch (.register 4)
    (.branch (.register 6) (recurse self) (terminal .gt))
    (.branch (.register 6) (terminal .lt) (recurse self))

def comparatorBody (self : Fin p) : Command p :=
  .load (.register 0) 3 15 4 (RegisterAdder.nilBitCases
    (.load (.register 1) 5 15 6 (RegisterAdder.nilBitCases (terminal .eq) .fail))
    (.load (.register 1) 5 15 6 (RegisterAdder.nilBitCases .fail (afterLoads self))))

theorem terminal_within (code : Code p) (h : Heap) (regs : Registers) (o : Ordering) :
    Within code h regs (terminal o) (flags o) h 5 := by
  simpa [terminal, flags, values, Atom.eval] using
    Within.ret code h regs [.flag (decide (o = .lt)), .flag (decide (o = .eq))]

theorem recurse_within (code : Code p) (self : Fin p) (h : Heap) (regs : Registers)
    (ap bp : Ptr) (o : Ordering) (budget : ℕ)
    (ha : regs 3 = .pointer ap) (hb : regs 5 = .pointer bp)
    (child : Within code h (initialRegisters [.pointer ap, .pointer bp]) (code self)
      (flags o) h budget) :
    Within code h regs (recurse self) (flags o) h (budget + 10) := by
  have hargs : values regs [.register 3, .register 5] = [.pointer ap, .pointer bp] := by
    simp [values, Atom.eval, ha, hb]
  have last : Within code h (bindResults regs [7, 8] (flags o))
      (.ret [.register 7, .register 8]) (flags o) h 5 := by
    simpa [flags, values, Atom.eval, bindResults] using
      Within.ret code h (bindResults regs [7, 8] (flags o)) [.register 7, .register 8]
  have call := Within.call (procedure := self) (arguments := [.register 3, .register 5])
    (results := [7, 8]) (regs := regs) (returned := flags o)
    (by simpa only [hargs] using child) last
  simpa [recurse, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using call

theorem afterLoads_within (code : Code p) (self : Fin p) (h : Heap) (regs : Registers)
    (a b : Bool) (tail : Ordering) (budget : ℕ) (hbudget : 5 ≤ budget)
    (ha : regs 4 = .flag a) (hb : regs 6 = .flag b)
    (child : Within code h regs (recurse self) (flags tail) h budget) :
    Within code h regs (afterLoads self)
      (flags (if a = b then tail else if a then .gt else .lt)) h (budget + 6) := by
  have lt := (terminal_within code h regs .lt).mono hbudget
  have gt := (terminal_within code h regs .gt).mono hbudget
  cases a <;> cases b
  · have h2 := Within.branch (test := .register 6)
      (yes := terminal .lt) (no := recurse self)
      (by simpa [Atom.eval] using hb) child
    have h1 := Within.branch (test := .register 4)
      (yes := .branch (.register 6) (recurse self) (terminal .gt))
      (no := .branch (.register 6) (terminal .lt) (recurse self))
      (by simpa [Atom.eval] using ha) h2
    simpa [afterLoads, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h1
  · have h2 := Within.branch (test := .register 6)
      (yes := terminal .lt) (no := recurse self)
      (by simpa [Atom.eval] using hb) lt
    have h1 := Within.branch (test := .register 4)
      (yes := .branch (.register 6) (recurse self) (terminal .gt))
      (no := .branch (.register 6) (terminal .lt) (recurse self))
      (by simpa [Atom.eval] using ha) h2
    simpa [afterLoads, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h1
  · have h2 := Within.branch (test := .register 6)
      (yes := recurse self) (no := terminal .gt)
      (by simpa [Atom.eval] using hb) gt
    have h1 := Within.branch (test := .register 4)
      (yes := .branch (.register 6) (recurse self) (terminal .gt))
      (no := .branch (.register 6) (terminal .lt) (recurse self))
      (by simpa [Atom.eval] using ha) h2
    simpa [afterLoads, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h1
  · have h2 := Within.branch (test := .register 6)
      (yes := recurse self) (no := terminal .gt)
      (by simpa [Atom.eval] using hb) child
    have h1 := Within.branch (test := .register 4)
      (yes := .branch (.register 6) (recurse self) (terminal .gt))
      (no := .branch (.register 6) (terminal .lt) (recurse self))
      (by simpa [Atom.eval] using ha) h2
    simpa [afterLoads, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h1

/-- The closed procedure terminates on represented equal-width words, returns
the exact Boolean comparison result, and performs linearly many events. -/
theorem compiled (code : Code p) (self : Fin p) (body : code self = comparatorBody self)
    {n : ℕ} {h : Heap} {ap bp : Ptr} {a b : Bits n}
    (ha : BitsAt h ap a) (hb : BitsAt h bp b) :
    Within code h (initialRegisters [.pointer ap, .pointer bp]) (code self)
      (flags (Bits.compare a b).1) h (36 * n + 25) := by
  induction a generalizing ap bp with
  | nil =>
      cases b
      cases ha with
      | nil hac =>
        cases hb with
        | nil hbc =>
          rw [body]
          let regs := initialRegisters [Value.pointer ap, .pointer bp]
          let first := loadRegisters regs 3 15 4 .nil
          let second := loadRegisters first 5 15 6 .nil
          have last := terminal_within code h second .eq
          have loadB := Within.load (address := .register 1) (first := 5) (second := 15) (bit := 6)
            (branches := RegisterAdder.nilBitCases (terminal .eq) .fail)
            (by simp [Atom.eval, first, regs, loadRegisters, decoded, initialRegisters]) hbc last
          have loadA := Within.load (address := .register 0) (first := 3) (second := 15) (bit := 4)
            (branches := RegisterAdder.nilBitCases
              (.load (.register 1) 5 15 6 (RegisterAdder.nilBitCases (terminal .eq) .fail))
              (.load (.register 1) 5 15 6 (RegisterAdder.nilBitCases .fail (afterLoads self))))
            (by simp [Atom.eval, regs, initialRegisters]) hac loadB
          simpa [comparatorBody, Bits.compare] using loadA
  | @cons n av as ih =>
      cases b with
      | cons bv bs =>
        cases ha with
        | @cons _ atail _ _ _ hac hat =>
          cases hb with
          | @cons _ btail _ _ _ hbc hbt =>
            have child := ih hat hbt
            rw [body]
            let regs := initialRegisters [Value.pointer ap, .pointer bp]
            let first := loadRegisters regs 3 15 4 (.bit av atail)
            let second := loadRegisters first 5 15 6 (.bit bv btail)
            have ha3 : second 3 = .pointer atail := by
              simp [second, first, regs, loadRegisters, decoded]
            have hb5 : second 5 = .pointer btail := by
              simp [second, first, regs, loadRegisters, decoded]
            have ha4 : second 4 = .flag av := by
              simp [second, first, regs, loadRegisters, decoded]
            have hb6 : second 6 = .flag bv := by
              simp [second, first, regs, loadRegisters, decoded]
            have hrec :=  recurse_within code self h second atail btail (Bits.compare as bs).1
              (36 * n + 25) ha3 hb5 child
            have last := afterLoads_within code self h second av bv (Bits.compare as bs).1
              (36 * n + 25 + 10) (by omega) ha4 hb6 hrec
            have loadB := Within.load (address := .register 1) (first := 5) (second := 15) (bit := 6)
              (branches := RegisterAdder.nilBitCases .fail (afterLoads self))
              (by simp [Atom.eval, first, regs, loadRegisters, decoded, initialRegisters]) hbc last
            have loadA := Within.load (address := .register 0) (first := 3) (second := 15) (bit := 4)
              (branches := RegisterAdder.nilBitCases
                (.load (.register 1) 5 15 6 (RegisterAdder.nilBitCases (terminal .eq) .fail))
                (.load (.register 1) 5 15 6 (RegisterAdder.nilBitCases .fail (afterLoads self))))
              (by simp [Atom.eval, regs, initialRegisters]) hac loadB
            have hout : (Bits.compare (.cons av as) (.cons bv bs)).1 =
                (if av = bv then (Bits.compare as bs).1 else if av then .gt else .lt) := by
              by_cases heq : av = bv <;> simp [Bits.compare, heq]
            rw [hout]
            exact loadA.mono (by omega)

end WeightedMIS.RegisterComparator
