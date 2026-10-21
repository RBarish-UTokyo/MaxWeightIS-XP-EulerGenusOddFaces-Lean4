module

public import WeightedMIS.ExpandedWords
public import WeightedMIS.RegisterComparator
public import WeightedMIS.CompiledTrie

/-!
# Binary-key membership by a finite register program

The program scans represented words and invokes the compiled comparator.
Its result is exact value membership, and every execution preserves the heap.
-/

@[expose] public section

namespace WeightedMIS.RegisterMembership

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch WeightedMIS.ExpandedWords

variable {p : ℕ}

def found {n : ℕ} (query : Bits n) (keys : List (Bits n)) : Bool :=
  keys.any (fun key => decide (key.value = query.value))

@[simp] theorem found_iff {n : ℕ} (query : Bits n) (keys : List (Bits n)) :
    found query keys = true ↔ ∃ key ∈ keys, key.value = query.value := by
  simp [found]

def recurseBody (self : Fin p) : Command p :=
  .call self [.register 0, .register 3] [7] (.ret [.register 7])

def compareBody (self cmp : Fin p) : Command p :=
  .call cmp [.register 0, .register 2] [5, 6]
    (.branch (.register 6) (.ret [.flag true]) (recurseBody self))

/-- Arguments are the query word and the list; the sole result is a flag. -/
def membershipBody (self cmp : Fin p) : Command p :=
  .load (.register 1) 2 3 4 { CompiledTrie.failCases with
    nil := .ret [.flag false]
    cons := compareBody self cmp }

def budget (width length : ℕ) : ℕ := (36 * width + 60) * length + 13

theorem compiled (code : Code p) (self cmp : Fin p)
    (hself : code self = membershipBody self cmp)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    {n : ℕ} {h : Heap} {qp lp : Ptr} {query : Bits n} {keys : List (Bits n)}
    (hq : BitsAt h qp query) (hk : WordsAt h lp keys) :
    Within code h (initialRegisters [.pointer qp, .pointer lp]) (code self)
      [.flag (found query keys)] h (budget n keys.length) := by
  induction keys generalizing lp with
  | nil =>
    have cell := WordsAt.nil_iff.mp hk
    rw [hself]
    let regs := initialRegisters [Value.pointer qp, .pointer lp]
    have last := Within.ret code h (loadRegisters regs 2 3 4 .nil) [.flag false]
    have load := Within.load (address := .register 1) (first := 2) (second := 3) (bit := 4)
      (branches := { CompiledTrie.failCases with
        nil := .ret [.flag false], cons := compareBody self cmp })
      (by simp [regs, Atom.eval, initialRegisters]) cell last
    simpa [membershipBody, found, budget, values, Atom.eval] using load
  | cons key keys ih =>
    obtain ⟨kp, tail, cell, hkey, htail⟩ := WordsAt.cons_iff.mp hk
    have child := ih htail
    have compare := RegisterComparator.compiled code cmp hcmp hq hkey
    let regs := initialRegisters [Value.pointer qp, .pointer lp]
    let loaded := loadRegisters regs 2 3 4 (.cons kp tail)
    let compared := bindResults loaded [5, 6] (RegisterComparator.flags (Bits.compare query key).1)
    have rargs : values compared [.register 0, .register 3] = [.pointer qp, .pointer tail] := by
      simp [compared, loaded, regs, bindResults, loadRegisters, decoded,
        initialRegisters, values, Atom.eval, RegisterComparator.flags]
    have last : Within code h
        (bindResults compared [7] [.flag (found query keys)]) (.ret [.register 7])
        [.flag (found query keys)] h 3 := by
      simpa [bindResults, values, Atom.eval] using Within.ret code h
        (bindResults compared [7] [.flag (found query keys)]) [.register 7]
    have recursion := Within.call (procedure := self) (regs := compared)
      (arguments := [.register 0, .register 3]) (results := [7])
      (by simpa only [rargs] using child) last
    have eqFlag : decide ((Bits.compare query key).1 = .eq) =
        decide (key.value = query.value) := by
      simp only [(Bits.compare_correct query key).2.1, eq_comm]
    have branch : Within code h compared
        (.branch (.register 6) (.ret [.flag true]) (recurseBody self))
        [.flag (found query (key :: keys))] h (budget n keys.length + 11) := by
      by_cases heq : key.value = query.value
      · have terminal := Within.ret code h compared [.flag true]
        have hb := Within.branch (test := .register 6) (b := true)
          (yes := .ret [.flag true]) (no := recurseBody self)
          (by simp [compared, bindResults, Atom.eval, RegisterComparator.flags, eqFlag, heq])
          terminal
        have hout : found query (key :: keys) = true := by simp [found, heq]
        rw [hout]
        exact hb.mono (by simp [budget])
      · have hb := Within.branch (test := .register 6) (b := false)
          (yes := .ret [.flag true]) (no := recurseBody self)
          (by simp [compared, bindResults, Atom.eval, RegisterComparator.flags, eqFlag, heq])
          recursion
        convert hb using 1 <;> simp [recurseBody, found, heq] <;> omega
    have cargs : values loaded [.register 0, .register 2] = [.pointer qp, .pointer kp] := by
      simp [loaded, regs, loadRegisters, decoded, initialRegisters, values, Atom.eval]
    have call := Within.call (procedure := cmp) (regs := loaded)
      (arguments := [.register 0, .register 2]) (results := [5, 6])
      (by simpa only [cargs] using compare) branch
    have load := Within.load (address := .register 1) (first := 2) (second := 3) (bit := 4)
      (branches := { CompiledTrie.failCases with
        nil := .ret [.flag false], cons := compareBody self cmp })
      (by simp [regs, Atom.eval, initialRegisters]) cell call
    rw [hself]
    exact load.mono (by simp [budget, List.length_cons, Nat.mul_add]; omega)

theorem budget_le (width length : ℕ) : budget width length ≤
    100 * (width + 1) * (length + 1) := by
  have hfactor : 36 * width + 60 ≤ 100 * (width + 1) := by omega
  have hconstant : 13 ≤ 100 * (width + 1) := by omega
  calc
    budget width length ≤ 100 * (width + 1) * length + 100 * (width + 1) :=
      Nat.add_le_add (Nat.mul_le_mul_right length hfactor) hconstant
    _ = 100 * (width + 1) * (length + 1) := (Nat.mul_succ _ _).symm

end WeightedMIS.RegisterMembership
