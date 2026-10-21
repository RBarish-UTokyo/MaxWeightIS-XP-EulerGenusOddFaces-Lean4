module

public import WeightedMIS.ResidualWords
public import WeightedMIS.RegisterMembership

/-! # Ordered endpoint membership in stored residual-arc lists -/

@[expose] public section

namespace WeightedMIS.RegisterArcMembership

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch WeightedMIS.ResidualWords

variable {p : ℕ}

def found {n b : ℕ} (source target : Bits n) (arcs : List (Arc n b)) : Bool :=
  arcs.any (fun a => decide (a.source.value = source.value ∧ a.target.value = target.value))

@[simp] theorem found_iff {n b : ℕ} (source target : Bits n) (arcs : List (Arc n b)) :
    found source target arcs = true ↔
      ∃ a ∈ arcs, a.source.value = source.value ∧ a.target.value = target.value := by
  simp [found]

def recurseBody (self : Fin p) : Command p :=
  .call self [.register 0, .register 1, .register 4] [14] (.ret [.register 14])

def targetBody (self cmp : Fin p) : Command p :=
  .call cmp [.register 1, .register 9] [12, 13]
    (.branch (.register 13) (.ret [.flag true]) (recurseBody self))

def sourceBody (self cmp : Fin p) : Command p :=
  .call cmp [.register 0, .register 6] [12, 13]
    (.branch (.register 13) (targetBody self cmp) (recurseBody self))

def recordBody (self cmp : Fin p) : Command p :=
  .load (.register 3) 6 7 8 { CompiledTrie.failCases with
    pair := .load (.register 7) 9 10 11 { CompiledTrie.failCases with
      pair := sourceBody self cmp } }

/-- Arguments are source, target, and the stored list; capacity is ignored. -/
def membershipBody (self cmp : Fin p) : Command p :=
  .load (.register 2) 3 4 5 { CompiledTrie.failCases with
    nil := .ret [.flag false]
    cons := recordBody self cmp }

def budget (width length : ℕ) : ℕ := (72 * width + 120) * length + 13

theorem branchFlag (code : Code p) (h out : Heap) (regs : Registers)
    (test : Atom) (b yesFlag noFlag : Bool) (yes no : Command p) (cost : ℕ)
    (ht : test.eval regs = .flag b)
    (hy : Within code h regs yes [.flag yesFlag] out cost)
    (hn : Within code h regs no [.flag noFlag] out cost) :
    Within code h regs (.branch test yes no) [.flag (if b then yesFlag else noFlag)] out
      (3 + cost) := by
  cases b
  · exact Within.branch ht hn
  · exact Within.branch ht hy

theorem recurse_within (code : Code p) (self : Fin p) (h : Heap) (regs : Registers)
    (sp tp tail : Ptr) (result : Bool) (cost : ℕ)
    (hs : regs 0 = .pointer sp) (ht : regs 1 = .pointer tp) (hl : regs 4 = .pointer tail)
    (child : Within code h (initialRegisters [.pointer sp, .pointer tp, .pointer tail])
      (code self) [.flag result] h cost) :
    Within code h regs (recurseBody self) [.flag result] h (cost + 10) := by
  have args : values regs [.register 0, .register 1, .register 4] =
      [.pointer sp, .pointer tp, .pointer tail] := by simp [values, Atom.eval, hs, ht, hl]
  have last : Within code h (bindResults regs [14] [.flag result])
      (.ret [.register 14]) [.flag result] h 3 := by
    simpa [values, Atom.eval, bindResults] using
      Within.ret code h (bindResults regs [14] [.flag result]) [.register 14]
  have call := Within.call (procedure := self) (regs := regs)
    (arguments := [.register 0, .register 1, .register 4]) (results := [14])
    (by simpa only [args] using child) last
  simpa [recurseBody, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using call

theorem compiled (code : Code p) (self cmp : Fin p)
    (hself : code self = membershipBody self cmp)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    {n b : ℕ} {h : Heap} {sp tp lp : Ptr} {source target : Bits n} {arcs : List (Arc n b)}
    (hs : BitsAt h sp source) (ht : BitsAt h tp target) (ha : TableAt h lp arcs) :
    Within code h (initialRegisters [.pointer sp, .pointer tp, .pointer lp]) (code self)
      [.flag (found source target arcs)] h (budget n arcs.length) := by
  induction arcs generalizing lp with
  | nil =>
    have cell := TableAt.nil_iff.mp ha
    rw [hself]
    let regs := initialRegisters [Value.pointer sp, .pointer tp, .pointer lp]
    have last := Within.ret code h (loadRegisters regs 3 4 5 .nil) [.flag false]
    have load := Within.load (address := .register 2) (first := 3) (second := 4) (bit := 5)
      (branches := { CompiledTrie.failCases with
        nil := .ret [.flag false], cons := recordBody self cmp })
      (by simp [regs, Atom.eval, initialRegisters]) cell last
    simpa [membershipBody, found, budget, values, Atom.eval] using load
  | cons arc arcs ih =>
    obtain ⟨head, tail, cell, hrecord, htail⟩ := TableAt.cons_iff.mp ha
    obtain ⟨asp, pairTail, atp, cap, hfirst, hsecond, has, hat, _⟩ := hrecord
    have child := ih htail
    let regs := initialRegisters [Value.pointer sp, .pointer tp, .pointer lp]
    let scanned := loadRegisters regs 3 4 5 (.cons head tail)
    let first := loadRegisters scanned 6 7 8 (.pair asp pairTail)
    let second := loadRegisters first 9 10 11 (.pair atp cap)
    let sourceOrder := (Bits.compare source arc.source).1
    let targetOrder := (Bits.compare target arc.target).1
    let sourceCompared := bindResults second [12, 13] (RegisterComparator.flags sourceOrder)
    let targetCompared := bindResults sourceCompared [12, 13] (RegisterComparator.flags targetOrder)
    let restCost := budget n arcs.length + 10
    have recurseS : Within code h sourceCompared (recurseBody self)
        [.flag (found source target arcs)] h restCost :=
      recurse_within code self h sourceCompared sp tp tail _ _
        (by simp [sourceCompared, second, first, scanned, regs, bindResults,
          loadRegisters, decoded, initialRegisters, RegisterComparator.flags])
        (by simp [sourceCompared, second, first, scanned, regs, bindResults,
          loadRegisters, decoded, initialRegisters, RegisterComparator.flags])
        (by simp [sourceCompared, second, first, scanned, regs, bindResults,
          loadRegisters, decoded, initialRegisters, RegisterComparator.flags]) child
    have recurseT : Within code h targetCompared (recurseBody self)
        [.flag (found source target arcs)] h restCost :=
      recurse_within code self h targetCompared sp tp tail _ _
        (by simp [targetCompared, sourceCompared, second, first, scanned, regs, bindResults,
          loadRegisters, decoded, initialRegisters, RegisterComparator.flags])
        (by simp [targetCompared, sourceCompared, second, first, scanned, regs, bindResults,
          loadRegisters, decoded, initialRegisters, RegisterComparator.flags])
        (by simp [targetCompared, sourceCompared, second, first, scanned, regs, bindResults,
          loadRegisters, decoded, initialRegisters, RegisterComparator.flags]) child
    have terminal : Within code h targetCompared (.ret [.flag true]) [.flag true] h restCost :=
      (Within.ret code h targetCompared [.flag true]).mono (by simp [restCost])
    have tbranch := branchFlag code h h targetCompared (.register 13)
      (decide (targetOrder = .eq)) true (found source target arcs)
      (.ret [.flag true]) (recurseBody self) restCost
      (by simp [targetCompared, bindResults, Atom.eval, RegisterComparator.flags]) terminal recurseT
    have targs : values sourceCompared [.register 1, .register 9] = [.pointer tp, .pointer atp] := by
      simp [sourceCompared, second, first, scanned, regs, bindResults, loadRegisters, decoded,
        initialRegisters, values, Atom.eval, RegisterComparator.flags]
    have tc := RegisterComparator.compiled code cmp hcmp ht hat
    have tcall := Within.call (procedure := cmp) (regs := sourceCompared)
      (arguments := [.register 1, .register 9]) (results := [12, 13])
      (by simpa only [targs] using tc) tbranch
    have tbound : Within code h sourceCompared (targetBody self cmp)
        [.flag (if decide (targetOrder = .eq) then true else found source target arcs)] h
        (restCost + 36 * n + 33) := by
      convert tcall using 1 <;> simp [targetBody] <;> omega
    have sbranch := branchFlag code h h sourceCompared (.register 13)
      (decide (sourceOrder = .eq))
      (if decide (targetOrder = .eq) then true else found source target arcs)
      (found source target arcs) (targetBody self cmp) (recurseBody self)
      (restCost + 36 * n + 33)
      (by simp [sourceCompared, bindResults, Atom.eval, RegisterComparator.flags])
      tbound (recurseS.mono (by omega))
    have sargs : values second [.register 0, .register 6] = [.pointer sp, .pointer asp] := by
      simp [second, first, scanned, regs, loadRegisters, decoded, initialRegisters, values, Atom.eval]
    have sc := RegisterComparator.compiled code cmp hcmp hs has
    have scall := Within.call (procedure := cmp) (regs := second)
      (arguments := [.register 0, .register 6]) (results := [12, 13])
      (by simpa only [sargs] using sc) sbranch
    have loadSecond := Within.load (address := .register 7) (first := 9) (second := 10) (bit := 11)
      (branches := { CompiledTrie.failCases with pair := sourceBody self cmp })
      (by simp [first, loadRegisters, decoded, Atom.eval]) hsecond scall
    have loadFirst := Within.load (address := .register 3) (first := 6) (second := 7) (bit := 8)
      (branches := { CompiledTrie.failCases with
        pair := .load (.register 7) 9 10 11 { CompiledTrie.failCases with pair := sourceBody self cmp } })
      (by simp [scanned, loadRegisters, decoded, Atom.eval]) hfirst loadSecond
    have loadList := Within.load (address := .register 2) (first := 3) (second := 4) (bit := 5)
      (branches := { CompiledTrie.failCases with
        nil := .ret [.flag false], cons := recordBody self cmp })
      (by simp [regs, Atom.eval, initialRegisters]) cell loadFirst
    have hout : (if decide (sourceOrder = .eq) then
        (if decide (targetOrder = .eq) then true else found source target arcs)
        else found source target arcs) = found source target (arc :: arcs) := by
      have hcs := (Bits.compare_correct source arc.source).2.1
      have hct := (Bits.compare_correct target arc.target).2.1
      have hsf : decide (sourceOrder = .eq) = decide (arc.source.value = source.value) := by
        simp only [sourceOrder, hcs, eq_comm]
      have htf : decide (targetOrder = .eq) = decide (arc.target.value = target.value) := by
        simp only [targetOrder, hct, eq_comm]
      rw [hsf, htf]
      simp only [found, List.any_cons, Bool.decide_and]
      cases decide (arc.source.value = source.value) <;>
        cases decide (arc.target.value = target.value) <;> rfl
    rw [hout] at loadList
    rw [hself]
    exact loadList.mono (by simp [restCost, budget, List.length_cons, Nat.mul_add]; omega)

theorem budget_le (width length : ℕ) : budget width length ≤
    200 * (width + 1) * (length + 1) := by
  have hfactor : 72 * width + 120 ≤ 200 * (width + 1) := by omega
  have hconstant : 13 ≤ 200 * (width + 1) := by omega
  calc
    budget width length ≤ 200 * (width + 1) * length + 200 * (width + 1) :=
      Nat.add_le_add (Nat.mul_le_mul_right length hfactor) hconstant
    _ = 200 * (width + 1) * (length + 1) := (Nat.mul_succ _ _).symm

end WeightedMIS.RegisterArcMembership
