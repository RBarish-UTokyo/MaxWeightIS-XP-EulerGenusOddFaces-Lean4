module

public import WeightedMIS.RegisterPotentialStep
public import WeightedMIS.ResidualWords
public import WeightedMIS.CompiledTrie

/-!
# Integer-potential propagation along shared reverse routes

Routes use the existing represented arc lists. Their capacity word stores the
original edge's nonnegative slack count. Recursion follows the predecessor tail
before applying the head edge, preserving the reverse-list route convention.
-/

@[expose] public section

namespace WeightedMIS.RegisterPotentialRoute

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch WeightedMIS.ResidualWords
open WeightedMIS.RegisterPotentialStep

variable {v b : ℕ}

def recover (one : Bits b) : List (Arc v b) → Word b → Word b
  | [], initial => initial
  | arc :: rest, initial => step one arc.capacity (recover one rest initial)

def propagate : List (Arc v b) → ℤ → ℤ
  | [], initial => initial
  | arc :: rest, initial => 1 - (arc.capacity.value : ℤ) - propagate rest initial

def mass (arcs : List (Arc v b)) : ℕ := arcs.length + (arcs.map (fun a => a.capacity.value)).sum

@[simp] theorem mass_nil : mass ([] : List (Arc v b)) = 0 := rfl
@[simp] theorem mass_cons (a : Arc v b) (rest : List (Arc v b)) :
    mass (a :: rest) = 1 + a.capacity.value + mass rest := by
  simp [mass]; omega

theorem recover_correct (one : Bits b) (arcs : List (Arc v b)) (initial : Word b)
    (hone : one.value = 1) (hwidth : initial.2.value + mass arcs < 2 ^ b) :
    value (recover one arcs initial) = propagate arcs (value initial) ∧
      (recover one arcs initial).2.value ≤ initial.2.value + mass arcs := by
  induction arcs with
  | nil => simp [recover, propagate]
  | cons a rest ih =>
    have hrest : initial.2.value + mass rest < 2 ^ b := by
      rw [mass_cons] at hwidth; omega
    obtain ⟨hvalue, hmagnitude⟩ := ih hrest
    have hfit : one.value + a.capacity.value + (recover one rest initial).2.value < 2 ^ b := by
      rw [mass_cons] at hwidth
      rw [hone]
      omega
    have hstep := step_value one a.capacity (recover one rest initial) hone hfit
    constructor
    · simpa only [recover, propagate, hvalue] using hstep
    · change (step one a.capacity (recover one rest initial)).2.value ≤ _
      rw [← value_natAbs, hstep]
      have hsub := Int.natAbs_sub_le (1 - (a.capacity.value : ℤ)) (value (recover one rest initial))
      have honecount := Int.natAbs_sub_le (1 : ℤ) (a.capacity.value : ℤ)
      rw [value_natAbs] at hsub
      simp only [Int.natAbs_one, Int.natAbs_natCast] at honecount
      rw [mass_cons]
      omega

variable {p : ℕ}

def stepBody (stepId : Fin p) : Command p :=
  .call stepId [.register 1, .register 9, .register 10, .register 11] [12, 13]
    (.ret [.register 12, .register 13])

def recurseBody (self stepId : Fin p) : Command p :=
  .call self [.register 5, .register 1, .register 2, .register 3] [10, 11] (stepBody stepId)

def recordBody (self stepId : Fin p) : Command p :=
  .load (.register 4) 6 7 15 { CompiledTrie.failCases with
    pair := .load (.register 7) 8 9 15 { CompiledTrie.failCases with
      pair := recurseBody self stepId } }

/-- Input: reverse route, one word, initial sign, initial magnitude.
Output: terminal sign and magnitude. -/
def routeBody (self stepId : Fin p) : Command p :=
  .load (.register 0) 4 5 15 { CompiledTrie.failCases with
    nil := .ret [.register 2, .register 3]
    cons := recordBody self stepId }

def budget (width length : ℕ) : ℕ := 400 * (width + 1) * length + 15

theorem compiled (code : Code p) (self stepId signedAdd cmp sub complement add : Fin p)
    (hself : code self = routeBody self stepId)
    (hstep : code stepId = RegisterPotentialStep.stepBody signedAdd)
    (hsigned : code signedAdd = RegisterSignedAdd.signedAddBody add cmp sub)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    (hsub : code sub = RegisterSubtractor.subtractorBody complement add)
    (hcomp : code complement = RegisterComplement.complementBody complement)
    (hadd : code add = RegisterAdder.adderBody add)
    {h : Heap} (hh : Valid h) {lp op ap : Ptr}
    {arcs : List (Arc v b)} {one : Bits b} {initial : Word b}
    (hl : TableAt h lp arcs) (ho : BitsAt h op one) (ha : BitsAt h ap initial.2) :
    ∃ out result, Extends h out ∧ Valid out ∧ BitsAt out result (recover one arcs initial).2 ∧
      Within code h (initialRegisters [.pointer lp, .pointer op, .flag initial.1, .pointer ap])
        (code self) [.flag (recover one arcs initial).1, .pointer result] out (budget b arcs.length) := by
  induction arcs generalizing h lp with
  | nil =>
    let regs := initialRegisters [Value.pointer lp, .pointer op, .flag initial.1, .pointer ap]
    have cell := TableAt.nil_iff.mp hl
    have last : Within code h (loadRegisters regs 4 5 15 .nil)
        (.ret [.register 2, .register 3]) [.flag initial.1, .pointer ap] h 5 := by
      simpa [regs, initialRegisters, loadRegisters, decoded, values, Atom.eval] using
        Within.ret code h (loadRegisters regs 4 5 15 .nil) [.register 2, .register 3]
    have load := Within.load (regs := regs) (address := .register 0)
      (first := 4) (second := 5) (bit := 15)
      (branches := { CompiledTrie.failCases with
        nil := .ret [.register 2, .register 3]
        cons := recordBody self stepId })
      (by simp [regs, initialRegisters, Atom.eval]) cell last
    refine ⟨h, ap, .refl h, hh, ha, ?_⟩
    simpa [hself, routeBody, budget, recover] using load
  | cons arc arcs ih =>
    obtain ⟨head, tail, cell, hhead, htail⟩ := TableAt.cons_iff.mp hl
    obtain ⟨sp, ep, tp, cp, record, edge, hs, ht, hc⟩ := hhead
    obtain ⟨mid, mp, hx, hv, hm, hrec⟩ := ih hh htail ho ha
    obtain ⟨out, result, hy, hw, hr, hcalc⟩ :=
      RegisterPotentialStep.compiled code signedAdd cmp sub complement add
        hsigned hcmp hsub hcomp hadd hv (ho.mono hx) (hc.mono hx) hm
    let regs := initialRegisters [Value.pointer lp, .pointer op, .flag initial.1, .pointer ap]
    let loaded := loadRegisters regs 4 5 15 (.cons head tail)
    let outer := loadRegisters loaded 6 7 15 (.pair sp ep)
    let inner := loadRegisters outer 8 9 15 (.pair tp cp)
    let recursed := bindResults inner [10, 11] [Value.flag (recover one arcs initial).1, .pointer mp]
    let done := bindResults recursed [12, 13] [Value.flag (recover one (arc :: arcs) initial).1, .pointer result]
    have last : Within code out done (.ret [.register 12, .register 13])
        [.flag (recover one (arc :: arcs) initial).1, .pointer result] out 5 := by
      simpa [done, bindResults, values, Atom.eval] using Within.ret code out done [.register 12, .register 13]
    have sargs : values recursed [.register 1, .register 9, .register 10, .register 11] =
        [.pointer op, .pointer cp, .flag (recover one arcs initial).1, .pointer mp] := by
      simp [recursed, inner, outer, loaded, regs, bindResults, loadRegisters, decoded,
        initialRegisters, values, Atom.eval]
    have calculated :=  Within.call (procedure := stepId) (regs := recursed)
      (arguments := [.register 1, .register 9, .register 10, .register 11]) (results := [12, 13])
      (by simpa only [sargs, hstep, recover] using hcalc) last
    have rargs : values inner [.register 5, .register 1, .register 2, .register 3] =
        [.pointer tail, .pointer op, .flag initial.1, .pointer ap] := by
      simp [inner, outer, loaded, regs, loadRegisters, decoded, initialRegisters, values, Atom.eval]
    have call := Within.call (procedure := self) (regs := inner)
      (arguments := [.register 5, .register 1, .register 2, .register 3]) (results := [10, 11])
      (by simpa only [rargs] using hrec) calculated
    have loadEdge := Within.load (regs := outer) (address := .register 7)
      (first := 8) (second := 9) (bit := 15)
      (branches := { CompiledTrie.failCases with pair := recurseBody self stepId })
      (by simp [outer, loadRegisters, decoded, Atom.eval]) edge call
    have loadRecord := Within.load (regs := loaded) (address := .register 4)
      (first := 6) (second := 7) (bit := 15)
      (branches := { CompiledTrie.failCases with pair := .load (.register 7) 8 9 15 { CompiledTrie.failCases with pair := recurseBody self stepId } })
      (by simp [loaded, loadRegisters, decoded, Atom.eval]) record loadEdge
    have loadList := Within.load (regs := regs) (address := .register 0)
      (first := 4) (second := 5) (bit := 15)
      (branches := { CompiledTrie.failCases with
        nil := .ret [.register 2, .register 3]
        cons := recordBody self stepId })
      (by simp [regs, initialRegisters, Atom.eval]) cell loadRecord
    refine ⟨out, result, hx.trans hy, hw, hr, ?_⟩
    rw [hself]
    exact loadList.mono (by simp [budget, Nat.mul_add, Nat.add_mul]; omega)

end WeightedMIS.RegisterPotentialRoute
