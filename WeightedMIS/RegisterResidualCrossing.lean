module

public import WeightedMIS.RegisterResidualPredicate

/-! # Finite register scan finding a residual crossing arc -/

@[expose] public section

namespace WeightedMIS.RegisterResidualCrossing

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.ExpandedWords WeightedMIS.ResidualWords

variable {p : ℕ}

def crossing {n b : ℕ} (seen : List (Bits n)) (d : Bits b) (xs : List (Arc n b)) : Option (Arc n b) :=
  xs.find? (RegisterResidualPredicate.accepts seen d)

def rejected : Command p := .ret [.flag false, .null, .null]

def recurseBody (self : Fin p) : Command p :=
  .call self [.register 0, .register 4, .register 2] [8, 9, 10]
    (.ret [.register 8, .register 9, .register 10])

def afterPredicate (self : Fin p) : Command p :=
  .branch (.register 5) (.ret [.flag true, .register 6, .register 7]) (recurseBody self)

/-- Inputs: reached word list, residual table, scale word. -/
def crossingBody (self predicate : Fin p) : Command p :=
  .load (.register 1) 3 4 15 { CompiledTrie.failCases with
    nil := rejected
    cons := .call predicate [.register 0, .register 3, .register 2] [5, 6, 7] (afterPredicate self) }

def budget (n b seen entries : ℕ) : ℕ :=
  (RegisterResidualPredicate.budget n b seen + 40) * entries + 17

theorem compiled (code : Code p) (self predicate member cmp : Fin p)
    (hself : code self = crossingBody self predicate)
    (hpred : code predicate = RegisterResidualPredicate.predicateBody member cmp)
    (hm : code member = RegisterMembership.membershipBody member cmp)
    (hc : code cmp = RegisterComparator.comparatorBody cmp)
    {n b : ℕ} {h : Heap} {seen : List (Bits n)} {d : Bits b} {xs : List (Arc n b)}
    {seenp xp dp : Ptr} (hs : WordsAt h seenp seen) (hx : TableAt h xp xs) (hd : BitsAt h dp d) :
    ∃ sp tp, AnswerAt h sp tp (crossing seen d xs) ∧
      Within code h (initialRegisters [.pointer seenp, .pointer xp, .pointer dp])
        (code self) [.flag (crossing seen d xs).isSome, .pointer sp, .pointer tp]
        h (budget n b seen.length xs.length) := by
  induction xs generalizing xp with
  | nil =>
    have cell := TableAt.nil_iff.mp hx
    refine ⟨0, 0, ⟨rfl, rfl⟩, ?_⟩
    let regs := initialRegisters [Value.pointer seenp, .pointer xp, .pointer dp]
    have last := Within.ret code h (loadRegisters regs 3 4 15 .nil) [.flag false, .null, .null]
    have load := Within.load (address := .register 1) (first := 3) (second := 4) (bit := 15)
      (branches := {CompiledTrie.failCases with
        nil := rejected
        cons := .call predicate [.register 0, .register 3, .register 2] [5, 6, 7] (afterPredicate self)})
      (by simp [Atom.eval, regs, initialRegisters]) cell last
    simpa [hself, crossingBody, rejected, crossing, budget, values, Atom.eval] using load
  | cons a xs ih =>
    obtain ⟨ap, tail, cell, ha, htail⟩ := TableAt.cons_iff.mp hx
    obtain ⟨asp, atp, hsrc, htgt, predRun⟩ := RegisterResidualPredicate.compiled code member cmp hm hc hs ha hd
    obtain ⟨sp, tp, hans, child⟩ := ih htail
    let regs := initialRegisters [Value.pointer seenp, .pointer xp, .pointer dp]
    let r1 := loadRegisters regs 3 4 15 (.cons ap tail)
    let r2 := bindResults r1 [5, 6, 7]
      [.flag (RegisterResidualPredicate.accepts seen d a), .pointer asp, .pointer atp]
    have pargs : values r1 [.register 0, .register 3, .register 2] =
        [.pointer seenp, .pointer ap, .pointer dp] := by
      simp [r1, regs, loadRegisters, decoded, initialRegisters, values, Atom.eval]
    have predCall : Within code h
        (initialRegisters (values r1 [.register 0, .register 3, .register 2]))
        (code predicate) [.flag (RegisterResidualPredicate.accepts seen d a), .pointer asp, .pointer atp]
        h (RegisterResidualPredicate.budget n b seen.length) := by
      simpa only [pargs, hpred] using predRun
    have h5 : r2 5 = .flag (RegisterResidualPredicate.accepts seen d a) := by simp [r2, bindResults]
    obtain ⟨fsp, ftp, answer, cont⟩ : ∃ fsp ftp,
        AnswerAt h fsp ftp (crossing seen d (a :: xs)) ∧
        Within code h r2 (afterPredicate self)
          [.flag (crossing seen d (a :: xs)).isSome, .pointer fsp, .pointer ftp]
          h (budget n b seen.length xs.length + 17) := by
      cases haok : RegisterResidualPredicate.accepts seen d a
      · refine ⟨sp, tp, ?_, ?_⟩
        · simpa [crossing, List.find?_cons, haok] using hans
        · have args : values r2 [.register 0, .register 4, .register 2] =
              [.pointer seenp, .pointer tail, .pointer dp] := by
            simp [r2, r1, regs, bindResults, loadRegisters, decoded, initialRegisters, values, Atom.eval]
          have last := Within.ret code h
            (bindResults r2 [8, 9, 10] [.flag (crossing seen d xs).isSome, .pointer sp, .pointer tp])
            [.register 8, .register 9, .register 10]
          have last' : Within code h
              (bindResults r2 [8, 9, 10] [.flag (crossing seen d xs).isSome, .pointer sp, .pointer tp])
              (.ret [.register 8, .register 9, .register 10])
              [.flag (crossing seen d xs).isSome, .pointer sp, .pointer tp] h 7 := by
            simpa [values, Atom.eval, bindResults] using last
          have call := Within.call (procedure := self) (regs := r2)
            (arguments := [.register 0, .register 4, .register 2]) (results := [8, 9, 10])
            (by simpa only [args] using child) last'
          have br := Within.branch (test := .register 5) (b := false)
            (yes := .ret [.flag true, .register 6, .register 7]) (no := recurseBody self)
            (by simpa [Atom.eval, haok] using h5) call
          simpa [afterPredicate, recurseBody, crossing, List.find?_cons, haok] using
            br.mono (b := budget n b seen.length xs.length + 17)
              (by simp only [List.length_cons, List.length_nil]; omega)
      · refine ⟨asp, atp, ?_, ?_⟩
        · simpa [crossing, List.find?_cons, haok, AnswerAt] using And.intro hsrc htgt
        · have last : Within code h r2 (.ret [.flag true, .register 6, .register 7])
              [.flag true, .pointer asp, .pointer atp] h 7 := by
            simpa [values, Atom.eval, r2, bindResults] using
              Within.ret code h r2 [.flag true, .register 6, .register 7]
          have br := Within.branch (test := .register 5) (b := true)
            (yes := .ret [.flag true, .register 6, .register 7]) (no := recurseBody self)
            (by simpa [Atom.eval, haok] using h5) last
          simpa [afterPredicate, crossing, List.find?_cons, haok] using
            br.mono (b := budget n b seen.length xs.length + 17) (by omega)
    have call := Within.call (procedure := predicate) (regs := r1)
      (arguments := [.register 0, .register 3, .register 2]) (results := [5, 6, 7]) predCall cont
    have load := Within.load (address := .register 1) (first := 3) (second := 4) (bit := 15)
      (branches := {CompiledTrie.failCases with
        nil := rejected
        cons := .call predicate [.register 0, .register 3, .register 2] [5, 6, 7] (afterPredicate self)})
      (by simp [Atom.eval, regs, initialRegisters]) cell call
    refine ⟨fsp, ftp, answer, ?_⟩
    simpa only [hself, crossingBody] using load.mono
      (b := budget n b seen.length (a :: xs).length) (by simp [budget, Nat.mul_add]; omega)

/-- The scan returns an actual first crossing entry. -/
theorem crossing_some {n b : ℕ} (seen : List (Bits n)) (d : Bits b) (xs : List (Arc n b))
    (a : Arc n b) (ha : crossing seen d xs = some a) :
    a ∈ xs ∧ (∃ key ∈ seen, key.value = a.source.value) ∧
      (¬ ∃ key ∈ seen, key.value = a.target.value) ∧ d.value ≤ a.capacity.value := by
  exact ⟨List.mem_of_find?_eq_some ha,
    (RegisterResidualPredicate.accepts_iff seen d a).mp (List.find?_some ha)⟩

/-- Failure means that every stored arc out of the reached set is below scale. -/
theorem crossing_none {n b : ℕ} (seen : List (Bits n)) (d : Bits b) (xs : List (Arc n b))
    (ha : crossing seen d xs = none) : ∀ a ∈ xs,
      (∃ key ∈ seen, key.value = a.source.value) →
      (¬ ∃ key ∈ seen, key.value = a.target.value) → a.capacity.value < d.value := by
  intro a ha' hs ht
  have hn := List.find?_eq_none.mp ha a ha'
  by_contra! hh
  have hh' := (RegisterResidualPredicate.accepts_iff seen d a).mpr ⟨hs, ht, hh⟩
  simp [hh'] at hn

end WeightedMIS.RegisterResidualCrossing
