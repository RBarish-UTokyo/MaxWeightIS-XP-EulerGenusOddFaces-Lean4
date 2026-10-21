module

public import WeightedMIS.RegisterAdjacencyScan
public import WeightedMIS.ResidualCrossingRefinement

/-!
# Lookup of one stored residual arc

The procedure scans a stored residual table (`ResidualWords.TableAt`) for the
first arc whose source and target words equal the two query words, compared
with the compiled binary comparator, and returns the shared pointer of that
arc's capacity word. When no arc matches it returns the supplied default
pointer. The heap is not changed.

On a table listing every ordered pair of an injectively encoded node list the
answer is the capacity word of the queried pair (`lookup_encoded`).
-/

@[expose] public section

namespace WeightedMIS.RegisterArcLookup

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ResidualWords

/-- The capacity word of the first arc from `s` to `t`, or `default`. -/
def lookup {n b : ℕ} (s t : Bits n) (default : Bits b) : List (Arc n b) → Bits b
  | [] => default
  | a :: rest => if a.source = s ∧ a.target = t then a.capacity else lookup s t default rest

/-- On the encoded list of ordered pairs the lookup returns the stored capacity. -/
theorem lookup_encoded {V : Type*} {n b : ℕ} (enc : V → Bits n)
    (hinj : Function.Injective enc) (caps : V → V → Bits b) (default : Bits b)
    (pairs : List (V × V)) (u v : V) (huv : (u, v) ∈ pairs) :
    lookup (enc u) (enc v) default
      (pairs.map (ResidualCrossingRefinement.encodeArc enc caps)) = caps u v := by
  induction pairs with
  | nil => simp at huv
  | cons x rest ih =>
    simp only [List.map_cons, lookup, ResidualCrossingRefinement.encodeArc]
    by_cases hx : enc x.1 = enc u ∧ enc x.2 = enc v
    · rw [hinj hx.1, hinj hx.2]; simp
    · simp only [hx, ↓reduceIte]
      apply ih
      rcases List.mem_cons.mp huv with h | h
      · exact absurd ⟨by rw [← h], by rw [← h]⟩ hx
      · exact h

variable {p : ℕ}

/-- Arguments: rest of the table, source word, target word, default word. -/
def recurseBody (self : Fin p) : Command p :=
  .call self [.register 5, .register 1, .register 2, .register 3] [13] (.ret [.register 13])

def targetBody (self cmp : Fin p) : Command p :=
  .call cmp [.register 8, .register 2] [10, 12]
    (.branch (.register 12) (.ret [.register 9]) (recurseBody self))

def compareBody (self cmp : Fin p) : Command p :=
  .call cmp [.register 6, .register 1] [10, 11]
    (.branch (.register 11) (targetBody self cmp) (recurseBody self))

def arcBody (self cmp : Fin p) : Command p :=
  .load (.register 4) 6 7 15 { CompiledTrie.failCases with
    pair := .load (.register 7) 8 9 15 { CompiledTrie.failCases with
      pair := compareBody self cmp } }

/-- Arguments: table, source word, target word, default word. Result: the
shared capacity word of the first matching arc, or the default word. -/
def lookupBody (self cmp : Fin p) : Command p :=
  .load (.register 0) 4 5 15 { CompiledTrie.failCases with
    nil := .ret [.register 3]
    cons := arcBody self cmp }

def budget (n length : ℕ) : ℕ := (72 * n + 150) * length + 15

theorem compiled (code : Code p) (self cmp : Fin p)
    (hself : code self = lookupBody self cmp)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    {n b : ℕ} {h : Heap} {tp sp qp dp : Ptr} {s t : Bits n} {default : Bits b}
    {table : List (Arc n b)}
    (htab : TableAt h tp table) (hs : BitsAt h sp s) (ht : BitsAt h qp t)
    (hd : BitsAt h dp default) :
    ∃ result, BitsAt h result (lookup s t default table) ∧
      Within code h (initialRegisters [.pointer tp, .pointer sp, .pointer qp, .pointer dp])
        (code self) [.pointer result] h (budget n table.length) := by
  induction table generalizing tp with
  | nil =>
    refine ⟨dp, hd, ?_⟩
    have cell := TableAt.nil_iff.mp htab
    let regs := initialRegisters [Value.pointer tp, .pointer sp, .pointer qp, .pointer dp]
    have last : Within code h (loadRegisters regs 4 5 15 .nil) (.ret [.register 3])
        [.pointer dp] h 3 := by
      simpa [values, Atom.eval, loadRegisters, decoded, regs, initialRegisters] using
        Within.ret code h (loadRegisters regs 4 5 15 .nil) [.register 3]
    have load := Within.load (address := .register 0) (first := 4) (second := 5) (bit := 15)
      (branches := { CompiledTrie.failCases with
        nil := .ret [.register 3], cons := arcBody self cmp })
      (by simp [regs, Atom.eval, initialRegisters]) cell last
    rw [hself]
    exact load.mono (by simp [budget])
  | cons arc rest ih =>
    obtain ⟨head, tail, cell, harc, hrest⟩ := TableAt.cons_iff.mp htab
    obtain ⟨asp, atail, atp, acp, c1, c2, has, hat, hac⟩ := harc
    obtain ⟨child, hchild, childRun⟩ := ih hrest
    let regs := initialRegisters [Value.pointer tp, .pointer sp, .pointer qp, .pointer dp]
    let r1 := loadRegisters regs 4 5 15 (.cons head tail)
    let r2 := loadRegisters r1 6 7 15 (.pair asp atail)
    let r3 := loadRegisters r2 8 9 15 (.pair atp acp)
    have g1 : r3 1 = .pointer sp := by
      simp [r3, r2, r1, regs, loadRegisters, decoded, initialRegisters]
    have g2 : r3 2 = .pointer qp := by
      simp [r3, r2, r1, regs, loadRegisters, decoded, initialRegisters]
    have g3 : r3 3 = .pointer dp := by
      simp [r3, r2, r1, regs, loadRegisters, decoded, initialRegisters]
    have g5 : r3 5 = .pointer tail := by
      simp [r3, r2, r1, loadRegisters, decoded]
    have g6 : r3 6 = .pointer asp := by simp [r3, r2, loadRegisters, decoded]
    have g8 : r3 8 = .pointer atp := by simp [r3, loadRegisters, decoded]
    have g9 : r3 9 = .pointer acp := by simp [r3, loadRegisters, decoded]
    -- the recursive tail call from any register bank agreeing with `r3` on 1, 2, 3, 5
    have recurse : ∀ regs' : Registers, regs' 1 = .pointer sp → regs' 2 = .pointer qp →
        regs' 3 = .pointer dp → regs' 5 = .pointer tail →
        Within code h regs' (recurseBody self) [.pointer child] h
          (budget n rest.length + 12) := by
      intro regs' e1 e2 e3 e5
      have last : Within code h (bindResults regs' [13] [.pointer child]) (.ret [.register 13])
          [.pointer child] h 3 := by
        simpa [values, Atom.eval, bindResults] using
          Within.ret code h (bindResults regs' [13] [.pointer child]) [.register 13]
      have a : values regs' [.register 5, .register 1, .register 2, .register 3] =
          [.pointer tail, .pointer sp, .pointer qp, .pointer dp] := by
        simp [values, Atom.eval, e1, e2, e3, e5]
      have c := Within.call (procedure := self) (regs := regs')
        (arguments := [.register 5, .register 1, .register 2, .register 3]) (results := [13])
        (by simpa only [a] using childRun) last
      exact c.mono (by simp; omega)
    have run1 := RegisterAdjacencyScan.cmp_run code cmp hcmp has hs
    let s1 := bindResults r3 [10, 11]
      [.flag (decide ((Bits.compare arc.source s).1 = .lt)), .flag (decide (arc.source = s))]
    have t1 : s1 1 = .pointer sp := by simp [s1, bindResults, g1]
    have t2 : s1 2 = .pointer qp := by simp [s1, bindResults, g2]
    have t3 : s1 3 = .pointer dp := by simp [s1, bindResults, g3]
    have t5 : s1 5 = .pointer tail := by simp [s1, bindResults, g5]
    have t8 : s1 8 = .pointer atp := by simp [s1, bindResults, g8]
    have t9 : s1 9 = .pointer acp := by simp [s1, bindResults, g9]
    have a1 : values r3 [.register 6, .register 1] = [.pointer asp, .pointer sp] := by
      simp [values, Atom.eval, g6, g1]
    have tree : ∃ result, BitsAt h result (lookup s t default (arc :: rest)) ∧
        Within code h r3 (compareBody self cmp) [.pointer result] h
          (72 * n + 120 + budget n rest.length) := by
      by_cases hsrc : arc.source = s
      · have run2 := RegisterAdjacencyScan.cmp_run code cmp hcmp hat ht
        let s2 := bindResults s1 [10, 12]
          [.flag (decide ((Bits.compare arc.target t).1 = .lt)), .flag (decide (arc.target = t))]
        have a2 : values s1 [.register 8, .register 2] = [.pointer atp, .pointer qp] := by
          simp [values, Atom.eval, t8, t2]
        by_cases htgt : arc.target = t
        · refine ⟨acp, by simpa [lookup, hsrc, htgt] using hac, ?_⟩
          have last : Within code h s2 (.ret [.register 9]) [.pointer acp] h 3 := by
            simpa [values, Atom.eval, s2, bindResults, t9] using
              Within.ret code h s2 [.register 9]
          have br2 := Within.branch (regs := s2) (test := .register 12) (b := true)
            (no := recurseBody self) (by simp [Atom.eval, s2, bindResults, htgt]) last
          have c2 := Within.call (procedure := cmp) (regs := s1)
            (arguments := [.register 8, .register 2]) (results := [10, 12])
            (by simpa only [a2] using run2) br2
          have br1 := Within.branch (regs := s1) (test := .register 11) (b := true)
            (no := recurseBody self) (by simp [Atom.eval, s1, bindResults, hsrc]) c2
          have c1 := Within.call (procedure := cmp) (regs := r3)
            (arguments := [.register 6, .register 1]) (results := [10, 11])
            (by simpa only [a1] using run1) br1
          exact c1.mono (by simp; omega)
        · refine ⟨child, by simpa [lookup, hsrc, htgt] using hchild, ?_⟩
          have tailRun := recurse s2 (by simp [s2, bindResults, t1]) (by simp [s2, bindResults, t2])
            (by simp [s2, bindResults, t3]) (by simp [s2, bindResults, t5])
          have br2 := Within.branch (regs := s2) (test := .register 12) (b := false)
            (yes := .ret [.register 9]) (by simp [Atom.eval, s2, bindResults, htgt]) tailRun
          have c2 := Within.call (procedure := cmp) (regs := s1)
            (arguments := [.register 8, .register 2]) (results := [10, 12])
            (by simpa only [a2] using run2) br2
          have br1 := Within.branch (regs := s1) (test := .register 11) (b := true)
            (no := recurseBody self) (by simp [Atom.eval, s1, bindResults, hsrc]) c2
          have c1 := Within.call (procedure := cmp) (regs := r3)
            (arguments := [.register 6, .register 1]) (results := [10, 11])
            (by simpa only [a1] using run1) br1
          exact c1.mono (by simp; omega)
      · refine ⟨child, by simpa [lookup, hsrc] using hchild, ?_⟩
        have tailRun := recurse s1 t1 t2 t3 t5
        have br1 := Within.branch (regs := s1) (test := .register 11) (b := false)
          (yes := targetBody self cmp) (by simp [Atom.eval, s1, bindResults, hsrc]) tailRun
        have c1 := Within.call (procedure := cmp) (regs := r3)
          (arguments := [.register 6, .register 1]) (results := [10, 11])
          (by simpa only [a1] using run1) br1
        exact c1.mono (by simp; omega)
    obtain ⟨result, hres, run⟩ := tree
    refine ⟨result, hres, ?_⟩
    have l3 := Within.load (regs := r2) (address := .register 7) (first := 8) (second := 9)
      (bit := 15) (branches := { CompiledTrie.failCases with pair := compareBody self cmp })
      (by simp [Atom.eval, r2, loadRegisters, decoded]) c2 run
    have l2 := Within.load (regs := r1) (address := .register 4) (first := 6) (second := 7)
      (bit := 15) (branches := { CompiledTrie.failCases with
        pair := .load (.register 7) 8 9 15 { CompiledTrie.failCases with
          pair := compareBody self cmp } })
      (by simp [Atom.eval, r1, loadRegisters, decoded]) c1 l3
    have l1 := Within.load (regs := regs) (address := .register 0) (first := 4) (second := 5)
      (bit := 15) (branches := { CompiledTrie.failCases with
        nil := .ret [.register 3], cons := arcBody self cmp })
      (by simp [Atom.eval, regs, initialRegisters]) cell l2
    rw [hself]
    exact l1.mono (by simp [budget, Nat.mul_add]; omega)

end WeightedMIS.RegisterArcLookup
