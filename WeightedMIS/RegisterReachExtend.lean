module

public import WeightedMIS.RegisterRoutePrepend
public import WeightedMIS.ExpandedWords

/-! # Constant-size extension of shared reached-set and reverse-route lists -/

@[expose] public section

namespace WeightedMIS.RegisterReachExtend

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.ResidualWords WeightedMIS.ExpandedWords

variable {p : ℕ}

/-- Inputs: source, target, scale, old reverse path, seen list, route list.
The four first allocations share their old tails; route insertion adds two
further cells. -/
def extendBody (prepend : Fin p) : Command p :=
  .allocate 6 (.pair (.register 1) (.register 2))
    (.allocate 7 (.pair (.register 0) (.register 6))
      (.allocate 8 (.cons (.register 7) (.register 3))
        (.allocate 9 (.cons (.register 1) (.register 4))
          (.call prepend [.register 1, .register 8, .register 5] [10]
            (.ret [.register 9, .register 10])))))

theorem compiled (code : Code p) (prepend : Fin p)
    (hp : code prepend = RegisterRouteLookup.prependBody)
    {n b : ℕ} {h : Heap} (hh : Valid h)
    {source target : Bits n} {d : Bits b} {path : List (Arc n b)}
    {seen : List (Bits n)} {routes : List (RegisterRouteLookup.Route n b)}
    {sp tp dp pp seenp routep : Ptr}
    (hs : BitsAt h sp source) (ht : BitsAt h tp target) (hd : BitsAt h dp d)
    (hpath : TableAt h pp path) (hseen : WordsAt h seenp seen)
    (hroutes : RegisterRouteLookup.RoutesAt h routep routes) :
    ∃ out newseen newroutes, Extends h out ∧ Valid out ∧
      WordsAt out newseen (target :: seen) ∧
      RegisterRouteLookup.RoutesAt out newroutes
        ((target, (⟨source, target, d⟩ : Arc n b) :: path) :: routes) ∧
      Within code h (initialRegisters [.pointer sp, .pointer tp, .pointer dp,
          .pointer pp, .pointer seenp, .pointer routep]) (extendBody prepend)
        [.pointer newseen, .pointer newroutes] out 63 := by
  have hfirst := safe_allocate h hh (.pair tp dp) (by
    intro p hp
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ht.allocated
    · exact hd.allocated)
  let h1 := h ++ [.pair tp dp]
  have hsecond := safe_allocate h1 hfirst.2.1 (.pair sp h.length) (by
    intro p hp
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact (hs.mono hfirst.1).allocated
    · simp [h1])
  let h2 := h1 ++ [.pair sp h.length]
  have he2 := hfirst.1.trans hsecond.1
  have harc : ArcAt h2 h1.length (⟨source, target, d⟩ : Arc n b) := by
    refine ⟨sp, h.length, tp, dp, ?_, ?_, hs.mono he2, ht.mono he2, hd.mono he2⟩
    · simp [h2]
    · exact hsecond.1.lookup (by simp [h1])
  have hthird := safe_allocate h2 hsecond.2.1 (.cons h1.length pp) (by
    intro p hp
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact harc.allocated
    · exact (hpath.mono he2).allocated)
  let h3 := h2 ++ [.cons h1.length pp]
  have he3 := he2.trans hthird.1
  have hnewpath : TableAt h3 h2.length ((⟨source, target, d⟩ : Arc n b) :: path) :=
    TableAt.cons (by simp [h3]) (harc.mono hthird.1) (hpath.mono he3)
  obtain ⟨hfourth, hnewseen⟩ := allocate_word_cons hthird.2.1 (ht.mono he3) (hseen.mono he3)
  let h4 := h3 ++ [.cons tp seenp]
  have he4 := he3.trans hfourth.1
  obtain ⟨out, result, he5, ho, hnewroutes, _, prependRun⟩ :=
    RegisterRouteLookup.prepend_compiled code prepend hp hfourth.2.1 (ht.mono he4)
      (hnewpath.mono hfourth.1) (hroutes.mono he4)
  let regs := initialRegisters [Value.pointer sp, .pointer tp, .pointer dp,
    .pointer pp, .pointer seenp, .pointer routep]
  let r1 := Function.update regs 6 (.pointer h.length)
  let r2 := Function.update r1 7 (.pointer h1.length)
  let r3 := Function.update r2 8 (.pointer h2.length)
  let r4 := Function.update r3 9 (.pointer h3.length)
  let r5 := bindResults r4 [10] [.pointer result]
  have ret : Within code out r5 (.ret [.register 9, .register 10])
      [.pointer h3.length, .pointer result] out 5 := by
    simpa [r5, r4, bindResults, values, Atom.eval] using
      Within.ret code out r5 [.register 9, .register 10]
  have args : values r4 [.register 1, .register 8, .register 5] =
      [.pointer tp, .pointer h2.length, .pointer routep] := by
    simp [r4, r3, r2, r1, regs, initialRegisters, values, Atom.eval]
  have call := Within.call (procedure := prepend) (regs := r4)
    (arguments := [.register 1, .register 8, .register 5]) (results := [10])
    (by simpa only [args] using prependRun) ret
  have a4 := Within.allocate (regs := r3) (dst := 9)
    (expr := .cons (.register 1) (.register 4))
    (by simp [CellExpr.eval, Atom.eval, r3, r2, r1, regs, initialRegisters, Value.asPointer]) call
  have a3 := Within.allocate (regs := r2) (dst := 8)
    (expr := .cons (.register 7) (.register 3))
    (by simp [CellExpr.eval, Atom.eval, r2, r1, regs, initialRegisters, Value.asPointer]) a4
  have a2 := Within.allocate (regs := r1) (dst := 7)
    (expr := .pair (.register 0) (.register 6))
    (by simp [CellExpr.eval, Atom.eval, r1, regs, initialRegisters, Value.asPointer]) a3
  have a1 := Within.allocate (regs := regs) (dst := 6)
    (expr := .pair (.register 1) (.register 2))
    (by simp [CellExpr.eval, Atom.eval, regs, initialRegisters, Value.asPointer]) a2
  refine ⟨out, h3.length, result, he4.trans he5, ho, hnewseen.mono he5, hnewroutes, ?_⟩
  simpa only [extendBody] using a1.mono (b := 63)
    (by simp only [CellExpr.args, List.length_cons, List.length_nil]; omega)

end WeightedMIS.RegisterReachExtend
