module

public import WeightedMIS.RegisterResidualReach

/-! # Closed initialization and complete residual search -/

@[expose] public section

namespace WeightedMIS.RegisterResidualSearch

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.ResidualWords WeightedMIS.ExpandedWords

structure Procedures (p : ℕ) where
  reach : Fin p
  crossing : Fin p
  predicate : Fin p
  member : Fin p
  lookup : Fin p
  extend : Fin p
  prepend : Fin p
  cmp : Fin p

def Procedures.Matches {p : ℕ} (d : Procedures p) (code : Code p) : Prop :=
  code d.reach = RegisterResidualReach.reachBody d.reach d.crossing d.lookup d.extend ∧
  code d.crossing = RegisterResidualCrossing.crossingBody d.crossing d.predicate ∧
  code d.predicate = RegisterResidualPredicate.predicateBody d.member d.cmp ∧
  code d.member = RegisterMembership.membershipBody d.member d.cmp ∧
  code d.lookup = RegisterRouteLookup.lookupBody d.lookup d.cmp ∧
  code d.extend = RegisterReachExtend.extendBody d.prepend ∧
  code d.prepend = RegisterRouteLookup.prependBody ∧
  code d.cmp = RegisterComparator.comparatorBody d.cmp

/-- Inputs: residual table, scale, complete vertex word list, source word. -/
def searchBody {p : ℕ} (reach prepend : Fin p) : Command p :=
  .allocate 4 (.cons (.register 3) .null)
    (.call prepend [.register 3, .null, .null] [5]
      (.call reach [.register 0, .register 1, .register 2, .register 4, .register 5] [6, 7]
        (.ret [.register 6, .register 7])))

def budget (n b entries nodes : ℕ) : ℕ :=
  RegisterResidualReach.budget n b (nodes + 1) entries nodes + 50

theorem compiled {p : ℕ} (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {n b : ℕ} {h : Heap} (hh : Valid h) {table : List (Arc n b)} {delta : Bits b}
    {nodes : List (Bits n)} {source : Bits n} {tablep dp np sp : Ptr}
    (ht : TableAt h tablep table) (hd : BitsAt h dp delta) (hn : WordsAt h np nodes)
    (hs : BitsAt h sp source) :
    ∃ out seenp routep, Extends h out ∧ Valid out ∧
      WordsAt out seenp (ResidualListReach.explore table delta nodes.length (ResidualListReach.initial source)).seen ∧
      RegisterRouteLookup.RoutesAt out routep
        (ResidualListReach.explore table delta nodes.length (ResidualListReach.initial source)).routes ∧
      Within code h (initialRegisters [.pointer tablep, .pointer dp, .pointer np, .pointer sp])
        (searchBody d.reach d.prepend) [.pointer seenp, .pointer routep] out (budget n b table.length nodes.length) := by
  obtain ⟨hreach, hcross, hpred, hmember, hlookup, hextend, hprepend, hcmp⟩ := hm
  obtain ⟨hcons, hseen⟩ := allocate_word_cons hh hs (WordsAt.nil hh.1 : WordsAt h 0 ([] : List (Bits n)))
  let mid := h ++ [.cons sp 0]
  obtain ⟨ready, routes, he2, hv2, hroutes, _, prependRun⟩ :=
    RegisterRouteLookup.prepend_compiled code d.prepend hprepend hcons.2.1
      (hs.mono hcons.1) (TableAt.nil hcons.2.1.1 : TableAt mid 0 ([] : List (Arc n b)))
      (RegisterRouteLookup.RoutesAt.nil hcons.2.1.1 : RegisterRouteLookup.RoutesAt mid 0 [])
  have hinit : WordsAt ready h.length (ResidualListReach.initial (b := b) source).seen := hseen.mono he2
  have hrinit : RegisterRouteLookup.RoutesAt ready routes (ResidualListReach.initial (b := b) source).routes := hroutes
  obtain ⟨out, seenp, routep, he3, ho, hseenOut, hroutesOut, reachRun⟩ :=
    RegisterResidualReach.compiled code d.reach d.crossing d.predicate d.member d.lookup d.extend d.prepend d.cmp
      hreach hcross hpred hmember hlookup hextend hprepend hcmp hv2 (ResidualListReach.initial source)
      (ht.mono (hcons.1.trans he2)) (hd.mono (hcons.1.trans he2)) (hn.mono (hcons.1.trans he2))
      hinit hrinit (nodes.length + 1) (by simp [ResidualListReach.initial]; omega)
      (by simp [ResidualListReach.initial]; omega)
  let regs := initialRegisters [Value.pointer tablep, .pointer dp, .pointer np, .pointer sp]
  let r1 := Function.update regs 4 (.pointer h.length)
  let r2 := bindResults r1 [5] [.pointer routes]
  let r3 := bindResults r2 [6, 7] [.pointer seenp, .pointer routep]
  have ret : Within code out r3 (.ret [.register 6, .register 7]) [.pointer seenp, .pointer routep] out 5 := by
    simpa [r3, bindResults, values, Atom.eval] using Within.ret code out r3 [.register 6, .register 7]
  have rargs : values r2 [.register 0, .register 1, .register 2, .register 4, .register 5] =
      [.pointer tablep, .pointer dp, .pointer np, .pointer h.length, .pointer routes] := by
    simp [r2, r1, regs, bindResults, initialRegisters, values, Atom.eval]
  have rcall := Within.call (procedure := d.reach) (regs := r2)
    (arguments := [.register 0, .register 1, .register 2, .register 4, .register 5]) (results := [6, 7])
    (by simpa only [rargs] using reachRun) ret
  have pargs : values r1 [.register 3, .null, .null] = [.pointer sp, .pointer 0, .pointer 0] := by
    simp [r1, regs, initialRegisters, values, Atom.eval]
  have pcall := Within.call (procedure := d.prepend) (regs := r1)
    (arguments := [.register 3, .null, .null]) (results := [5])
    (by simpa only [pargs] using prependRun) rcall
  have alloc := Within.allocate (regs := regs) (dst := 4) (expr := .cons (.register 3) .null)
    (by simp [CellExpr.eval, Atom.eval, regs, initialRegisters, Value.asPointer]) pcall
  refine ⟨out, seenp, routep, (hcons.1.trans he2).trans he3, ho, hseenOut, hroutesOut, ?_⟩
  simpa only [searchBody] using alloc.mono (b := budget n b table.length nodes.length)
    (by simp only [budget, CellExpr.args, List.length_cons, List.length_nil]; omega)

end WeightedMIS.RegisterResidualSearch
