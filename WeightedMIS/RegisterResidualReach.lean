module

public import WeightedMIS.RegisterReachExtend
public import WeightedMIS.ResidualListReach

/-! # A finite register loop for residual reachability and shared routes -/

@[expose] public section

namespace WeightedMIS.RegisterResidualReach

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.ResidualWords WeightedMIS.ExpandedWords

variable {p : ℕ}

def stop : Command p := .ret [.register 3, .register 4]

def discovered (self lookup extend : Fin p) : Command p :=
  .call lookup [.register 8, .register 4] [10]
    (.call extend [.register 8, .register 9, .register 1, .register 10, .register 3, .register 4] [11, 12]
      (.call self [.register 0, .register 1, .register 6, .register 11, .register 12] [13, 14]
        (.ret [.register 13, .register 14])))

/-- Inputs: residual table, scale, round-list, reached words, stored routes. -/
def reachBody (self crossing lookup extend : Fin p) : Command p :=
  .load (.register 2) 5 6 15 {CompiledTrie.failCases with
    nil := stop
    cons := .call crossing [.register 3, .register 0, .register 1] [7, 8, 9]
      (.branch (.register 7) (discovered self lookup extend) stop)}

def stepBudget (n b limit entries : ℕ) : ℕ :=
  RegisterResidualCrossing.budget n b limit entries + RegisterRouteLookup.budget n limit + 130

def budget (n b limit entries fuel : ℕ) : ℕ := stepBudget n b limit entries * fuel + 15

theorem crossing_budget_mono (n b small large entries : ℕ) (hle : small ≤ large) :
    RegisterResidualCrossing.budget n b small entries ≤
      RegisterResidualCrossing.budget n b large entries := by
  unfold RegisterResidualCrossing.budget RegisterResidualPredicate.budget RegisterMembership.budget
  have hmul := Nat.mul_le_mul_left (36 * n + 60) hle
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _

theorem lookup_budget_mono (n small large : ℕ) (hle : small ≤ large) :
    RegisterRouteLookup.budget n small ≤ RegisterRouteLookup.budget n large := by
  unfold RegisterRouteLookup.budget
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hle) _

theorem compiled (code : Code p) (self crossing predicate member lookup extend prepend cmp : Fin p)
    (hself : code self = reachBody self crossing lookup extend)
    (hcross : code crossing = RegisterResidualCrossing.crossingBody crossing predicate)
    (hpred : code predicate = RegisterResidualPredicate.predicateBody member cmp)
    (hmember : code member = RegisterMembership.membershipBody member cmp)
    (hlookup : code lookup = RegisterRouteLookup.lookupBody lookup cmp)
    (hextend : code extend = RegisterReachExtend.extendBody prepend)
    (hprepend : code prepend = RegisterRouteLookup.prependBody)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    {n b : ℕ} {table : List (Arc n b)} {delta : Bits b} {fuel : List (Bits n)}
    {h : Heap} (hh : Valid h) (q : ResidualListReach.State n b)
    {tablep dp fp sp rp : Ptr} (ht : TableAt h tablep table) (hd : BitsAt h dp delta)
    (hf : WordsAt h fp fuel) (hs : WordsAt h sp q.seen) (hr : RegisterRouteLookup.RoutesAt h rp q.routes)
    (limit : ℕ) (hsl : q.seen.length + fuel.length ≤ limit) (hrl : q.routes.length + fuel.length ≤ limit) :
    ∃ out seenp routep, Extends h out ∧ Valid out ∧
      WordsAt out seenp (ResidualListReach.explore table delta fuel.length q).seen ∧
      RegisterRouteLookup.RoutesAt out routep (ResidualListReach.explore table delta fuel.length q).routes ∧
      Within code h (initialRegisters [.pointer tablep, .pointer dp, .pointer fp, .pointer sp, .pointer rp])
        (code self) [.pointer seenp, .pointer routep] out (budget n b limit table.length fuel.length) := by
  induction fuel generalizing h q tablep dp fp sp rp with
  | nil =>
    have cell := WordsAt.nil_iff.mp hf
    let regs := initialRegisters [Value.pointer tablep, .pointer dp, .pointer fp, .pointer sp, .pointer rp]
    have ret : Within code h (loadRegisters regs 5 6 15 .nil) stop [.pointer sp, .pointer rp] h 5 := by
      simpa [stop, regs, initialRegisters, loadRegisters, decoded, values, Atom.eval] using
        Within.ret code h (loadRegisters regs 5 6 15 .nil) [.register 3, .register 4]
    have ld := Within.load (address := .register 2) (first := 5) (second := 6) (bit := 15)
      (branches := {CompiledTrie.failCases with
        nil := stop
        cons := .call crossing [.register 3, .register 0, .register 1] [7, 8, 9]
          (.branch (.register 7) (discovered self lookup extend) stop)})
      (by simp [regs, initialRegisters, Atom.eval]) cell ret
    refine ⟨h, sp, rp, .refl h, hh, hs, hr, ?_⟩
    simpa [hself, reachBody, budget] using ld
  | cons f fuel ih =>
    obtain ⟨fhead, ftail, fcell, _, hftail⟩ := WordsAt.cons_iff.mp hf
    obtain ⟨sourcep, targetp, answer, crossRun⟩ :=
      RegisterResidualCrossing.compiled code crossing predicate member cmp hcross hpred hmember hcmp hs ht hd
    let regs := initialRegisters [Value.pointer tablep, .pointer dp, .pointer fp, .pointer sp, .pointer rp]
    let r1 := loadRegisters regs 5 6 15 (.cons fhead ftail)
    let r2 := bindResults r1 [7, 8, 9]
      [.flag (RegisterResidualCrossing.crossing q.seen delta table).isSome, .pointer sourcep, .pointer targetp]
    have argsC : values r1 [.register 3, .register 0, .register 1] =
        [.pointer sp, .pointer tablep, .pointer dp] := by
      simp [r1, regs, loadRegisters, decoded, initialRegisters, values, Atom.eval]
    have crun : Within code h (initialRegisters (values r1 [.register 3, .register 0, .register 1]))
        (code crossing) [.flag (RegisterResidualCrossing.crossing q.seen delta table).isSome,
          .pointer sourcep, .pointer targetp] h (RegisterResidualCrossing.budget n b limit table.length) := by
      simpa only [argsC] using crossRun.mono (crossing_budget_mono n b q.seen.length limit table.length (by omega))
    have h7 : r2 7 = .flag (RegisterResidualCrossing.crossing q.seen delta table).isSome := by
      simp [r2, bindResults]
    obtain ⟨out, seenp, routep, he, ho, hseen, hroute, cont⟩ :
        ∃ out seenp routep, Extends h out ∧ Valid out ∧
          WordsAt out seenp (ResidualListReach.explore table delta (fuel.length + 1) q).seen ∧
          RegisterRouteLookup.RoutesAt out routep (ResidualListReach.explore table delta (fuel.length + 1) q).routes ∧
          Within code h r2 (.branch (.register 7) (discovered self lookup extend) stop)
            [.pointer seenp, .pointer routep] out
            (RegisterRouteLookup.budget n limit + budget n b limit table.length fuel.length + 113) := by
      cases hx : RegisterResidualCrossing.crossing q.seen delta table with
      | none =>
        refine ⟨h, sp, rp, .refl h, hh, ?_, ?_, ?_⟩
        · simpa [ResidualListReach.explore, hx] using hs
        · simpa [ResidualListReach.explore, hx] using hr
        · have ret : Within code h r2 stop [.pointer sp, .pointer rp] h 5 := by
            simpa [stop, r2, r1, regs, bindResults, loadRegisters, decoded, initialRegisters, values, Atom.eval] using
              Within.ret code h r2 [.register 3, .register 4]
          have br := Within.branch (test := .register 7) (b := false)
            (yes := discovered self lookup extend) (no := stop)
            (by simpa [Atom.eval, hx] using h7) ret
          exact br.mono (by omega)
      | some a =>
        have repr : BitsAt h sourcep a.source ∧ BitsAt h targetp a.target := by
          simpa [hx, AnswerAt] using answer
        obtain ⟨pathp, hpath, lookupRun⟩ :=
          RegisterRouteLookup.compiled code lookup cmp hlookup hcmp hh repr.1 hr
        obtain ⟨mid, newseen, newroutes, he1, hm, hnewseen, hnewroutes, extendRun⟩ :=
          RegisterReachExtend.compiled code prepend hprepend hh repr.1 repr.2 hd hpath hs hr
        have hns : WordsAt mid newseen (ResidualListReach.extend q delta a).seen := hnewseen
        have hnr : RegisterRouteLookup.RoutesAt mid newroutes (ResidualListReach.extend q delta a).routes := hnewroutes
        obtain ⟨out, seenp, routep, he2, ho, hseen, hroute, child⟩ := ih hm (ResidualListReach.extend q delta a)
          (ht.mono he1) (hd.mono he1) (hftail.mono he1) hns hnr
          (by simp only [ResidualListReach.extend, List.length_cons] at hsl ⊢; omega)
          (by simp only [ResidualListReach.extend, List.length_cons] at hrl ⊢; omega)
        let r3 := bindResults r2 [10] [.pointer pathp]
        let r4 := bindResults r3 [11, 12] [.pointer newseen, .pointer newroutes]
        let r5 := bindResults r4 [13, 14] [.pointer seenp, .pointer routep]
        have ret : Within code out r5 (.ret [.register 13, .register 14]) [.pointer seenp, .pointer routep] out 5 := by
          simpa [r5, bindResults, values, Atom.eval] using Within.ret code out r5 [.register 13, .register 14]
        have argsR : values r4 [.register 0, .register 1, .register 6, .register 11, .register 12] =
            [.pointer tablep, .pointer dp, .pointer ftail, .pointer newseen, .pointer newroutes] := by
          simp [r4, r3, r2, r1, regs, bindResults, loadRegisters, decoded, initialRegisters, values, Atom.eval]
        have recurse := Within.call (procedure := self) (regs := r4)
          (arguments := [.register 0, .register 1, .register 6, .register 11, .register 12]) (results := [13, 14])
          (by simpa only [argsR] using child) ret
        have argsE : values r3 [.register 8, .register 9, .register 1, .register 10, .register 3, .register 4] =
            [.pointer sourcep, .pointer targetp, .pointer dp, .pointer pathp, .pointer sp, .pointer rp] := by
          simp [r3, r2, r1, regs, bindResults, loadRegisters, decoded, initialRegisters, values, Atom.eval]
        have extcall := Within.call (procedure := extend) (regs := r3)
          (arguments := [.register 8, .register 9, .register 1, .register 10, .register 3, .register 4]) (results := [11, 12])
          (by simpa only [argsE, hextend] using extendRun) recurse
        have argsL : values r2 [.register 8, .register 4] = [.pointer sourcep, .pointer rp] := by
          simp [r2, r1, regs, bindResults, loadRegisters, decoded, initialRegisters, values, Atom.eval]
        have lookcall := Within.call (procedure := lookup) (regs := r2)
          (arguments := [.register 8, .register 4]) (results := [10])
          (by simpa only [argsL] using lookupRun.mono (lookup_budget_mono n q.routes.length limit (by omega))) extcall
        have br := Within.branch (test := .register 7) (b := true)
          (yes := discovered self lookup extend) (no := stop)
          (by simpa [Atom.eval, hx] using h7) lookcall
        refine ⟨out, seenp, routep, he1.trans he2, ho, ?_, ?_, ?_⟩
        · simpa [ResidualListReach.explore, hx] using hseen
        · simpa [ResidualListReach.explore, hx] using hroute
        · exact br.mono (by simp only [List.length_cons, List.length_nil]; omega)
    have call := Within.call (procedure := crossing) (regs := r1)
      (arguments := [.register 3, .register 0, .register 1]) (results := [7, 8, 9]) crun cont
    have ld := Within.load (address := .register 2) (first := 5) (second := 6) (bit := 15)
      (branches := {CompiledTrie.failCases with
        nil := stop
        cons := .call crossing [.register 3, .register 0, .register 1] [7, 8, 9]
          (.branch (.register 7) (discovered self lookup extend) stop)})
      (by simp [Atom.eval, regs, initialRegisters]) fcell call
    refine ⟨out, seenp, routep, he, ho, hseen, hroute, ?_⟩
    simpa only [hself, reachBody] using ld.mono
      (b := budget n b limit table.length (f :: fuel).length)
      (by simp only [budget, stepBudget, List.length_cons, List.length_nil, Nat.mul_add, Nat.mul_one]; omega)

end WeightedMIS.RegisterResidualReach
