module

public import WeightedMIS.RegisterResidualSearch
public import WeightedMIS.ResidualListPhase

/-! # Finite register implementation of one capacity-scaling phase -/

@[expose] public section

namespace WeightedMIS.RegisterResidualPhase

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.ResidualWords WeightedMIS.ExpandedWords

structure Procedures (p : ℕ) where
  reach : RegisterResidualSearch.Procedures p
  search : Fin p
  tableUpdate : Fin p
  arcUpdate : Fin p
  arcMember : Fin p
  adjust : Fin p
  sub : Fin p
  complement : Fin p
  add : Fin p

def Procedures.Matches {p : ℕ} (d : Procedures p) (code : Code p) : Prop :=
  d.reach.Matches code ∧
  code d.search = RegisterResidualSearch.searchBody d.reach.reach d.reach.prepend ∧
  code d.tableUpdate = RegisterResidualTableUpdate.tableBody d.tableUpdate d.arcUpdate ∧
  code d.arcUpdate = RegisterResidualUpdate.updateBody d.arcMember d.adjust ∧
  code d.arcMember = RegisterArcMembership.membershipBody d.arcMember d.reach.cmp ∧
  code d.adjust = RegisterResidualAdjust.adjustBody d.sub d.add ∧
  code d.sub = RegisterSubtractor.subtractorBody d.complement d.add ∧
  code d.complement = RegisterComplement.complementBody d.complement ∧
  code d.add = RegisterAdder.adderBody d.add

variable {p : ℕ}

def stop : Command p := .ret [.register 0, .register 6]

def augmentBody (self lookup update : Fin p) : Command p :=
  .call lookup [.register 4, .register 7] [11]
    (.call update [.register 0, .register 11, .register 1] [12]
      (.call self [.register 12, .register 1, .register 2, .register 3, .register 4, .register 9] [13, 14]
        (.ret [.register 13, .register 14])))

def afterSearch (self member lookup update : Fin p) : Command p :=
  .load (.register 5) 8 9 15 {CompiledTrie.failCases with
    nil := stop
    cons := .call member [.register 4, .register 6] [10]
      (.branch (.register 10) (augmentBody self lookup update) stop)}

/-- Inputs: residual table, scale, vertex words, source, sink, attempt list. -/
def phaseBody (self search member lookup update : Fin p) : Command p :=
  .call search [.register 0, .register 1, .register 2, .register 3] [6, 7]
    (afterSearch self member lookup update)

def stepBudget (n b nodes entries : ℕ) : ℕ :=
  RegisterResidualSearch.budget n b entries nodes + RegisterMembership.budget n (nodes + 1) +
    RegisterRouteLookup.budget n (nodes + 1) + RegisterResidualTableUpdate.budget n b nodes entries + 100

def budget (n b nodes entries fuel : ℕ) : ℕ := stepBudget n b nodes entries * (fuel + 1)

theorem member_budget_mono (n small large : ℕ) (hle : small ≤ large) :
    RegisterMembership.budget n small ≤ RegisterMembership.budget n large := by
  unfold RegisterMembership.budget
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hle) _

theorem update_budget_mono (n b small large entries : ℕ) (hle : small ≤ large) :
    RegisterResidualTableUpdate.budget n b small entries ≤
      RegisterResidualTableUpdate.budget n b large entries := by
  unfold RegisterResidualTableUpdate.budget RegisterResidualUpdate.budget RegisterArcMembership.budget
  have hm := Nat.mul_le_mul_left (72 * n + 120) hle
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _

theorem compiled (code : Code p) (d : Procedures p) (hm : d.Matches code) (self : Fin p)
    (hself : code self = phaseBody self d.search d.reach.member d.reach.lookup d.tableUpdate)
    {n b : ℕ} {h : Heap} (hh : Valid h) {table : List (Arc n b)} {delta : Bits b}
    {nodes fuel : List (Bits n)} {source sink : Bits n} {tablep dp np sp tp fp : Ptr}
    (ht : TableAt h tablep table) (hd : BitsAt h dp delta) (hn : WordsAt h np nodes)
    (hs : BitsAt h sp source) (hterm : BitsAt h tp sink) (hf : WordsAt h fp fuel) :
    ∃ out result seenp, Extends h out ∧ Valid out ∧
      TableAt out result (ResidualListPhase.phase delta nodes source sink fuel.length table).table ∧
      WordsAt out seenp (ResidualListPhase.phase delta nodes source sink fuel.length table).seen ∧
      Within code h (initialRegisters [.pointer tablep, .pointer dp, .pointer np, .pointer sp, .pointer tp, .pointer fp])
        (code self) [.pointer result, .pointer seenp] out (budget n b nodes.length table.length fuel.length) := by
  obtain ⟨hreach, hsearch, htable, harc, ham, hadjust, hsub, hcomp, hadd⟩ := hm
  have hmember := hreach.2.2.2.1
  have hlookup := hreach.2.2.2.2.1
  have hcmp := hreach.2.2.2.2.2.2.2
  induction fuel generalizing h table tablep dp np sp tp fp with
  | nil =>
    have fcell := WordsAt.nil_iff.mp hf
    obtain ⟨mid, seenp, routep, he, hv, hseen, hroutes, searchRun⟩ :=
      RegisterResidualSearch.compiled code d.reach hreach hh ht hd hn hs
    let regs := initialRegisters [Value.pointer tablep, .pointer dp, .pointer np, .pointer sp, .pointer tp, .pointer fp]
    let r1 := bindResults regs [6, 7] [.pointer seenp, .pointer routep]
    have ret : Within code mid (loadRegisters r1 8 9 15 .nil) stop [.pointer tablep, .pointer seenp] mid 5 := by
      simpa [stop, r1, regs, bindResults, loadRegisters, decoded, initialRegisters, values, Atom.eval] using
        Within.ret code mid (loadRegisters r1 8 9 15 .nil) [.register 0, .register 6]
    have ld := Within.load (address := .register 5) (first := 8) (second := 9) (bit := 15)
      (branches := {CompiledTrie.failCases with
        nil := stop
        cons := .call d.reach.member [.register 4, .register 6] [10]
          (.branch (.register 10) (augmentBody self d.reach.lookup d.tableUpdate) stop)})
      (by simp [Atom.eval, r1, regs, bindResults, initialRegisters]) (he.lookup fcell) ret
    have args : values regs [.register 0, .register 1, .register 2, .register 3] =
        [.pointer tablep, .pointer dp, .pointer np, .pointer sp] := by
      simp [regs, initialRegisters, values, Atom.eval]
    have call := Within.call (procedure := d.search) (regs := regs)
      (arguments := [.register 0, .register 1, .register 2, .register 3]) (results := [6, 7])
      (by simpa only [args, hsearch] using searchRun) ld
    refine ⟨mid, tablep, seenp, he, hv, ht.mono he, hseen, ?_⟩
    simpa only [hself, phaseBody, afterSearch] using call.mono
      (b := budget n b nodes.length table.length ([] : List (Bits n)).length)
      (by simp only [budget, stepBudget, List.length_nil, List.length_cons, Nat.zero_add, Nat.mul_one]; omega)
  | cons f fuel ih =>
    obtain ⟨fhead, ftail, fcell, _, hftail⟩ := WordsAt.cons_iff.mp hf
    obtain ⟨mid, seenp, routep, he1, hv, hseen, hroutes, searchRun⟩ :=
      RegisterResidualSearch.compiled code d.reach hreach hh ht hd hn hs
    let q := ResidualListPhase.search table delta nodes source
    have hq : ResidualListPhase.search table delta nodes source = q := rfl
    have hseenq : WordsAt mid seenp q.seen := hseen
    have hroutesq : RegisterRouteLookup.RoutesAt mid routep q.routes := hroutes
    have hlengths := ResidualListReach.explore_lengths table delta nodes.length (ResidualListReach.initial source)
    have hsl : q.seen.length ≤ nodes.length + 1 := by
      simpa [q, ResidualListPhase.search, ResidualListReach.initial, Nat.add_comm] using hlengths.1
    have hrl : q.routes.length ≤ nodes.length + 1 := by
      simpa [q, ResidualListPhase.search, ResidualListReach.initial, Nat.add_comm] using hlengths.2
    have memberRun := RegisterMembership.compiled code d.reach.member d.reach.cmp hmember hcmp
      (hterm.mono he1) hseenq
    let regs := initialRegisters [Value.pointer tablep, .pointer dp, .pointer np, .pointer sp, .pointer tp, .pointer fp]
    let r1 := bindResults regs [6, 7] [.pointer seenp, .pointer routep]
    let r2 := loadRegisters r1 8 9 15 (.cons fhead ftail)
    let r3 := bindResults r2 [10] [.flag (RegisterMembership.found sink q.seen)]
    have h10 : r3 10 = .flag (RegisterMembership.found sink q.seen) := by simp [r3, bindResults]
    obtain ⟨out, result, cutp, he2, ho, htableOut, hseenOut, cont⟩ :
        ∃ out result cutp, Extends mid out ∧ Valid out ∧
          TableAt out result (ResidualListPhase.phase delta nodes source sink (fuel.length + 1) table).table ∧
          WordsAt out cutp (ResidualListPhase.phase delta nodes source sink (fuel.length + 1) table).seen ∧
          Within code mid r3 (.branch (.register 10) (augmentBody self d.reach.lookup d.tableUpdate) stop)
            [.pointer result, .pointer cutp] out
            (RegisterRouteLookup.budget n (nodes.length + 1) +
              RegisterResidualTableUpdate.budget n b nodes.length table.length +
              budget n b nodes.length table.length fuel.length + 70) := by
      cases hfound : RegisterMembership.found sink q.seen with
      | false =>
        have hph : ResidualListPhase.phase delta nodes source sink (fuel.length + 1) table =
            ⟨table, q.seen⟩ := by
          simp only [ResidualListPhase.phase, hq, hfound, Bool.false_eq_true, if_false]
        refine ⟨mid, tablep, seenp, .refl mid, hv, ?_, ?_, ?_⟩
        · rw [hph]; exact ht.mono he1
        · rw [hph]; exact hseenq
        · have ret : Within code mid r3 stop [.pointer tablep, .pointer seenp] mid 5 := by
            simpa [stop, r3, r2, r1, regs, bindResults, loadRegisters, decoded, initialRegisters, values, Atom.eval] using
              Within.ret code mid r3 [.register 0, .register 6]
          have br := Within.branch (test := .register 10) (b := false)
            (yes := augmentBody self d.reach.lookup d.tableUpdate) (no := stop)
            (by simpa [Atom.eval, hfound] using h10) ret
          exact br.mono (by omega)
      | true =>
        obtain ⟨pathp, hpath, lookupRun⟩ :=
          RegisterRouteLookup.compiled code d.reach.lookup d.reach.cmp hlookup hcmp hv (hterm.mono he1) hroutesq
        have hpathlen : (RegisterRouteLookup.lookup sink q.routes).length ≤ nodes.length :=
          ResidualListReach.search_lookup_length table delta nodes source sink
        obtain ⟨updatedHeap, updatedp, he3, hv3, hupdated, updateRun⟩ :=
          RegisterResidualTableUpdate.compiled code d.tableUpdate d.arcUpdate d.arcMember d.reach.cmp
            d.adjust d.sub d.complement d.add htable harc ham hcmp hadjust hsub hcomp hadd
            hv (ht.mono he1) hpath (hd.mono he1)
        let updated := table.map (fun a => RegisterResidualUpdate.update a (RegisterRouteLookup.lookup sink q.routes) delta)
        have hupdated' : TableAt updatedHeap updatedp updated := hupdated
        have he13 := he1.trans he3
        obtain ⟨out, result, cutp, he4, ho, houtTable, houtSeen, child⟩ := ih hv3 hupdated'
          (hd.mono he13) (hn.mono he13) (hs.mono he13) (hterm.mono he13) (hftail.mono he13)
        let r4 := bindResults r3 [11] [.pointer pathp]
        let r5 := bindResults r4 [12] [.pointer updatedp]
        let r6 := bindResults r5 [13, 14] [.pointer result, .pointer cutp]
        have ret : Within code out r6 (.ret [.register 13, .register 14]) [.pointer result, .pointer cutp] out 5 := by
          simpa [r6, bindResults, values, Atom.eval] using Within.ret code out r6 [.register 13, .register 14]
        have argsR : values r5 [.register 12, .register 1, .register 2, .register 3, .register 4, .register 9] =
            [.pointer updatedp, .pointer dp, .pointer np, .pointer sp, .pointer tp, .pointer ftail] := by
          simp [r5, r4, r3, r2, r1, regs, bindResults, loadRegisters, decoded, initialRegisters, values, Atom.eval]
        have recurse := Within.call (procedure := self) (regs := r5)
          (arguments := [.register 12, .register 1, .register 2, .register 3, .register 4, .register 9]) (results := [13, 14])
          (by simpa only [argsR, updated, List.length_map] using child) ret
        have argsU : values r4 [.register 0, .register 11, .register 1] =
            [.pointer tablep, .pointer pathp, .pointer dp] := by
          simp [r4, r3, r2, r1, regs, bindResults, loadRegisters, decoded, initialRegisters, values, Atom.eval]
        have ucall := Within.call (procedure := d.tableUpdate) (regs := r4)
          (arguments := [.register 0, .register 11, .register 1]) (results := [12])
          (by simpa only [argsU] using updateRun.mono (update_budget_mono n b _ nodes.length table.length hpathlen)) recurse
        have argsL : values r3 [.register 4, .register 7] = [.pointer tp, .pointer routep] := by
          simp [r3, r2, r1, regs, bindResults, loadRegisters, decoded, initialRegisters, values, Atom.eval]
        have lcall := Within.call (procedure := d.reach.lookup) (regs := r3)
          (arguments := [.register 4, .register 7]) (results := [11])
          (by simpa only [argsL] using lookupRun.mono (RegisterResidualReach.lookup_budget_mono n _ _ hrl)) ucall
        have br := Within.branch (test := .register 10) (b := true)
          (yes := augmentBody self d.reach.lookup d.tableUpdate) (no := stop)
          (by simpa [Atom.eval, hfound] using h10) lcall
        have hph : ResidualListPhase.phase delta nodes source sink (fuel.length + 1) table =
            ResidualListPhase.phase delta nodes source sink fuel.length updated := by
          simp only [ResidualListPhase.phase, hq, hfound, if_true, updated]
        refine ⟨out, result, cutp, he3.trans he4, ho, ?_, ?_, ?_⟩
        · rw [hph]; exact houtTable
        · rw [hph]; exact houtSeen
        · exact br.mono (by simp only [List.length_cons, List.length_nil]; omega)
    have argsM : values r2 [.register 4, .register 6] = [.pointer tp, .pointer seenp] := by
      simp [r2, r1, regs, loadRegisters, decoded, bindResults, initialRegisters, values, Atom.eval]
    have mcall := Within.call (procedure := d.reach.member) (regs := r2)
      (arguments := [.register 4, .register 6]) (results := [10])
      (by simpa only [argsM] using memberRun.mono (member_budget_mono n _ _ hsl)) cont
    have ld := Within.load (address := .register 5) (first := 8) (second := 9) (bit := 15)
      (branches := {CompiledTrie.failCases with
        nil := stop
        cons := .call d.reach.member [.register 4, .register 6] [10]
          (.branch (.register 10) (augmentBody self d.reach.lookup d.tableUpdate) stop)})
      (by simp [Atom.eval, r1, regs, bindResults, initialRegisters]) (he1.lookup fcell) mcall
    have argsS : values regs [.register 0, .register 1, .register 2, .register 3] =
        [.pointer tablep, .pointer dp, .pointer np, .pointer sp] := by
      simp [regs, initialRegisters, values, Atom.eval]
    have scall := Within.call (procedure := d.search) (regs := regs)
      (arguments := [.register 0, .register 1, .register 2, .register 3]) (results := [6, 7])
      (by simpa only [argsS, hsearch] using searchRun) ld
    refine ⟨out, result, cutp, he1.trans he2, ho, htableOut, hseenOut, ?_⟩
    simpa only [hself, phaseBody, afterSearch] using scall.mono
      (b := budget n b nodes.length table.length (f :: fuel).length)
      (by simp only [budget, stepBudget, List.length_cons, List.length_nil, Nat.mul_add, Nat.mul_one]; omega)

end WeightedMIS.RegisterResidualPhase
