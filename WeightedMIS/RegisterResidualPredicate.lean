module

public import WeightedMIS.ResidualWords
public import WeightedMIS.RegisterMembership

/-! # Closed register test for a residual arc crossing the reached set -/

@[expose] public section

namespace WeightedMIS.RegisterResidualPredicate

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.ExpandedWords WeightedMIS.ResidualWords

variable {p : ℕ}

def accepts {n b : ℕ} (seen : List (Bits n)) (d : Bits b) (a : Arc n b) : Bool :=
  RegisterMembership.found a.source seen && !RegisterMembership.found a.target seen &&
    !(decide ((Bits.compare a.capacity d).1 = .lt))

def result (b : Bool) : Command p := .ret [.flag b, .register 3, .register 5]

def finalBody : Command p :=
  .branch (.register 7)
    (.branch (.register 8) (result false)
      (.branch (.register 9) (result false) (result true)))
    (result false)

/-- Inputs: reached word list, arc record, scale word. Outputs: acceptance
flag followed by the two endpoint word pointers. -/
def predicateBody (member cmp : Fin p) : Command p :=
  .load (.register 1) 3 4 15 { CompiledTrie.failCases with
    pair := .load (.register 4) 5 6 15 { CompiledTrie.failCases with
      pair := .call member [.register 3, .register 0] [7]
        (.call member [.register 5, .register 0] [8]
          (.call cmp [.register 6, .register 2] [9, 10] finalBody)) } }

theorem final_compiled (code : Code p) (h : Heap) (regs : Registers)
    (u v lt : Bool) (sp tp : Ptr)
    (h7 : regs 7 = .flag u) (h8 : regs 8 = .flag v) (h9 : regs 9 = .flag lt)
    (h3 : regs 3 = .pointer sp) (h5 : regs 5 = .pointer tp) :
    Within code h regs finalBody [.flag (u && !v && !lt), .pointer sp, .pointer tp] h 16 := by
  have ret (b : Bool) : Within code h regs (result b)
      [.flag b, .pointer sp, .pointer tp] h 7 := by
    simpa [result, values, Atom.eval, h3, h5] using
      Within.ret code h regs [.flag b, .register 3, .register 5]
  have inner : Within code h regs (.branch (.register 9) (result false) (result true))
      [.flag (!lt), .pointer sp, .pointer tp] h 10 := by
    cases lt <;> apply Within.branch (test := .register 9) (budget := 7)
      (by simpa [Atom.eval] using h9) <;> simpa using ret _
  have mid : Within code h regs
      (.branch (.register 8) (result false)
        (.branch (.register 9) (result false) (result true)))
      [.flag (!v && !lt), .pointer sp, .pointer tp] h 13 := by
    cases v
    · simpa using Within.branch (test := .register 8) (b := false)
        (yes := result false) (no := .branch (.register 9) (result false) (result true))
        (by simpa [Atom.eval] using h8) inner
    · simpa using Within.branch (test := .register 8) (b := true)
        (yes := result false) (no := .branch (.register 9) (result false) (result true))
        (by simpa [Atom.eval] using h8) ((ret false).mono (by omega : 7 ≤ 10))
  cases u
  · simpa [finalBody] using Within.branch (test := .register 7) (b := false)
      (yes := .branch (.register 8) (result false)
        (.branch (.register 9) (result false) (result true))) (no := result false)
      (by simpa [Atom.eval] using h7) ((ret false).mono (by omega : 7 ≤ 13))
  · simpa [finalBody] using Within.branch (test := .register 7) (b := true)
      (yes := .branch (.register 8) (result false)
        (.branch (.register 9) (result false) (result true))) (no := result false)
      (by simpa [Atom.eval] using h7) mid

def budget (n b length : ℕ) : ℕ :=
  2 * RegisterMembership.budget n length + 36 * b + 76

theorem compiled (code : Code p) (member cmp : Fin p)
    (hm : code member = RegisterMembership.membershipBody member cmp)
    (hc : code cmp = RegisterComparator.comparatorBody cmp)
    {n b : ℕ} {h : Heap} {seen : List (Bits n)} {d : Bits b} {a : Arc n b}
    {seenp ap dp : Ptr} (hs : WordsAt h seenp seen) (ha : ArcAt h ap a) (hd : BitsAt h dp d) :
    ∃ sp tp, BitsAt h sp a.source ∧ BitsAt h tp a.target ∧
      Within code h (initialRegisters [.pointer seenp, .pointer ap, .pointer dp])
        (predicateBody member cmp) [.flag (accepts seen d a), .pointer sp, .pointer tp]
        h (budget n b seen.length) := by
  obtain ⟨sp, tail, tp, cp, hac, htail, hsrc, htgt, hcap⟩ := ha
  have runS := RegisterMembership.compiled code member cmp hm hc hsrc hs
  have runT := RegisterMembership.compiled code member cmp hm hc htgt hs
  have runC := RegisterComparator.compiled code cmp hc hcap hd
  let regs := initialRegisters [Value.pointer seenp, .pointer ap, .pointer dp]
  let r1 := loadRegisters regs 3 4 15 (.pair sp tail)
  let r2 := loadRegisters r1 5 6 15 (.pair tp cp)
  let r3 := bindResults r2 [7] [.flag (RegisterMembership.found a.source seen)]
  let r4 := bindResults r3 [8] [.flag (RegisterMembership.found a.target seen)]
  let r5 := bindResults r4 [9, 10] (RegisterComparator.flags (Bits.compare a.capacity d).1)
  have last := final_compiled code h r5
    (RegisterMembership.found a.source seen) (RegisterMembership.found a.target seen)
    (decide ((Bits.compare a.capacity d).1 = .lt)) sp tp
    (by simp [r5, r4, r3, bindResults, RegisterComparator.flags])
    (by simp [r5, r4, bindResults, RegisterComparator.flags])
    (by simp [r5, bindResults, RegisterComparator.flags])
    (by simp [r5, r4, r3, r2, r1, bindResults, loadRegisters, decoded, RegisterComparator.flags])
    (by simp [r5, r4, r3, r2, bindResults, loadRegisters, decoded, RegisterComparator.flags])
  have cargs : values r4 [.register 6, .register 2] = [.pointer cp, .pointer dp] := by
    simp [r4, r3, r2, r1, regs, bindResults, loadRegisters, decoded, initialRegisters, values, Atom.eval]
  have cc := Within.call (procedure := cmp) (regs := r4)
    (arguments := [.register 6, .register 2]) (results := [9, 10])
    (by simpa only [cargs] using runC) last
  have targs : values r3 [.register 5, .register 0] = [.pointer tp, .pointer seenp] := by
    simp [r3, r2, r1, regs, bindResults, loadRegisters, decoded, initialRegisters, values, Atom.eval]
  have tc := Within.call (procedure := member) (regs := r3)
    (arguments := [.register 5, .register 0]) (results := [8])
    (by simpa only [targs] using runT) cc
  have sargs : values r2 [.register 3, .register 0] = [.pointer sp, .pointer seenp] := by
    simp [r2, r1, regs, loadRegisters, decoded, initialRegisters, values, Atom.eval]
  have sc := Within.call (procedure := member) (regs := r2)
    (arguments := [.register 3, .register 0]) (results := [7])
    (by simpa only [sargs] using runS) tc
  have ld2 := Within.load (address := .register 4) (first := 5) (second := 6) (bit := 15)
    (branches := {CompiledTrie.failCases with
      pair := .call member [.register 3, .register 0] [7]
        (.call member [.register 5, .register 0] [8]
          (.call cmp [.register 6, .register 2] [9, 10] finalBody))})
    (by simp [Atom.eval, r1, loadRegisters, decoded]) htail sc
  have ld1 := Within.load (address := .register 1) (first := 3) (second := 4) (bit := 15)
    (branches := {CompiledTrie.failCases with
      pair := .load (.register 4) 5 6 15 {CompiledTrie.failCases with
        pair := .call member [.register 3, .register 0] [7]
          (.call member [.register 5, .register 0] [8]
            (.call cmp [.register 6, .register 2] [9, 10] finalBody))}})
    (by simp [Atom.eval, regs, initialRegisters]) hac ld2
  refine ⟨sp, tp, hsrc, htgt, ?_⟩
  simpa only [predicateBody, accepts] using ld1.mono
    (b := budget n b seen.length) (by simp [budget]; omega)

theorem accepts_iff {n b : ℕ} (seen : List (Bits n)) (d : Bits b) (a : Arc n b) :
    accepts seen d a = true ↔
      (∃ key ∈ seen, key.value = a.source.value) ∧
      (¬ ∃ key ∈ seen, key.value = a.target.value) ∧ d.value ≤ a.capacity.value := by
  simp [accepts, Bool.eq_false_iff, RegisterMembership.found_iff,
    (Bits.compare_correct a.capacity d).1, and_assoc]

end WeightedMIS.RegisterResidualPredicate
