module

public import WeightedMIS.RegisterFaceBlock
public import WeightedMIS.RegisterFlagMembership
public import WeightedMIS.FrontCycleEnumeration

/-!
# Finite first-unseen enumeration of stored facial roots

The program scans actual stored flag records, tests their actual binary keys,
traces both boundary orientations when a new face is encountered, and shares
the accumulated seen list. The output is exactly the deterministic roots used
to construct the actual even-face matrix.
-/

@[expose] public section

namespace WeightedMIS.RegisterFaceEnumeration

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.CompiledTrie
open WeightedMIS.EfficientSearch WeightedMIS.FiniteCycleEnumeration
open WeightedMIS.RegisterPermutationMirror WeightedMIS.RegisterFlagMembership

variable {p : ℕ}

def skipBody (self : Fin p) : Command p :=
  .call self [.register 5, .register 1, .register 2, .register 3] [14] (.ret [.register 14])

def freshBody (self block : Fin p) : Command p :=
  .call block [.register 2, .register 4, .register 1] [14]
    (.call self [.register 5, .register 14, .register 2, .register 3] [15]
      (.allocate 13 (.cons (.register 4) (.register 15)) (.ret [.register 13])))

def afterInfo (self member block : Fin p) : Command p :=
  .call member [.register 10, .register 1] [13]
    (.branch (.register 13) (skipBody self) (freshBody self block))

/-- Arguments are the input flag order, seen flags, traversal fuel, and output tail. -/
def enumerationBody (self member block : Fin p) : Command p :=
  .load (.register 0) 4 5 6 {
    failCases with
    nil := .ret [.register 3]
    cons := .load (.register 4) 7 8 9 {
      failCases with
      pair := .load (.register 7) 10 11 12 {failCases with pair := afterInfo self member block}
    }
  }

/-- A coarse uniform bound on all membership scans and boundary traversals. -/
def budget (width count cap length : ℕ) : ℕ :=
  length * ((36 * width + 80) * cap + 86 * count + 130) + 13

theorem mapped_records {α : Type*} {width : ℕ} {h : Heap} {pointer : α → Ptr}
    {key : α → Bits width} (hk : ∀ x, KeyAt h (pointer x) (key x)) (xs : List α) :
    List.Forall₂ (KeyAt h) (xs.map pointer) (xs.map key) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (hk x) ih

theorem found_map_iff {α : Type*} {width : ℕ} (key : α → Bits width)
    (hinj : Function.Injective (fun x => (key x).value)) (x : α) (seen : List α) :
    RegisterMembership.found (key x) (seen.map key) = true ↔ x ∈ seen := by
  rw [RegisterMembership.found_iff]
  constructor
  · rintro ⟨word, hw, he⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hw
    exact hinj he ▸ hy
  · intro hx
    exact ⟨key x, List.mem_map.mpr ⟨x, hx, rfl⟩, rfl⟩

/-- Exact compilation of the first-unseen scan with a uniform cap on its
accumulated actual seen-flag list. -/
theorem compiled {α : Type*} [DecidableEq α] {width : ℕ}
    (code : Code p) (self member cmp block ordinary mirrored : Fin p)
    (selfCode : code self = enumerationBody self member block)
    (memberCode : code member = RegisterFlagMembership.membershipBody member cmp)
    (cmpCode : code cmp = RegisterComparator.comparatorBody cmp)
    (blockCode : code block = RegisterFaceBlock.blockBody ordinary mirrored)
    (ordinaryCode : code ordinary = RegisterPermutationTrace.traceBody ordinary)
    (mirroredCode : code mirrored = RegisterPermutationMirror.traceBody mirrored)
    (next : Equiv.Perm α) (mirror : α → α) (pointer : α → Ptr) (key : α → Bits width)
    (hinj : Function.Injective (fun x => (key x).value)) (order : List α)
    {h : Heap} (hh : Valid h) (graph : FlagLinksAt next mirror pointer h)
    (keys : ∀ x, KeyAt h (pointer x) (key x))
    {orderPtr seenPtr fuel tail : Ptr} {seen : List α} {fuelItems tailItems : List Ptr}
    (orderAt : ListAt h orderPtr (order.map pointer))
    (seenAt : ListAt h seenPtr (seen.map pointer))
    (fuelAt : ListAt h fuel fuelItems) (tailAt : ListAt h tail tailItems)
    (cap : ℕ) (hcap : seen.length + 2 * fuelItems.length * order.length ≤ cap) :
    ∃ out final, Within code h
      (initialRegisters [.pointer orderPtr, .pointer seenPtr, .pointer fuel, .pointer tail])
      (code self) [.pointer out] final (budget width fuelItems.length cap order.length) ∧
      Valid final ∧ Extends h final ∧ ListAt final out
        ((frontRepresentatives (bothTrace next mirror fuelItems.length) seen order).map pointer ++ tailItems) := by
  induction order generalizing h orderPtr seenPtr seen with
  | nil =>
    cases orderAt with
    | nil cell =>
      let regs := initialRegisters [Value.pointer orderPtr, .pointer seenPtr, .pointer fuel, .pointer tail]
      let loaded := loadRegisters regs 4 5 6 .nil
      have last : Within code h loaded (.ret [.register 3]) [.pointer tail] h 3 := by
        simpa [values, Atom.eval, loaded, regs, loadRegisters, decoded, initialRegisters] using
          Within.ret code h loaded [.register 3]
      have run := Within.load (address := .register 0) (first := 4) (second := 5) (bit := 6)
        (branches := {failCases with
          nil := .ret [.register 3]
          cons := .load (.register 4) 7 8 9 {
            failCases with
            pair := .load (.register 7) 10 11 12 {failCases with pair := afterInfo self member block}
          }})
        (by simp [Atom.eval, regs, initialRegisters]) cell last
      refine ⟨tail, h, ?_, hh, Extends.refl h, ?_⟩
      · simpa [selfCode, enumerationBody, budget] using run
      · simpa [frontRepresentatives] using tailAt
  | cons x order ih =>
    cases orderAt with
    | @cons _ _ orderTail _ orderCell orderRest =>
      obtain ⟨info, nextPtr, keyPtr, mirrorPtr, flagCell, infoCell, keyAt⟩ := keys x
      have seenKeys : FlagWordsAt h seenPtr (seen.map key) :=
        ⟨seen.map pointer, seenAt, mapped_records keys seen⟩
      have membership := RegisterFlagMembership.compiled code member cmp memberCode cmpCode keyAt seenKeys
      let r0 := initialRegisters [Value.pointer orderPtr, .pointer seenPtr, .pointer fuel, .pointer tail]
      let r1 := loadRegisters r0 4 5 6 (.cons (pointer x) orderTail)
      let r2 := loadRegisters r1 7 8 9 (.pair info nextPtr)
      let r3 := loadRegisters r2 10 11 12 (.pair keyPtr mirrorPtr)
      let r4 := bindResults r3 [13] [.flag (RegisterMembership.found (key x) (seen.map key))]
      have membership' : Within code h
          (initialRegisters (values r3 [.register 10, .register 1])) (code member)
          [.flag (RegisterMembership.found (key x) (seen.map key))] h
          ((36 * width + 80) * seen.length + 13) := by
        simpa [RegisterFlagMembership.budget, values, Atom.eval, r3, r2, r1, r0,
          loadRegisters, decoded, initialRegisters] using membership
      have branchResult : ∃ out final, Within code h r4
          (.branch (.register 13) (skipBody self) (freshBody self block)) [.pointer out] final
          (budget width fuelItems.length cap order.length + 86 * fuelItems.length + 73) ∧
          Valid final ∧ Extends h final ∧ ListAt final out
            ((frontRepresentatives (bothTrace next mirror fuelItems.length) seen (x :: order)).map pointer ++ tailItems) := by
        by_cases hx : x ∈ seen
        · have hfound := (found_map_iff key hinj x seen).mpr hx
          obtain ⟨out, final, child, valid, ext, result⟩ := ih hh graph keys orderRest seenAt fuelAt tailAt
            (by simp only [List.length_cons] at hcap; nlinarith)
          let returned := bindResults r4 [14] [Value.pointer out]
          have last : Within code final returned (.ret [.register 14]) [.pointer out] final 3 := by
            simpa [values, Atom.eval, returned, bindResults] using Within.ret code final returned [.register 14]
          have call := Within.call (procedure := self) (regs := r4)
            (arguments := [.register 5, .register 1, .register 2, .register 3]) (results := [14])
            (by simpa [values, Atom.eval, r4, r3, r2, r1, r0, bindResults,
              loadRegisters, decoded, initialRegisters] using child) last
          have branch := Within.branch (test := .register 13) (b := true)
            (yes := skipBody self) (no := freshBody self block)
            (by simp [Atom.eval, r4, bindResults, hfound]) call
          exact ⟨out, final, branch.mono (by simp only [List.length_cons, List.length_nil]; omega),
            valid, ext, by simpa [frontRepresentatives, hx] using result⟩
        · have hfound : RegisterMembership.found (key x) (seen.map key) = false := by
            apply Bool.eq_false_iff.mpr
            exact fun hf => hx ((found_map_iff key hinj x seen).mp hf)
          obtain ⟨midPtr, mid, traced, midValid, midExt, midAt⟩ := RegisterFaceBlock.compiled
            code ordinary mirrored ordinaryCode mirroredCode next mirror pointer hh graph fuelAt seenAt x
          have midAt' : ListAt mid midPtr
              ((bothTrace next mirror fuelItems.length x ++ seen).map pointer) := by
            simpa only [List.map_append] using midAt
          have nextCap : (bothTrace next mirror fuelItems.length x ++ seen).length +
              2 * fuelItems.length * order.length ≤ cap := by
            rw [List.length_append, bothTrace_length]
            simp only [List.length_cons] at hcap
            nlinarith
          obtain ⟨out, final, child, valid, finalExt, result⟩ := ih midValid (graph.mono midExt)
            (fun y => (keys y).mono midExt) (orderRest.mono midExt) midAt'
            (fuelAt.mono midExt) (tailAt.mono midExt) nextCap
          have allocated : pointer x < final.length :=
            lt_of_lt_of_le (List.getElem?_eq_some_iff.mp flagCell |>.1) (midExt.trans finalExt).length_le
          obtain ⟨safe, prepended⟩ := allocate_cons valid allocated result
          let endHeap := final ++ [.cons (pointer x) out]
          let r5 := bindResults r4 [14] [Value.pointer midPtr]
          let r6 := bindResults r5 [15] [Value.pointer out]
          have last : Within code endHeap (Function.update r6 13 (.pointer final.length))
              (.ret [.register 13]) [.pointer final.length] endHeap 3 := by
            simpa [values, Atom.eval] using
              Within.ret code endHeap (Function.update r6 13 (.pointer final.length)) [.register 13]
          have allocation := Within.allocate (dst := 13)
            (expr := .cons (.register 4) (.register 15)) (c := .cons (pointer x) out)
            (by simp [CellExpr.eval, Atom.eval, r6, r5, r4, r3, r2, r1, bindResults,
              loadRegisters, decoded, Value.asPointer]) last
          have recurse := Within.call (procedure := self) (regs := r5)
            (arguments := [.register 5, .register 14, .register 2, .register 3]) (results := [15])
            (by simpa [values, Atom.eval, r5, r4, r3, r2, r1, r0, bindResults,
              loadRegisters, decoded, initialRegisters] using child) allocation
          have blockCall := Within.call (procedure := block) (regs := r4)
            (arguments := [.register 2, .register 4, .register 1]) (results := [14])
            (by simpa [blockCode, values, Atom.eval, r4, r3, r2, r1, r0, bindResults,
              loadRegisters, decoded, initialRegisters] using traced) recurse
          have branch := Within.branch (test := .register 13) (b := false)
            (yes := skipBody self) (no := freshBody self block)
            (by simp [Atom.eval, r4, bindResults, hfound]) blockCall
          refine ⟨final.length, endHeap, ?_, safe.2.1, (midExt.trans finalExt).trans safe.1, ?_⟩
          · exact branch.mono (by simp [CellExpr.args]; omega)
          · simpa [frontRepresentatives, hx, Program.allocate] using prepended
      obtain ⟨out, final, branch, valid, ext, result⟩ := branchResult
      have memberCall := Within.call (procedure := member) (regs := r3)
        (arguments := [.register 10, .register 1]) (results := [13]) membership' branch
      have infoLoad := Within.load (address := .register 7) (first := 10) (second := 11) (bit := 12)
        (branches := {failCases with pair := afterInfo self member block})
        (by simp [Atom.eval, r2, loadRegisters, decoded]) infoCell memberCall
      have flagLoad := Within.load (address := .register 4) (first := 7) (second := 8) (bit := 9)
        (branches := {failCases with
          pair := .load (.register 7) 10 11 12 {failCases with pair := afterInfo self member block}})
        (by simp [Atom.eval, r1, loadRegisters, decoded]) flagCell infoLoad
      have listLoad := Within.load (address := .register 0) (first := 4) (second := 5) (bit := 6)
        (branches := {failCases with
          nil := .ret [.register 3]
          cons := .load (.register 4) 7 8 9 {
            failCases with
            pair := .load (.register 7) 10 11 12 {failCases with pair := afterInfo self member block}
          }})
        (by simp [Atom.eval, r0, initialRegisters]) orderCell flagLoad
      refine ⟨out, final, ?_, valid, ext, result⟩
      rw [selfCode]
      apply listLoad.mono
      have hs : seen.length ≤ cap := by omega
      have hm := Nat.mul_le_mul_left (36 * width + 80) hs
      simp [budget, List.length_cons]
      nlinarith

end WeightedMIS.RegisterFaceEnumeration
