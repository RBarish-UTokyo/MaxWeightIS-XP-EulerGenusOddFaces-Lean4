module

public import WeightedMIS.RegisterMembership
public import WeightedMIS.RegisterComparator
public import WeightedMIS.CompiledTrie

/-!
# Finite membership scans of actual stored flag records

Each list item is an actual flag record. Two fixed pointer loads expose its
immutable key, then the compiled binary comparator decides membership. The
result is exact key membership and the heap is unchanged.
-/

@[expose] public section

namespace WeightedMIS.RegisterFlagMembership

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch WeightedMIS.ExpandedWords

variable {p : ℕ}

open WeightedMIS.RegisterMembership (found found_iff)

/-- A flag record stores its key in the first field of its information record. -/
def KeyAt {n : ℕ} (h : Heap) (p : Ptr) (key : Bits n) : Prop :=
  ∃ info next kp mirror, h[p]? = some (.pair info next) ∧
    h[info]? = some (.pair kp mirror) ∧ BitsAt h kp key

def FlagWordsAt {n : ℕ} (h : Heap) (p : Ptr) (keys : List (Bits n)) : Prop :=
  ∃ pointers, ListAt h p pointers ∧ List.Forall₂ (KeyAt h) pointers keys

theorem KeyAt.mono {n : ℕ} {h h' : Heap} (ext : Extends h h') {p : Ptr} {key : Bits n}
    (hk : KeyAt h p key) : KeyAt h' p key := by
  obtain ⟨info, next, kp, mirror, hc, hi, hkey⟩ := hk
  exact ⟨info, next, kp, mirror, ext.lookup hc, ext.lookup hi, hkey.mono ext⟩

theorem FlagWordsAt.mono {n : ℕ} {h h' : Heap} (ext : Extends h h') {p : Ptr}
    {keys : List (Bits n)} (hk : FlagWordsAt h p keys) : FlagWordsAt h' p keys := by
  obtain ⟨ps, hl, hr⟩ := hk
  exact ⟨ps, hl.mono ext, hr.imp (fun _ _ hx => hx.mono ext)⟩

def recurseBody (self : Fin p) : Command p :=
  .call self [.register 0, .register 3] [7] (.ret [.register 7])

def compareBody (self cmp : Fin p) : Command p :=
  .call cmp [.register 0, .register 2] [5, 6]
    (.branch (.register 6) (.ret [.flag true]) (recurseBody self))

def recordBody (self cmp : Fin p) : Command p :=
  .load (.register 2) 8 9 10 { CompiledTrie.failCases with
    pair := .load (.register 8) 2 11 12 { CompiledTrie.failCases with
      pair := compareBody self cmp } }

/-- Arguments are the query word and the list; the sole result is a flag. -/
def membershipBody (self cmp : Fin p) : Command p :=
  .load (.register 1) 2 3 4 { CompiledTrie.failCases with
    nil := .ret [.flag false]
    cons := recordBody self cmp }

def budget (width length : ℕ) : ℕ := (36 * width + 80) * length + 13

theorem compiled (code : Code p) (self cmp : Fin p)
    (hself : code self = membershipBody self cmp)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    {n : ℕ} {h : Heap} {qp lp : Ptr} {query : Bits n} {keys : List (Bits n)}
    (hq : BitsAt h qp query) (hk : FlagWordsAt h lp keys) :
    Within code h (initialRegisters [.pointer qp, .pointer lp]) (code self)
      [.flag (found query keys)] h (budget n keys.length) := by
  induction keys generalizing lp with
  | nil =>
    obtain ⟨ps, hl, hr⟩ := hk
    cases hr
    cases hl with
    | nil cell =>
      rw [hself]
      let regs := initialRegisters [Value.pointer qp, .pointer lp]
      have last := Within.ret code h (loadRegisters regs 2 3 4 .nil) [.flag false]
      have load := Within.load (address := .register 1) (first := 2) (second := 3) (bit := 4)
        (branches := { CompiledTrie.failCases with
          nil := .ret [.flag false], cons := recordBody self cmp })
        (by simp [regs, Atom.eval, initialRegisters]) cell last
      simpa [membershipBody, found, budget, values, Atom.eval] using load
  | cons key keys ih =>
    obtain ⟨ps, hl, hr⟩ := hk
    cases hr with
    | @cons record _ pointers _ hrecord hrecords =>
      cases hl with
      | @cons _ _ tail _ cell rest =>
        obtain ⟨info, next, kp, mirror, recordCell, infoCell, hkey⟩ := hrecord
        have htail : FlagWordsAt h tail keys := ⟨_, rest, hrecords⟩
        have child := ih htail
        have compare := RegisterComparator.compiled code cmp hcmp hq hkey
        let regs := initialRegisters [Value.pointer qp, .pointer lp]
        let loaded := loadRegisters regs 2 3 4 (.cons record tail)
        let recLoaded := loadRegisters loaded 8 9 10 (.pair info next)
        let keyLoaded := loadRegisters recLoaded 2 11 12 (.pair kp mirror)
        let compared := bindResults keyLoaded [5, 6] (RegisterComparator.flags (Bits.compare query key).1)
        have rargs : values compared [.register 0, .register 3] = [.pointer qp, .pointer tail] := by
          simp [compared, keyLoaded, recLoaded, loaded, regs, bindResults, loadRegisters, decoded,
            initialRegisters, values, Atom.eval, RegisterComparator.flags]
        have last : Within code h
            (bindResults compared [7] [.flag (found query keys)]) (.ret [.register 7])
            [.flag (found query keys)] h 3 := by
          simpa [bindResults, values, Atom.eval] using Within.ret code h
            (bindResults compared [7] [.flag (found query keys)]) [.register 7]
        have recursion := Within.call (procedure := self) (regs := compared)
          (arguments := [.register 0, .register 3]) (results := [7])
          (by simpa only [rargs] using child) last
        have eqFlag : decide ((Bits.compare query key).1 = .eq) =
            decide (key.value = query.value) := by
          simp only [(Bits.compare_correct query key).2.1, eq_comm]
        have branch : Within code h compared
            (.branch (.register 6) (.ret [.flag true]) (recurseBody self))
            [.flag (found query (key :: keys))] h (budget n keys.length + 11) := by
          by_cases heq : key.value = query.value
          · have terminal := Within.ret code h compared [.flag true]
            have hb := Within.branch (test := .register 6) (b := true)
              (yes := .ret [.flag true]) (no := recurseBody self)
              (by simp [compared, bindResults, Atom.eval, RegisterComparator.flags, eqFlag, heq])
              terminal
            have hout : found query (key :: keys) = true := by simp [found, heq]
            rw [hout]
            exact hb.mono (by simp [budget])
          · have hb := Within.branch (test := .register 6) (b := false)
              (yes := .ret [.flag true]) (no := recurseBody self)
              (by simp [compared, bindResults, Atom.eval, RegisterComparator.flags, eqFlag, heq])
              recursion
            convert hb using 1 <;> simp [recurseBody, found, heq] <;> omega
        have cargs : values keyLoaded [.register 0, .register 2] = [.pointer qp, .pointer kp] := by
          simp [keyLoaded, recLoaded, loaded, regs, loadRegisters, decoded, initialRegisters, values, Atom.eval]
        have call := Within.call (procedure := cmp) (regs := keyLoaded)
          (arguments := [.register 0, .register 2]) (results := [5, 6])
          (by simpa only [cargs] using compare) branch
        have keyLoad := Within.load (address := .register 8) (first := 2) (second := 11) (bit := 12)
          (branches := {CompiledTrie.failCases with pair := compareBody self cmp})
          (by simp [Atom.eval, recLoaded, loadRegisters, decoded]) infoCell call
        have recordLoad := Within.load (address := .register 2) (first := 8) (second := 9) (bit := 10)
          (branches := {CompiledTrie.failCases with
            pair := .load (.register 8) 2 11 12 {CompiledTrie.failCases with pair := compareBody self cmp}})
          (by simp [Atom.eval, loaded, loadRegisters, decoded]) recordCell keyLoad
        have load := Within.load (address := .register 1) (first := 2) (second := 3) (bit := 4)
          (branches := { CompiledTrie.failCases with
            nil := .ret [.flag false], cons := recordBody self cmp })
          (by simp [regs, Atom.eval, initialRegisters]) cell recordLoad
        rw [hself]
        exact load.mono (by simp [budget, List.length_cons, Nat.mul_add]; omega)



end WeightedMIS.RegisterFlagMembership
