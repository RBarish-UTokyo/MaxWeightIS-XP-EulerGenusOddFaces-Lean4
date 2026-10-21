module

public import WeightedMIS.ResidualWords
public import WeightedMIS.RegisterMembership

/-! # Lookup in a materialized table of vertex routes -/

@[expose] public section

namespace WeightedMIS.RegisterRouteLookup

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch WeightedMIS.EfficientSearch.Pointer
open WeightedMIS.ResidualWords

abbrev Route (n b : ℕ) := Bits n × List (Arc n b)

def RouteAt {n b : ℕ} (h : Heap) (p : Ptr) (entry : Route n b) : Prop :=
  ∃ kp pp, h[p]? = some (.pair kp pp) ∧ BitsAt h kp entry.1 ∧ TableAt h pp entry.2

def RoutesAt {n b : ℕ} (h : Heap) (p : Ptr) (routes : List (Route n b)) : Prop :=
  ListRep RouteAt h p routes

theorem RouteAt.allocated {n b : ℕ} {h : Heap} {p : Ptr} {entry : Route n b}
    (he : RouteAt h p entry) : p < h.length := by
  obtain ⟨_, _, hc, _⟩ := he
  exact List.getElem?_eq_some_iff.mp hc |>.1

theorem RouteAt.mono {n b : ℕ} {h h' : Heap} (he : Extends h h')
    {p : Ptr} {entry : Route n b} (hr : RouteAt h p entry) : RouteAt h' p entry := by
  obtain ⟨kp, pp, hc, hk, hp⟩ := hr
  exact ⟨kp, pp, he.lookup hc, hk.mono he, hp.mono he⟩

theorem RoutesAt.allocated {n b : ℕ} {h : Heap} {p : Ptr} {routes : List (Route n b)}
    (hr : RoutesAt h p routes) : p < h.length := ListRep.allocated hr

theorem RoutesAt.mono {n b : ℕ} {h h' : Heap} (he : Extends h h')
    {p : Ptr} {routes : List (Route n b)} (hr : RoutesAt h p routes) : RoutesAt h' p routes :=
  ListRep.mono he (fun _ _ h => h.mono he) hr

theorem RoutesAt.nil {n b : ℕ} {h : Heap} {p : Ptr} (hc : h[p]? = some .nil) :
    RoutesAt h p ([] : List (Route n b)) := ⟨[], .nil hc, .nil⟩

theorem RoutesAt.cons {n b : ℕ} {h : Heap} {p head tail : Ptr}
    {entry : Route n b} {routes : List (Route n b)}
    (hc : h[p]? = some (.cons head tail)) (hh : RouteAt h head entry)
    (ht : RoutesAt h tail routes) : RoutesAt h p (entry :: routes) := by
  obtain ⟨ps, hp, hw⟩ := ht
  exact ⟨head :: ps, .cons hc hp, .cons hh hw⟩

theorem RoutesAt.nil_iff {n b : ℕ} {h : Heap} {p : Ptr} :
    RoutesAt h p ([] : List (Route n b)) ↔ h[p]? = some .nil := by
  constructor
  · rintro ⟨ps, hp, hw⟩
    cases hw
    cases hp with
    | nil hc => exact hc
  · exact RoutesAt.nil

theorem RoutesAt.cons_iff {n b : ℕ} {h : Heap} {p : Ptr}
    {entry : Route n b} {routes : List (Route n b)} :
    RoutesAt h p (entry :: routes) ↔ ∃ head tail, h[p]? = some (.cons head tail) ∧
      RouteAt h head entry ∧ RoutesAt h tail routes := by
  constructor
  · rintro ⟨ps, hp, hw⟩
    cases hw with
    | cons head rest =>
      cases hp with
      | cons hc ht => exact ⟨_, _, hc, head, _, ht, rest⟩
  · rintro ⟨head, tail, hc, hh, ht⟩
    exact RoutesAt.cons hc hh ht

def lookup {n b : ℕ} (query : Bits n) : List (Route n b) → List (Arc n b)
  | [] => []
  | entry :: rest => if query.value = entry.1.value then entry.2 else lookup query rest

variable {p : ℕ}

def recurseBody (self : Fin p) : Command p :=
  .call self [.register 0, .register 3] [8] (.ret [.register 8])

def compareBody (self cmp : Fin p) : Command p :=
  .call cmp [.register 0, .register 4] [6, 7]
    (.branch (.register 7) (.ret [.register 5]) (recurseBody self))

def recordBody (self cmp : Fin p) : Command p :=
  .load (.register 2) 4 5 9 { CompiledTrie.failCases with pair := compareBody self cmp }

/-- The returned pointer is shared with the first matching stored route. -/
def lookupBody (self cmp : Fin p) : Command p :=
  .load (.register 1) 2 3 9 { CompiledTrie.failCases with
    nil := .ret [.null]
    cons := recordBody self cmp }

def budget (width length : ℕ) : ℕ := (36 * width + 70) * length + 13

theorem compiled (code : Code p) (self cmp : Fin p)
    (hself : code self = lookupBody self cmp)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    {n b : ℕ} {h : Heap} (hh : Valid h) {qp rp : Ptr}
    {query : Bits n} {routes : List (Route n b)}
    (hq : BitsAt h qp query) (hr : RoutesAt h rp routes) :
    ∃ result, TableAt h result (lookup query routes) ∧
      Within code h (initialRegisters [.pointer qp, .pointer rp]) (code self)
        [.pointer result] h (budget n routes.length) := by
  induction routes generalizing rp with
  | nil =>
    refine ⟨0, TableAt.nil hh.1, ?_⟩
    have cell := RoutesAt.nil_iff.mp hr
    rw [hself]
    let regs := initialRegisters [Value.pointer qp, .pointer rp]
    have last := Within.ret code h (loadRegisters regs 2 3 9 .nil) [.null]
    have load := Within.load (address := .register 1) (first := 2) (second := 3) (bit := 9)
      (branches := { CompiledTrie.failCases with nil := .ret [.null], cons := recordBody self cmp })
      (by simp [regs, Atom.eval, initialRegisters]) cell last
    simpa [lookupBody, budget, values, Atom.eval] using load
  | cons entry routes ih =>
    obtain ⟨head, tail, cell, hentry, htail⟩ := RoutesAt.cons_iff.mp hr
    obtain ⟨kp, pp, hrecord, hk, hp⟩ := hentry
    let regs := initialRegisters [Value.pointer qp, .pointer rp]
    let scanned := loadRegisters regs 2 3 9 (.cons head tail)
    let loaded := loadRegisters scanned 4 5 9 (.pair kp pp)
    let compared := bindResults loaded [6, 7] (RegisterComparator.flags (Bits.compare query entry.1).1)
    have eqFlag : decide ((Bits.compare query entry.1).1 = .eq) =
        decide (query.value = entry.1.value) := by
      simp only [(Bits.compare_correct query entry.1).2.1]
    have cargs : values loaded [.register 0, .register 4] = [.pointer qp, .pointer kp] := by
      simp [loaded, scanned, regs, loadRegisters, decoded, initialRegisters, values, Atom.eval]
    have compare := RegisterComparator.compiled code cmp hcmp hq hk
    have finish (result : Ptr)
        (branch : Within code h compared
          (.branch (.register 7) (.ret [.register 5]) (recurseBody self))
          [.pointer result] h (budget n routes.length + 11)) :
        Within code h regs (code self) [.pointer result] h (budget n (entry :: routes).length) := by
      have call := Within.call (procedure := cmp) (regs := loaded)
        (arguments := [.register 0, .register 4]) (results := [6, 7])
        (by simpa only [cargs] using compare) branch
      have record := Within.load (address := .register 2) (first := 4) (second := 5) (bit := 9)
        (branches := { CompiledTrie.failCases with pair := compareBody self cmp })
        (by simp [scanned, loadRegisters, decoded, Atom.eval]) hrecord call
      have list := Within.load (address := .register 1) (first := 2) (second := 3) (bit := 9)
        (branches := { CompiledTrie.failCases with nil := .ret [.null], cons := recordBody self cmp })
        (by simp [regs, Atom.eval, initialRegisters]) cell record
      rw [hself]
      exact list.mono (by simp [budget, List.length_cons, Nat.mul_add]; omega)
    by_cases heq : query.value = entry.1.value
    · refine ⟨pp, by simpa [lookup, heq] using hp, finish pp ?_⟩
      have terminal : Within code h compared (.ret [.register 5]) [.pointer pp] h 3 := by
        simpa [values, Atom.eval, compared, bindResults, loaded, loadRegisters, decoded,
          RegisterComparator.flags] using Within.ret code h compared [.register 5]
      have branch := Within.branch (test := .register 7) (b := true)
        (yes := .ret [.register 5]) (no := recurseBody self)
        (by simp [compared, bindResults, Atom.eval, RegisterComparator.flags, eqFlag, heq]) terminal
      exact branch.mono (by omega)
    · obtain ⟨result, hresult, child⟩ := ih htail
      refine ⟨result, by simpa [lookup, heq] using hresult, finish result ?_⟩
      have rargs : values compared [.register 0, .register 3] = [.pointer qp, .pointer tail] := by
        simp [compared, loaded, scanned, regs, bindResults, loadRegisters, decoded,
          initialRegisters, values, Atom.eval, RegisterComparator.flags]
      have last : Within code h (bindResults compared [8] [.pointer result])
          (.ret [.register 8]) [.pointer result] h 3 := by
        simpa [bindResults, values, Atom.eval] using Within.ret code h
          (bindResults compared [8] [.pointer result]) [.register 8]
      have call := Within.call (procedure := self) (regs := compared)
        (arguments := [.register 0, .register 3]) (results := [8])
        (by simpa only [rargs] using child) last
      have branch := Within.branch (test := .register 7) (b := false)
        (yes := .ret [.register 5]) (no := recurseBody self)
        (by simp [compared, bindResults, Atom.eval, RegisterComparator.flags, eqFlag, heq]) call
      exact branch.mono (by simp; omega)

end WeightedMIS.RegisterRouteLookup
