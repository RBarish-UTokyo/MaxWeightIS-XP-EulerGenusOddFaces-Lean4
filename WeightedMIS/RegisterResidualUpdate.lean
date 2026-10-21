module

public import WeightedMIS.RegisterArcMembership
public import WeightedMIS.RegisterResidualAdjust

/-!
# Updating represented residual capacities along a stored path

For each arc, fixed code tests forward and reversed endpoint membership,
executes the checked conditional subtraction/addition, then allocates a new
record sharing both endpoint words. The original residual table is immutable.
-/

@[expose] public section

namespace WeightedMIS.RegisterResidualUpdate

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch WeightedMIS.ResidualWords

variable {p : ℕ}

def update {n b pb : ℕ} (arc : Arc n b) (path : List (Arc n pb)) (delta : Bits b) : Arc n b :=
  ⟨arc.source, arc.target, RegisterResidualAdjust.adjust arc.capacity delta
    (RegisterArcMembership.found arc.source arc.target path)
    (RegisterArcMembership.found arc.target arc.source path)⟩

/-- Endpoint membership is independent of the stored route orientation. -/
@[simp] theorem update_reverse {n b pb : ℕ} (arc : Arc n b)
    (path : List (Arc n pb)) (delta : Bits b) :
    update arc path.reverse delta = update arc path delta := by
  simp [update, RegisterArcMembership.found]

@[simp] theorem table_update_reverse {n b pb : ℕ} (arcs : List (Arc n b))
    (path : List (Arc n pb)) (delta : Bits b) :
    arcs.map (fun arc => update arc path.reverse delta) =
      arcs.map (fun arc => update arc path delta) := by
  simp

def recordBody : Command p :=
  .allocate 10 (.pair (.register 5) (.register 9))
    (.allocate 11 (.pair (.register 3) (.register 10)) (.ret [.register 11]))

def adjustBody (adjust : Fin p) : Command p :=
  .call adjust [.register 6, .register 2, .register 7, .register 8] [9] recordBody

def reverseBody (member adjust : Fin p) : Command p :=
  .call member [.register 5, .register 3, .register 1] [8] (adjustBody adjust)

def forwardBody (member adjust : Fin p) : Command p :=
  .call member [.register 3, .register 5, .register 1] [7] (reverseBody member adjust)

/-- Inputs: arc record, path list, delta word. Output: updated arc record. -/
def updateBody (member adjust : Fin p) : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    pair := .load (.register 4) 5 6 15 { CompiledTrie.failCases with
      pair := forwardBody member adjust } }

def budget (vertexBits capacityBits pathLength : ℕ) : ℕ :=
  2 * RegisterArcMembership.budget vertexBits pathLength + 247 * capacityBits + 200

theorem record_compiled (code : Code p) {n b : ℕ} {h : Heap} (hh : Valid h)
    (regs : Registers) {sp tp cp : Ptr} {arc : Arc n b}
    (hs : BitsAt h sp arc.source) (ht : BitsAt h tp arc.target) (hc : BitsAt h cp arc.capacity)
    (h3 : regs 3 = .pointer sp) (h5 : regs 5 = .pointer tp) (h9 : regs 9 = .pointer cp) :
    ∃ out result, Extends h out ∧ Valid out ∧ ArcAt out result arc ∧
      Within code h regs recordBody [.pointer result] out 19 := by
  have hfirst := safe_allocate h hh (.pair tp cp) (by
    intro p hp
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ht.allocated
    · exact hc.allocated)
  let middle := h ++ [.pair tp cp]
  have hsecond := safe_allocate middle hfirst.2.1 (.pair sp h.length) (by
    intro p hp
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact (hs.mono hfirst.1).allocated
    · simp [middle])
  let r1 := Function.update regs 10 (Value.pointer h.length)
  let r2 := Function.update r1 11 (Value.pointer middle.length)
  have last : Within code (middle ++ [.pair sp h.length]) r2 (.ret [.register 11])
      [.pointer middle.length] (middle ++ [.pair sp h.length]) 3 := by
    simpa [r2, values, Atom.eval] using
      Within.ret code (middle ++ [.pair sp h.length]) r2 [.register 11]
  have second := Within.allocate (regs := r1) (dst := 11)
    (expr := .pair (.register 3) (.register 10))
    (by simp [CellExpr.eval, Atom.eval, r1, h3, Value.asPointer]) last
  have first := Within.allocate (regs := regs) (dst := 10)
    (expr := .pair (.register 5) (.register 9))
    (by simp [CellExpr.eval, Atom.eval, h5, h9, Value.asPointer]) second
  have hext := hfirst.1.trans hsecond.1
  refine ⟨middle ++ [.pair sp h.length], middle.length, hext, hsecond.2.1, ?_, by simpa [recordBody, CellExpr.args] using first⟩
  refine ⟨sp, h.length, tp, cp, ?_, ?_, hs.mono hext, ht.mono hext, hc.mono hext⟩
  · simp
  · exact hsecond.1.lookup (by simp [middle])

/-- Every endpoint-membership and arithmetic call is refined by its concrete
finite body. The output has exactly the Boolean-directed residual update. -/
theorem compiled (code : Code p) (member cmp adjust sub complement add : Fin p)
    (hmember : code member = RegisterArcMembership.membershipBody member cmp)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    (hadjust : code adjust = RegisterResidualAdjust.adjustBody sub add)
    (hsub : code sub = RegisterSubtractor.subtractorBody complement add)
    (hcomplement : code complement = RegisterComplement.complementBody complement)
    (hadd : code add = RegisterAdder.adderBody add)
    {n b pb : ℕ} {h : Heap} (hh : Valid h) {ap pp dp : Ptr}
    {arc : Arc n b} {path : List (Arc n pb)} {delta : Bits b}
    (ha : ArcAt h ap arc) (hp : TableAt h pp path) (hd : BitsAt h dp delta) :
    ∃ out result, Extends h out ∧ Valid out ∧ ArcAt out result (update arc path delta) ∧
      Within code h (initialRegisters [.pointer ap, .pointer pp, .pointer dp])
        (updateBody member adjust) [.pointer result] out (budget n b path.length) := by
  obtain ⟨sp, tail, tp, cp, hcell, htailCell, hs, ht, hc⟩ := ha
  have forward := RegisterArcMembership.compiled code member cmp hmember hcmp hs ht hp
  have reverse := RegisterArcMembership.compiled code member cmp hmember hcmp ht hs hp
  obtain ⟨changed, newcp, hext, hv, hcapacity, hac⟩ :=
    RegisterResidualAdjust.compiled code sub complement add hsub hcomplement hadd hh hc hd
      (RegisterArcMembership.found arc.source arc.target path)
      (RegisterArcMembership.found arc.target arc.source path)
  rw [← hadjust] at hac
  let regs := initialRegisters [Value.pointer ap, .pointer pp, .pointer dp]
  let outer := loadRegisters regs 3 4 15 (.pair sp tail)
  let inner := loadRegisters outer 5 6 15 (.pair tp cp)
  let forwardDone := bindResults inner [7]
    [Value.flag (RegisterArcMembership.found arc.source arc.target path)]
  let reverseDone := bindResults forwardDone [8]
    [Value.flag (RegisterArcMembership.found arc.target arc.source path)]
  let adjusted := bindResults reverseDone [9] [Value.pointer newcp]
  obtain ⟨out, result, hrecordExt, hout, hrecord, hrecordCode⟩ :=
    record_compiled code (arc := update arc path delta) (sp := sp) (tp := tp) (cp := newcp) hv adjusted
      (hs.mono hext) (ht.mono hext) hcapacity
      (by simp [adjusted, reverseDone, forwardDone, inner, outer, bindResults, loadRegisters, decoded])
      (by simp [adjusted, reverseDone, forwardDone, inner, bindResults, loadRegisters, decoded])
      (by simp [adjusted, bindResults])
  have haargs : values reverseDone [.register 6, .register 2, .register 7, .register 8] =
      [.pointer cp, .pointer dp, .flag (RegisterArcMembership.found arc.source arc.target path),
        .flag (RegisterArcMembership.found arc.target arc.source path)] := by
    simp [reverseDone, forwardDone, inner, outer, regs, bindResults, loadRegisters, decoded,
      initialRegisters, values, Atom.eval]
  have adjustCall := Within.call (procedure := adjust) (regs := reverseDone)
    (arguments := [.register 6, .register 2, .register 7, .register 8]) (results := [9])
    (by simpa only [haargs] using hac) hrecordCode
  have hrargs : values forwardDone [.register 5, .register 3, .register 1] =
      [.pointer tp, .pointer sp, .pointer pp] := by
    simp [forwardDone, inner, outer, regs, bindResults, loadRegisters, decoded,
      initialRegisters, values, Atom.eval]
  have reverseCall := Within.call (procedure := member) (regs := forwardDone)
    (arguments := [.register 5, .register 3, .register 1]) (results := [8])
    (by simpa only [hrargs] using reverse) adjustCall
  have hfargs : values inner [.register 3, .register 5, .register 1] =
      [.pointer sp, .pointer tp, .pointer pp] := by
    simp [inner, outer, regs, loadRegisters, decoded, initialRegisters, values, Atom.eval]
  have forwardCall := Within.call (procedure := member) (regs := inner)
    (arguments := [.register 3, .register 5, .register 1]) (results := [7])
    (by simpa only [hfargs] using forward) reverseCall
  have loadInner := Within.load (regs := outer) (address := .register 4)
    (first := 5) (second := 6) (bit := 15)
    (branches := { CompiledTrie.failCases with pair := forwardBody member adjust })
    (by simp [outer, loadRegisters, decoded, Atom.eval]) htailCell forwardCall
  have loadOuter := Within.load (regs := regs) (address := .register 0)
    (first := 3) (second := 4) (bit := 15)
    (branches := { CompiledTrie.failCases with
      pair := .load (.register 4) 5 6 15 { CompiledTrie.failCases with pair := forwardBody member adjust } })
    (by simp [regs, initialRegisters, Atom.eval]) hcell loadInner
  refine ⟨out, result, hext.trans hrecordExt, hout, hrecord, loadOuter.mono ?_⟩
  simp only [budget, List.length_cons, List.length_nil]
  omega

/-- The same represented update equals ordinary natural residual arithmetic
once the residual invariant supplies its underflow and width bounds. -/
theorem update_capacity_value {n b pb : ℕ} (arc : Arc n b) (path : List (Arc n pb)) (delta : Bits b)
    (hsub : RegisterArcMembership.found arc.source arc.target path = true → delta.value ≤ arc.capacity.value)
    (hbound : (arc.capacity.value - if RegisterArcMembership.found arc.source arc.target path then delta.value else 0) +
      (if RegisterArcMembership.found arc.target arc.source path then delta.value else 0) < 2 ^ b) :
    (update arc path delta).capacity.value =
      (arc.capacity.value - if RegisterArcMembership.found arc.source arc.target path then delta.value else 0) +
        (if RegisterArcMembership.found arc.target arc.source path then delta.value else 0) :=
  RegisterResidualAdjust.adjust_value _ _ _ _ hsub hbound

end WeightedMIS.RegisterResidualUpdate
