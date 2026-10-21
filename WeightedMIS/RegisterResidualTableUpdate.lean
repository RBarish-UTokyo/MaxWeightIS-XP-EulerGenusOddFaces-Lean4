module

public import WeightedMIS.RegisterResidualUpdate

/-! # A finite-code traversal updating all stored residual-arc records -/

@[expose] public section

namespace WeightedMIS.RegisterResidualTableUpdate

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch WeightedMIS.ResidualWords

variable {p : ℕ}

def tableBody (self updateArc : Fin p) : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    nil := .ret [.null]
    cons := .call updateArc [.register 3, .register 1, .register 2] [5]
      (.call self [.register 4, .register 1, .register 2] [6]
        (.allocate 7 (.cons (.register 5) (.register 6)) (.ret [.register 7]))) }

def budget (vertexBits capacityBits pathLength arcCount : ℕ) : ℕ :=
  (RegisterResidualUpdate.budget vertexBits capacityBits pathLength + 35) * arcCount + 13

/-- The executable table traversal returns precisely the pointwise residual
update, preserving the supplied arc order and sharing all endpoint words. -/
theorem compiled (code : Code p) (self updateArc member cmp adjust sub complement add : Fin p)
    (hself : code self = tableBody self updateArc)
    (hupdate : code updateArc = RegisterResidualUpdate.updateBody member adjust)
    (hmember : code member = RegisterArcMembership.membershipBody member cmp)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    (hadjust : code adjust = RegisterResidualAdjust.adjustBody sub add)
    (hsub : code sub = RegisterSubtractor.subtractorBody complement add)
    (hcomplement : code complement = RegisterComplement.complementBody complement)
    (hadd : code add = RegisterAdder.adderBody add)
    {n b pb : ℕ} {h : Heap} (hh : Valid h) {ap pp dp : Ptr}
    {arcs : List (Arc n b)} {path : List (Arc n pb)} {delta : Bits b}
    (ha : TableAt h ap arcs) (hp : TableAt h pp path) (hd : BitsAt h dp delta) :
    ∃ out result, Extends h out ∧ Valid out ∧
      TableAt out result (arcs.map (fun a => RegisterResidualUpdate.update a path delta)) ∧
      Within code h (initialRegisters [.pointer ap, .pointer pp, .pointer dp])
        (code self) [.pointer result] out (budget n b path.length arcs.length) := by
  induction arcs generalizing h ap pp dp with
  | nil =>
    have hcell := TableAt.nil_iff.mp ha
    let regs := initialRegisters [Value.pointer ap, .pointer pp, .pointer dp]
    have last := Within.ret code h (loadRegisters regs 3 4 15 .nil) [.null]
    have load := Within.load (regs := regs) (address := .register 0)
      (first := 3) (second := 4) (bit := 15)
      (branches := { CompiledTrie.failCases with
        nil := .ret [.null]
        cons := .call updateArc [.register 3, .register 1, .register 2] [5]
          (.call self [.register 4, .register 1, .register 2] [6]
            (.allocate 7 (.cons (.register 5) (.register 6)) (.ret [.register 7]))) })
      (by simp [regs, initialRegisters, Atom.eval]) hcell last
    refine ⟨h, 0, Extends.refl h, hh, TableAt.nil hh.1, ?_⟩
    rw [hself]
    exact load
  | cons arc arcs ih =>
    obtain ⟨arcPtr, tailPtr, hcell, harc, htail⟩ := TableAt.cons_iff.mp ha
    obtain ⟨mid, updatedPtr, hext, hv, hupdated, hupdateCode⟩ :=
      RegisterResidualUpdate.compiled code member cmp adjust sub complement add
        hmember hcmp hadjust hsub hcomplement hadd hh harc hp hd
    rw [← hupdate] at hupdateCode
    obtain ⟨out, result, hext', hv', hresult, hrestCode⟩ :=
      ih hv (htail.mono hext) (hp.mono hext) (hd.mono hext)
    have hupdated' := hupdated.mono hext'
    have halloc := safe_allocate out hv' (.cons updatedPtr result) (by
      intro p hp
      simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hupdated'.allocated
      · exact hresult.allocated)
    let regs := initialRegisters [Value.pointer ap, .pointer pp, .pointer dp]
    let loaded := loadRegisters regs 3 4 15 (.cons arcPtr tailPtr)
    let updated := bindResults loaded [5] [Value.pointer updatedPtr]
    let recursed := bindResults updated [6] [Value.pointer result]
    have last : Within code (out ++ [.cons updatedPtr result])
        (Function.update recursed 7 (.pointer out.length)) (.ret [.register 7])
        [.pointer out.length] (out ++ [.cons updatedPtr result]) 3 := by
      simpa [values, Atom.eval] using Within.ret code (out ++ [.cons updatedPtr result])
        (Function.update recursed 7 (.pointer out.length)) [.register 7]
    have alloc := Within.allocate (regs := recursed) (dst := 7)
      (expr := .cons (.register 5) (.register 6))
      (by simp [recursed, updated, bindResults, CellExpr.eval, Atom.eval, Value.asPointer]) last
    have hrargs : values updated [.register 4, .register 1, .register 2] =
        [.pointer tailPtr, .pointer pp, .pointer dp] := by
      simp [updated, loaded, regs, bindResults, loadRegisters, decoded, initialRegisters, values, Atom.eval]
    have recurse := Within.call (procedure := self) (regs := updated)
      (arguments := [.register 4, .register 1, .register 2]) (results := [6])
      (by simpa only [hrargs] using hrestCode) alloc
    have huargs : values loaded [.register 3, .register 1, .register 2] =
        [.pointer arcPtr, .pointer pp, .pointer dp] := by
      simp [loaded, regs, loadRegisters, decoded, initialRegisters, values, Atom.eval]
    have updateCall := Within.call (procedure := updateArc) (regs := loaded)
      (arguments := [.register 3, .register 1, .register 2]) (results := [5])
      (by simpa only [huargs] using hupdateCode) recurse
    have load := Within.load (regs := regs) (address := .register 0)
      (first := 3) (second := 4) (bit := 15)
      (branches := { CompiledTrie.failCases with
        nil := .ret [.null]
        cons := .call updateArc [.register 3, .register 1, .register 2] [5]
          (.call self [.register 4, .register 1, .register 2] [6]
            (.allocate 7 (.cons (.register 5) (.register 6)) (.ret [.register 7]))) })
      (by simp [regs, initialRegisters, Atom.eval]) hcell updateCall
    refine ⟨out ++ [.cons updatedPtr result], out.length, hext.trans (hext'.trans halloc.1), halloc.2.1,
      TableAt.cons (by simp) (hupdated'.mono halloc.1) (hresult.mono halloc.1), ?_⟩
    rw [hself]
    apply load.mono
    simp only [budget, List.length_cons, List.length_nil, CellExpr.args, Nat.mul_add]
    omega

end WeightedMIS.RegisterResidualTableUpdate
