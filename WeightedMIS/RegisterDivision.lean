module

public import WeightedMIS.RegisterShift

/-!
# Closed register implementation of restoring binary division

The loop consumes the numerator's linked bits. Every iteration invokes the
closed shift, comparison and subtraction procedures, then recursively processes
the tail. Quotient bits are materialized while returning. No width or fuel is
part of the finite procedure body.
-/

@[expose] public section

namespace WeightedMIS.RegisterDivision

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch

variable {p : ℕ}

def finish (bit : Bool) : Command p :=
  .allocate 10 (.bit (.flag bit) (.register 8)) (.ret [.register 10, .register 9])

def tailBody (self : Fin p) (rem : Register) (bit : Bool) : Command p :=
  .call self [.register 0, .register 3, .register rem] [8, 9] (finish bit)

def chooseBody (self sub : Fin p) : Command p :=
  .branch (.register 6) (tailBody self 5 false)
    (.call sub [.register 5, .register 0] [11, 12] (tailBody self 11 true))

def auxBody (self shift cmp sub : Fin p) : Command p :=
  .load (.register 1) 3 15 4 (RegisterAdder.nilBitCases
    (.ret [.register 1, .register 2])
    (.call shift [.register 2, .register 4] [5]
      (.call cmp [.register 5, .register 0] [6, 7] (chooseBody self sub))))

theorem finish_within (code : Code p) (h : Heap) (regs : Registers) (bit : Bool)
    (qp rp : Ptr) (hq : regs 8 = .pointer qp) (hr : regs 9 = .pointer rp) :
    Within code h regs (finish bit) [.pointer h.length, .pointer rp]
      (h ++ [.bit bit qp]) 13 := by
  have last : Within code (h ++ [.bit bit qp])
      (Function.update regs 10 (.pointer h.length)) (.ret [.register 10, .register 9])
      [.pointer h.length, .pointer rp] (h ++ [.bit bit qp]) 5 := by
    simpa [values, Atom.eval, hr] using
      Within.ret code (h ++ [.bit bit qp])
        (Function.update regs 10 (.pointer h.length)) [.register 10, .register 9]
  have halloc := Within.allocate (dst := 10) (expr := .bit (.flag bit) (.register 8))
    (by simp [CellExpr.eval, Atom.eval, hq, Value.asPointer, Value.asFlag]) last
  simpa [finish, CellExpr.args] using halloc

theorem tail_within (code : Code p) (self : Fin p) (h mid : Heap) (regs : Registers)
    (rem : Register) (bit : Bool) (dp ap rp qp outRem : Ptr) (budget : ℕ)
    (hd : regs 0 = .pointer dp) (ha : regs 3 = .pointer ap)
    (hr : regs rem = .pointer rp)
    (child : Within code h (initialRegisters [.pointer dp, .pointer ap, .pointer rp])
      (code self) [.pointer qp, .pointer outRem] mid budget) :
    Within code h regs (tailBody self rem bit) [.pointer mid.length, .pointer outRem]
      (mid ++ [.bit bit qp]) (budget + 20) := by
  let ready := bindResults regs [8, 9] [Value.pointer qp, .pointer outRem]
  have hq8 : ready 8 = .pointer qp := by simp [ready, bindResults]
  have hr9 : ready 9 = .pointer outRem := by simp [ready, bindResults]
  have last := finish_within code mid ready bit qp outRem hq8 hr9
  have hargs : values regs [.register 0, .register 3, .register rem] =
      [.pointer dp, .pointer ap, .pointer rp] := by simp [values, Atom.eval, hd, ha, hr]
  have hcall := Within.call (procedure := self)
    (arguments := [.register 0, .register 3, .register rem]) (results := [8, 9])
    (regs := regs) (returned := [.pointer qp, .pointer outRem])
    (by simpa only [hargs] using child) last
  simpa [tailBody, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hcall

/-- Exact quotient and remainder arrays are produced by the closed loop. -/
theorem aux_compiled (code : Code p) (self shift snoc cmp sub complement add : Fin p)
    (hself : code self = auxBody self shift cmp sub)
    (hshift : code shift = RegisterShift.shiftInBody snoc)
    (hsnoc : code snoc = RegisterShift.snocBody snoc)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    (hsub : code sub = RegisterSubtractor.subtractorBody complement add)
    (hcomp : code complement = RegisterComplement.complementBody complement)
    (hadd : code add = RegisterAdder.adderBody add)
    {n m : ℕ} {h : Heap} (hh : Valid h) {dp ap rp : Ptr}
    {den : Bits n} {a : Bits m} {rem : Bits n}
    (hd : BitsAt h dp den) (ha : BitsAt h ap a) (hr : BitsAt h rp rem) :
    ∃ out : Heap, ∃ qp outRem : Ptr, Extends h out ∧ Valid out ∧
      BitsAt out qp (Bits.divideAux den a rem).1 ∧
      BitsAt out outRem (Bits.divideAux den a rem).2.1 ∧
      Within code h (initialRegisters [.pointer dp, .pointer ap, .pointer rp]) (code self)
        [.pointer qp, .pointer outRem] out (200 * (n + 1) * m + 15) := by
  induction a generalizing h ap rp rem with
  | nil =>
      cases ha with
      | nil hac =>
        refine ⟨h, ap, rp, .refl h, hh, .nil hac, hr, ?_⟩
        rw [hself]
        let regs := initialRegisters [Value.pointer dp, .pointer ap, .pointer rp]
        let loaded := loadRegisters regs 3 15 4 Cell.nil
        have last : Within code h loaded (.ret [.register 1, .register 2])
            [.pointer ap, .pointer rp] h 5 := by
          simpa [values, Atom.eval, loaded, regs, loadRegisters, decoded, initialRegisters] using
            Within.ret code h loaded [.register 1, .register 2]
        exact Within.load (address := .register 1) (first := 3) (second := 15) (bit := 4)
          (branches := RegisterAdder.nilBitCases (.ret [.register 1, .register 2])
            (.call shift [.register 2, .register 4] [5]
              (.call cmp [.register 5, .register 0] [6, 7] (chooseBody self sub))))
          (by simp [Atom.eval, regs, initialRegisters]) hac last
  | @cons m bit tail ih =>
      cases ha with
      | @cons _ atail _ _ _ hac hat =>
        obtain ⟨shiftHeap, sp, hext, hvalid, hrep, hlen, hse⟩ :=
          RegisterShift.shiftIn_compiled code snoc hsnoc hh hr bit
        rw [← hshift] at hse
        let sh := (Bits.shiftIn rem bit).1
        let comparison := (Bits.compare sh den).1
        have hde := hd.mono hext
        have hae := hat.mono hext
        have hce := RegisterComparator.compiled code cmp hcmp hrep hde
        let regs := initialRegisters [Value.pointer dp, .pointer ap, .pointer rp]
        let loaded := loadRegisters regs 3 15 4 (.bit bit atail)
        let shifted := bindResults loaded [5] [Value.pointer sp]
        let compared := bindResults shifted [6, 7] (RegisterComparator.flags comparison)
        have hd0 : compared 0 = .pointer dp := by
          simp [compared, shifted, loaded, regs, bindResults, RegisterComparator.flags,
            loadRegisters, decoded, initialRegisters]
        have ha3 : compared 3 = .pointer atail := by
          simp [compared, shifted, loaded, bindResults, RegisterComparator.flags,
            loadRegisters, decoded]
        have hs5 : compared 5 = .pointer sp := by
          simp [compared, shifted, bindResults, RegisterComparator.flags]
        have hc6 : compared 6 = .flag (decide (comparison = .lt)) := by
          simp [compared, bindResults, RegisterComparator.flags]
        obtain ⟨out, qp, op, hext2, hvalid2, hqrep, hrrep, hchoose⟩ :
            ∃ out : Heap, ∃ qp op : Ptr, Extends shiftHeap out ∧ Valid out ∧
              BitsAt out qp (Bits.divideAux den (.cons bit tail) rem).1 ∧
              BitsAt out op (Bits.divideAux den (.cons bit tail) rem).2.1 ∧
              Within code shiftHeap compared (chooseBody self sub) [.pointer qp, .pointer op]
                out (200 * (n + 1) * m + 15 + 137 * n + 86) := by
          by_cases hlt : comparison = .lt
          · obtain ⟨mid, tq, tr, hx, hv, hqr, hrr, child⟩ := ih hvalid hde hae hrep
            have alloc := allocate_bit hv false hqr
            have htail := tail_within code self shiftHeap mid compared 5 false dp atail sp tq tr
              (200 * (n + 1) * m + 15) hd0 ha3 hs5 child
            have hbranch : Within code shiftHeap compared (chooseBody self sub)
                [.pointer mid.length, .pointer tr] (mid ++ [.bit false tq])
                (200 * (n + 1) * m + 15 + 23) := by
              have hb := Within.branch (b := true) (test := .register 6)
                (yes := tailBody self 5 false)
                (no := .call sub [.register 5, .register 0] [11, 12] (tailBody self 11 true))
                (by simpa [Atom.eval, hlt] using hc6) htail
              exact hb.mono (by omega)
            refine ⟨mid ++ [.bit false tq], mid.length, tr, hx.trans alloc.1.1,
              alloc.1.2.1, ?_, ?_, hbranch.mono (by omega)⟩
            · simpa [Bits.divideAux, comparison, sh, hlt, Program.allocate] using alloc.2
            · simpa [Bits.divideAux, comparison, sh, hlt, Program.allocate] using hrr.mono alloc.1.1
          · obtain ⟨subHeap, subp, hxsub, hvsub, hsubrep, hsube⟩ :=
              RegisterSubtractor.compiled code complement add hcomp hadd hvalid hrep hde
            rw [← hsub] at hsube
            have hds := hde.mono hxsub
            have has := hae.mono hxsub
            obtain ⟨mid, tq, tr, hx, hv, hqr, hrr, child⟩ := ih hvsub hds has hsubrep
            have alloc := allocate_bit hv true hqr
            let afterSub := bindResults compared [11, 12]
              [Value.pointer subp, .flag (Bits.subtract sh den).2.1]
            have hsd : afterSub 0 = .pointer dp := by simp [afterSub, bindResults, hd0]
            have hsa : afterSub 3 = .pointer atail := by simp [afterSub, bindResults, ha3]
            have hsr : afterSub 11 = .pointer subp := by simp [afterSub, bindResults]
            have htail := tail_within code self subHeap mid afterSub 11 true dp atail subp tq tr
              (200 * (n + 1) * m + 15) hsd hsa hsr child
            have hargs : values compared [.register 5, .register 0] = [.pointer sp, .pointer dp] := by
              simp [values, Atom.eval, hs5, hd0]
            have hcall := Within.call (procedure := sub) (arguments := [.register 5, .register 0])
              (results := [11, 12]) (regs := compared)
              (returned := [.pointer subp, .flag (Bits.subtract sh den).2.1])
              (by simpa only [hargs] using hsube) htail
            have hbranch := Within.branch (b := false) (test := .register 6)
              (yes := tailBody self 5 false)
              (no := .call sub [.register 5, .register 0] [11, 12] (tailBody self 11 true))
              (by simpa [Atom.eval, hlt] using hc6) hcall
            refine ⟨mid ++ [.bit true tq], mid.length, tr,
              hxsub.trans (hx.trans alloc.1.1), alloc.1.2.1, ?_, ?_, ?_⟩
            · simpa [Bits.divideAux, comparison, sh, hlt, Program.allocate] using alloc.2
            · simpa [Bits.divideAux, comparison, sh, hlt, Program.allocate] using hrr.mono alloc.1.1
            · exact hbranch.mono (by simp only [List.length_cons, List.length_nil]; omega)
        refine ⟨out, qp, op, hext.trans hext2, hvalid2, hqrep, hrrep, ?_⟩
        rw [hself]
        have hargsC : values shifted [.register 5, .register 0] = [.pointer sp, .pointer dp] := by
          simp [values, Atom.eval, shifted, loaded, regs, bindResults, loadRegisters, decoded,
            initialRegisters]
        have hcallC := Within.call (procedure := cmp) (arguments := [.register 5, .register 0])
          (results := [6, 7]) (regs := shifted) (returned := RegisterComparator.flags comparison)
          (by simpa only [hargsC] using hce) hchoose
        have hargsS : values loaded [.register 2, .register 4] = [.pointer rp, .flag bit] := by
          simp [values, Atom.eval, loaded, regs, loadRegisters, decoded, initialRegisters]
        have hcallS := Within.call (procedure := shift) (arguments := [.register 2, .register 4])
          (results := [5]) (regs := loaded) (returned := [.pointer sp])
          (by simpa only [hargsS] using hse) hcallC
        have hload := Within.load (address := .register 1) (first := 3) (second := 15) (bit := 4)
          (branches := RegisterAdder.nilBitCases (.ret [.register 1, .register 2])
            (.call shift [.register 2, .register 4] [5]
              (.call cmp [.register 5, .register 0] [6, 7] (chooseBody self sub))))
          (by simp [Atom.eval, regs, initialRegisters]) hac hcallS
        exact hload.mono (by simp only [List.length_cons, List.length_nil]; nlinarith)

end WeightedMIS.RegisterDivision
