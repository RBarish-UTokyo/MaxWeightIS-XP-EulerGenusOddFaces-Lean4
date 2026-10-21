module

public import WeightedMIS.RegisterCandidate
public import WeightedMIS.RegisterNodeEncode

/-! # Encoding, parity update and emission continuations of a move -/

@[expose] public section

namespace WeightedMIS.RegisterCandidate

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.ExpandedWords WeightedMIS.EfficientSearch.Pointer

variable {p n cbits : ℕ}

def WordIn (h : Heap) (regs : Registers) (r : Register) (word : Bits n) : Prop :=
  ∃ ptr, regs r = .pointer ptr ∧ BitsAt h ptr word

structure Ready (h : Heap) (regs : Registers) (ctx : WorkContext n) (target box parity : Bits n)
    (metadata : ArcMetadata n cbits) (tail : List (RawArc Ptr n cbits)) : Prop where
  source : WordIn h regs 9 ctx.source
  anchor : WordIn h regs 11 ctx.anchor
  target : WordIn h regs 7 target
  box : WordIn h regs 14 box
  parity : WordIn h regs 13 parity
  states : WordIn h regs 1 ctx.arithmetic.states
  block : WordIn h regs 4 ctx.arithmetic.block
  one : WordIn h regs 8 ctx.arithmetic.one
  two : WordIn h regs 10 ctx.arithmetic.two
  cost : ∃ cp, regs 3 = .pointer cp ∧ CostLabelAt h cp metadata.weight metadata.label
  tail : ∃ tp, regs 2 = .pointer tp ∧ TraceAt h tp tail

def emitted (ctx : WorkContext n) (target box parity : Bits n) (metadata : ArcMetadata n cbits) :
    RawArc Ptr n cbits :=
  (ctx.source, ⟨ScalarNodeCodec.encodeWords ctx.arithmetic.states ctx.arithmetic.block
    ctx.arithmetic.one ctx.arithmetic.two ⟨false,ctx.anchor,target,box,parity⟩,metadata.weight,metadata.label⟩)

theorem finish_compiled (code : Code p) (ids : Procedures p) (arith : RegisterHorner.Procedures p)
    (harith : arith.Matches code)
    (hencode : code ids.encode = RegisterNodeEncode.encodeBody arith.mul arith.add)
    (hemit : code ids.emit = RegisterArcEmitter.emitBody)
    {h : Heap} (hh : Valid h) {regs : Registers} {ctx : WorkContext n} {target box parity : Bits n}
    {metadata : ArcMetadata n cbits} {tail : List (RawArc Ptr n cbits)}
    (ready : Ready h regs ctx target box parity metadata tail) :
    ∃ out q, Extends h out ∧ Valid out ∧ TraceAt out q (emitted ctx target box parity metadata :: tail) ∧
      Within code h regs (encodeAndEmit ids) [.pointer q] out (1200 * (n + 1) ^ 2 + 60) := by
  obtain ⟨sp, r9, hs⟩ := ready.source
  obtain ⟨ap, r11, ha⟩ := ready.anchor
  obtain ⟨vp, r7, hv⟩ := ready.target
  obtain ⟨zp, r14, hz⟩ := ready.box
  obtain ⟨pp, r13, hp⟩ := ready.parity
  obtain ⟨s, r1, hS⟩ := ready.states
  obtain ⟨t, r4, hT⟩ := ready.block
  obtain ⟨one, r8, h1⟩ := ready.one
  obtain ⟨two, r10, h2⟩ := ready.two
  obtain ⟨cp, r3, hc⟩ := ready.cost
  obtain ⟨acc, r2, hacc⟩ := ready.tail
  let node : ScalarNodeCodec.Words n := ⟨false,ctx.anchor,target,box,parity⟩
  let ptrs : RegisterNodeDecode.Pointers := ⟨false,ap,vp,zp,pp⟩
  have hn : RegisterNodeDecode.At h ptrs node := ⟨rfl,ha,hv,hz,hp⟩
  obtain ⟨mid, dest, he, hm, hd, enc⟩ := RegisterNodeEncode.compiled code arith harith hh node ptrs hn hS hT h1 h2
  obtain ⟨out, q, heout, ho, hq, emit⟩ := RegisterArcEmitter.compiled code hm
    (hs.mono he) hd (hc.mono he) (hacc.mono he)
  refine ⟨out,q,he.trans heout,ho,hq,?_⟩
  let rs := bindResults regs [0] [.pointer dest]
  let rt := bindResults rs [1] [.pointer q]
  have ret : Within code out rt (.ret [.register 1]) [.pointer q] out 3 := by
    simpa [values, Atom.eval, rt, bindResults] using Within.ret code out rt [.register 1]
  have eargs : values rs [.register 9,.register 0,.register 3,.register 2] =
      [.pointer sp,.pointer dest,.pointer cp,.pointer acc] := by
    simp [values, Atom.eval, rs, bindResults, r9, r3, r2]
  have ecall := Within.call (procedure := ids.emit) (arguments := [.register 9,.register 0,.register 3,.register 2])
    (results := [1]) (regs := rs) (by simpa only [eargs, hemit] using emit) ret
  have args : values regs [.flag false,.register 11,.register 7,.register 14,.register 13,
      .register 1,.register 4,.register 8,.register 10] =
      ptrs.outputs ++ [.pointer s,.pointer t,.pointer one,.pointer two] := by
    simp [values, Atom.eval, r11,r7,r14,r13,r1,r4,r8,r10,ptrs,RegisterNodeDecode.Pointers.outputs]
  have call := Within.call (procedure := ids.encode)
    (arguments := [.flag false,.register 11,.register 7,.register 14,.register 13,
      .register 1,.register 4,.register 8,.register 10]) (results := [0]) (regs := regs)
    (by simpa only [args,hencode] using enc) ecall
  exact call.mono (by simp; omega)

theorem Ready.updateParity {h h' : Heap} (he : Extends h h') {regs : Registers}
    {ctx : WorkContext n} {target box old new : Bits n} {metadata : ArcMetadata n cbits}
    {tail : List (RawArc Ptr n cbits)} (ready : Ready h regs ctx target box old metadata tail)
    {ptr : Ptr} (hp : BitsAt h' ptr new) (carry : Bool) :
    Ready h' (bindResults regs [13,5] [.pointer ptr,.flag carry]) ctx target box new metadata tail := by
  constructor
  · obtain ⟨p,hr,hw⟩ := ready.source; exact ⟨p,by simpa [bindResults] using hr,hw.mono he⟩
  · obtain ⟨p,hr,hw⟩ := ready.anchor; exact ⟨p,by simpa [bindResults] using hr,hw.mono he⟩
  · obtain ⟨p,hr,hw⟩ := ready.target; exact ⟨p,by simpa [bindResults] using hr,hw.mono he⟩
  · obtain ⟨p,hr,hw⟩ := ready.box; exact ⟨p,by simpa [bindResults] using hr,hw.mono he⟩
  · exact ⟨ptr,by simp [bindResults],hp⟩
  · obtain ⟨p,hr,hw⟩ := ready.states; exact ⟨p,by simpa [bindResults] using hr,hw.mono he⟩
  · obtain ⟨p,hr,hw⟩ := ready.block; exact ⟨p,by simpa [bindResults] using hr,hw.mono he⟩
  · obtain ⟨p,hr,hw⟩ := ready.one; exact ⟨p,by simpa [bindResults] using hr,hw.mono he⟩
  · obtain ⟨p,hr,hw⟩ := ready.two; exact ⟨p,by simpa [bindResults] using hr,hw.mono he⟩
  · obtain ⟨p,hr,hw⟩ := ready.cost; exact ⟨p,by simpa [bindResults] using hr,hw.mono he⟩
  · obtain ⟨p,hr,hw⟩ := ready.tail; exact ⟨p,by simpa [bindResults] using hr,hw.mono he⟩

theorem parity_compiled (code : Code p) (ids : Procedures p) (arith : RegisterHorner.Procedures p)
    (harith : arith.Matches code) (complement : Fin p)
    (hencode : code ids.encode = RegisterNodeEncode.encodeBody arith.mul arith.add)
    (hemit : code ids.emit = RegisterArcEmitter.emitBody)
    (hsub : code ids.subtract = RegisterSubtractor.subtractorBody complement arith.add)
    (hcomp : code complement = RegisterComplement.complementBody complement)
    {h : Heap} (hh : Valid h) {regs : Registers} {ctx : WorkContext n} {target box parity : Bits n}
    {metadata : ArcMetadata n cbits} {tail : List (RawArc Ptr n cbits)}
    (ready : Ready h regs ctx target box parity metadata tail) (h15 : regs 15 = .flag metadata.parity) :
    ∃ out q, Extends h out ∧ Valid out ∧ TraceAt out q
      (emitted ctx target box (if metadata.parity then (Bits.subtract ctx.arithmetic.one parity).1 else parity) metadata :: tail) ∧
      Within code h regs (.branch (.register 15)
        (.call ids.subtract [.register 8,.register 13] [13,5] (encodeAndEmit ids)) (encodeAndEmit ids))
        [.pointer q] out (1200 * (n + 1) ^ 2 + 137 * n + 130) := by
  cases hp : metadata.parity with
  | false =>
    obtain ⟨out,q,he,ho,hq,hc⟩ := finish_compiled code ids arith harith hencode hemit hh ready
    refine ⟨out,q,he,ho,by simpa [hp] using hq,?_⟩
    have hb := Within.branch (test := .register 15) (b := false)
      (yes := .call ids.subtract [.register 8,.register 13] [13,5] (encodeAndEmit ids))
      (no := encodeAndEmit ids) (by simpa [Atom.eval,hp] using h15) hc
    exact hb.mono (by omega)
  | true =>
    obtain ⟨op,r8,h1⟩ := ready.one
    obtain ⟨pp,r13,hpword⟩ := ready.parity
    have hadd := harith.2.2.2.2.2.2
    obtain ⟨mid,par,he,hm,hpar,sub⟩ := RegisterSubtractor.compiled code complement arith.add hcomp hadd hh h1 hpword
    let rs := bindResults regs [13,5] [.pointer par,.flag (Bits.subtract ctx.arithmetic.one parity).2.1]
    have ready' := ready.updateParity he hpar (Bits.subtract ctx.arithmetic.one parity).2.1
    obtain ⟨out,q,heout,ho,hq,hc⟩ := finish_compiled code ids arith harith hencode hemit hm ready'
    refine ⟨out,q,he.trans heout,ho,by simpa [hp] using hq,?_⟩
    have args : values regs [.register 8,.register 13] = [.pointer op,.pointer pp] := by
      simp [values,Atom.eval,r8,r13]
    have call := Within.call (procedure := ids.subtract) (arguments := [.register 8,.register 13])
      (results := [13,5]) (regs := regs) (by simpa only [args,hsub] using sub) hc
    have branch := Within.branch (test := .register 15) (b := true)
      (yes := .call ids.subtract [.register 8,.register 13] [13,5] (encodeAndEmit ids))
      (no := encodeAndEmit ids) (by simpa [Atom.eval,hp] using h15) call
    exact branch.mono (by simp; omega)

end WeightedMIS.RegisterCandidate
