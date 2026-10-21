module

public import WeightedMIS.RegisterCandidateParsing
public import WeightedMIS.RegisterCandidateFinish

/-! # Compilation of an actual expanded-graph move candidate -/

@[expose] public section

namespace WeightedMIS.RegisterCandidate

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.ExpandedWords WeightedMIS.EfficientSearch.Pointer WeightedMIS.RegisterPairReads

set_option maxRecDepth 4000

variable {p n cbits : ℕ} {Row : Type*}

structure Procedures.Matches (ids : Procedures p) (code : Code p)
    (arith : RegisterHorner.Procedures p) (digit complement : Fin p) : Prop where
  arithmetic : arith.Matches code
  compare : code ids.compare = RegisterComparator.comparatorBody ids.compare
  coordinates : code ids.coordinates = RegisterCoordinates.wordsBody ids.coordinates digit
  digit : code digit = RegisterCoordinate.digitBody arith.add ids.compare ids.subtract
  horner : code ids.horner = code arith.self
  subtract : code ids.subtract = RegisterSubtractor.subtractorBody complement arith.add
  complement : code complement = RegisterComplement.complementBody complement
  encode : code ids.encode = RegisterNodeEncode.encodeBody arith.mul arith.add
  emit : code ids.emit = RegisterArcEmitter.emitBody

def continuationBudget (n d : ℕ) : ℕ :=
  500*(n+1)*d + RegisterHorner.digitBudget n*d + 1200*(n+1)^2 + 137*n + 200

def candidateBudget (n d : ℕ) : ℕ := continuationBudget n d + 36*n + 200

theorem updateWords_length {base : Bits n} {xs ys : List (Bits n)} {ds : List (SignedWord n)}
    (h : updateWords base xs ds = some ys) : ys.length = xs.length := by
  induction xs generalizing ds ys with
  | nil => cases ds <;> simp [updateWords] at h; subst ys; rfl
  | cons x xs ih =>
    cases ds with
    | nil => simp [updateWords] at h
    | cons d ds =>
      cases hx : updateDigit base x d with
      | none => simp [updateWords,hx] at h
      | some y =>
        cases ht : updateWords base xs ds with
        | none => simp [updateWords,hx,ht] at h
        | some zs =>
          have hy : y :: zs = ys := by simpa [updateWords,hx,ht] using h
          subst ys
          simp only [List.length_cons, ih ht]

theorem Matched.ready {h out : Heap} (he : Extends h out) {regs : Registers}
    {ctx : WorkContext n} {target box : Bits n} {metadata : ArcMetadata n cbits}
    {tail : List (RawArc Ptr n cbits)} (hm : Matched h regs ctx target metadata tail)
    {wp bp cp : Ptr} (hb : BitsAt out bp box) (hc : CostLabelAt h cp metadata.weight metadata.label) :
    Ready out (loadRegisters (bindResults
      (bindResults regs [5,14] [.flag true,.pointer wp]) [14] [.pointer bp])
      3 5 15 (.bit metadata.parity cp)) ctx target box ctx.parity metadata tail := by
  constructor
  · obtain ⟨q,hr,hq⟩ := hm.source
    exact ⟨q,by simpa [bindResults,loadRegisters,decoded] using hr,hq.mono he⟩
  · obtain ⟨q,hr,hq⟩ := hm.anchor
    exact ⟨q,by simpa [bindResults,loadRegisters,decoded] using hr,hq.mono he⟩
  · obtain ⟨q,hr,hq⟩ := hm.target
    exact ⟨q,by simpa [bindResults,loadRegisters,decoded] using hr,hq.mono he⟩
  · exact ⟨bp,by simp [bindResults,loadRegisters,decoded],hb⟩
  · obtain ⟨q,hr,hq⟩ := hm.parity
    exact ⟨q,by simpa [bindResults,loadRegisters,decoded] using hr,hq.mono he⟩
  · obtain ⟨q,hr,hq⟩ := hm.states
    exact ⟨q,by simpa [bindResults,loadRegisters,decoded] using hr,hq.mono he⟩
  · obtain ⟨q,hr,hq⟩ := hm.block
    exact ⟨q,by simpa [bindResults,loadRegisters,decoded] using hr,hq.mono he⟩
  · obtain ⟨q,hr,hq⟩ := hm.one
    exact ⟨q,by simpa [bindResults,loadRegisters,decoded] using hr,hq.mono he⟩
  · obtain ⟨q,hr,hq⟩ := hm.two
    exact ⟨q,by simpa [bindResults,loadRegisters,decoded] using hr,hq.mono he⟩
  · exact ⟨cp,by simp [bindResults,loadRegisters,decoded],hc.mono he⟩
  · obtain ⟨q,hr,hq⟩ := hm.tail
    exact ⟨q,by simpa [bindResults,loadRegisters,decoded] using hr,hq.mono he⟩

def updatedArcs (ctx : WorkContext n) (target : Bits n) (metadata : ArcMetadata n cbits) :
    List (RawArc Ptr n cbits) :=
  match updateWords ctx.arithmetic.base ctx.digits metadata.deltas with
  | none => []
  | some updated =>
      [emitted ctx target (RegisterHorner.encodeWords ctx.arithmetic.base updated)
        (if metadata.parity then (Bits.subtract ctx.arithmetic.one ctx.parity).1 else ctx.parity) metadata]

theorem afterParsing_compiled (code : Code p) (ids : Procedures p) (arith : RegisterHorner.Procedures p)
    (digit complement : Fin p) (hc : ids.Matches code arith digit complement)
    {h : Heap} (hh : Valid h) {regs : Registers} {ctx : WorkContext n} {target : Bits n}
    {metadata : ArcMetadata n cbits} {tail : List (RawArc Ptr n cbits)}
    (hm : Matched h regs ctx target metadata tail) (hlen : ctx.digits.length = metadata.deltas.length) :
    ∃ out q, Extends h out ∧ Valid out ∧ TraceAt out q (updatedArcs ctx target metadata ++ tail) ∧
      Within code h regs (.call ids.coordinates [.register 0,.register 14,.register 5] [5,14]
        (afterCoordinates ids)) [.pointer q] out (continuationBudget n ctx.digits.length) := by
  obtain ⟨base,r0,hb⟩ := hm.base
  obtain ⟨digits,r14,hd⟩ := hm.digits
  obtain ⟨deltas,r5,hdelta⟩ := hm.deltas
  obtain ⟨zp,r12,hz⟩ := hm.zero
  obtain ⟨acc,r2,hacc⟩ := hm.tail
  obtain ⟨pc,cp,r6,hpc,hcost⟩ := hm.parityCost
  have hadd := hc.arithmetic.2.2.2.2.2.2
  obtain ⟨mid,wp,he,hmiddle,hw,coords⟩ := RegisterCoordinates.compiled code ids.coordinates digit
    arith.add ids.compare ids.subtract complement hc.coordinates hc.digit hadd hc.compare hc.subtract
    hc.complement hh hb hd hdelta hlen
  let rA := bindResults regs [5,14]
    [.flag (updateWords ctx.arithmetic.base ctx.digits metadata.deltas).isSome,.pointer wp]
  have args : values regs [.register 0,.register 14,.register 5] =
      [.pointer base,.pointer digits,.pointer deltas] := by simp [values,Atom.eval,r0,r14,r5]
  cases hu : updateWords ctx.arithmetic.base ctx.digits metadata.deltas with
  | none =>
    refine ⟨mid,acc,he,hmiddle,?_,?_⟩
    · simpa [updatedArcs,hu] using hacc.mono he
    · have ret : Within code mid rA skip [.pointer acc] mid 3 := by
        simpa [skip,values,Atom.eval,rA,bindResults,r2] using Within.ret code mid rA [.register 2]
      have branch := Within.branch (test := .register 5) (b := false)
        (yes := .call ids.horner [.register 14,.register 0,.register 12] [14] (updateParity ids))
        (no := skip) (by simp [Atom.eval,rA,bindResults,hu]) ret
      have call := Within.call (procedure := ids.coordinates)
        (arguments := [.register 0,.register 14,.register 5]) (results := [5,14]) (regs := regs)
        (by simpa only [args] using coords) branch
      exact call.mono (by simp [continuationBudget]; omega)
  | some updated =>
    have words : WordsAt mid wp updated := by simpa [hu,OptionWordsAt] using hw
    have hul := updateWords_length hu
    obtain ⟨mid2,bp,he2,hm2,hbox,horner⟩ := RegisterHorner.compiled code arith hc.arithmetic
      hmiddle words (hb.mono he) (hz.mono he)
    let rB := bindResults rA [14] [.pointer bp]
    let rC := loadRegisters rB 3 5 15 (.bit metadata.parity cp)
    have ready : Ready mid2 rC ctx target (RegisterHorner.encodeWords ctx.arithmetic.base updated)
        ctx.parity metadata tail := by
      simpa [rC,rB,rA,hu] using hm.ready (wp := wp) (he.trans he2) hbox hcost
    obtain ⟨out,q,he3,ho,hq,parity⟩ := parity_compiled code ids arith hc.arithmetic complement
      hc.encode hc.emit hc.subtract hc.complement hm2 ready
      (by simp [rC,loadRegisters,decoded])
    refine ⟨out,q,(he.trans he2).trans he3,ho,?_,?_⟩
    · simpa [updatedArcs,hu] using hq
    · have load := Within.load (address := .register 6) (first := 3) (second := 5) (bit := 15)
        (branches := {CompiledTrie.failCases with bit := (.branch (.register 15)
          (.call ids.subtract [.register 8,.register 13] [13,5] (encodeAndEmit ids)) (encodeAndEmit ids))})
        (by simpa [Atom.eval,rB,rA,bindResults] using r6) ((he.trans he2).lookup hpc) parity
      have hargs : values rA [.register 14,.register 0,.register 12] =
          [.pointer wp,.pointer base,.pointer zp] := by simp [values,Atom.eval,rA,bindResults,r0,r12]
      have hcall := Within.call (procedure := ids.horner)
        (arguments := [.register 14,.register 0,.register 12]) (results := [14]) (regs := rA)
        (by simpa only [hargs,hc.horner] using horner) load
      have branch := Within.branch (test := .register 5) (b := true)
        (yes := .call ids.horner [.register 14,.register 0,.register 12] [14] (updateParity ids))
        (no := skip) (by simp [Atom.eval,rA,bindResults,hu]) hcall
      have call := Within.call (procedure := ids.coordinates)
        (arguments := [.register 0,.register 14,.register 5]) (results := [5,14]) (regs := regs)
        (by simpa only [args] using coords) branch
      exact call.mono (by simp [continuationBudget,hul]; omega)

theorem compiled (code : Code p) (ids : Procedures p) (arith : RegisterHorner.Procedures p)
    (digit complement : Fin p) (hc : ids.Matches code arith digit complement)
    {key : Walks.State Row → Bits n} {h : Heap} (hh : Valid h)
    {tp cp ap : Ptr} {ctx : WorkContext n}
    {a : CompiledTemplates.Template Row (ArcMetadata n cbits)} {tail : List (RawArc Ptr n cbits)}
    (ht : CompiledTemplates.TemplateAt key MetadataAt h tp a) (hctx : ContextAt h cp ctx)
    (ha : TraceAt h ap tail) (hlen : ctx.digits.length = a.metadata.deltas.length) :
    ∃ out q, Extends h out ∧ Valid out ∧ TraceAt out q (candidate key ctx a ++ tail) ∧
      Within code h (initialRegisters [.pointer tp,.pointer cp,.pointer ap]) (candidateBody ids)
        [.pointer q] out (candidateBudget n ctx.digits.length) := by
  obtain ⟨regs,reads,hi⟩ := parse_initial ht hctx ha
  obtain ⟨sp,r5,hs⟩ := hi.sourceKey
  obtain ⟨vp,r13,hv⟩ := hi.current
  have compare := RegisterComparator.compiled code ids.compare hc.compare hs hv
  let order := (Bits.compare (key a.source) ctx.current).1
  let ra := bindResults regs [15,6] (RegisterComparator.flags order)
  have hi' : Initial key h ra ctx a tail := hi.afterCompare (decide (order = .lt)) (decide (order = .eq))
  obtain ⟨out,q,he,ho,hq,branch⟩ :
      ∃ out q, Extends h out ∧ Valid out ∧ TraceAt out q (candidate key ctx a ++ tail) ∧
        Within code h ra (.branch (.register 6) (matched ids) skip) [.pointer q] out
          (continuationBudget n ctx.digits.length + 73) := by
    by_cases hm : order = .eq
    · obtain ⟨loaded,more,hparsed⟩ := parse_matched hi'
      obtain ⟨out,q,he,ho,hq,run⟩ := afterParsing_compiled code ids arith digit complement hc hh hparsed hlen
      have inner := more.within run
      have branch := Within.branch (test := .register 6) (b := true) (yes := matched ids) (no := skip)
        (by simp [Atom.eval,ra,RegisterComparator.flags,bindResults,hm]) inner
      refine ⟨out,q,he,ho,?_,?_⟩
      · have heq : candidate key ctx a = updatedArcs ctx (key a.target) a.metadata := by
          unfold candidate
          rw [if_pos hm]
          rfl
        simpa only [heq] using hq
      · exact branch.mono (by simp [matchedReads]; omega)
    · obtain ⟨acc,r2,hacc⟩ := hi'.tail
      have ret : Within code h ra skip [.pointer acc] h 3 := by
        simpa [skip,values,Atom.eval,r2] using Within.ret code h ra [.register 2]
      have branch := Within.branch (test := .register 6) (b := false) (yes := matched ids) (no := skip)
        (by simp [Atom.eval,ra,RegisterComparator.flags,bindResults,hm]) ret
      refine ⟨h,acc,.refl h,hh,?_,branch.mono (by omega)⟩
      simpa [candidate,show (Bits.compare (key a.source) ctx.current).1 ≠ .eq from hm] using hacc
  refine ⟨out,q,he,ho,hq,?_⟩
  have args : values regs [.register 5,.register 13] = [.pointer sp,.pointer vp] := by
    simp [values,Atom.eval,r5,r13]
  have call := Within.call (procedure := ids.compare) (arguments := [.register 5,.register 13])
    (results := [15,6]) (regs := regs) (by simpa only [args] using compare) branch
  have run := reads.within call
  exact run.mono (by simp [candidateBudget,initialReads]; omega)

end WeightedMIS.RegisterCandidate
