module

public import WeightedMIS.RegisterSourceDispatch
public import WeightedMIS.RegisterWordRange
public import WeightedMIS.RegisterHubSource

/-! # Finite range-driven traversal of every expanded source key -/

@[expose] public section

namespace WeightedMIS.RegisterAllSources

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.ExpandedWords WeightedMIS.EfficientSearch.Pointer

variable {p n cbits : ℕ} {Row : Type*}

/-- The executable list follows increasing binary IDs, with no pair scan. -/
def sourceWords (limit : Bits n) : List (Bits n) :=
  (List.range' 0 limit.value).map (SparseSearchGraph.encodeBits n)

theorem words_eq_range {limit : Bits n} {words : List (Bits n)}
    (hv : words.map Bits.value = List.range' 0 limit.value) : words = sourceWords limit := by
  simpa only [sourceWords,List.range_eq_range'] using RegisterHubSource.words_eq_encoded limit words hv

def body (range scan : Fin p) : Command p :=
  .call range [.register 2,.register 1,.register 3] [5]
    (.call scan [.register 5,.register 0,.register 4] [6] (.ret [.register 6]))

/-- Local source refinement composed into the actual linked source traversal. -/
theorem scan_compiled (code : Code p) (scan source : Fin p)
    (hscan : code scan = RegisterListFlatMap.body scan source)
    (key : Walks.State Row → Bits n) (data : GenerationData Row n cbits)
    (outgoing : Bits n → List (RawArc Ptr n cbits)) (sourceBudget : ℕ)
    (sourceCompiled : ∀ {h : Heap}, Valid h → ∀ {sp dp acc : Ptr} {word : Bits n}
      {tail : List (RawArc Ptr n cbits)}, BitsAt h sp word → GenerationAt key h dp data → TraceAt h acc tail →
      ∃ out q, Extends h out ∧ Valid out ∧ TraceAt out q (outgoing word ++ tail) ∧
        Within code h (initialRegisters [.pointer sp,.pointer dp,.pointer acc]) (code source)
          [.pointer q] out sourceBudget)
    {h : Heap} (hh : Valid h) {sources dp acc : Ptr} {words : List (Bits n)}
    {tail : List (RawArc Ptr n cbits)} (hw : WordsAt h sources words) (hg : GenerationAt key h dp data)
    (ht : TraceAt h acc tail) :
    ∃ out q, Extends h out ∧ Valid out ∧ TraceAt out q (words.flatMap outgoing ++ tail) ∧
      Within code h (initialRegisters [.pointer sources,.pointer dp,.pointer acc]) (code scan)
        [.pointer q] out ((sourceBudget+27)*words.length+13) := by
  exact RegisterListFlatMap.compiled (data := ()) code scan source hscan
    (fun h p w => BitsAt h p w) (fun h p (_ : Unit) => GenerationAt key h p data) TraceAt
    (fun he _ _ ht => ht.mono he) (fun he _ _ ht => ht.mono he)
    (fun (_ : Unit) w => outgoing w) sourceBudget
    (by
      intro heap valid xp dp acc word unit tail hx hd ha
      exact sourceCompiled valid hx hd ha) hh hw hg ht

/-- Generate IDs by binary range code, then invoke the same finite source
procedure once for each produced word. -/
theorem compiled (code : Code p) (range scan source add compare : Fin p)
    (hrange : code range = RegisterWordRange.rangeBody range add compare)
    (hscan : code scan = RegisterListFlatMap.body scan source)
    (hadd : code add = RegisterAdder.adderBody add)
    (hcompare : code compare = RegisterComparator.comparatorBody compare)
    (key : Walks.State Row → Bits n) (data : GenerationData Row n cbits)
    (outgoing : Bits n → List (RawArc Ptr n cbits)) (sourceBudget : ℕ)
    (sourceCompiled : ∀ {h : Heap}, Valid h → ∀ {sp dp acc : Ptr} {word : Bits n}
      {tail : List (RawArc Ptr n cbits)}, BitsAt h sp word → GenerationAt key h dp data → TraceAt h acc tail →
      ∃ out q, Extends h out ∧ Valid out ∧ TraceAt out q (outgoing word ++ tail) ∧
        Within code h (initialRegisters [.pointer sp,.pointer dp,.pointer acc]) (code source)
          [.pointer q] out sourceBudget)
    {h : Heap} (hh : Valid h) {dp lp zp op acc : Ptr} {limit one : Bits n}
    {tail : List (RawArc Ptr n cbits)} (hg : GenerationAt key h dp data)
    (hl : BitsAt h lp limit) (hz : BitsAt h zp (Bits.zero n)) (ho : BitsAt h op one)
    (hone : one.value = 1) (ht : TraceAt h acc tail) :
    ∃ out q, Extends h out ∧ Valid out ∧ TraceAt out q ((sourceWords limit).flatMap outgoing ++ tail) ∧
      Within code h (initialRegisters [.pointer dp,.pointer lp,.pointer zp,.pointer op,.pointer acc])
        (body range scan) [.pointer q] out
          (200*(n+1)*(limit.value+1)+(sourceBudget+27)*limit.value+30) := by
  obtain ⟨mid,sources,words,he,vm,hw,hv,enumerate⟩ :=
    RegisterWordRange.compiled code range add compare hrange hadd hcompare hh hz hl ho hone
  have heq : words = sourceWords limit := words_eq_range (by simpa only [Bits.value_zero,Nat.sub_zero] using hv)
  have hlen : words.length = limit.value := by simp [heq,sourceWords]
  obtain ⟨out,q,heout,vo,hq,scanRun⟩ := scan_compiled code scan source hscan key data outgoing sourceBudget
    sourceCompiled vm hw (hg.mono he) (ht.mono he)
  let r0 := initialRegisters [Value.pointer dp,.pointer lp,.pointer zp,.pointer op,.pointer acc]
  let r1 := bindResults r0 [5] [.pointer sources]
  let r2 := bindResults r1 [6] [.pointer q]
  have ret : Within code out r2 (.ret [.register 6]) [.pointer q] out 3 := by
    simpa [values,Atom.eval,r2,bindResults] using Within.ret code out r2 [.register 6]
  have scanArgs : values r1 [.register 5,.register 0,.register 4] =
      [.pointer sources,.pointer dp,.pointer acc] := by simp [values,Atom.eval,r1,r0,bindResults,initialRegisters]
  have scanCall := Within.call (procedure := scan) (arguments := [.register 5,.register 0,.register 4])
    (results := [6]) (regs := r1) (by simpa only [scanArgs] using scanRun) ret
  have rangeArgs : values r0 [.register 2,.register 1,.register 3] =
      [.pointer zp,.pointer lp,.pointer op] := by simp [values,Atom.eval,r0,initialRegisters]
  have rangeCall := Within.call (procedure := range) (arguments := [.register 2,.register 1,.register 3])
    (results := [5]) (regs := r0) (by simpa only [rangeArgs] using enumerate) scanCall
  refine ⟨out,q,he.trans heout,vo,by simpa only [heq] using hq,?_⟩
  exact rangeCall.mono (by simp only [RegisterWordRange.budget,Bits.value_zero,Nat.sub_zero,hlen,
    List.length_cons,List.length_nil];omega)

end WeightedMIS.RegisterAllSources
