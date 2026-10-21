module

public import WeightedMIS.RegisterCandidateCompiled
public import WeightedMIS.RegisterListFlatMap
public import WeightedMIS.CompiledTemplatePrimitives

/-! # Finite scanning of the actual signed-column arc templates -/

@[expose] public section

namespace WeightedMIS.RegisterTemplateScan

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.ExpandedWords WeightedMIS.EfficientSearch.Pointer WeightedMIS.CompiledTemplates

variable {p n cbits : ℕ} {Row : Type*}

def TemplateOfLengthAt (key : Walks.State Row → Bits n) (d : ℕ) (h : Heap) (ptr : Ptr)
    (a : Template Row (ArcMetadata n cbits)) : Prop :=
  TemplateAt key MetadataAt h ptr a ∧ a.metadata.deltas.length = d

def ContextOfLengthAt (d : ℕ) (h : Heap) (ptr : Ptr) (ctx : WorkContext n) : Prop :=
  ContextAt h ptr ctx ∧ ctx.digits.length = d

theorem ListRep.strengthen {α : Type*} {R : Heap → Ptr → α → Prop} {h : Heap} {ptr : Ptr}
    {xs : List α} (hl : ListRep R h ptr xs) (P : α → Prop) (hp : ∀ x ∈ xs, P x) :
    ListRep (fun h p x => R h p x ∧ P x) h ptr xs := by
  obtain ⟨ps,hl,hr⟩ := hl
  refine ⟨ps,hl,?_⟩
  clear hl
  induction hr with
  | nil => exact .nil
  | @cons a x ps xs hhead htail ih =>
    exact .cons ⟨hhead,hp x (by simp)⟩ (ih (fun y hy => hp y (by simp [hy])))

theorem compiled (code : Code p) (self item : Fin p)
    (ids : RegisterCandidate.Procedures p) (arith : RegisterHorner.Procedures p)
    (digit complement : Fin p) (hc : ids.Matches code arith digit complement)
    (hself : code self = RegisterListFlatMap.body self item)
    (hitem : code item = RegisterCandidate.candidateBody ids)
    {key : Walks.State Row → Bits n} {d : ℕ} {h : Heap} (hh : Valid h)
    {list cp ap : Ptr} {ctx : WorkContext n} {as : List (Template Row (ArcMetadata n cbits))}
    {tail : List (RawArc Ptr n cbits)}
    (hl : ListRep (TemplateAt key MetadataAt) h list as) (hctx : ContextAt h cp ctx)
    (ha : TraceAt h ap tail) (hcd : ctx.digits.length = d)
    (had : ∀ a ∈ as, a.metadata.deltas.length = d) :
    ∃ out q, Extends h out ∧ Valid out ∧ TraceAt out q (as.flatMap (candidate key ctx) ++ tail) ∧
      Within code h (initialRegisters [.pointer list,.pointer cp,.pointer ap]) (code self)
        [.pointer q] out ((RegisterCandidate.candidateBudget n d + 27)*as.length + 13) := by
  apply RegisterListFlatMap.compiled code self item hself
    (TemplateOfLengthAt key d) (ContextOfLengthAt d) TraceAt
    (f := candidate key) (itemBudget := RegisterCandidate.candidateBudget n d)
  · intro old new he ptr a ht
    exact ⟨TemplateAt.mono (metaAt := MetadataAt) (fun ext hp => MetadataAt.mono ext hp) he ht.1,ht.2⟩
  · intro old new he ptr ctx ht
    exact ⟨ContextAt.mono he ht.1,ht.2⟩
  · intro old ho tp cp ap a ctx tail ht hctx ha
    obtain ⟨out,q,he,hv,hq,run⟩ := RegisterCandidate.compiled code ids arith digit complement hc ho
      ht.1 hctx.1 ha (hctx.2.trans ht.2.symm)
    exact ⟨out,q,he,hv,hq,by simpa only [hitem,hctx.2] using run⟩
  · exact hh
  · exact ListRep.strengthen hl (fun a => a.metadata.deltas.length = d) had
  · exact ⟨hctx,hcd⟩
  · exact ha

end WeightedMIS.RegisterTemplateScan
