module

public import WeightedMIS.FaceStageProgram

/-!
# A concrete code table for the face stage

All procedures of the face stage are placed in one fixed table of 36 finite
command bodies; the comparator and the binary adder are shared. The entry
procedure is number 0.
-/

@[expose] public section

namespace WeightedMIS.FaceStageCode

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.RibbonTable WeightedMIS.EmbeddingFaces WeightedMIS.CompiledTemplates
open WeightedMIS.RegisterFaceColumns WeightedMIS.RegisterEvenMatrix WeightedMIS.FaceStageProgram
open WeightedMIS.RegisterFaceRow WeightedMIS.RegisterPotentialStep WeightedMIS.EfficientSearch.Pointer

/-- The fixed face-stage program. -/
def program : Code 36 :=
  ![stageBody 1 18 28 29 31 34,
    RegisterRibbonCycles.cyclesBody 2 6,
    RegisterRibbonCycles.keysBody 3,
    RegisterListFlatMap.body 3 4,
    RegisterRibbonCycles.keyItemBody,
    RegisterRibbonCycles.rotBody 13 14,
    RegisterKeyFaceEnumeration.scanBody 6 7 9 11,
    RegisterMembership.membershipBody 7 8,
    RegisterComparator.comparatorBody 8,
    RegisterKeyTrace.cycleBody 10 5,
    RegisterKeyTrace.loopBody 10 5 8,
    RegisterListFlatMap.body 11 12,
    RegisterKeyFaceEnumeration.mirrorItemBody 13,
    RegisterFlagKeys.alongBody,
    RegisterRecordLookup.cornerBody 15 16,
    RegisterFlagKeys.splitBody,
    RegisterListFind.body 16 17,
    RegisterRecordLookup.keyMatchBody 8,
    RegisterListMap.body 18 19,
    rowsItemBody 20,
    RegisterListMap.body 20 21,
    rowItemBody 22,
    entryBody 22 23 8 24,
    RegisterFlagKeys.edgePartBody,
    RegisterSignedAdd.signedAddBody 25 8 26,
    RegisterAdder.adderBody 25,
    RegisterSubtractor.subtractorBody 27 25,
    RegisterComplement.complementBody 27,
    RegisterRowRecords.recordsBody 28 25,
    RegisterListMap.body 29 30,
    RegisterFaceColumnStage.initItemBody,
    RegisterFaceColumnStage.colsBody 31 32,
    RegisterListZip.body 32 33,
    stubItemBody 8,
    RegisterListMap.body 34 35,
    RegisterFaceColumnStage.convItemBody]

/-- Procedure numbers of the fixed program. -/
def ids : FaceStageProgram.Procedures 36 where
  top := 0
  cyc :=
    { top := 1, keys := 2, keyFlat := 3, keyItem := 4, rot := 5,
      enum := ⟨6, 7, 8, 9, 10, 5, 11, 12, 13⟩,
      lookup := { corner := 14, split := 15, find := 16, keyMatch := 17, cmp := 8 } }
  rowsIds :=
    { rows := 18, rowsItem := 19, row := 20, rowItem := 21, entry := 22, edge := 23,
      ar := { sadd := 24, add := 25, cmp := 8, sub := 26, complement := 27 } }
  records := 28
  init := 29
  initItem := 30
  cols := 31
  zip := 32
  stubItem := 33
  conv := 34
  convItem := 35

theorem ids_matches : ids.Matches program :=
  ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl⟩⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The fixed program computes the even-face columns in the template ABI, the
stored even rows as signed words, and the state counter `2 r + 1`. -/
theorem program_correct {W b wk n m : ℕ} {left right : Fin m → Fin n} (R : Ribbon left right)
    (hW : m < 2 ^ W) (hb : 4 * m < 2 ^ b) (hwk : 8 * m + 1 < 2 ^ wk)
    (one zero : Bits b) (hone : one.value = 1) (hzero : zero.value = 0)
    {h : Heap} (hh : Valid h) {tp cp op : Ptr} (hT : RecordsAt h tp (encodeRibbon W R))
    (hc : ConstsAt one zero h cp) (ho : BitsAt h op (word wk 1)) :
    ∃ out colsPtr rowsPtr cntPtr, ∃ ws : List (List (Word b)), Extends h out ∧ Valid out ∧
      ListRep (ColumnAt (stateKey wk (R.evenRootIndices (Flag.canonicalOrder m)).length)) out colsPtr
        ((List.finRange m).map (R.computedColumn (Flag.canonicalOrder m))) ∧
      RowsAt out rowsPtr ws ∧
      List.Forall₂ (List.Forall₂ (fun w z => value w = z)) ws R.storedEvenMatrix ∧
      BitsAt out cntPtr (word wk (2 * (R.evenRootIndices (Flag.canonicalOrder m)).length + 1)) ∧
      Within program h (initialRegisters [.pointer tp, .pointer cp, .pointer op]) (program 0)
        [.pointer colsPtr, .pointer rowsPtr, .pointer cntPtr] out (stageBudget W b wk m) :=
  stage_compiled ids program ids_matches R hW hb hwk one zero hone hzero hh hT hc ho

end WeightedMIS.FaceStageCode
