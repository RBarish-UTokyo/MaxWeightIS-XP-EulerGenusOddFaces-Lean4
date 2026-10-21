module

public import WeightedMIS.ExpandedEmptyCoordinates
public import WeightedMIS.ExpandedContext

/-! # Exact local signed-arc semantics of the binary candidate calculation -/

@[expose] public section

namespace WeightedMIS.ExpandedWords

open WeightedMIS.EfficientSearch WeightedMIS.SparseSearchGraph WeightedMIS.NodeEncoding
open WeightedMIS.Expanded WeightedMIS.RegisterHorner WeightedMIS.SearchConstruction
open WeightedMIS.PointerMemory WeightedMIS.Walks

/-- The shared arithmetic words contain the actual finite graph dimensions. -/
def ArithmeticRepresents {width : ℕ} (ar : ArithmeticWords width) (r d radius : ℕ) : Prop :=
  (d = 0 ∨ ar.base.value = 4 * radius + 1) ∧ ar.states.value = 2 * r + 1 ∧
    ar.block.value = 2 * (4 * radius + 1) ^ d ∧ ar.one.value = 1 ∧ ar.two.value = 2

/-- A working context contains the actual signed states, parity, and box digits. -/
def ContextRepresents {width r d radius : ℕ} (ctx : WorkContext width)
    (anchor current : State (Fin r)) (z : Box (Fin d) radius) (parity : ZMod 2) : Prop :=
  ctx.anchor.value = (stateEquiv r anchor).val ∧
    ctx.current.value = (stateEquiv r current).val ∧ ctx.parity.value = parity.val ∧
    ctx.digits = boxWords width z ∧ ArithmeticRepresents ctx.arithmetic r d radius

/-- Toggling an actual binary parity digit computes addition in ZMod 2. -/
theorem toggle_parity_value {width : ℕ} (one word : Bits width) (parity : ZMod 2) (bit : Bool)
    (h1 : one.value = 1) (hp : word.value = parity.val) :
    (if bit then (Bits.subtract one word).1 else word).value =
      (parity + if bit then 1 else 0 : ZMod 2).val := by
  cases bit with
  | false => simpa using hp
  | true =>
    have hle : word.value ≤ one.value := by
      have hlt : parity.val < 2 := parity.isLt
      omega
    simp only [ite_true]
    rw [(Bits.subtract_value_of_le one word hle).2, h1, hp]
    fin_cases parity <;> decide

/-- The finite node arithmetic encodes an actual target working state exactly. -/
theorem encode_target_word {width r d radius : ℕ} (ar : ArithmeticWords width)
    (ha : ArithmeticRepresents ar r d radius) (anchorWord currentWord boxWord parityWord : Bits width)
    (anchor current : State (Fin r)) (z : Box (Fin d) radius) (parity : ZMod 2)
    (hanchor : anchorWord.value = (stateEquiv r anchor).val)
    (hcurrent : currentWord.value = (stateEquiv r current).val)
    (hbox : boxWord.value = (boxEquiv d radius z).val) (hparity : parityWord.value = parity.val)
    (hcap : nodeCount r d radius ≤ 2 ^ width) :
    ScalarNodeCodec.encodeWords ar.states ar.block ar.one ar.two
      ⟨false, anchorWord, currentWord, boxWord, parityWord⟩ =
        encodeBits width (nodeEquiv r d radius (.work anchor current z parity)).val := by
  obtain ⟨_, hs, ht, h1, h2⟩ := ha
  have hcoords : (ScalarNodeCodec.Words.values
      ⟨false, anchorWord, currentWord, boxWord, parityWord⟩) =
      ScalarNodeCodec.coordinates (.work anchor current z parity) := by
    simp [ScalarNodeCodec.Words.values, ScalarNodeCodec.coordinates, hanchor, hcurrent, hbox, hparity]
  have he : ScalarNodeCodec.encode ar.states.value ar.block.value
      (ScalarNodeCodec.Words.values ⟨false, anchorWord, currentWord, boxWord, parityWord⟩) =
      (nodeEquiv r d radius (.work anchor current z parity)).val := by
    rw [hs, ht, hcoords, ScalarNodeCodec.encode_coordinates]
  have hfit := (nodeEquiv r d radius (.work anchor current z parity)).isLt.trans_le hcap
  apply bits_value_injective
  rw [ScalarNodeCodec.encodeWords_exact _ _ _ _ _ h1 h2 (by rw [he]; exact hfit), he]
  exact (encodeBits_value _ _ hfit).symm

/-- Every binary candidate is exactly the corresponding genuine expanded-graph
move, including range rejection and the original shared weight/label record. -/
theorem candidate_eq_moveCandidate {width cbits r m d radius : ℕ}
    (key : State (Fin r) → Bits width) (hkey : ∀ v, (key v).value = (stateEquiv r v).val)
    (C : Fin m → Column (Fin r)) (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2)
    (anchor current : State (Fin r)) (z : Box (Fin d) radius) (parity : ZMod 2)
    (ctx : WorkContext width) (hctx : ContextRepresents ctx anchor current z parity)
    (a : Walks.Arc C) (metadata : ArcMetadata width cbits)
    (deltas : Fin d → SignedWord width)
    (hdeltas : metadata.deltas = List.ofFn deltas)
    (hdelta : ∀ i, (deltas i).value = W a.val.1 i)
    (hparity : (if metadata.parity then 1 else 0 : ZMod 2) = π a.val.1)
    (hcap : nodeCount r d radius ≤ 2 ^ width) :
    candidate key ctx ⟨source C a, target C a, metadata⟩ =
      (moveCandidate C W π radius anchor current z parity a).toList.map (fun x =>
        (ctx.source, ⟨encodeBits width (nodeEquiv r d radius x.2).val,
          metadata.weight, metadata.label⟩)) := by
  obtain ⟨ha, hc, hp, hd, har⟩ := hctx
  have hcmp : (Bits.compare (key (source C a)) ctx.current).1 = .eq ↔ source C a = current := by
    rw [(Bits.compare_correct _ _).2.1, hkey, hc]
    exact ⟨fun h => (stateEquiv r).injective (Fin.ext h), fun h => by rw [h]⟩
  have hboxcap : (4 * radius + 1) ^ d ≤ 2 ^ width := by
    apply le_trans _ hcap
    calc
      (4 * radius + 1) ^ d ≤ 2 * (4 * radius + 1) ^ d := by omega
      _ ≤ nodeCount r d radius := Nat.le_mul_of_pos_right _ (by omega)
  by_cases hsource : source C a = current
  · have htest := hcmp.mpr hsource
    unfold candidate
    rw [if_pos htest]
    simp only [hd, hdeltas, moveCandidate, hsource, ↓reduceIte]
    rw [updateWords_box_or_empty ctx.arithmetic.base z deltas (W a.val.1) har.1 hdelta]
    cases hu : updateBox radius z (W a.val.1) with
    | none => rfl
    | some out =>
      simp only [Option.map_some, Option.toList_some, List.map_cons, List.map_nil]
      have hbox := encodeWords_box_or_empty ctx.arithmetic.base out har.1 hboxcap
      have hpar := toggle_parity_value ctx.arithmetic.one ctx.parity parity metadata.parity har.2.2.2.1 hp
      rw [hparity] at hpar
      have henc := encode_target_word ctx.arithmetic har ctx.anchor (key (target C a))
        (encodeWords ctx.arithmetic.base (boxWords width out))
        (if metadata.parity then (Bits.subtract ctx.arithmetic.one ctx.parity).1 else ctx.parity)
        anchor (target C a) out (parity + π a.val.1) ha (hkey _) hbox hpar hcap
      rw [henc]
  · have htest := mt hcmp.mp hsource
    simp [candidate, htest, moveCandidate, hsource]

end WeightedMIS.ExpandedWords
