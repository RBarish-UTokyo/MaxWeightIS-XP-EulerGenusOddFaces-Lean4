module

public import WeightedMIS.SpecFaces
public import WeightedMIS.OriginalFaces
public import WeightedMIS.Orientable

/-!
# Statement orientability gives a coherent face orientation

A two-colouring of the flags changed by `along`, `across` and `corner` is
constant on each oriented boundary cycle. Reading the colour at the chosen
root of every traced face gives face signs; the colour change across each edge
is exactly the internal coherence condition.
-/

@[expose] public section

namespace WeightedMIS.Spec

open EmbeddingFaces

/-- The sign bookkeeping on the four flags of one edge. -/
theorem boolSign_coherence (g : Bool → Bool → Bool)
    (halong : ∀ b t, g b (!t) ≠ g b t) (hacross : ∀ b t, g (!b) t ≠ g b t) (f0 f1 : Bool) :
    boolSign (g false (!f0)) * boolSign f0 = -(boolSign (g true (!f1)) * boolSign f1) := by
  have h1 := halong false false
  have h2 := halong true false
  have h3 := hacross false false
  simp only [Bool.not_false] at h1 h2 h3
  clear halong hacross
  cases f0 <;> cases f1 <;> simp only [Bool.not_false, Bool.not_true] <;>
  · generalize g false false = a at *
    generalize g false true = b at *
    generalize g true false = c at *
    generalize g true true = d at *
    cases a <;> cases b <;> cases c <;> cases d <;> simp at h1 h2 h3 <;> norm_num [boolSign]

namespace Map

variable (A : Map) (hA : A.IsClosedSurface)

/-- The flag of an edge side with the chosen boundary direction. -/
theorem oriented_side (e : Fin A.edges) (b : Bool) :
    (A.ribbon hA).Oriented ⟨e, b, !(A.ribbon hA).sidePairing.forward e b⟩ := by
  have hstart : (A.ribbon hA).sidePairing.startFlag ((A.ribbon hA).sidePairing.side e b) =
      ⟨e, b, !(A.ribbon hA).sidePairing.forward e b⟩ := by
    simp [SidePairing.startFlag, SidePairing.side, SidePairing.forward]
  rw [← hstart, Ribbon.sidePairing_startFlag]
  exact (A.ribbon hA).orbitFlag_oriented _

theorem faceOf_endpoint (e : Fin A.edges) (b t : Bool) :
    (A.ribbon hA).faceOf ⟨e, b, t⟩ = (A.ribbon hA).faceOf ⟨e, b, false⟩ := by
  cases t
  · rfl
  · exact (A.ribbon hA).faceOf_along ⟨e, b, false⟩

variable {A hA}

/-- A flag colouring of an orientable map is constant on rotation cycles. -/
theorem colour_sameCycle {c : Flag (Fin A.edges) → Bool}
    (hc : ∀ x, c x.along ≠ c x ∧ c x.across ≠ c x ∧ c (A.corner x) ≠ c x)
    {x y : EmbeddingFaces.Flag (Fin A.edges)} (h : (A.ribbon hA).rotation.SameCycle x y) :
    c ((Flag.equiv _).symm x) = c ((Flag.equiv _).symm y) := by
  have hrot : ∀ z, c ((Flag.equiv _).symm ((A.ribbon hA).rotation z)) = c ((Flag.equiv _).symm z) := by
    intro z
    obtain ⟨w, rfl⟩ := (Flag.equiv _).surjective z
    rw [A.ribbon_rotation hA, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    have h1 := (hc w.along).2.2
    have h2 := (hc w).1
    revert h1 h2
    cases c (A.corner w.along) <;> cases c w.along <;> cases c w <;> simp
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, hrot, ih]

/-- Statement orientability yields a coherent orientation of the internal
cellular embedding. -/
theorem nonempty_orientation (hO : A.Orientable) :
    Nonempty (A.cellular hA).sides.Orientation := by
  obtain ⟨c, hc⟩ := hO
  let R := A.ribbon hA
  have hroot : ∀ e b, c ((Flag.equiv _).symm (R.faceRoot (R.sidePairing.face e b))) =
      c ⟨e, b, !R.sidePairing.forward e b⟩ := by
    intro e b
    have ho := A.oriented_side hA e b
    unfold Ribbon.Oriented at ho
    rw [Ribbon.sidePairing_face, ← A.faceOf_endpoint hA e b (!R.sidePairing.forward e b)]
    exact colour_sameCycle hc ho
  refine ⟨⟨fun f => boolSign (c ((Flag.equiv _).symm (R.faceRoot f))), ?_, ?_⟩⟩
  · intro f
    cases c ((Flag.equiv _).symm (R.faceRoot f)) <;> simp [boolSign]
  · intro e
    change boolSign (c ((Flag.equiv _).symm (R.faceRoot (R.sidePairing.face e false)))) *
        boolSign (R.sidePairing.forward e false) =
      -(boolSign (c ((Flag.equiv _).symm (R.faceRoot (R.sidePairing.face e true)))) *
        boolSign (R.sidePairing.forward e true))
    rw [hroot, hroot]
    exact boolSign_coherence (fun b t => c ⟨e, b, t⟩) (fun b t => (hc ⟨e, b, t⟩).1)
      (fun b t => (hc ⟨e, b, t⟩).2.1) _ _

end Map

end WeightedMIS.Spec
