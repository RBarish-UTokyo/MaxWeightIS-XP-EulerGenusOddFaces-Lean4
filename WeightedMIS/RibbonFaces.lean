module

public import WeightedMIS.RibbonTracing

/-!
# Facial components and their two orientations

The two fixed-point-free matchings of a ribbon boundary form unoriented
circles. Their rotation has exactly two oriented orbits on every circle.
A representative of each component chooses one orientation; the chosen flags
contain exactly one endpoint of every original edge side.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces.Ribbon

open SidePairing

variable {V E : Type*} [Fintype E] {left right : E → V} (R : Ribbon left right)

omit [Fintype E] in
@[simp] theorem corner_symm (x : Flag E) : R.corner.symm x = R.corner x := by
  apply R.corner.injective
  rw [Equiv.apply_symm_apply, R.involutive]

omit [Fintype E] in
theorem along_reverses_rotation : Function.Semiconj along R.rotation R.rotation.symm := by
  intro x
  simp only [rotation, Equiv.trans_apply, Equiv.symm_trans_apply, R.corner_symm]
  rfl

omit [Fintype E] in
theorem reflected_rotation_ne_self (x : Flag E) : along (R.rotation x) ≠ x := by
  intro h
  apply R.ne_self (along x)
  have heq := congrArg along h
  simpa only [rotation, Equiv.trans_apply, along_along] using heq

/-- Reversing a side exchanges its two distinct rotation orbits. -/
theorem not_sameCycle_along (x : Flag E) : ¬R.rotation.SameCycle x (along x) :=
  PermutationDeletion.reversing_no_sameCycle R.rotation along R.along_reverses_rotation
    along_ne_self R.reflected_rotation_ne_self x

theorem sameCycle_along {x y : Flag E} (h : R.rotation.SameCycle x y) :
    R.rotation.SameCycle (along x) (along y) := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have htrace := R.along_reverses_rotation.iterate_right n x
  have hn' : (R.rotation : Flag E → Flag E)^[n] x = y := by
    simpa only [Equiv.Perm.coe_pow] using hn
  rw [hn'] at htrace
  have hi : (R.rotation⁻¹).SameCycle (along x) (along y) := by
    refine ⟨(n : ℤ), ?_⟩
    simpa only [zpow_natCast, Equiv.Perm.coe_pow, Equiv.Perm.coe_inv] using htrace.symm
  exact hi.of_inv

@[simp] theorem sameCycle_along_iff (x y : Flag E) :
    R.rotation.SameCycle (along x) (along y) ↔ R.rotation.SameCycle x y := by
  constructor
  · intro h
    simpa only [along_along] using R.sameCycle_along h
  · exact R.sameCycle_along

/-- Two flags lie on the same unoriented boundary circle. -/
def SameFace (x y : Flag E) : Prop :=
  R.rotation.SameCycle x y ∨ R.rotation.SameCycle x (along y)

omit [Fintype E] in
theorem sameFace_refl (x : Flag E) : R.SameFace x x :=
  Or.inl (Equiv.Perm.SameCycle.refl _ _)

theorem sameFace_symm {x y : Flag E} (h : R.SameFace x y) : R.SameFace y x := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by simpa only [along_along] using (R.sameCycle_along h).symm)

theorem sameFace_trans {x y z : Flag E} (hxy : R.SameFace x y) (hyz : R.SameFace y z) :
    R.SameFace x z := by
  rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
  · exact Or.inl (hxy.trans hyz)
  · exact Or.inr (hxy.trans hyz)
  · exact Or.inr (hxy.trans (R.sameCycle_along hyz))
  · exact Or.inl (hxy.trans (by simpa only [along_along] using R.sameCycle_along hyz))

/-- The equivalence relation of actual unoriented boundary circles. -/
def faceSetoid : Setoid (Flag E) where
  r := R.SameFace
  iseqv := ⟨R.sameFace_refl, R.sameFace_symm, R.sameFace_trans⟩

/-- Boundary circles of the ribbon, prior to choosing their orientations. -/
abbrev FaceIndex := Quotient R.faceSetoid

noncomputable instance : Fintype R.FaceIndex := Fintype.ofFinite _

/-- The boundary circle containing a flag. -/
def faceOf (x : Flag E) : R.FaceIndex := Quotient.mk _ x

/-- Choose one flag, and therefore one direction, on each boundary circle. -/
noncomputable def faceRoot (f : R.FaceIndex) : Flag E := Quotient.out f

@[simp] theorem faceOf_root (f : R.FaceIndex) : R.faceOf (R.faceRoot f) = f :=
  Quotient.out_eq f

theorem root_related (x : Flag E) : R.SameFace (R.faceRoot (R.faceOf x)) x :=
  Quotient.exact (R.faceOf_root (R.faceOf x))

@[simp] theorem faceOf_along (x : Flag E) : R.faceOf (along x) = R.faceOf x := by
  apply Quotient.sound
  exact Or.inr (Equiv.Perm.SameCycle.refl _ _)

theorem faceOf_eq_of_sameCycle {x y : Flag E} (h : R.rotation.SameCycle x y) :
    R.faceOf x = R.faceOf y := Quotient.sound (Or.inl h)

/-- The chosen orientation on a boundary circle. -/
def Oriented (x : Flag E) : Prop := R.rotation.SameCycle (R.faceRoot (R.faceOf x)) x

/-- Exactly one of a side's two endpoint flags has the chosen direction. -/
theorem oriented_or_along (x : Flag E) : R.Oriented x ∨ R.Oriented (along x) := by
  have h := R.root_related x
  simpa only [Oriented, SameFace, R.faceOf_along] using h

theorem not_oriented_both (x : Flag E) : ¬(R.Oriented x ∧ R.Oriented (along x)) := by
  rintro ⟨hx, hy⟩
  unfold Oriented at hx hy
  rw [R.faceOf_along] at hy
  exact R.not_sameCycle_along x (hx.symm.trans hy)

@[simp] theorem oriented_along_iff (x : Flag E) : R.Oriented (along x) ↔ ¬R.Oriented x := by
  constructor
  · intro h hx
    exact R.not_oriented_both x ⟨hx, h⟩
  · intro h
    exact (R.oriented_or_along x).resolve_left h

/-- Flags whose direction agrees with the selected boundary orientation. -/
abbrev OrientedFlag := {x : Flag E // R.Oriented x}

/-- Forget the endpoint of an oriented side traversal. -/
def orientedSide (x : R.OrientedFlag) : E × Bool := (x.val.edge, x.val.side)

theorem orientedSide_injective : Function.Injective R.orientedSide := by
  rintro ⟨⟨e, s, t⟩, hx⟩ ⟨⟨e', s', t'⟩, hy⟩ h
  have he : e = e' := congrArg Prod.fst h
  have hs : s = s' := congrArg Prod.snd h
  subst e'
  subst s'
  apply Subtype.ext
  by_cases ht : t = t'
  · subst t'
    rfl
  · exfalso
    have hflip : t' = !t := by cases t <;> cases t' <;> simp_all
    subst t'
    exact R.not_oriented_both ⟨e, s, t⟩ ⟨hx, hy⟩

theorem orientedSide_surjective : Function.Surjective R.orientedSide := by
  rintro ⟨e, s⟩
  rcases R.oriented_or_along (⟨e, s, false⟩ : Flag E) with h | h
  · exact ⟨⟨⟨e, s, false⟩, h⟩, rfl⟩
  · exact ⟨⟨⟨e, s, true⟩, h⟩, rfl⟩

/-- Chosen directed occurrences are in bijection with actual edge sides. -/
noncomputable def orientedSideEquiv : R.OrientedFlag ≃ E × Bool :=
  Equiv.ofBijective R.orientedSide ⟨R.orientedSide_injective, R.orientedSide_surjective⟩

/-- Indexed positions along one chosen orientation of each boundary circle. -/
abbrev RotationOccurrence := Σ f : R.FaceIndex,
  Fin (Function.minimalPeriod R.rotation (R.faceRoot f))

/-- The actual flag visited at an indexed boundary position. -/
noncomputable def orbitFlag (d : R.RotationOccurrence) : Flag E :=
  (R.rotation : Flag E → Flag E)^[d.2.val] (R.faceRoot d.1)

theorem root_sameCycle_orbitFlag (d : R.RotationOccurrence) :
    R.rotation.SameCycle (R.faceRoot d.1) (R.orbitFlag d) := by
  refine ⟨(d.2.val : ℤ), ?_⟩
  rw [zpow_natCast, Equiv.Perm.coe_pow]
  rfl

@[simp] theorem faceOf_orbitFlag (d : R.RotationOccurrence) :
    R.faceOf (R.orbitFlag d) = d.1 := by
  rw [← R.faceOf_eq_of_sameCycle (R.root_sameCycle_orbitFlag d), R.faceOf_root]

theorem orbitFlag_oriented (d : R.RotationOccurrence) : R.Oriented (R.orbitFlag d) := by
  unfold Oriented
  rw [R.faceOf_orbitFlag]
  exact R.root_sameCycle_orbitFlag d

noncomputable def orbitMap (d : R.RotationOccurrence) : R.OrientedFlag :=
  ⟨R.orbitFlag d, R.orbitFlag_oriented d⟩

theorem orbitMap_injective : Function.Injective R.orbitMap := by
  rintro ⟨f, i⟩ ⟨g, j⟩ h
  have hf := congrArg (fun x : R.OrientedFlag => R.faceOf x.val) h
  simp only [orbitMap, R.faceOf_orbitFlag] at hf
  subst g
  have hv := congrArg (fun x : R.OrientedFlag => x.val) h
  change (R.rotation : Flag E → Flag E)^[i.val] (R.faceRoot f) =
    (R.rotation : Flag E → Flag E)^[j.val] (R.faceRoot f) at hv
  have hij : i = j := Fin.ext
    ((Function.iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt).mp hv)
  subst j
  rfl

theorem orbitMap_surjective : Function.Surjective R.orbitMap := by
  intro y
  obtain ⟨n, hn⟩ := y.property.exists_nat_pow_eq
  have hp : 0 < Function.minimalPeriod R.rotation (R.faceRoot (R.faceOf y.val)) :=
    Function.minimalPeriod_pos_of_mem_periodicPts (R.rotation.injective.mem_periodicPts _)
  refine ⟨⟨R.faceOf y.val, ⟨n % Function.minimalPeriod R.rotation (R.faceRoot (R.faceOf y.val)),
    Nat.mod_lt _ hp⟩⟩, ?_⟩
  apply Subtype.ext
  change (R.rotation : Flag E → Flag E)^[n % Function.minimalPeriod R.rotation
    (R.faceRoot (R.faceOf y.val))] (R.faceRoot (R.faceOf y.val)) = y.val
  rw [Function.iterate_mod_minimalPeriod_eq]
  simpa only [Equiv.Perm.coe_pow] using hn

/-- Chosen facial trace positions enumerate exactly the oriented flags. -/
noncomputable def orbitEquiv : R.RotationOccurrence ≃ R.OrientedFlag :=
  Equiv.ofBijective R.orbitMap ⟨R.orbitMap_injective, R.orbitMap_surjective⟩

/-- The actual closed facial walks obtained from the corner system. -/
noncomputable def faces (f : R.FaceIndex) : Faces.Face left right :=
  R.tracedFace (R.faceRoot f)

/-- Boundary position indices agree with the periods used by the tracer. -/
noncomputable def occurrenceEquiv : Occurrence R.faces ≃ R.RotationOccurrence :=
  Equiv.sigmaCongrRight (fun f => finCongr (R.tracedFace_length (R.faceRoot f)))

/-- Every actual original edge side appears exactly once among the newly
traced closed facial walks. This pairing is constructed from the corner
matching rather than assumed. -/
noncomputable def sidePairing : SidePairing R.faces where
  pairing := R.occurrenceEquiv.trans (R.orbitEquiv.trans R.orientedSideEquiv)
  edge_eq d := by
    change (R.tracedFace (R.faceRoot d.1)).boundary.edgeAt d.2 =
      ((R.rotation : Flag E → Flag E)^[d.2.val] (R.faceRoot d.1)).edge
    exact R.tracedFace_edgeAt (R.faceRoot d.1) d.2

theorem faces_positive (f : R.FaceIndex) : 0 < (R.faces f).boundary.length :=
  R.tracedFace_positive _

/-- The flag at a genuine boundary occurrence in the constructed faces. -/
noncomputable def positionFlag (d : Occurrence R.faces) : Flag E :=
  R.orbitFlag (R.occurrenceEquiv d)

@[simp] theorem sidePairing_startFlag (d : Occurrence R.faces) :
    R.sidePairing.startFlag d = R.positionFlag d := by
  change (⟨(R.positionFlag d).edge, (R.positionFlag d).side,
    !((R.faces d.1).boundary.forwardAt d.2)⟩ : Flag E) = _
  have h : (R.faces d.1).boundary.forwardAt d.2 = !(R.positionFlag d).endpoint :=
    R.tracedFace_forwardAt (R.faceRoot d.1) d.2
  rw [h]
  change (⟨(R.positionFlag d).edge, (R.positionFlag d).side,
    !(!(R.positionFlag d).endpoint)⟩ : Flag E) = _
  simp only [Bool.not_not]

@[simp] theorem sidePairing_endFlag (d : Occurrence R.faces) :
    R.sidePairing.endFlag d = along (R.positionFlag d) := by
  change (⟨(R.positionFlag d).edge, (R.positionFlag d).side,
    (R.faces d.1).boundary.forwardAt d.2⟩ : Flag E) = _
  have h : (R.faces d.1).boundary.forwardAt d.2 = !(R.positionFlag d).endpoint :=
    R.tracedFace_forwardAt (R.faceRoot d.1) d.2
  rw [h]
  rfl

/-- Rotating a finite period list follows the underlying permutation even at
its last-to-first position. -/
theorem iterate_finRotate {A : Type*} (f : A → A) (x : A) (n : ℕ)
    (hperiod : f^[n] x = x) (i : Fin n) :
    f^[(finRotate n i).val] x = f (f^[i.val] x) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      rw [coe_finRotate]
      by_cases hi : i = Fin.last n
      · subst i
        simp only [ite_true, Function.iterate_zero, id_eq, Fin.val_last]
        rw [Function.iterate_succ_apply'] at hperiod
        exact hperiod.symm
      · rw [ite_eq_right hi, Function.iterate_succ_apply']

/-- Consecutive constructed facial occurrences are the actual corner-system
rotation, including the last-to-first corner. -/
theorem positionFlag_faceNext (d : Occurrence R.faces) :
    R.positionFlag (faceNext d) = R.rotation (R.positionFlag d) := by
  change (R.rotation : Flag E → Flag E)^[(finRotate (R.faces d.1).boundary.length d.2).val]
    (R.faceRoot d.1) = R.rotation ((R.rotation : Flag E → Flag E)^[d.2.val] (R.faceRoot d.1))
  apply iterate_finRotate
  simp only [faces, R.tracedFace_length, Function.iterate_minimalPeriod]

/-- Tracing and pairing recover precisely the original corner involution. -/
theorem sidePairing_corner (x : Flag E) : R.sidePairing.corner x = R.corner x := by
  obtain ⟨⟨d, t⟩, rfl⟩ := R.sidePairing.flagEquiv.surjective x
  cases t
  · rw [R.sidePairing.flagEquiv_false, R.sidePairing.corner_startFlag,
      R.sidePairing_startFlag, R.sidePairing_endFlag]
    have h := R.positionFlag_faceNext (facePrev d)
    simp only [facePrev, Equiv.apply_symm_apply] at h
    rw [h]
    change along (R.positionFlag (facePrev d)) = R.corner (R.corner (along (R.positionFlag (facePrev d))))
    rw [R.involutive]
  · rw [R.sidePairing.flagEquiv_true, R.sidePairing.corner_endFlag,
      R.sidePairing_endFlag, R.sidePairing_startFlag, R.positionFlag_faceNext]
    rfl

end WeightedMIS.EmbeddingFaces.Ribbon
