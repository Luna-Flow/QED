import QEDFV.HOL.Definitions

/-! Consequences of constructor congruence: a sequent that does not mention a
type-constructor id `k` keeps its validity when the carrier of `k` is changed, and the
hypothesis cannot be dropped. -/
namespace QEDFV.HOL

variable {κ κ' : TyConVal}

theorem admissible_iff_of_isAdmissible (hκ : κ.IsAdmissible) (hκ' : κ'.IsAdmissible)
    (ρ : TypeVal) : Admissible κ ρ ↔ Admissible κ' ρ :=
  ⟨fun h ↦ ⟨h.var, hκ'⟩, fun h ↦ ⟨h.var, hκ⟩⟩

/-- Changing the carrier of a constructor id `k` that the sequent does not mention
preserves validity, provided both constructor interpretations are admissible. -/
theorem valid_iff_of_tyCon_absent (hκ : κ.IsAdmissible) (hκ' : κ'.IsAdmissible) (k : Nat)
    (hoff : ∀ j, j ≠ k → ∀ (n : Nat) (as : Fin n → Type), κ.carrier j n as = κ'.carrier j n as)
    {S : Signature} {Γ : List Ty} (I : ConstVal κ S) (J : ConstVal κ' S) (s : Sequent S Γ)
    (hk : k ∉ s.tyCons) (hAgree : ∀ c, c ∈ s.constIds → I.AgreeAt J s.tyCons c) :
    Valid I s ↔ Valid J s :=
  valid_iff_κ I J (admissible_iff_of_isAdmissible hκ hκ')
    (fun j hj n as ↦ hoff j (fun h ↦ hk (h ▸ hj)) n as) hAgree

/-- The nullary type `k`. -/
def conTy (k : Nat) : Ty := .con k 0 Fin.elim0

@[simp] theorem conTy_tyCons (k : Nat) : (conTy k).tyCons = {k} := by
  ext i
  simp [conTy, Ty.tyCons]

/-- `∀ x y : A, x = y`. -/
def allEqSentence (S : Signature) (A : Ty) : Sequent S [] :=
  { hyps := []
  , concl := Term.all (a := A) (Γ := [])
      (Term.all (a := A) (Γ := [A])
        (Term.equal (Γ := [A, A]) (a := A) (Term.var (.succ .zero)) (Term.var .zero))) }

/-- A constructor interpretation in which constructor `0` denotes `Bool`. -/
def boolAtZero : TyConVal := ⟨fun j _ _ ↦ if j = 0 then Bool else PUnit⟩

theorem boolAtZero_isAdmissible : boolAtZero.IsAdmissible := by
  intro k n as _
  by_cases h : k = 0
  · exact ⟨by simpa [boolAtZero, h] using true⟩
  · exact ⟨by simpa [boolAtZero, h] using PUnit.unit⟩

theorem defaultTyCon_isAdmissible : defaultTyCon.IsAdmissible :=
  fun _ _ _ _ ↦ ⟨PUnit.unit⟩

theorem allEqSentence_constIds (S : Signature) (A : Ty) :
    (allEqSentence S A).constIds = ∅ := by
  simp [allEqSentence, Sequent.constIds, Term.constIds]

theorem allEqSentence_tyCons (S : Signature) (A : Ty) :
    (allEqSentence S A).tyCons = A.tyCons := by
  ext k
  simp [allEqSentence, Sequent.tyCons, Term.tyCons, Ty.tyCons]

/-- A sentence about constructor `1` only is valid under the default interpretation and
stays valid when constructor `0` is reinterpreted as `Bool`, for every pair of constant
interpretations. -/
theorem valid_allEq_one_unchanged (S : Signature) (I : ConstVal defaultTyCon S)
    (J : ConstVal boolAtZero S) :
    Valid I (allEqSentence S (conTy 1)) ∧ Valid J (allEqSentence S (conTy 1)) := by
  have hI : Valid I (allEqSentence S (conTy 1)) := by
    intro ρ hρ η _ x y
    rfl
  refine ⟨hI, ?_⟩
  refine (valid_iff_of_tyCon_absent defaultTyCon_isAdmissible boolAtZero_isAdmissible 0
    ?_ I J _ ?_ ?_).mp hI
  · intro j hj n as
    simp [defaultTyCon, boolAtZero, hj]
  · simp [allEqSentence_tyCons]
  · intro c hc
    simp [allEqSentence_constIds] at hc

/-- The hypothesis `k ∉ s.tyCons` cannot be dropped: `∀ x y : k, x = y` is valid when
constructor `0` denotes `PUnit` and invalid when it denotes `Bool`. -/
theorem valid_allEq_zero_changes (S : Signature) :
    Valid (canonicalConstVal defaultTyCon S) (allEqSentence S (conTy 0)) ∧
    ¬ Valid (canonicalConstVal boolAtZero S) (allEqSentence S (conTy 0)) := by
  refine ⟨?_, ?_⟩
  · intro ρ hρ η _ x y
    rfl
  · intro h
    have hρ : Admissible boolAtZero baseTypeVal :=
      ⟨fun _ ↦ ⟨()⟩, boolAtZero_isAdmissible⟩
    have h0 := h baseTypeVal hρ (fun _ v ↦ nomatch v) (fun _ hh ↦ nomatch hh)
    change ∀ x y : Bool, x = y at h0
    exact Bool.noConfusion (h0 true false)

end QEDFV.HOL
