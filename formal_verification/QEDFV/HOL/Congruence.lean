import QEDFV.HOL.Rules

/-! Congruence of denotation and evaluation. Denotation and evaluation depend only on the
type variables and type-constructor ids that occur in the type or term, and on the constants
that occur in the term. The general lemma `Term.eval_congr` relates two evaluations that may
differ in the constructor interpretation, the type valuation, the constant interpretation
and the environment; `Term.eval_congr_κ` and `Term.eval_congr_vars` are its two specialisations.
The dependent-type bookkeeping is done with `HEq`. -/
namespace QEDFV.HOL

variable {κ κ' : TyConVal}

theorem heq_app_of_types {A A' B B' : Type} {f : A → B} {f' : A' → B'} {x : A} {x' : A'}
    (hA : A = A') (hB : B = B') (hf : HEq f f') (hx : HEq x x') : HEq (f x) (f' x') := by
  subst hA
  subst hB
  cases hf
  cases hx
  rfl

theorem heq_lam_of_types {A A' B B' : Type} {f : A → B} {f' : A' → B'}
    (hA : A = A') (hB : B = B')
    (h : ∀ (x : A) (x' : A'), HEq x x' → HEq (f x) (f' x')) : HEq f f' := by
  subst hA
  subst hB
  exact heq_of_eq (funext fun x ↦ eq_of_heq (h x x HEq.rfl))

theorem heq_forall_of_types {A A' : Type} {P : A → Prop} {P' : A' → Prop} (hA : A = A')
    (h : ∀ (x : A) (x' : A'), HEq x x' → (P x ↔ P' x')) : (∀ x, P x) = (∀ x', P' x') := by
  subst hA
  exact propext ⟨fun hp x ↦ (h x x HEq.rfl).mp (hp x), fun hp x ↦ (h x x HEq.rfl).mpr (hp x)⟩

theorem heq_exists_of_types {A A' : Type} {P : A → Prop} {P' : A' → Prop} (hA : A = A')
    (h : ∀ (x : A) (x' : A'), HEq x x' → (P x ↔ P' x')) : (∃ x, P x) = (∃ x', P' x') := by
  subst hA
  exact propext ⟨fun ⟨x, hx⟩ ↦ ⟨x, (h x x HEq.rfl).mp hx⟩,
    fun ⟨x, hx⟩ ↦ ⟨x, (h x x HEq.rfl).mpr hx⟩⟩

theorem heq_eq_fun_of_types {A A' : Type} (h : A = A') :
    HEq (fun x y : A => x = y) (fun x y : A' => x = y) := by
  subst h
  rfl

theorem heq_select_of_types {A A' : Type} [Nonempty A] [Nonempty A'] (h : A = A') :
    HEq (select A) (select A') := by
  subst h
  rfl

theorem Env.extend_heq {ρ ρ' : TypeVal} {Γ : List Ty} {a : Ty} (V C : Set Nat)
    {η : Env κ ρ Γ} {η' : Env κ' ρ' Γ} {x : Ty.denote κ ρ a} {x' : Ty.denote κ' ρ' a}
    (hx : HEq x x')
    (hη : ∀ b (v : Var Γ b), b.typeVars ⊆ V → b.tyCons ⊆ C → HEq (η b v) (η' b v)) :
    ∀ b (v : Var (a :: Γ) b), b.typeVars ⊆ V → b.tyCons ⊆ C →
      HEq (Env.extend (a := a) η x b v) (Env.extend (a := a) η' x' b v) := by
  intro b v h1 h2
  cases v with
  | zero => exact hx
  | succ v => exact hη b v h1 h2

/-- General congruence of evaluation. Two evaluations of the same term, under possibly
different constructor interpretations `κ κ'`, valuations `ρ ρ'`, constant interpretations
`I I'` and environments, have `HEq` values provided that:
* `ρ` and `ρ'` agree on the type variables `V` and `κ`, `κ'` agree on the constructors `C`,
  covering the term's `annotVars` (every type annotation, see `Term.annotVars`) and `tyCons`;
* the constants in `K` (a superset of the term's constants) are interpreted compatibly at
  every instance of their schema covered by `V` and `C`;
* the environments are `HEq` on every variable whose type is covered by `V` and `C`. -/
theorem Term.eval_congr (V C : Set Nat) (K : Finset Nat) {ρ ρ' : TypeVal}
    {I : ConstVal κ S} {I' : ConstVal κ' S}
    (hρ : Admissible κ ρ) (hρ' : Admissible κ' ρ')
    (hV : ∀ i, i ∈ V → ρ i = ρ' i) (hC : κ.AgreeOn C κ')
    (hI : ∀ c, c ∈ K → ∀ σ : TypeSub,
      ((S c).subst σ).typeVars ⊆ V → ((S c).subst σ).tyCons ⊆ C →
        HEq (I (σ.pull κ ρ) (σ.pull_admissible κ ρ hρ) c)
          (I' (σ.pull κ' ρ') (σ.pull_admissible κ' ρ' hρ') c))
    {Γ : List Ty} {a : Ty} (t : Term S Γ a)
    (htv : t.annotVars ⊆ V) (htc : t.tyCons ⊆ C) (htk : t.constIds ⊆ K)
    (η : Env κ ρ Γ) (η' : Env κ' ρ' Γ)
    (hη : ∀ b (v : Var Γ b), b.typeVars ⊆ V → b.tyCons ⊆ C → HEq (η b v) (η' b v)) :
    HEq (t.eval I ρ hρ η) (t.eval I' ρ' hρ' η') := by
  have hden : ∀ b : Ty, b.typeVars ⊆ V → b.tyCons ⊆ C → b.denote κ ρ = b.denote κ' ρ' :=
    fun b h1 h2 ↦ b.denote_congr_gen V C hV hC h1 h2
  induction t with
  | var v => exact hη _ v htv htc
  | const c σ =>
      simp only [Term.eval]
      exact (cast_heq _ _).trans
        ((hI c (htk (by simp [Term.constIds])) σ htv htc).trans (cast_heq _ _).symm)
  | @app Γ' a' b' f x ihf ihx =>
      have hf : f.annotVars ⊆ V := fun i hi ↦ htv (Or.inl hi)
      have hx : x.annotVars ⊆ V := fun i hi ↦ htv (Or.inr hi)
      have hfc : f.tyCons ⊆ C := fun i hi ↦ htc (Or.inl hi)
      have hxc : x.tyCons ⊆ C := fun i hi ↦ htc (Or.inr hi)
      have hfk : f.constIds ⊆ K := fun i hi ↦ htk (Finset.mem_union_left _ hi)
      have hxk : x.constIds ⊆ K := fun i hi ↦ htk (Finset.mem_union_right _ hi)
      simp only [Term.eval]
      exact heq_app_of_types
        (hden _ (x.ty_annotVars_subset.trans hx) (x.ty_tyCons_subset.trans hxc))
        (hden _ (fun i hi ↦ f.ty_annotVars_subset (Or.inr hi) |> hf)
          (fun i hi ↦ f.ty_tyCons_subset (Or.inr hi) |> hfc))
        (ihf hf hfc hfk η η' hη) (ihx hx hxc hxk η η' hη)
  | @lam a' Γ' b' b ih =>
      have hA := hden a' (fun i hi ↦ htv (Or.inl hi)) (fun i hi ↦ htc (Or.inl hi))
      have hbv : b.annotVars ⊆ V := fun i hi ↦ htv (Or.inr hi)
      have hbc : b.tyCons ⊆ C := fun i hi ↦ htc (Or.inr hi)
      have hB := hden b' (fun i hi ↦ b.ty_annotVars_subset hi |> hbv)
        (fun i hi ↦ b.ty_tyCons_subset hi |> hbc)
      simp only [Term.eval]
      exact heq_lam_of_types hA hB fun x x' hx ↦
        ih hbv hbc htk (η.extend x) (η'.extend x') (Env.extend_heq V C hx hη)
  | truth => exact HEq.rfl
  | falsity => exact HEq.rfl
  | conj p q ihp ihq =>
      have hp := ihp (fun i hi ↦ htv (Or.inl hi)) (fun i hi ↦ htc (Or.inl hi))
        (fun i hi ↦ htk (Finset.mem_union_left _ hi)) η η' hη
      have hq := ihq (fun i hi ↦ htv (Or.inr hi)) (fun i hi ↦ htc (Or.inr hi))
        (fun i hi ↦ htk (Finset.mem_union_right _ hi)) η η' hη
      simp only [Term.eval]
      exact heq_of_eq (congrArg₂ And (eq_of_heq hp) (eq_of_heq hq))
  | imp p q ihp ihq =>
      have hp := ihp (fun i hi ↦ htv (Or.inl hi)) (fun i hi ↦ htc (Or.inl hi))
        (fun i hi ↦ htk (Finset.mem_union_left _ hi)) η η' hη
      have hq := ihq (fun i hi ↦ htv (Or.inr hi)) (fun i hi ↦ htc (Or.inr hi))
        (fun i hi ↦ htk (Finset.mem_union_right _ hi)) η η' hη
      simp only [Term.eval]
      exact heq_of_eq (by rw [eq_of_heq hp, eq_of_heq hq])
  | @all a' Γ' p ih =>
      have hA := hden a' (fun i hi ↦ htv (Or.inl hi)) (fun i hi ↦ htc (Or.inl hi))
      simp only [Term.eval]
      refine heq_of_eq (heq_forall_of_types hA fun x x' hx ↦ ?_)
      exact (eq_of_heq (ih (fun i hi ↦ htv (Or.inr hi)) (fun i hi ↦ htc (Or.inr hi)) htk
        (η.extend x) (η'.extend x') (Env.extend_heq V C hx hη))) ▸ Iff.rfl
  | @ex a' Γ' p ih =>
      have hA := hden a' (fun i hi ↦ htv (Or.inl hi)) (fun i hi ↦ htc (Or.inl hi))
      simp only [Term.eval]
      refine heq_of_eq (heq_exists_of_types hA fun x x' hx ↦ ?_)
      exact (eq_of_heq (ih (fun i hi ↦ htv (Or.inr hi)) (fun i hi ↦ htc (Or.inr hi)) htk
        (η.extend x) (η'.extend x') (Env.extend_heq V C hx hη))) ▸ Iff.rfl
  | @eq Γ' a' =>
      exact heq_eq_fun_of_types (hden a' (fun i hi ↦ htv (by simp [Term.annotVars, Ty.typeVars, hi]))
        (fun i hi ↦ htc (by simp [Term.tyCons, Ty.tyCons, hi])))
  | @choice Γ' a' =>
      have hA := hden a' (fun i hi ↦ htv (by simp [Term.annotVars, Ty.typeVars, hi]))
        (fun i hi ↦ htc (by simp [Term.tyCons, Ty.tyCons, hi]))
      haveI : Nonempty (Ty.denote κ ρ a') := a'.carrier_nonempty κ ρ hρ
      haveI : Nonempty (Ty.denote κ' ρ' a') := a'.carrier_nonempty κ' ρ' hρ'
      exact heq_select_of_types hA

theorem TyConVal.AgreeOn.refl (κ : TyConVal) (C : Set Nat) : κ.AgreeOn C κ :=
  fun _ _ _ _ ↦ rfl

theorem TyConVal.AgreeOn.symm {C : Set Nat} (h : κ.AgreeOn C κ') : κ'.AgreeOn C κ :=
  fun k hk n as ↦ (h k hk n as).symm

theorem TyConVal.AgreeOn.mono {C D : Set Nat} (hCD : C ⊆ D) (h : κ.AgreeOn D κ') :
    κ.AgreeOn C κ' :=
  fun k hk n as ↦ h k (hCD hk) n as

/-- Cross-model agreement of the interpretation of the constant `c`: the values of `I`
(under `κ`) and `J` (under `κ'`) coincide, as `HEq`, at every instance `σ` of the schema of
`c` whose type-constructor ids lie in `C`. Valuations are compared at the pull-back
`σ.pull κ ρ` resp. `σ.pull κ' ρ` of one and the same base valuation. When `κ' = κ` this is
exactly pointwise equality `I ρ hρ c = J ρ hρ c`
(`ConstVal.AgreeAt.of_eq`). -/
def ConstVal.AgreeAt (I : ConstVal κ S) (J : ConstVal κ' S) (C : Set Nat) (c : Nat) : Prop :=
  ∀ (ρ : TypeVal) (hρ : Admissible κ ρ) (hρ' : Admissible κ' ρ) (σ : TypeSub),
    ((S c).subst σ).tyCons ⊆ C →
      HEq (I (σ.pull κ ρ) (σ.pull_admissible κ ρ hρ) c)
        (J (σ.pull κ' ρ) (σ.pull_admissible κ' ρ hρ') c)

theorem ConstVal.AgreeAt.of_eq {I J : ConstVal κ S} {C : Set Nat} {c : Nat}
    (h : ∀ (ρ : TypeVal) (hρ : Admissible κ ρ), I ρ hρ c = J ρ hρ c) : I.AgreeAt J C c :=
  fun _ _ _ _ _ ↦ heq_of_eq (h _ _)

theorem ConstVal.AgreeAt.congr_left {I I' : ConstVal κ S} {J : ConstVal κ' S} {C : Set Nat}
    {c : Nat} (h : ∀ (ρ : TypeVal) (hρ : Admissible κ ρ), I ρ hρ c = I' ρ hρ c)
    (hA : I'.AgreeAt J C c) : I.AgreeAt J C c :=
  fun ρ hρ hρ' σ hσ ↦ (heq_of_eq (h _ _)).trans (hA ρ hρ hρ' σ hσ)

theorem ConstVal.AgreeAt.symm {I : ConstVal κ S} {J : ConstVal κ' S} {C : Set Nat} {c : Nat}
    (h : I.AgreeAt J C c) : J.AgreeAt I C c :=
  fun ρ hρ' hρ σ hσ ↦ (h ρ hρ hρ' σ hσ).symm

theorem ConstVal.AgreeAt.mono {I : ConstVal κ S} {J : ConstVal κ' S} {C D : Set Nat} {c : Nat}
    (hCD : C ⊆ D) (h : I.AgreeAt J D c) : I.AgreeAt J C c :=
  fun ρ hρ hρ' σ hσ ↦ h ρ hρ hρ' σ (hσ.trans hCD)

/-- The constant `c` is interpreted *locally*: its value at a valuation depends only on the
type variables of its schema. -/
def ConstVal.Local (I : ConstVal κ S) (c : Nat) : Prop :=
  ∀ (ρ : TypeVal) (hρ : Admissible κ ρ) (ρ' : TypeVal) (hρ' : Admissible κ ρ'),
    (∀ i, i ∈ (S c).typeVars → ρ i = ρ' i) → HEq (I ρ hρ c) (I ρ' hρ' c)

/-- Evaluation under `(κ, I)` and `(κ', I')` agree (as `HEq`) when the constructor
interpretations agree on the constructors occurring in the term, the constants agree
(`ConstVal.AgreeAt`) on the constants occurring, and the environments agree on every
variable whose type lies in the agreement region. This generalises `Term.eval_agree`. -/
theorem Term.eval_congr_κ {ρ : TypeVal} (hρ : Admissible κ ρ) (hρ' : Admissible κ' ρ)
    {I : ConstVal κ S} {I' : ConstVal κ' S} {Γ : List Ty} {a : Ty} (t : Term S Γ a)
    (hC : κ.AgreeOn t.tyCons κ')
    (hI : ∀ c, c ∈ t.constIds → I.AgreeAt I' t.tyCons c)
    (η : Env κ ρ Γ) (η' : Env κ' ρ Γ)
    (hη : ∀ b (v : Var Γ b), b.tyCons ⊆ t.tyCons → HEq (η b v) (η' b v)) :
    HEq (t.eval I ρ hρ η) (t.eval I' ρ hρ' η') :=
  Term.eval_congr Set.univ t.tyCons t.constIds hρ hρ' (fun _ _ ↦ rfl) hC
    (fun c hc σ _ hσc ↦ hI c hc ρ hρ hρ' σ hσc) t (Set.subset_univ _) subset_rfl subset_rfl
    η η' (fun b v _ h ↦ hη b v h)

/-- Evaluation depends only on the type variables occurring in the term's type annotations
(`Term.annotVars`), provided the constants occurring in it are interpreted locally
(`ConstVal.Local`). The closure-gate support `Term.typeVars` is not enough: it omits the
domain of an unused lambda binder, and `λx:α₅. True` depends on the carrier of `α₅`. -/
theorem Term.eval_congr_vars {ρ ρ' : TypeVal} (hρ : Admissible κ ρ) (hρ' : Admissible κ ρ')
    (I : ConstVal κ S) {Γ : List Ty} {a : Ty} (t : Term S Γ a)
    (hρρ : ∀ i, i ∈ t.annotVars → ρ i = ρ' i)
    (hI : ∀ c, c ∈ t.constIds → I.Local c)
    (η : Env κ ρ Γ) (η' : Env κ ρ' Γ)
    (hη : ∀ b (v : Var Γ b), b.typeVars ⊆ t.annotVars → HEq (η b v) (η' b v)) :
    HEq (t.eval I ρ hρ η) (t.eval I ρ' hρ' η') := by
  refine Term.eval_congr t.annotVars Set.univ t.constIds hρ hρ' hρρ
    (TyConVal.AgreeOn.refl κ _) ?_ t subset_rfl (Set.subset_univ _) subset_rfl η η'
    (fun b v h _ ↦ hη b v h)
  intro c hc σ hσv _
  apply hI c hc
  intro i hi
  exact (σ i).denote_congr_vars κ (fun j hj ↦ hρρ j (hσv (by
    rw [Ty.typeVars_subst]
    exact ⟨i, hi, hj⟩)))

/-- Closed terms whose type variables lie below `n` evaluate identically under valuations
that agree below `n` (the situation of a gate with `typeVarsClosed`-style hypotheses). -/
theorem Term.eval_congr_vars_lt {ρ ρ' : TypeVal} (hρ : Admissible κ ρ)
    (hρ' : Admissible κ ρ') (I : ConstVal κ S) {a : Ty} (t : Term S [] a) (n : Nat)
    (hn : ∀ i, i ∈ t.annotVars → i < n) (hρρ : ∀ i, i < n → ρ i = ρ' i)
    (hI : ∀ c, c ∈ t.constIds → I.Local c)
    (η : Env κ ρ []) (η' : Env κ ρ' []) :
    HEq (t.eval I ρ hρ η) (t.eval I ρ' hρ' η') :=
  Term.eval_congr_vars hρ hρ' I t (fun i hi ↦ hρρ i (hn i hi)) hI η η'
    (fun _ v _ ↦ nomatch v)

/-- Transport of an environment along a constructor-interpretation change: variables whose
types lie in the agreement region `C` are cast; the others (which no term in the region can
mention) are filled with an arbitrary inhabitant. -/
noncomputable def Env.crossCast (C : Set Nat) (hC : κ.AgreeOn C κ') {ρ : TypeVal}
    (hρ : Admissible κ ρ) {Γ : List Ty} (η' : Env κ' ρ Γ) : Env κ ρ Γ := fun b v ↦ by
  classical
  exact if h : b.tyCons ⊆ C then
    cast (b.denote_congr_gen Set.univ C (fun _ _ ↦ rfl) hC (Set.subset_univ _) h).symm (η' b v)
  else Classical.choice (b.carrier_nonempty κ ρ hρ)

theorem Env.crossCast_heq (C : Set Nat) (hC : κ.AgreeOn C κ') {ρ : TypeVal}
    (hρ : Admissible κ ρ) {Γ : List Ty} (η' : Env κ' ρ Γ) (b : Ty) (v : Var Γ b)
    (h : b.tyCons ⊆ C) : HEq (Env.crossCast C hC hρ η' b v) (η' b v) := by
  classical
  simp only [Env.crossCast, dif_pos h]
  exact cast_heq _ _

/-- Type-constructor ids occurring in the hypotheses and conclusion of a sequent. Types of
unused context variables are deliberately not counted. -/
def Sequent.tyCons (s : Sequent S Γ) : Set Nat :=
  {k | (∃ h, h ∈ s.hyps ∧ k ∈ h.tyCons) ∨ k ∈ s.concl.tyCons}

theorem Sequent.tyCons_hyp {s : Sequent S Γ} {h : Term S Γ .bool} (hh : h ∈ s.hyps) :
    h.tyCons ⊆ s.tyCons :=
  fun _ hk ↦ Or.inl ⟨h, hh, hk⟩

theorem Sequent.tyCons_concl (s : Sequent S Γ) : s.concl.tyCons ⊆ s.tyCons :=
  fun _ hk ↦ Or.inr hk

end QEDFV.HOL
