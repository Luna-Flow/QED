import QEDFV.HOL.TdKfree

/-! The translation of the type-definition constants `rep` and `abs`, and of the three laws
at an arbitrary instance `θ` of the type parameters.

At the instance `θ` the defined type is `k(θ₀,…,θₙ₋₁)`. Everything below depends on `θ` only
through the arguments `args = (θ₀,…,θₙ₋₁)`, so that two instances with the same arguments have
the same laws. The translation sends `k(args)` to `R[args']`, with `args' = tr ∘ args`. Two
normalisers act on `R[args']`: `NK`, the oracle at `k(args)`, which projects onto the
translated predicate, and `NR`, the normalisation at the type `R[args]`, which is nontrivial
when `args` mentions `k`. The ideal translations are `rep ↦ λx. NR (NK x)` and
`abs ↦ λx. NK (NR x)`. -/
namespace QEDFV.HOL

namespace TypeDefGate

variable {S : Signature} (G : TypeDefGate S)

/-- Normalisation at a type equal to an arrow type, computed on the erasure. -/
theorem erase_nrmTy_arr (N : G.Oracle) {τ X Y : Ty} (h : τ = .arr X Y)
    (hk : G.k ∈ (Ty.arr X Y).tyCons) {Γ : List Ty} (u : Term S Γ (G.tr τ)) :
    (G.nrmTy N τ u).erase
      = (Term.lam (G.nrmTy N Y (((congrArg G.tr h ▸ u : Term S Γ (G.tr (.arr X Y))).rename
          Var.succ).app (G.nrmTy N X (Term.var Var.zero))))).erase := by
  subst h
  simp only [nrmTy, if_pos hk]

/-- The substitution with the given arguments for the first `n` type variables. -/
abbrev canonSub (args : Fin G.n → Ty) : TypeSub := Ty.argsSub G.n args

/-- The arguments of an instance. -/
abbrev θa (θ : TypeSub) : Fin G.n → Ty := fun i ↦ θ i.val

/-- The translated representation type at the arguments `args`. -/
abbrev RT (args : Fin G.n → Ty) : Ty :=
  G.repTy.subst (Ty.argsSub G.n (fun i ↦ G.tr (args i)))

theorem tr_new_eq (args : Fin G.n → Ty) : G.tr (.con G.k G.n args) = G.RT args :=
  G.tr_con_pos ⟨rfl, rfl⟩

theorem subst_trSub_eq (θ : TypeSub) :
    G.repTy.subst (G.trSub θ) = G.RT (G.θa θ) := by
  refine Ty.subst_congr G.repTy (fun i hi ↦ ?_)
  have hi' : i < G.n := G.repTy_typeVars_lt i hi
  simp [Ty.argsSub, hi', trSub, θa]

theorem tr_R_eq (args : Fin G.n → Ty) :
    G.tr (G.repTy.subst (G.canonSub args)) = G.RT args := by
  rw [G.tr_repTy_subst]
  refine Ty.subst_congr G.repTy (fun i hi ↦ ?_)
  have hi' : i < G.n := G.repTy_typeVars_lt i hi
  simp [Ty.argsSub, hi', trSub]

theorem tr_Q_eq (args : Fin G.n → Ty) :
    G.tr ((Ty.arr G.repTy .bool).subst (G.canonSub args)) = Ty.arr (G.RT args) .bool := by
  change Ty.arr (G.tr (G.repTy.subst (G.canonSub args))) Ty.bool = _
  rw [G.tr_R_eq]

theorem tr_newTy_eq (θ : TypeSub) : G.tr (G.newTy.subst θ) = G.RT (G.θa θ) :=
  G.tr_new_eq (G.θa θ)

theorem tr_RT_eq (θ : TypeSub) : G.tr (G.repTy.subst θ) = G.RT (G.θa θ) := by
  rw [G.tr_repTy_subst]; exact G.subst_trSub_eq θ

/-- The normaliser at the new type `k(args)`, read at the type `R[args']`. -/
noncomputable def NK (N : G.Oracle) (args : Fin G.n → Ty) {Γ : List Ty}
    (x : Term S Γ (G.RT args)) : Term S Γ (G.RT args) :=
  (G.tr_new_eq args) ▸ (((N (.con G.k G.n args)).closedLift).app ((G.tr_new_eq args).symm ▸ x))

/-- The normalisation at the representation type `R[args]`, read at `R[args']`. -/
noncomputable def NR (N : G.Oracle) (args : Fin G.n → Ty) {Γ : List Ty}
    (x : Term S Γ (G.RT args)) : Term S Γ (G.RT args) :=
  (G.tr_R_eq args) ▸ G.nrmTy N (G.repTy.subst (G.canonSub args)) ((G.tr_R_eq args).symm ▸ x)

/-- The ideal translation of `rep`: `λx. NR ((λy. y) (NK x))`. -/
noncomputable def repI (N : G.Oracle) (args : Fin G.n → Ty) (Γ : List Ty) :
    Term S Γ (.arr (G.RT args) (G.RT args)) :=
  Term.lam (G.NR N args ((Term.lam (Term.var Var.zero)).app (G.NK N args (Term.var Var.zero))))

/-- The ideal translation of `abs`: `λx. NK ((λy. y) (NR x))`. -/
noncomputable def absI (N : G.Oracle) (args : Fin G.n → Ty) (Γ : List Ty) :
    Term S Γ (.arr (G.RT args) (G.RT args)) :=
  Term.lam (G.NK N args ((Term.lam (Term.var Var.zero)).app (G.NR N args (Term.var Var.zero))))

/-- The translation of the predicate at the arguments `args`, a closed predicate on `R[args']`. -/
noncomputable def QT (N : G.Oracle) (args : Fin G.n → Ty) : Term S [] (.arr (G.RT args) .bool) :=
  (G.tr_Q_eq args) ▸ G.trans N (G.pred.instType (G.canonSub args))

theorem S_rep_subst (σ : TypeSub) :
    (S G.rep).subst σ = .arr (G.newTy.subst σ) (G.repTy.subst σ) := by
  rw [G.rep_ty]; rfl

theorem S_abs_subst (σ : TypeSub) :
    (S G.abs).subst σ = .arr (G.repTy.subst σ) (G.newTy.subst σ) := by
  rw [G.abs_ty]; rfl

theorem newTy_subst_eq (σ : TypeSub) :
    G.newTy.subst σ = .con G.k G.n (fun i : Fin G.n ↦ σ i.val) := rfl

theorem k_mem_newTy_subst (σ : TypeSub) : G.k ∈ (G.newTy.subst σ).tyCons := by
  rw [G.newTy_subst_eq]
  simp [Ty.tyCons]

theorem nrmTy_heq (N : G.Oracle) {X X' : Ty} (hX : X = X') {Γ1 Γ2 : List Ty} (h : Γ1 = Γ2)
    {u1 : Term S Γ1 (G.tr X)} {u2 : Term S Γ2 (G.tr X')} (hu : HEq u1 u2) :
    HEq (G.nrmTy N X u1) (G.nrmTy N X' u2) := by
  subst hX
  subst h
  have := eq_of_heq hu
  subst this
  rfl

theorem erase_of_heq {Γ1 Γ2 : List Ty} {a : Ty} (h : Γ1 = Γ2) {t1 : Term S Γ1 a}
    {t2 : Term S Γ2 a} (ht : HEq t1 t2) : t1.erase = t2.erase := by
  subst h
  have := eq_of_heq ht
  subst this
  rfl

theorem nrmTy_newTy (N : G.Oracle) (args : Fin G.n → Ty) {Γ : List Ty}
    (u : Term S Γ (G.tr (.con G.k G.n args))) :
    G.nrmTy N (.con G.k G.n args) u = ((N (.con G.k G.n args)).closedLift).app u := by
  simp only [nrmTy, and_self, if_true]

theorem erase_of_heq' {Γ1 Γ2 : List Ty} {a1 a2 : Ty} (h : Γ1 = Γ2) (ha : a1 = a2)
    {t1 : Term S Γ1 a1} {t2 : Term S Γ2 a2} (ht : HEq t1 t2) : t1.erase = t2.erase := by
  subst h; subst ha
  have := eq_of_heq ht
  subst this
  rfl

theorem nrmTy_newTy' (N : G.Oracle) (θ : TypeSub) {Γ : List Ty}
    (u : Term S Γ (G.tr (G.newTy.subst θ))) :
    G.nrmTy N (G.newTy.subst θ) u = ((N (G.newTy.subst θ)).closedLift).app u := by
  simp only [newTy, paramTy, Ty.subst, nrmTy, and_self, if_true]

theorem erase_closedLift_ctx {a : Ty} (t : Term S [] a) {C1 C2 : List Ty} (h : C1 = C2) :
    (t.closedLift : Term S C1 a).erase = (t.closedLift : Term S C2 a).erase := by
  subst h; rfl

/-! ### Calculus facts about `NK` and `NR` -/

section Calc

variable {es : List (ModelExtension S)}

theorem NK_substitute (N : G.Oracle) (args : Fin G.n → Ty) {Γ Δ : List Ty} (x : Term S Γ (G.RT args))
    (σ : Sub S Γ Δ) : (G.NK N args x).substitute σ = G.NK N args (x.substitute σ) := by
  unfold NK
  rw [Term.substitute_cast, Term.substitute, Term.closedLift_substitute, Term.substitute_cast]

theorem NR_substitute (N : G.Oracle) (args : Fin G.n → Ty) {Γ Δ : List Ty} (x : Term S Γ (G.RT args))
    (σ : Sub S Γ Δ) : (G.NR N args x).substitute σ = G.NR N args (x.substitute σ) := by
  unfold NR
  rw [Term.substitute_cast, G.nrmTy_substitute, Term.substitute_cast]

theorem NK_congr (N : G.Oracle) (args : Fin G.n → Ty) {Γ : List Ty} {L : List (Term S Γ .bool)}
    {x y : Term S Γ (G.RT args)}
    (h : HistoryDerivation S es { hyps := L, concl := x.equal y }) :
    HistoryDerivation S es { hyps := L, concl := (G.NK N args x).equal (G.NK N args y) } := by
  unfold NK
  refine HistoryDerivation.cast_equal (G.tr_new_eq args) ?_
  exact HistoryDerivation.mkComb' (HistoryDerivation.refl' _)
    (HistoryDerivation.cast_equal (G.tr_new_eq args).symm h)

theorem NR_congr (N : G.Oracle) (args : Fin G.n → Ty) {Γ : List Ty} {L : List (Term S Γ .bool)}
    {x y : Term S Γ (G.RT args)}
    (h : HistoryDerivation S es { hyps := L, concl := x.equal y }) :
    HistoryDerivation S es { hyps := L, concl := (G.NR N args x).equal (G.NR N args y) } := by
  unfold NR
  refine HistoryDerivation.cast_equal (G.tr_R_eq args) ?_
  exact G.nrmTy_congr N _ (HistoryDerivation.cast_equal (G.tr_R_eq args).symm h)

theorem NR_idem (N : G.Oracle) (hI : G.Idem N es) (args : Fin G.n → Ty) {Γ : List Ty}
    (L : List (Term S Γ .bool)) (x : Term S Γ (G.RT args)) :
    HistoryDerivation S es { hyps := L, concl := (G.NR N args (G.NR N args x)).equal (G.NR N args x) } := by
  unfold NR
  rw [Term.cast_cast]
  exact HistoryDerivation.cast_equal (G.tr_R_eq args) (G.nrmTy_idem N hI _ L _)

theorem repI_app (N : G.Oracle) (args : Fin G.n → Ty) {Γ : List Ty} {L : List (Term S Γ .bool)}
    (z : Term S Γ (G.RT args)) :
    HistoryDerivation S es { hyps := L, concl := ((G.repI N args Γ).app z).equal (G.NR N args (G.NK N args z)) } := by
  have b1 := (HistoryDerivation.core (es := es)
    (Derivation.beta (G.NR N args ((Term.lam (Term.var Var.zero)).app (G.NK N args (Term.var Var.zero)))) z)).mono
    (L := L) (fun _ hh ↦ by simp at hh)
  have hb : ((G.NR N args ((Term.lam (Term.var Var.zero)).app (G.NK N args (Term.var Var.zero)))).substitute
      (Sub.single z) : Term S Γ (G.RT args))
      = G.NR N args ((Term.lam (Term.var Var.zero)).app (G.NK N args z)) := by
    rw [G.NR_substitute]
    simp only [Term.substitute, G.NK_substitute]
    rfl
  rw [hb] at b1
  have b2 := (HistoryDerivation.core (es := es)
    (Derivation.beta (Term.var Var.zero : Term S (G.RT args :: Γ) (G.RT args)) (G.NK N args z))).mono
    (L := L) (fun _ hh ↦ by simp at hh)
  exact HistoryDerivation.trans' b1 (G.NR_congr N args b2)

theorem absI_app (N : G.Oracle) (args : Fin G.n → Ty) {Γ : List Ty} {L : List (Term S Γ .bool)}
    (z : Term S Γ (G.RT args)) :
    HistoryDerivation S es { hyps := L, concl := ((G.absI N args Γ).app z).equal (G.NK N args (G.NR N args z)) } := by
  have b1 := (HistoryDerivation.core (es := es)
    (Derivation.beta (G.NK N args ((Term.lam (Term.var Var.zero)).app (G.NR N args (Term.var Var.zero)))) z)).mono
    (L := L) (fun _ hh ↦ by simp at hh)
  have hb : ((G.NK N args ((Term.lam (Term.var Var.zero)).app (G.NR N args (Term.var Var.zero)))).substitute
      (Sub.single z) : Term S Γ (G.RT args))
      = G.NK N args ((Term.lam (Term.var Var.zero)).app (G.NR N args z)) := by
    rw [G.NK_substitute]
    simp only [Term.substitute, G.NR_substitute]
    rfl
  rw [hb] at b1
  have b2 := (HistoryDerivation.core (es := es)
    (Derivation.beta (Term.var Var.zero : Term S (G.RT args :: Γ) (G.RT args)) (G.NR N args z))).mono
    (L := L) (fun _ hh ↦ by simp at hh)
  exact HistoryDerivation.trans' b1 (G.NK_congr N args b2)

/-! ### The translated predicate and the laws -/

/-- The gate's retraction data. -/
def cfg : NormCfg S := ⟨G.repTy, G.pred⟩

theorem predIn_eq (Γ : List Ty) : G.predIn Γ = (G.pred.closedLift : Term S Γ (.arr G.repTy .bool)) :=
  G.cfg.predIn_eq Γ

/-- The oracle's content at an instance, as far as the laws need it: the retraction
`NK` lands in the elements fixed by `NR` and satisfying the translated predicate, and fixes
them. -/
structure LawData (N : G.Oracle) (es : List (ModelExtension S)) (args : Fin G.n → Ty) : Prop where
  rangeR : ∀ {Γ : List Ty} (L : List (Term S Γ .bool)) (x : Term S Γ (G.RT args)),
    HistoryDerivation S es { hyps := L, concl := (G.NR N args (G.NK N args x)).equal (G.NK N args x) }
  rangeQ : ∀ {Γ : List Ty} (L : List (Term S Γ .bool)) (x : Term S Γ (G.RT args)),
    HistoryDerivation S es { hyps := L, concl := ((G.QT N args).closedLift).app (G.NK N args x) }
  fix : ∀ {Γ : List Ty} (L : List (Term S Γ .bool)) (x : Term S Γ (G.RT args)),
    HistoryDerivation S es { hyps := L, concl := (G.NR N args x).equal x } →
    HistoryDerivation S es { hyps := L, concl := ((G.QT N args).closedLift).app x } →
    HistoryDerivation S es { hyps := L, concl := (G.NK N args x).equal x }

theorem LawData.idem {N : G.Oracle} {es : List (ModelExtension S)} {args : Fin G.n → Ty}
    (h : G.LawData N es args) {Γ : List Ty} (L : List (Term S Γ .bool)) (x : Term S Γ (G.RT args)) :
    HistoryDerivation S es { hyps := L, concl := (G.NK N args (G.NK N args x)).equal (G.NK N args x) } :=
  h.fix L (G.NK N args x) (h.rangeR L x) (h.rangeQ L x)

theorem law1_gen (N : G.Oracle) (hI : G.Idem N es) (args : Fin G.n → Ty) (hD : G.LawData N es args)
    {Γ' : List Ty} {L : List (Term S Γ' .bool)} {X Y : Ty}
    (hX : X = G.RT args) (hY : Y = G.RT args) {f : Term S Γ' (.arr X Y)} {g : Term S Γ' (.arr Y X)}
    (hf : HEq f (G.repI N args Γ')) (hg : HEq g (G.absI N args Γ')) (x : Term S Γ' X)
    (hyp : HistoryDerivation S es
      { hyps := L, concl := (hX.symm ▸ G.NK N args (hX ▸ x) : Term S Γ' X).equal x }) :
    HistoryDerivation S es { hyps := L, concl := (g.app (f.app x)).equal x } := by
  subst hX; subst hY
  have hf' := eq_of_heq hf
  have hg' := eq_of_heq hg
  subst hf'; subst hg'
  have s1 := HistoryDerivation.mkComb' (HistoryDerivation.refl' (es := es) (L := L) (G.absI N args Γ'))
    (G.repI_app N args (es := es) (L := L) x)
  have s2 := G.absI_app N args (es := es) (L := L) (G.NR N args (G.NK N args x))
  have s3 := G.NK_congr N args (es := es) (L := L)
    (HistoryDerivation.trans' (G.NR_idem N hI args L (G.NK N args x)) (hD.rangeR L x))
  have s4 := LawData.idem G hD L x
  exact HistoryDerivation.trans' s1 (HistoryDerivation.trans' s2
    (HistoryDerivation.trans' s3 (HistoryDerivation.trans' s4 hyp)))

theorem law2_gen (N : G.Oracle) (args : Fin G.n → Ty) (hD : G.LawData N es args)
    {Γ' : List Ty} {L : List (Term S Γ' .bool)} {X Y : Ty}
    (hX : X = G.RT args) (hY : Y = G.RT args) {f : Term S Γ' (.arr X Y)} {p : Term S Γ' (.arr Y .bool)}
    (hf : HEq f (G.repI N args Γ')) (hp : HEq p ((G.QT N args).closedLift : Term S Γ' _))
    (x : Term S Γ' X) :
    HistoryDerivation S es { hyps := L, concl := p.app (f.app x) } := by
  subst hX; subst hY
  have hf' := eq_of_heq hf
  have hp' := eq_of_heq hp
  subst hf'; subst hp'
  have s1 := HistoryDerivation.mkComb'
    (HistoryDerivation.refl' (es := es) (L := L) ((G.QT N args).closedLift : Term S Γ' _))
    (G.repI_app N args (es := es) (L := L) x)
  have s2 := HistoryDerivation.mkComb'
    (HistoryDerivation.refl' (es := es) (L := L) ((G.QT N args).closedLift : Term S Γ' _))
    (hD.rangeR L x)
  exact HistoryDerivation.eqMp' (HistoryDerivation.sym (HistoryDerivation.trans' s1 s2))
    (hD.rangeQ L x)

theorem law3_gen (N : G.Oracle) (args : Fin G.n → Ty) (hD : G.LawData N es args)
    {Γ' : List Ty} {L : List (Term S Γ' .bool)} {X Y : Ty}
    (hX : X = G.RT args) (hY : Y = G.RT args) {f : Term S Γ' (.arr X Y)} {g : Term S Γ' (.arr Y X)}
    {p : Term S Γ' (.arr Y .bool)}
    (hf : HEq f (G.repI N args Γ')) (hg : HEq g (G.absI N args Γ'))
    (hp : HEq p ((G.QT N args).closedLift : Term S Γ' _)) (x : Term S Γ' Y)
    (hR : HistoryDerivation S es
      { hyps := L, concl := (hY.symm ▸ G.NR N args (hY ▸ x) : Term S Γ' Y).equal x })
    (hyp : HistoryDerivation S es { hyps := L, concl := p.app x }) :
    HistoryDerivation S es { hyps := L, concl := (f.app (g.app x)).equal x } := by
  subst hX; subst hY
  have hf' := eq_of_heq hf
  have hg' := eq_of_heq hg
  have hp' := eq_of_heq hp
  subst hf'; subst hg'; subst hp'
  have s1 := HistoryDerivation.mkComb' (HistoryDerivation.refl' (es := es) (L := L) (G.repI N args Γ'))
    (G.absI_app N args (es := es) (L := L) x)
  have s2 := G.repI_app N args (es := es) (L := L) (G.NK N args (G.NR N args x))
  have s3 := G.NR_congr N args (es := es) (L := L) (LawData.idem G hD L (G.NR N args x))
  have s4 := G.NR_congr N args (es := es) (L := L) (G.NK_congr N args (es := es) (L := L) hR)
  have s5 := hD.rangeR L x
  have s6 := hD.fix L x hR hyp
  exact HistoryDerivation.trans' s1 (HistoryDerivation.trans' s2 (HistoryDerivation.trans' s3
    (HistoryDerivation.trans' s4 (HistoryDerivation.trans' s5 s6))))


theorem tr_rep_a (σ : TypeSub) :
    G.tr ((S G.rep).subst σ) = Ty.arr (G.RT (G.θa σ)) (G.RT (G.θa σ)) := by
  rw [G.tr_rep_ty rfl σ, G.subst_trSub_eq]

theorem tr_abs_a (σ : TypeSub) :
    G.tr ((S G.abs).subst σ) = Ty.arr (G.RT (G.θa σ)) (G.RT (G.θa σ)) := by
  rw [G.tr_abs_ty rfl σ, G.subst_trSub_eq]

theorem repTy_subst_canon (σ : TypeSub) :
    G.repTy.subst σ = G.repTy.subst (G.canonSub (G.θa σ)) := by
  refine Ty.subst_congr G.repTy (fun i hi ↦ ?_)
  have hi' : i < G.n := G.repTy_typeVars_lt i hi
  simp [Ty.argsSub, hi', θa]

theorem trans_rep_heq' (N : G.Oracle) (σ : TypeSub) {Γ : List Ty} :
    HEq (G.trans N (Term.const (S := S) (Γ := Γ) G.rep ((S G.rep).subst σ) ⟨σ, rfl⟩))
      (G.repI N (G.θa σ) (Γ.map G.tr)) := by
  refine Term.erase_inj_heq' _ _ rfl (G.tr_rep_a σ) ?_
  have hk : G.k ∈ (Ty.arr (G.newTy.subst σ) (G.repTy.subst σ)).tyCons := by
    simp only [Ty.tyCons, Set.mem_union]
    exact Or.inl (G.k_mem_newTy_subst σ)
  have hS : ¬ G.k ∉ (S G.rep).tyCons := by
    rw [G.rep_ty]; simp [paramTy, Ty.tyCons]
  simp only [trans]
  rw [G.erase_nrmTy_arr N (G.S_rep_subst σ) hk]
  have hraw : (G.rawConst G.rep _ ⟨σ, rfl⟩ : Term S (Γ.map G.tr) _)
      = idTerm (S := S) (G.tr ((S G.rep).subst σ)) (Γ.map G.tr) := by
    unfold rawConst; rw [dif_neg hS, if_pos (Or.inl rfl)]
  rw [hraw]
  have hnew := G.tr_newTy_eq σ
  have hctx : (G.tr (G.newTy.subst σ) :: Γ.map G.tr) = (G.RT (G.θa σ) :: Γ.map G.tr) := by
    rw [hnew]
  simp only [repI, Term.erase]
  refine congrArg₂ UTerm.lam hnew ?_
  unfold NR
  rw [Term.erase_cast]
  refine erase_of_heq' hctx (congrArg G.tr (G.repTy_subst_canon σ)) (nrmTy_heq G N (G.repTy_subst_canon σ) hctx ?_)
  refine Term.erase_inj_heq' _ _ hctx (congrArg G.tr (G.repTy_subst_canon σ)) ?_
  simp only [Term.erase, Term.erase_cast, Term.rename_cast, idTerm_rename]
  have e1 : (idTerm (S := S) (G.tr ((S G.rep).subst σ)) (G.tr (G.newTy.subst σ) :: Γ.map G.tr)).erase
      = UTerm.lam (G.RT (G.θa σ)) (UTerm.var 0) := erase_idTerm (G.tr_rep_a σ) _
  have e2 : (G.nrmTy N (G.newTy.subst σ) (Term.var Var.zero :
        Term S (G.tr (G.newTy.subst σ) :: Γ.map G.tr) (G.tr (G.newTy.subst σ)))).erase
      = (G.NK N (G.θa σ) (Term.var Var.zero :
        Term S (G.RT (G.θa σ) :: Γ.map G.tr) (G.RT (G.θa σ)))).erase := by
    change (G.nrmTy N (.con G.k G.n (G.θa σ)) _).erase = _
    rw [G.nrmTy_newTy]
    unfold NK
    rw [Term.erase_cast]
    simp only [Term.erase, Term.erase_cast]
    rw [erase_closedLift_ctx (N (.con G.k G.n (G.θa σ))) hctx]
    rfl
  rw [e1, e2]
  simp only [Var.erase]
  exact congrArg (fun a => UTerm.app a (UTerm.lam (G.RT (G.θa σ)) (UTerm.var 0))
    (G.NK N (G.θa σ) (Term.var Var.zero :
      Term S (G.RT (G.θa σ) :: Γ.map G.tr) (G.RT (G.θa σ)))).erase) hnew

theorem trans_abs_heq' (N : G.Oracle) (σ : TypeSub) {Γ : List Ty} :
    HEq (G.trans N (Term.const (S := S) (Γ := Γ) G.abs ((S G.abs).subst σ) ⟨σ, rfl⟩))
      (G.absI N (G.θa σ) (Γ.map G.tr)) := by
  refine Term.erase_inj_heq' _ _ rfl (G.tr_abs_a σ) ?_
  have hk : G.k ∈ (Ty.arr (G.repTy.subst σ) (G.newTy.subst σ)).tyCons := by
    simp only [Ty.tyCons, Set.mem_union]
    exact Or.inr (G.k_mem_newTy_subst σ)
  have hS : ¬ G.k ∉ (S G.abs).tyCons := by
    rw [G.abs_ty]; simp [paramTy, Ty.tyCons]
  simp only [trans]
  rw [G.erase_nrmTy_arr N (G.S_abs_subst σ) hk]
  have hraw : (G.rawConst G.abs _ ⟨σ, rfl⟩ : Term S (Γ.map G.tr) _)
      = idTerm (S := S) (G.tr ((S G.abs).subst σ)) (Γ.map G.tr) := by
    unfold rawConst; rw [dif_neg hS, if_pos (Or.inr rfl)]
  rw [hraw]
  have hR := G.tr_RT_eq σ
  have hnew := G.tr_newTy_eq σ
  have hctx : (G.tr (G.repTy.subst σ) :: Γ.map G.tr) = (G.RT (G.θa σ) :: Γ.map G.tr) := by
    rw [hR]
  simp only [absI, Term.erase]
  refine congrArg₂ UTerm.lam hR ?_
  unfold NK
  rw [Term.erase_cast]
  rw [G.nrmTy_newTy']
  simp only [Term.erase, Term.erase_cast, Term.rename_cast, idTerm_rename]
  rw [erase_closedLift_ctx (N (G.newTy.subst σ)) hctx]
  have e1 : (idTerm (S := S) (G.tr ((S G.abs).subst σ)) (G.tr (G.repTy.subst σ) :: Γ.map G.tr)).erase
      = UTerm.lam (G.RT (G.θa σ)) (UTerm.var 0) := erase_idTerm (G.tr_abs_a σ) _
  have e2 : (G.nrmTy N (G.repTy.subst σ) (Term.var Var.zero :
        Term S (G.tr (G.repTy.subst σ) :: Γ.map G.tr) (G.tr (G.repTy.subst σ)))).erase
      = (G.NR N (G.θa σ) (Term.var Var.zero :
        Term S (G.RT (G.θa σ) :: Γ.map G.tr) (G.RT (G.θa σ)))).erase := by
    unfold NR
    rw [Term.erase_cast]
    exact erase_of_heq' hctx (congrArg G.tr (G.repTy_subst_canon σ))
      (nrmTy_heq G N (G.repTy_subst_canon σ) hctx
        (Term.erase_inj_heq' _ _ hctx (congrArg G.tr (G.repTy_subst_canon σ))
          (by simp [Term.erase, Term.erase_cast]; rfl)))
  rw [e1, e2]
  simp only [Var.erase]
  exact congrArg (fun a => UTerm.app (G.tr (G.newTy.subst σ)) (N (G.newTy.subst σ)).closedLift.erase
    (UTerm.app a (UTerm.lam (G.RT (G.θa σ)) (UTerm.var 0))
      (G.NR N (G.θa σ) (Term.var Var.zero :
        Term S (G.RT (G.θa σ) :: Γ.map G.tr) (G.RT (G.θa σ)))).erase)) hR

theorem trans_rep_heq (N : G.Oracle) (τ : Ty) (h : (S G.rep).IsInst τ) (σ : TypeSub)
    (hσ : (S G.rep).subst σ = τ) {Γ : List Ty} :
    HEq (G.trans N (Term.const (S := S) (Γ := Γ) G.rep τ h)) (G.repI N (G.θa σ) (Γ.map G.tr)) := by
  subst hσ
  exact G.trans_rep_heq' N σ

theorem trans_abs_heq (N : G.Oracle) (τ : Ty) (h : (S G.abs).IsInst τ) (σ : TypeSub)
    (hσ : (S G.abs).subst σ = τ) {Γ : List Ty} :
    HEq (G.trans N (Term.const (S := S) (Γ := Γ) G.abs τ h)) (G.absI N (G.θa σ) (Γ.map G.tr)) := by
  subst hσ
  exact G.trans_abs_heq' N σ

theorem trans_repTerm_heq (N : G.Oracle) (θ : TypeSub) {Γ : List Ty} :
    HEq (G.trans N ((G.repTerm (Γ := Γ)).instType θ))
      (G.repI N (G.θa θ) ((Γ.map (Ty.subst θ)).map G.tr)) := by
  unfold repTerm
  exact G.trans_rep_heq N _ _ θ (congrArg (Ty.subst θ) G.rep_ty)

theorem trans_absTerm_heq (N : G.Oracle) (θ : TypeSub) {Γ : List Ty} :
    HEq (G.trans N ((G.absTerm (Γ := Γ)).instType θ))
      (G.absI N (G.θa θ) ((Γ.map (Ty.subst θ)).map G.tr)) := by
  unfold absTerm
  exact G.trans_abs_heq N _ _ θ (congrArg (Ty.subst θ) G.abs_ty)

theorem heq_rename_closed {A B : Ty} (hAB : A = B) {u : Term S [] A}
    {v : Term S [] B} (huv : HEq u v) {Δ : List Ty} (r r' : Ren [] Δ) :
    HEq (u.rename r) (v.rename r') := by
  subst hAB
  have := eq_of_heq huv
  subst this
  rw [Ren.empty_ext r r']

theorem trans_heq_type (N : G.Oracle) {a a' : Ty} (h : a = a') {t : Term S [] a}
    {t' : Term S [] a'} (ht : HEq t t') : HEq (G.trans N t) (G.trans N t') := by
  subst h
  have := eq_of_heq ht
  subst this
  rfl

theorem pred_instType_canon (θ : TypeSub) :
    HEq (G.pred.instType θ) (G.pred.instType (G.canonSub (G.θa θ))) := by
  refine Term.instType_congr G.pred (fun i hi ↦ ?_)
  have hi' : i < G.n := G.closed i hi
  simp [Ty.argsSub, hi', θa]

theorem trans_predIn_heq (N : G.Oracle) (θ : TypeSub) (Γ : List Ty) :
    HEq (G.trans N ((G.predIn Γ).instType θ))
      ((G.QT N (G.θa θ)).closedLift : Term S ((Γ.map (Ty.subst θ)).map G.tr) _) := by
  rw [G.predIn_eq]
  unfold Term.closedLift
  rw [Term.rename_instType, ← G.trans_rename N]
  have hty : (Ty.arr G.repTy .bool).subst θ = (Ty.arr G.repTy .bool).subst (G.canonSub (G.θa θ)) :=
    congrArg (fun X ↦ Ty.arr X Ty.bool) (G.repTy_subst_canon θ)
  have h1 := G.trans_heq_type N hty (G.pred_instType_canon θ)
  have hQ : HEq (G.trans N (G.pred.instType (G.canonSub (G.θa θ)))) (G.QT N (G.θa θ)) := by
    unfold QT; exact (eqRec_heq _ _).symm
  exact heq_rename_closed ((congrArg G.tr hty).trans (G.tr_Q_eq (G.θa θ))) (h1.trans hQ) _ _

theorem NR_cast_eq (N : G.Oracle) (θ : TypeSub) {Γ : List Ty}
    (x : Term S Γ (G.tr (G.repTy.subst θ))) :
    ((G.tr_RT_eq θ).symm ▸ G.NR N (G.θa θ) ((G.tr_RT_eq θ) ▸ x) :
      Term S Γ (G.tr (G.repTy.subst θ))) = G.nrmTy N (G.repTy.subst θ) x := by
  apply eq_of_heq
  refine (eqRec_heq _ _).trans ?_
  unfold NR
  refine (eqRec_heq _ _).trans ?_
  refine G.nrmTy_heq N (G.repTy_subst_canon θ).symm rfl ?_
  exact (eqRec_heq _ _).trans (eqRec_heq _ _)

theorem trans_law1 (N : G.Oracle) (hI : G.Idem N es) (θ : TypeSub)
    (hD : G.LawData N es (G.θa θ)) :
    HistoryDerivation S es (G.transSeq N (typeSubstSequent θ G.absRepSequent)) := by
  refine G.fromEq N hI (fun h' hh' ↦ ?_) ?_
  · simp only [transSeq, List.mem_append]; exact Or.inl hh'
  refine G.law1_gen N hI (G.θa θ) hD (G.tr_newTy_eq θ) (G.tr_RT_eq θ) (G.trans_repTerm_heq N θ)
    (G.trans_absTerm_heq N θ) _ ?_
  have hmem : (G.nrmTy N (Ty.subst θ G.newTy) (Term.var Var.zero)).equal (Term.var Var.zero) ∈
      G.ctxFix N [Ty.subst θ G.newTy] := List.mem_cons_self ..
  rw [G.nrmTy_newTy'] at hmem
  simp only [NK, Term.cast_cast]
  exact HistoryDerivation.assume' _ (List.mem_append_left _ hmem)

theorem trans_law2 (N : G.Oracle) (hI : G.Idem N es) (θ : TypeSub)
    (hD : G.LawData N es (G.θa θ)) :
    HistoryDerivation S es (G.transSeq N (typeSubstSequent θ G.repRangeSequent)) :=
  G.law2_gen N (G.θa θ) hD (G.tr_newTy_eq θ) (G.tr_RT_eq θ) (G.trans_repTerm_heq N θ)
    (G.trans_predIn_heq N θ _) _

theorem trans_law3 (N : G.Oracle) (hI : G.Idem N es) (θ : TypeSub)
    (hD : G.LawData N es (G.θa θ)) :
    HistoryDerivation S es (G.transSeq N (typeSubstSequent θ G.repAbsSequent)) := by
  refine G.fromEq N hI (fun h' hh' ↦ ?_) ?_
  · simp only [transSeq, List.mem_append]; exact Or.inl hh'
  refine G.law3_gen N (G.θa θ) hD (G.tr_newTy_eq θ) (G.tr_RT_eq θ) (G.trans_repTerm_heq N θ)
    (G.trans_absTerm_heq N θ) (G.trans_predIn_heq N θ _) _ ?_ ?_
  · have hmem : (G.nrmTy N (Ty.subst θ G.repTy) (Term.var Var.zero)).equal (Term.var Var.zero) ∈
        G.ctxFix N [Ty.subst θ G.repTy] := List.mem_cons_self ..
    rw [G.NR_cast_eq N θ]
    exact HistoryDerivation.assume' _ (List.mem_append_left _ hmem)
  · exact HistoryDerivation.assume' _ (List.mem_append_right _ (List.mem_map.mpr
      ⟨((G.predIn [G.repTy]).app (Term.var Var.zero)).instType θ,
        List.mem_singleton_self _, rfl⟩))

end Calc

end TypeDefGate

end QEDFV.HOL
