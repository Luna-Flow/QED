import QEDFV.HOL.Transport

/-! Syntactic laws of the typed term operations, used by constant-replacement
(erasure) arguments: fusion of renaming and substitution, closed terms, and the functor laws
of type instantiation. The functor laws of `Term.instType` are proved through an
annotation-preserving erasure to untyped terms (`UTerm`), which avoids heterogeneous
equalities of terms with different type indices. -/
namespace QEDFV.HOL

variable {S : Signature} {Γ Δ Θ : List Ty} {a b : Ty}

/-! ### Renaming and substitution -/

def Ren.comp (r' : Ren Δ Θ) (r : Ren Γ Δ) : Ren Γ Θ := fun v ↦ r' (r v)

theorem Ren.lift_comp (r' : Ren Δ Θ) (r : Ren Γ Δ) :
    @Eq (Ren (b :: Γ) (b :: Θ)) (Ren.lift (Ren.comp r' r))
      (Ren.comp (Ren.lift r') (Ren.lift r)) := by
  funext c v
  cases v <;> rfl

theorem Term.rename_rename (t : Term S Γ a) (r : Ren Γ Δ) (r' : Ren Δ Θ) :
    (t.rename r).rename r' = t.rename (Ren.comp r' r) := by
  induction t generalizing Δ Θ with
  | var v => rfl
  | const c σ => rfl
  | app f x ihf ihx => simp only [Term.rename, ihf, ihx]
  | lam b ih => simp only [Term.rename, ih, Ren.lift_comp]
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq => simp only [Term.rename, ihp, ihq]
  | imp p q ihp ihq => simp only [Term.rename, ihp, ihq]
  | all p ih => simp only [Term.rename, ih, Ren.lift_comp]
  | ex p ih => simp only [Term.rename, ih, Ren.lift_comp]
  | eq => rfl
  | choice => rfl



theorem Ren.lift_id : @Eq (Ren (b :: Γ) (b :: Γ)) (Ren.lift (fun v ↦ v)) (fun v ↦ v) := by
  funext c v; cases v <;> rfl

theorem Sub.lift_var (r : Ren Γ Δ) :
    @Eq (Sub S (b :: Γ) (b :: Δ)) (Sub.lift (fun v ↦ Term.var (r v)))
      (fun v ↦ Term.var (Ren.lift r v)) := by
  funext c v; cases v <;> rfl

theorem Sub.lift_ren (r : Ren Γ Δ) (σ : Sub S Δ Θ) :
    @Eq (Sub S (b :: Γ) (b :: Θ)) (Sub.lift (fun v ↦ σ (r v)))
      (fun v ↦ (Sub.lift σ) (Ren.lift r v)) := by
  funext c v; cases v <;> rfl

theorem Sub.lift_rename (σ : Sub S Γ Δ) (r : Ren Δ Θ) :
    @Eq (Sub S (b :: Γ) (b :: Θ)) (Sub.lift (fun v ↦ (σ v).rename r))
      (fun v ↦ ((Sub.lift σ) v).rename (Ren.lift r)) := by
  funext c v
  cases v with
  | zero => rfl
  | succ v =>
      change ((σ v).rename r).rename Var.succ =
        ((σ v).rename Var.succ).rename (Ren.lift r)
      rw [Term.rename_rename, Term.rename_rename]
      rfl

theorem Term.rename_id (t : Term S Γ a) : t.rename (fun v ↦ v) = t := by
  induction t with
  | var v => rfl
  | const c σ => rfl
  | app f x ihf ihx => simp only [Term.rename, ihf, ihx]
  | lam b ih =>
      simp only [Term.rename, Ren.lift_id, ih]
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq => simp only [Term.rename, ihp, ihq]
  | imp p q ihp ihq => simp only [Term.rename, ihp, ihq]
  | all p ih =>
      simp only [Term.rename, Ren.lift_id, ih]
  | ex p ih =>
      simp only [Term.rename, Ren.lift_id, ih]
  | eq => rfl
  | choice => rfl

theorem Term.substitute_var (t : Term S Γ a) (r : Ren Γ Δ) :
    t.substitute (fun v ↦ Term.var (r v)) = t.rename r := by
  induction t generalizing Δ with
  | var v => rfl
  | const c σ => rfl
  | app f x ihf ihx => simp only [Term.substitute, Term.rename, ihf, ihx]
  | lam b ih =>
      simp only [Term.substitute, Term.rename, Sub.lift_var, ih]
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq => simp only [Term.substitute, Term.rename, ihp, ihq]
  | imp p q ihp ihq => simp only [Term.substitute, Term.rename, ihp, ihq]
  | all p ih =>
      simp only [Term.substitute, Term.rename, Sub.lift_var, ih]
  | ex p ih =>
      simp only [Term.substitute, Term.rename, Sub.lift_var, ih]
  | eq => rfl
  | choice => rfl

theorem Term.substitute_rename (t : Term S Γ a) (r : Ren Γ Δ) (σ : Sub S Δ Θ) :
    (t.rename r).substitute σ = t.substitute (fun v ↦ σ (r v)) := by
  induction t generalizing Δ Θ with
  | var v => rfl
  | const c θ => rfl
  | app f x ihf ihx => simp only [Term.rename, Term.substitute, ihf, ihx]
  | lam b ih =>
      simp only [Term.rename, Term.substitute, ih, Sub.lift_ren]
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq => simp only [Term.rename, Term.substitute, ihp, ihq]
  | imp p q ihp ihq => simp only [Term.rename, Term.substitute, ihp, ihq]
  | all p ih =>
      simp only [Term.rename, Term.substitute, ih, Sub.lift_ren]
  | ex p ih =>
      simp only [Term.rename, Term.substitute, ih, Sub.lift_ren]
  | eq => rfl
  | choice => rfl

theorem Term.rename_substitute (t : Term S Γ a) (σ : Sub S Γ Δ) (r : Ren Δ Θ) :
    (t.substitute σ).rename r = t.substitute (fun v ↦ (σ v).rename r) := by
  induction t generalizing Δ Θ with
  | var v => rfl
  | const c θ => rfl
  | app f x ihf ihx => simp only [Term.substitute, Term.rename, ihf, ihx]
  | lam b ih =>
      simp only [Term.substitute, Term.rename, ih, Sub.lift_rename]
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq => simp only [Term.substitute, Term.rename, ihp, ihq]
  | imp p q ihp ihq => simp only [Term.substitute, Term.rename, ihp, ihq]
  | all p ih =>
      simp only [Term.substitute, Term.rename, ih, Sub.lift_rename]
  | ex p ih =>
      simp only [Term.substitute, Term.rename, ih, Sub.lift_rename]
  | eq => rfl
  | choice => rfl

/-! ### Closed terms -/

/-- The unique renaming out of the empty context. -/
def Ren.empty : Ren [] Δ := fun v ↦ nomatch v

theorem Ren.empty_ext (r r' : Ren [] Δ) : @Eq (Ren [] Δ) r r' := by
  funext c v
  cases v

/-- Embed a closed term in any context. -/
def Term.closedLift (t : Term S [] a) : Term S Γ a :=
  t.rename Ren.empty

theorem Term.closedLift_rename (t : Term S [] a) (r : Ren Γ Δ) :
    (t.closedLift : Term S Γ a).rename r = t.closedLift := by
  unfold Term.closedLift
  rw [Term.rename_rename]
  exact congrArg (fun r => t.rename r) (Ren.empty_ext _ _)

theorem Term.closedLift_substitute (t : Term S [] a) (σ : Sub S Γ Δ) :
    (t.closedLift : Term S Γ a).substitute σ = t.closedLift := by
  unfold Term.closedLift
  rw [Term.substitute_rename]
  have h : @Eq (Sub S [] Δ) (fun v ↦ σ (Ren.empty v)) (fun v ↦ Term.var (Ren.empty v)) := by
    funext c v; cases v
  exact (congrArg (fun f => t.substitute f) h).trans (Term.substitute_var t _)

theorem Term.closedLift_nil (t : Term S [] a) : (t.closedLift : Term S [] a) = t := by
  unfold Term.closedLift
  have h : @Eq (Ren [] []) Ren.empty (fun v ↦ v) := Ren.empty_ext _ _
  rw [h, Term.rename_id]

/-! ### Type instantiation commutes with renaming -/

/-- The renaming induced on type-instantiated contexts. -/
def Ren.mapTypes (θ : TypeSub) :
    {Γ Δ : List Ty} → Ren Γ Δ → Ren (Γ.map (Ty.subst θ)) (Δ.map (Ty.subst θ))
  | [], _, _ => fun v ↦ nomatch v
  | _ :: _, _, r => fun v ↦
      match v with
      | .zero => (r .zero).mapTypes θ
      | .succ w => Ren.mapTypes θ (fun u ↦ r (.succ u)) w

theorem Ren.mapTypes_apply (θ : TypeSub) (r : Ren Γ Δ) (v : Var Γ a) :
    Ren.mapTypes θ r (v.mapTypes θ) = (r v).mapTypes θ := by
  induction v with
  | zero => rfl
  | succ v ih => exact ih (fun u ↦ r (.succ u))

theorem Ren.mapTypes_succ (θ : TypeSub) (r : Ren Γ Δ) {c : Ty} (w : Var (Γ.map (Ty.subst θ)) c) :
    Ren.mapTypes θ (fun u ↦ Var.succ (r u) : Ren Γ (b :: Δ)) w
      = Var.succ (Ren.mapTypes θ r w) := by
  induction Γ generalizing Δ with
  | nil => cases w
  | cons x Γ ih =>
      cases w with
      | zero => rfl
      | succ w => exact ih (fun u ↦ r (.succ u)) w

theorem Ren.mapTypes_lift (θ : TypeSub) (r : Ren Γ Δ) :
    @Eq (Ren ((b :: Γ).map (Ty.subst θ)) ((b :: Δ).map (Ty.subst θ)))
      (Ren.mapTypes θ (Ren.lift r : Ren (b :: Γ) (b :: Δ)))
      (Ren.lift (Ren.mapTypes θ r)) := by
  funext c v
  cases v with
  | zero => rfl
  | succ w => exact Ren.mapTypes_succ θ r w

theorem Term.rename_cast {h : a = b} (t : Term S Γ a) (r : Ren Γ Δ) :
    (h ▸ t).rename r = h ▸ t.rename r := by
  cases h; rfl

theorem Term.rename_instType (t : Term S Γ a) (θ : TypeSub) (r : Ren Γ Δ) :
    (t.rename r).instType θ = (t.instType θ).rename (Ren.mapTypes θ r) := by
  induction t generalizing Δ with
  | var v => exact congrArg Term.var (Ren.mapTypes_apply θ r v).symm
  | const c σ => simp only [Term.rename, Term.instType, Term.rename_cast]
  | app f x ihf ihx => simp only [Term.rename, Term.instType, ihf, ihx]
  | lam b ih => simp only [Term.rename, Term.instType, ih, Ren.mapTypes_lift]
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq => simp only [Term.rename, Term.instType, ihp, ihq]
  | imp p q ihp ihq => simp only [Term.rename, Term.instType, ihp, ihq]
  | all p ih => simp only [Term.rename, Term.instType, ih, Ren.mapTypes_lift]
  | ex p ih => simp only [Term.rename, Term.instType, ih, Ren.mapTypes_lift]
  | eq => rfl
  | choice => rfl

theorem Term.closedLift_instType (t : Term S [] a) (θ : TypeSub) :
    (t.closedLift : Term S Γ a).instType θ
      = (t.instType θ).closedLift := by
  unfold Term.closedLift
  rw [Term.rename_instType]
  exact congrArg (fun r => (t.instType θ).rename r) (Ren.empty_ext _ _)

/-! ### Erasure to annotated untyped terms -/

/-- Untyped terms that keep every type annotation. Two typed terms of the same context and
type with equal erasures are equal (`Term.erase_inj`). -/
inductive UTerm where
  | var (n : Nat)
  | const (c : Nat) (σ : TypeSub)
  | app (a : Ty) (f x : UTerm)
  | lam (a : Ty) (b : UTerm)
  | truth
  | falsity
  | conj (p q : UTerm)
  | imp (p q : UTerm)
  | all (a : Ty) (p : UTerm)
  | ex (a : Ty) (p : UTerm)
  | eq (a : Ty)
  | choice (a : Ty)

def Var.erase {Γ : List Ty} {a : Ty} (v : Var Γ a) : Nat :=
  match v with
  | .zero => 0
  | .succ w => w.erase + 1

theorem Var.erase_inj (v : Var Γ a) (w : Var Γ a) (h : v.erase = w.erase) : v = w := by
  induction v with
  | zero => cases w with
    | zero => rfl
    | succ w => simp [Var.erase] at h
  | succ v ih => cases w with
    | zero => simp [Var.erase] at h
    | succ w => exact congrArg Var.succ (ih w (by simpa [Var.erase] using h))

def Term.erase {Γ : List Ty} {a : Ty} (t : Term S Γ a) : UTerm :=
  match t with
  | .var v => .var v.erase
  | .const c σ => .const c σ
  | @Term.app _ _ a _ f x => .app a f.erase x.erase
  | @Term.lam _ a _ _ b => .lam a b.erase
  | .truth => .truth
  | .falsity => .falsity
  | .conj p q => .conj p.erase q.erase
  | .imp p q => .imp p.erase q.erase
  | @Term.all _ a _ p => .all a p.erase
  | @Term.ex _ a _ p => .ex a p.erase
  | @Term.eq _ _ a => .eq a
  | @Term.choice _ _ a => .choice a

theorem Term.erase_inj_heq (t : Term S Γ a) :
    ∀ {a' : Ty} (t' : Term S Γ a'), a = a' → t.erase = t'.erase → HEq t t' := by
  induction t with
  | var v =>
      intro a' t' ha h
      cases t' <;> simp [Term.erase] at h
      subst ha
      exact heq_of_eq (congrArg Term.var (Var.erase_inj _ _ h))
  | const c σ =>
      intro a' t' ha h
      cases t' <;> simp [Term.erase] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | app f x ihf ihx =>
      intro a' t' ha h
      cases t' <;> simp [Term.erase] at h
      obtain ⟨rfl, hf, hx⟩ := h
      subst ha
      have h1 := ihf _ rfl hf
      have h2 := ihx _ rfl hx
      rw [eq_of_heq h1, eq_of_heq h2]
  | lam b ih =>
      intro a' t' ha h
      cases t' <;> simp [Term.erase] at h
      obtain ⟨rfl, rfl⟩ := Ty.arr.inj ha
      rw [eq_of_heq (ih _ rfl h.2)]
  | truth =>
      intro a' t' ha h
      cases t' <;> simp [Term.erase] at h
      rfl
  | falsity =>
      intro a' t' ha h
      cases t' <;> simp [Term.erase] at h
      rfl
  | conj p q ihp ihq =>
      intro a' t' ha h
      cases t' <;> simp [Term.erase] at h
      rw [eq_of_heq (ihp _ rfl h.1), eq_of_heq (ihq _ rfl h.2)]
  | imp p q ihp ihq =>
      intro a' t' ha h
      cases t' <;> simp [Term.erase] at h
      rw [eq_of_heq (ihp _ rfl h.1), eq_of_heq (ihq _ rfl h.2)]
  | all p ih =>
      intro a' t' ha h
      cases t' <;> simp [Term.erase] at h
      obtain ⟨rfl, h⟩ := h
      rw [eq_of_heq (ih _ rfl h)]
  | ex p ih =>
      intro a' t' ha h
      cases t' <;> simp [Term.erase] at h
      obtain ⟨rfl, h⟩ := h
      rw [eq_of_heq (ih _ rfl h)]
  | eq =>
      intro a' t' ha h
      cases t' <;> simp [Term.erase] at h
      subst h
      rfl
  | choice =>
      intro a' t' ha h
      cases t' <;> simp [Term.erase] at h
      subst h
      rfl

theorem Term.erase_inj_heq' (t : Term S Γ a) :
    ∀ {Γ' : List Ty} {a' : Ty} (t' : Term S Γ' a'), Γ = Γ' → a = a' → t.erase = t'.erase →
      HEq t t' := by
  induction t with
  | var v =>
      intro Γ' a' t' hΓ ha h
      subst hΓ
      cases t' <;> simp [Term.erase] at h
      subst ha
      exact heq_of_eq (congrArg Term.var (Var.erase_inj _ _ h))
  | const c σ =>
      intro Γ' a' t' hΓ ha h
      subst hΓ
      cases t' <;> simp [Term.erase] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | app f x ihf ihx =>
      intro Γ' a' t' hΓ ha h
      subst hΓ
      cases t' <;> simp [Term.erase] at h
      obtain ⟨rfl, hf, hx⟩ := h
      subst ha
      have h1 := ihf _ rfl rfl hf
      have h2 := ihx _ rfl rfl hx
      rw [eq_of_heq h1, eq_of_heq h2]
  | lam b ih =>
      intro Γ' a' t' hΓ ha h
      subst hΓ
      cases t' <;> simp [Term.erase] at h
      obtain ⟨rfl, rfl⟩ := Ty.arr.inj ha
      rw [eq_of_heq (ih _ rfl rfl h.2)]
  | truth =>
      intro Γ' a' t' hΓ ha h
      subst hΓ
      cases t' <;> simp [Term.erase] at h
      rfl
  | falsity =>
      intro Γ' a' t' hΓ ha h
      subst hΓ
      cases t' <;> simp [Term.erase] at h
      rfl
  | conj p q ihp ihq =>
      intro Γ' a' t' hΓ ha h
      subst hΓ
      cases t' <;> simp [Term.erase] at h
      rw [eq_of_heq (ihp _ rfl rfl h.1), eq_of_heq (ihq _ rfl rfl h.2)]
  | imp p q ihp ihq =>
      intro Γ' a' t' hΓ ha h
      subst hΓ
      cases t' <;> simp [Term.erase] at h
      rw [eq_of_heq (ihp _ rfl rfl h.1), eq_of_heq (ihq _ rfl rfl h.2)]
  | all p ih =>
      intro Γ' a' t' hΓ ha h
      subst hΓ
      cases t' <;> simp [Term.erase] at h
      obtain ⟨rfl, h⟩ := h
      rw [eq_of_heq (ih _ rfl rfl h)]
  | ex p ih =>
      intro Γ' a' t' hΓ ha h
      subst hΓ
      cases t' <;> simp [Term.erase] at h
      obtain ⟨rfl, h⟩ := h
      rw [eq_of_heq (ih _ rfl rfl h)]
  | eq =>
      intro Γ' a' t' hΓ ha h
      subst hΓ
      cases t' <;> simp [Term.erase] at h
      subst h
      rfl
  | choice =>
      intro Γ' a' t' hΓ ha h
      subst hΓ
      cases t' <;> simp [Term.erase] at h
      subst h
      rfl

theorem Term.erase_inj {t t' : Term S Γ a} (h : t.erase = t'.erase) : t = t' :=
  eq_of_heq (Term.erase_inj_heq t t' rfl h)

/-! ### Functor laws of type instantiation -/

def UTerm.inst (θ : TypeSub) : UTerm → UTerm
  | .var n => .var n
  | .const c σ => .const c (θ.comp σ)
  | .app a f x => .app (a.subst θ) (f.inst θ) (x.inst θ)
  | .lam a b => .lam (a.subst θ) (b.inst θ)
  | .truth => .truth
  | .falsity => .falsity
  | .conj p q => .conj (p.inst θ) (q.inst θ)
  | .imp p q => .imp (p.inst θ) (q.inst θ)
  | .all a p => .all (a.subst θ) (p.inst θ)
  | .ex a p => .ex (a.subst θ) (p.inst θ)
  | .eq a => .eq (a.subst θ)
  | .choice a => .choice (a.subst θ)

theorem UTerm.inst_var (u : UTerm) : u.inst Ty.var = u := by
  induction u <;> simp_all [UTerm.inst]
  rename_i c σ
  funext i
  simp [TypeSub.comp]

theorem UTerm.inst_comp (u : UTerm) (σ θ : TypeSub) :
    (u.inst σ).inst θ = u.inst (θ.comp σ) := by
  induction u <;> simp_all [UTerm.inst]
  rename_i c τ
  funext i
  simp [TypeSub.comp]

theorem Term.erase_cast {h : a = b} (t : Term S Γ a) : (h ▸ t).erase = t.erase := by
  cases h; rfl

theorem Var.erase_mapTypes (θ : TypeSub) (v : Var Γ a) : (v.mapTypes θ).erase = v.erase := by
  induction v with
  | zero => rfl
  | succ v ih => simp [Var.mapTypes, Var.erase, ih]

theorem Term.erase_instType (t : Term S Γ a) (θ : TypeSub) :
    (t.instType θ).erase = t.erase.inst θ := by
  induction t with
  | var v => simp [Term.instType, Term.erase, UTerm.inst, Var.erase_mapTypes]
  | const c σ => simp [Term.instType, Term.erase_cast, Term.erase, UTerm.inst]
  | app f x ihf ihx => simp [Term.instType, Term.erase, UTerm.inst, ihf, ihx]
  | lam b ih => simp [Term.instType, Term.erase, UTerm.inst, ih]
  | truth => rfl
  | falsity => rfl
  | conj p q ihp ihq => simp [Term.instType, Term.erase, UTerm.inst, ihp, ihq]
  | imp p q ihp ihq => simp [Term.instType, Term.erase, UTerm.inst, ihp, ihq]
  | all p ih => simp [Term.instType, Term.erase, UTerm.inst, ih]
  | ex p ih => simp [Term.instType, Term.erase, UTerm.inst, ih]
  | eq => rfl
  | choice => rfl

/-- Instantiating a closed term at the identity substitution does not change it. -/
theorem Term.instType_var (t : Term S [] a) :
    (Ty.subst_id a ▸ t.instType Ty.var : Term S [] a) = t := by
  apply Term.erase_inj
  rw [Term.erase_cast, Term.erase_instType, UTerm.inst_var]

/-- Instantiating a closed term twice is instantiating once at the composite. -/
theorem Term.instType_instType (t : Term S [] a) (σ θ : TypeSub) :
    (Ty.subst_comp a θ σ ▸ (t.instType σ).instType θ : Term S [] (a.subst (θ.comp σ)))
      = t.instType (θ.comp σ) := by
  apply Term.erase_inj
  rw [Term.erase_cast, Term.erase_instType, Term.erase_instType, Term.erase_instType,
    UTerm.inst_comp]

end QEDFV.HOL
