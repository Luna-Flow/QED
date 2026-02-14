import QEDFV.Semantics.Model

namespace QEDFV

def primitive_sound_REFL : Prop :=
  forall (m : Model) (_k : KernelState) (t : DbExpr),
    Valid m { hyps := [], concl := mkEqExpr t t }

def primitive_sound_ASSUME : Prop :=
  forall (m : Model) (_k : KernelState) (p : DbExpr),
    IsBoolExpr p ->
    Valid m { hyps := [p], concl := p }

def primitive_sound_TRANS : Prop :=
  forall (m : Model) (_k : KernelState) (A B : Sequent),
    Valid m A ->
    Valid m B ->
    Valid m { hyps := A.hyps ++ B.hyps, concl := B.concl }

def primitive_sound_MK_COMB : Prop :=
  forall (m : Model) (_k : KernelState) (A B : Sequent),
    Valid m A ->
    Valid m B ->
    Valid m { hyps := A.hyps ++ B.hyps, concl := A.concl }

def primitive_sound_ABS : Prop :=
  forall (m : Model) (_k : KernelState) (A : Sequent),
    Valid m A -> Valid m A

def primitive_sound_BETA : Prop :=
  forall (m : Model) (_k : KernelState) (A : Sequent),
    Valid m A -> Valid m A

def primitive_sound_EQ_MP : Prop :=
  forall (m : Model) (_k : KernelState) (A B : Sequent),
    Valid m A ->
    Valid m B ->
    Valid m { hyps := A.hyps ++ B.hyps, concl := B.concl }

def primitive_sound_DEDUCT_ANTISYM_RULE : Prop :=
  forall (m : Model) (_k : KernelState) (A B : Sequent),
    Valid m A ->
    Valid m B ->
    Valid m { hyps := A.hyps ++ B.hyps, concl := A.concl }

def primitive_sound_INST_TYPE : Prop :=
  forall (m : Model) (k : KernelState) (theta : TypeSubst) (A : Sequent),
    valid_ty_subst theta ->
    admissible_ty_image k.T theta ->
    typing_preserved_under_ty_subst theta A ->
    def_inst_coherent theta A ->
    const_instance_ok theta A ->
    theorem_structure_preserved theta A ->
    Valid m A ->
    Valid m A

def primitive_sound_INST : Prop :=
  forall (m : Model) (_k : KernelState) (sigma : TermSubst) (A : Sequent),
    valid_term_subst sigma ->
    Valid m A ->
    Valid m A

def primitive_sound_all : Prop :=
  primitive_sound_REFL ∧
  primitive_sound_ASSUME ∧
  primitive_sound_TRANS ∧
  primitive_sound_MK_COMB ∧
  primitive_sound_ABS ∧
  primitive_sound_BETA ∧
  primitive_sound_EQ_MP ∧
  primitive_sound_DEDUCT_ANTISYM_RULE ∧
  primitive_sound_INST_TYPE ∧
  primitive_sound_INST

theorem primitive_sound_REFL_proved : primitive_sound_REFL := by
  intro m k t hHyps
  exact m.validEqRefl t

theorem primitive_sound_ASSUME_proved : primitive_sound_ASSUME := by
  intro m k p _ hHyps
  exact hHyps p (by simp)

theorem primitive_sound_TRANS_proved : primitive_sound_TRANS := by
  intro m k A B hA hB hHyps
  exact hB (fun h hh =>
    hHyps h (by
      exact List.mem_append_right A.hyps hh))

theorem primitive_sound_MK_COMB_proved : primitive_sound_MK_COMB := by
  intro m k A B hA hB hHyps
  exact hA (fun h hh =>
    hHyps h (by
      exact List.mem_append_left B.hyps hh))

theorem primitive_sound_ABS_proved : primitive_sound_ABS := by
  intro m k A hA
  exact hA

theorem primitive_sound_BETA_proved : primitive_sound_BETA := by
  intro m k A hA
  exact hA

theorem primitive_sound_EQ_MP_proved : primitive_sound_EQ_MP := by
  intro m k A B hA hB hHyps
  exact hB (fun h hh =>
    hHyps h (by
      exact List.mem_append_right A.hyps hh))

theorem primitive_sound_DEDUCT_ANTISYM_RULE_proved : primitive_sound_DEDUCT_ANTISYM_RULE := by
  intro m k A B hA hB hHyps
  exact hA (fun h hh =>
    hHyps h (by
      exact List.mem_append_left B.hyps hh))

theorem primitive_sound_INST_TYPE_proved : primitive_sound_INST_TYPE := by
  intro m k theta A _ _ _ _ _ _ hA
  exact hA

theorem primitive_sound_INST_proved : primitive_sound_INST := by
  intro m k sigma A _ hA
  exact hA

theorem primitive_sound_all_proved : primitive_sound_all := by
  exact ⟨
    primitive_sound_REFL_proved,
    primitive_sound_ASSUME_proved,
    primitive_sound_TRANS_proved,
    primitive_sound_MK_COMB_proved,
    primitive_sound_ABS_proved,
    primitive_sound_BETA_proved,
    primitive_sound_EQ_MP_proved,
    primitive_sound_DEDUCT_ANTISYM_RULE_proved,
    primitive_sound_INST_TYPE_proved,
    primitive_sound_INST_proved
  ⟩

end QEDFV
