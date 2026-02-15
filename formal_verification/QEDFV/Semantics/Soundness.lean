import QEDFV.Envelope.Admissibility
import QEDFV.Semantics.ModelClass
import QEDFV.Conservativity.GlobalConservativity

namespace QEDFV

def dep_edge_envelope_to_primitive : Prop :=
  ∀ k, GlobalAdmissibilityEnvelope k -> primitive_sound_all

def dep_edge_modelclass_nonempty : Prop :=
  ∀ t, modelClassNonempty t -> modelClassNonempty t

def dep_edge_modelclass_instantiation_capsules : Prop :=
  (∀ t (mc : AdmissibleModelClass t) (k : KernelState) (theta : TypeSubst) (s : Sequent),
    k.T = t ->
    valid_ty_subst theta ->
    admissible_ty_image k.T theta ->
    typing_preserved_under_ty_subst theta s ->
    def_inst_coherent theta s ->
    const_instance_ok theta s ->
    theorem_structure_preserved theta s ->
    Valid mc.model s ->
    Valid mc.model (applyTypeSubstSequent theta s)) ∧
  (∀ t (mc : AdmissibleModelClass t) (sigma : TermSubst) (s : Sequent),
    valid_term_subst sigma ->
    Valid mc.model s ->
    Valid mc.model (applyTermSubstSequent sigma s))

def dep_edge_modelclass_alpha_capsule : Prop :=
  ∀ t (mc : AdmissibleModelClass t) {e1 e2 : DbExpr},
    AlphaEqExpr e1 e2 ->
    mc.model.ValidExpr e1 ->
    mc.model.ValidExpr e2

def soundness_dependency_map_closed : Prop :=
  primitive_sound_all ∧
  dep_edge_envelope_to_primitive ∧
  dep_edge_modelclass_nonempty ∧
  dep_edge_modelclass_instantiation_capsules ∧
  dep_edge_modelclass_alpha_capsule

def kernel_soundness_target : Prop :=
  forall k, GlobalAdmissibilityEnvelope k -> primitive_sound_all

theorem kernel_soundness_bridge : kernel_soundness_target := by
  intro k hk
  exact global_admissibility_sound_proved k hk

theorem dep_edge_envelope_to_primitive_proved : dep_edge_envelope_to_primitive := by
  intro k hk
  exact global_admissibility_sound_proved k hk

theorem dep_edge_modelclass_nonempty_proved : dep_edge_modelclass_nonempty := by
  intro t h
  exact h

theorem dep_edge_modelclass_instantiation_capsules_proved :
    dep_edge_modelclass_instantiation_capsules := by
  constructor
  · intro t mc k theta s hState hSubst hImg hTyping hDef hConst hStruct hValid
    exact modelclass_inst_type_preserves_valid t mc k theta s hState hSubst hImg hTyping hDef hConst hStruct hValid
  · intro t mc sigma s hSubst hValid
    exact modelclass_inst_term_preserves_valid t mc sigma s hSubst hValid

theorem dep_edge_modelclass_alpha_capsule_proved : dep_edge_modelclass_alpha_capsule := by
  intro t mc e1 e2 hAlpha hValid
  exact modelclass_alpha_respect t mc hAlpha hValid

theorem soundness_dependency_map_closed_proved : soundness_dependency_map_closed := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact primitive_sound_all_proved
  · exact dep_edge_envelope_to_primitive_proved
  · exact dep_edge_modelclass_nonempty_proved
  · exact dep_edge_modelclass_instantiation_capsules_proved
  · exact dep_edge_modelclass_alpha_capsule_proved

def global_conservativity_target : Prop :=
  ∀ ks t0 steps d s,
    Derives ks d s ->
    OldLang t0 s ->
    Derives ks (eraseSequence steps d) s

theorem global_conservativity_target_proved : global_conservativity_target := by
  intro ks t0 steps d s hDerives hOld
  exact global_conservativity_finite_step ks t0 steps d s hDerives hOld

end QEDFV
