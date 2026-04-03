///|
/// Type-definition admission wrapper (TypeDefOK gate).
pub fn logic_register_typedef(
  state : KernelState,
  tycon : String,
  params : Array[String],
  rep_name : String,
  predicate : Term,
  witness : Thm,
) -> Result[KernelState, SigError] {
  ks_register_type_definition(
    state, tycon, params, rep_name, predicate, witness,
  )
}

///|
/// Specification admission wrapper (SpecOK over choice + def).
pub fn logic_specify_const(
  state : KernelState,
  name : String,
  decl_ty : HolType,
  predicate : Term,
  witness : Thm,
) -> Result[(KernelState, Thm), SigError] {
  ks_specify_const(state, name, decl_ty, predicate, witness)
}

///|
/// Infinity-anchor registration wrapper.
pub fn logic_register_ind_infinity_anchor(
  state : KernelState,
  anchor : Thm,
) -> Result[KernelState, SigError] {
  ks_register_ind_infinity_axiom(state, anchor)
}

///|
pub fn logic_ind_infinity_anchor(state : KernelState) -> Result[Thm, SigError] {
  ks_ind_infinity_axiom(state)
}

///|
pub fn logic_typedef_contract(
  state : KernelState,
  tycon : String,
) -> Result[(Thm, Thm, Thm), SigError] {
  ks_typedef_contract(state, tycon)
}

///|
pub fn logic_extension_cert_count(state : KernelState) -> Int {
  ks_extension_cert_count(state)
}

///|
pub fn logic_extension_cert_at(
  state : KernelState,
  idx : Int,
) -> ExtensionCert? {
  ks_extension_cert_at(state, idx)
}

///|
pub fn logic_conservative_replay_ok(
  base_state : KernelState,
  extended_state : KernelState,
  th : Thm,
) -> Bool {
  ks_conservative_replay_ok(base_state, extended_state, th)
}

///|
pub fn logic_extensions_phase0_ready() -> Bool {
  true
}
