///|
/// Type-definition admission wrapper (TypeDefOK gate).
pub fn logic_register_typedef(
  state : @kernel.KernelState,
  tycon : String,
  params : Array[String],
  rep_name : String,
  predicate : @kernel.Term,
  witness : @kernel.Thm,
) -> Result[@kernel.KernelState, @kernel.SigError] {
  @kernel.ks_register_type_definition(
    state, tycon, params, rep_name, predicate, witness,
  )
}

///|
/// Specification admission wrapper (SpecOK over choice + def).
pub fn logic_specify_const(
  state : @kernel.KernelState,
  name : String,
  decl_ty : @kernel.HolType,
  predicate : @kernel.Term,
  witness : @kernel.Thm,
) -> Result[(@kernel.KernelState, @kernel.Thm), @kernel.SigError] {
  @kernel.ks_specify_const(state, name, decl_ty, predicate, witness)
}

///|
/// Infinity-anchor registration wrapper.
pub fn logic_register_ind_infinity_anchor(
  state : @kernel.KernelState,
  anchor : @kernel.Thm,
) -> Result[@kernel.KernelState, @kernel.SigError] {
  @kernel.ks_register_ind_infinity_axiom(state, anchor)
}

///|
pub fn logic_ind_infinity_anchor(
  state : @kernel.KernelState,
) -> Result[@kernel.Thm, @kernel.SigError] {
  @kernel.ks_ind_infinity_axiom(state)
}

///|
pub fn logic_typedef_contract(
  state : @kernel.KernelState,
  tycon : String,
) -> Result[(@kernel.Thm, @kernel.Thm, @kernel.Thm), @kernel.SigError] {
  @kernel.ks_typedef_contract(state, tycon)
}

///|
pub fn logic_extension_cert_count(state : @kernel.KernelState) -> Int {
  @kernel.ks_extension_cert_count(state)
}

///|
pub fn logic_extension_cert_at(
  state : @kernel.KernelState,
  idx : Int,
) -> @kernel.ExtensionCert? {
  @kernel.ks_extension_cert_at(state, idx)
}

///|
pub fn logic_conservative_replay_ok(
  base_state : @kernel.KernelState,
  extended_state : @kernel.KernelState,
  th : @kernel.Thm,
) -> Bool {
  @kernel.ks_conservative_replay_ok(base_state, extended_state, th)
}

///|
pub fn logic_extensions_phase0_ready() -> Bool {
  true
}
