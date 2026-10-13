///|
fn mutate_immutability_type(ty : @kernel.HolType) -> Unit {
  match ty {
    @kernel.HolType::TyApp(_, args) => args.push(@kernel.ind_ty())
    @kernel.HolType::TyVal(_) => ()
  }
}

///|
fn mutate_immutability_term(term : @kernel.Term) -> Unit {
  match term {
    @kernel.Term::Var(_, ty) => mutate_immutability_type(ty)
    @kernel.Term::Const(_, ty, _) => mutate_immutability_type(ty)
    @kernel.Term::Comb(f, x) => {
      mutate_immutability_term(f)
      mutate_immutability_term(x)
    }
    @kernel.Term::Abs(v, body) => {
      mutate_immutability_term(v)
      mutate_immutability_term(body)
    }
  }
}

///|
fn mutate_immutability_db_term(term : @kernel.DbTerm) -> Unit {
  match term {
    @kernel.DbTerm::DbBound(_, ty) => mutate_immutability_type(ty)
    @kernel.DbTerm::DbFree(_, ty) => mutate_immutability_type(ty)
    @kernel.DbTerm::DbConst(_, ty, _) => mutate_immutability_type(ty)
    @kernel.DbTerm::DbComb(f, x) => {
      mutate_immutability_db_term(f)
      mutate_immutability_db_term(x)
    }
    @kernel.DbTerm::DbAbs(ty, body) => {
      mutate_immutability_type(ty)
      mutate_immutability_db_term(body)
    }
  }
}

///|
test "theorem admission snapshots caller-owned type arrays" {
  let st = @kernel.empty_kernel_state()
  let b = @kernel.bool_ty()
  let left_dom = @kernel.fun_ty(b, b)
  let right_dom_args = [b, b]
  let right_dom = @kernel.mk_tyapp("fun", right_dom_args)
  let left = @kernel.mk_comb(
    @kernel.mk_var("f", @kernel.fun_ty(left_dom, b)),
    @kernel.mk_var("x", left_dom),
  )
  let right = @kernel.mk_comb(
    @kernel.mk_var("f", @kernel.fun_ty(right_dom, b)),
    @kernel.mk_var("x", right_dom),
  )
  let left_refl = @kernel.refl_checked(st, left).unwrap()
  let right_refl = @kernel.refl_checked(st, right).unwrap()
  let theorem = @kernel.trans_checked(st, left_refl, right_refl).unwrap()
  let before = @kernel.thm_to_string(theorem)
  right_dom_args[0] = @kernel.ind_ty()
  right_dom_args[1] = @kernel.ind_ty()
  assert_eq(@kernel.thm_to_string(theorem), before)
  assert_true(@kernel.thm_is_admissible(st, theorem))
}

///|
test "theorem destructors return detached type arrays" {
  let st = @kernel.empty_kernel_state()
  let ty = @kernel.fun_ty(@kernel.bool_ty(), @kernel.bool_ty())
  let th = @kernel.refl_checked(st, @kernel.mk_var("f", ty)).unwrap()
  let before = @kernel.thm_to_string(th)
  mutate_immutability_term(@kernel.thm_concl(th).unwrap())
  assert_eq(@kernel.thm_to_string(th), before)
  assert_true(@kernel.thm_is_admissible(st, th))

  let predicate = @kernel.mk_var("p", @kernel.fun_ty(ty, @kernel.bool_ty()))
  let assumption = @kernel.assume_checked(
    st,
    @kernel.mk_comb(predicate, @kernel.mk_var("f", ty)),
  ).unwrap()
  let assumption_before = @kernel.thm_to_string(assumption)
  let hyp = @kernel.thm_hyps(assumption).unwrap()[0]
  mutate_immutability_term(hyp)
  assert_eq(@kernel.thm_to_string(assumption), assumption_before)
  assert_true(@kernel.thm_is_admissible(st, assumption))
}

///|
test "kernel signature snapshots cannot mutate state or descendants" {
  let st = @kernel.ks_add_const(
    @kernel.empty_kernel_state(),
    "X",
    @kernel.bool_ty(),
  ).unwrap()
  let child = @kernel.ks_push_scope(st)
  let @kernel.GlobalSig::Sig(scopes) = @kernel.ks_sig(st)
  scopes[0].push(("Y", 12345, @kernel.bool_ty()))
  assert_true(@kernel.ks_lookup_const(st, "Y") is None)
  assert_true(@kernel.ks_lookup_const(child, "Y") is None)
  assert_true(@kernel.ks_lookup_const(st, "X") is Some(_))
  let @kernel.GlobalSig::Sig(choice_scopes) = @kernel.ks_sig(st)
  let (_, _, choice_ty) = choice_scopes[0][0]
  mutate_immutability_type(choice_ty)
  let a = @kernel.mk_tyvar("A")
  assert_true(
    @kernel.ty_eq(
      @kernel.ks_lookup_const(st, "@").unwrap(),
      @kernel.fun_ty(@kernel.fun_ty(a, @kernel.bool_ty()), a),
    ),
  )
}

///|
test "signature types are detached at admission and observation" {
  let args = [@kernel.bool_ty(), @kernel.bool_ty()]
  let ty = @kernel.mk_tyapp("fun", args)
  let st = @kernel.ks_add_const(@kernel.empty_kernel_state(), "f", ty).unwrap()
  args[0] = @kernel.ind_ty()
  mutate_immutability_type(ty)
  let expected = @kernel.fun_ty(@kernel.bool_ty(), @kernel.bool_ty())
  assert_true(
    @kernel.ty_eq(@kernel.ks_lookup_const(st, "f").unwrap(), expected),
  )
  let schema = @kernel.ks_const_schema(st, "f").unwrap()
  mutate_immutability_type(schema)
  mutate_immutability_type(@kernel.ks_lookup_const(st, "f").unwrap())
  let const_term = @kernel.ks_mk_const(st, "f").unwrap()
  mutate_immutability_term(const_term)
  assert_true(
    @kernel.ty_eq(@kernel.ks_lookup_const(st, "f").unwrap(), expected),
  )
}

///|
test "named and De Bruijn conversion detach types in both directions" {
  let ty = @kernel.fun_ty(@kernel.bool_ty(), @kernel.bool_ty())
  let variable = @kernel.mk_var("x", ty)
  let named = @kernel.mk_abs(variable, variable)
  let named_before = @kernel.term_to_string(named)
  let db = @kernel.to_db_term(named).unwrap()
  let db_before = @kernel.db_term_to_string(db)
  mutate_immutability_db_term(db)
  assert_eq(@kernel.term_to_string(named), named_before)
  let db2 = @kernel.to_db_term(named).unwrap()
  mutate_immutability_term(named)
  assert_eq(@kernel.db_term_to_string(db2), db_before)

  let lifted = @kernel.from_db_term(db2).unwrap()
  let lifted_before = @kernel.term_to_string(lifted)
  mutate_immutability_db_term(db2)
  assert_eq(@kernel.term_to_string(lifted), lifted_before)
  let db3 = @kernel.to_db_term(lifted).unwrap()
  let db3_before = @kernel.db_term_to_string(db3)
  mutate_immutability_term(lifted)
  assert_eq(@kernel.db_term_to_string(db3), db3_before)
}

///|
test "De Bruijn substitutions and beta reduction detach their results" {
  let ty = @kernel.fun_ty(@kernel.bool_ty(), @kernel.bool_ty())
  let input = @kernel.to_db_term(@kernel.mk_var("x", ty)).unwrap()
  let before = @kernel.db_term_to_string(input)
  let unchanged = @kernel.db_subst_free_parallel(input, []).unwrap()
  mutate_immutability_db_term(unchanged)
  assert_eq(@kernel.db_term_to_string(input), before)

  let key = @kernel.to_db_term(@kernel.mk_var("y", ty)).unwrap()
  let replaced = @kernel.db_subst_free_parallel(key, [(key, input)]).unwrap()
  mutate_immutability_db_term(replaced)
  assert_eq(@kernel.db_term_to_string(input), before)
  let variable = @kernel.mk_var("x", ty)
  let redex = @kernel.to_db_term(
    @kernel.mk_comb(@kernel.mk_abs(variable, variable), variable),
  ).unwrap()
  let redex_before = @kernel.db_term_to_string(redex)
  let reduced = @kernel.db_beta_reduce_once(redex).unwrap()
  mutate_immutability_db_term(reduced)
  assert_eq(@kernel.db_term_to_string(redex), redex_before)

  let polymorphic = @kernel.to_db_term(
    @kernel.mk_var("z", @kernel.mk_tyvar("A")),
  ).unwrap()
  let replacement_before = @kernel.hol_type_to_string(ty)
  let instantiated = @kernel.db_apply_ty_subst([("A", ty)], polymorphic)
  mutate_immutability_db_term(instantiated)
  assert_eq(@kernel.hol_type_to_string(ty), replacement_before)
  let db_fresh = @kernel.db_apply_ty_subst([("A", ty)], polymorphic)
  let db_fresh_before = @kernel.db_term_to_string(db_fresh)
  mutate_immutability_type(ty)
  assert_eq(@kernel.db_term_to_string(db_fresh), db_fresh_before)
}

///|
test "public signature updates return detached scopes and types" {
  let ty = @kernel.fun_ty(@kernel.bool_ty(), @kernel.bool_ty())
  let original = @kernel.sig_add_const_idempotent_e(
    @kernel.empty_sig(),
    "f",
    ty,
  ).unwrap()
  let original_before = @kernel.ks_lookup_const(
    @kernel.ks_add_const(@kernel.empty_kernel_state(), "f", ty).unwrap(),
    "f",
  ).unwrap()
  let pushed = @kernel.sig_push_scope(original)
  let added = @kernel.sig_add_const_idempotent_e(original, "g", ty).unwrap()
  let idempotent = @kernel.sig_add_const_idempotent_e(original, "f", ty).unwrap()
  for copy in [pushed, added, idempotent] {
    let @kernel.GlobalSig::Sig(scopes) = copy
    let (_, _, exposed_ty) = scopes[0][0]
    mutate_immutability_type(exposed_ty)
    scopes[0].push(("escaped", 42, @kernel.bool_ty()))
  }
  assert_false(@kernel.sig_has_const(original, "escaped"))
  assert_true(
    @kernel.ty_eq(
      @kernel.sig_lookup_const(original, "f").unwrap(),
      original_before,
    ),
  )

  let nested = @kernel.sig_push_scope(original)
  let popped = @kernel.sig_pop_scope_e(nested).unwrap()
  let @kernel.GlobalSig::Sig(scopes) = popped
  scopes[0].push(("escaped", 42, @kernel.bool_ty()))
  assert_false(@kernel.sig_has_const(nested, "escaped"))
}

///|
test "definition inputs outputs and certificate observations cannot mutate state" {
  let args = [@kernel.bool_ty(), @kernel.bool_ty()]
  let ty = @kernel.mk_tyapp("fun", args)
  let variable = @kernel.mk_var("x", ty)
  let rhs = @kernel.mk_abs(variable, variable)
  let decl = @kernel.fun_ty(ty, ty)
  let (state, equation) = @kernel.ks_define_const(
    @kernel.empty_kernel_state(),
    "identity",
    decl,
    rhs,
  ).unwrap()
  let theorem = @kernel.ks_definition_theorem(state, "identity").unwrap()
  let before = @kernel.thm_to_string(theorem)
  args[0] = @kernel.ind_ty()
  mutate_immutability_type(decl)
  mutate_immutability_term(rhs)
  mutate_immutability_term(equation)
  mutate_immutability_term(@kernel.thm_concl(theorem).unwrap())
  let (_, heads, _) = @kernel.ks_extension_cert_at(state, 0).unwrap()
  heads.push("escaped")
  let (_, fresh_heads, _) = @kernel.ks_extension_cert_at(state, 0).unwrap()
  assert_eq(fresh_heads, ["identity"])
  assert_eq(
    @kernel.thm_to_string(
      @kernel.ks_definition_theorem(state, "identity").unwrap(),
    ),
    before,
  )
  assert_true(@kernel.thm_is_admissible(state, theorem))
  assert_true(
    @kernel.ty_eq(
      @kernel.ks_lookup_const(state, "identity").unwrap(),
      @kernel.fun_ty(
        @kernel.fun_ty(@kernel.bool_ty(), @kernel.bool_ty()),
        @kernel.fun_ty(@kernel.bool_ty(), @kernel.bool_ty()),
      ),
    ),
  )
}

///|
test "theorem rebinding rejects descendant shadowing of raw constants" {
  let bool = @kernel.bool_ty()
  let base = @kernel.empty_kernel_state()
  let source = @kernel.ks_add_const(base, "source", bool).unwrap()
  let (defined, theorem) = @kernel.ks_define_const_thm(
    source,
    "alias",
    bool,
    @kernel.mk_const("source", bool),
  ).unwrap()
  let descendant = @kernel.ks_add_const(
    @kernel.ks_push_scope(defined),
    "source",
    bool,
  ).unwrap()
  assert_false(@kernel.thm_is_admissible(descendant, theorem))
  assert_true(@kernel.thm_bind_const_ids(descendant, theorem) is Err(_))
}

///|
/// Public constructors and destructors do not copy, so building a deep term and
/// walking it must stay linear. The isolation of kernel-held data happens once,
/// where a theorem is created or kernel state is observed.
test "deep terms are built and walked in linear time" {
  let a = @kernel.mk_tyvar("A")
  let f = @kernel.mk_var("f", @kernel.fun_ty(a, a))
  let mut term = @kernel.mk_var("x", a)
  for _ in 0..<10000 {
    term = @kernel.mk_comb(f, term)
  }
  let mut depth = 0
  let mut current = term
  while true {
    match @kernel.dest_comb(current) {
      Some((_, arg)) => {
        depth += 1
        current = arg
      }
      None => break
    }
  }
  assert_eq(depth, 10000)
}
