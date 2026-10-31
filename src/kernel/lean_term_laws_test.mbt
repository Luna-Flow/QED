// Property tests derived from the type and term laws proved in
// formal_verification/QEDFV/HOL (Types.lean, TermLaws.lean, InstLaws.lean,
// TdSubst.lean).
//
// Each test is named after the Lean theorem it follows and checks the same
// equation on the MoonBit operations, over terms drawn from a fixed-seed
// generator. Lean terms are intrinsically typed de Bruijn terms, so the
// equations are compared on `DbTerm`, where syntactic equality is
// alpha-equivalence. Lean's `Ty.var` identity substitution is the empty array
// here, and `θ.comp σ` (first σ, then θ) is `lt_comp(σ, θ)`.

///|
priv struct LtRng {
  mut state : UInt64
}

///|
fn LtRng::new(seed : UInt64) -> LtRng {
  { state: seed * 6364136223846793005UL + 1442695040888963407UL, }
}

///|
fn LtRng::below(self : LtRng, n : Int32) -> Int32 {
  self.state = self.state * 6364136223846793005UL + 1442695040888963407UL
  ((self.state >> 33) % n.to_uint64()).to_int()
}

///|
let lt_tyvar_names : Array[String] = ["A", "B", "C"]

///|
fn lt_gen_ty(rng : LtRng, depth : Int32) -> HolType {
  let k = rng.below(if depth <= 0 { 4 } else { 7 })
  match k {
    0 | 1 | 2 => mk_tyvar(lt_tyvar_names[k])
    3 => bool_ty()
    4 | 5 => fun_ty(lt_gen_ty(rng, depth - 1), lt_gen_ty(rng, depth - 1))
    _ => mk_tyapp("list", [lt_gen_ty(rng, depth - 1)])
  }
}

///|
let lt_binder_names : Array[String] = ["x", "y", "z"]

///|
let lt_free_names : Array[String] = ["u", "v", "x"]

///|
/// The names of the enclosing binders of type `ty` that are not shadowed.
fn lt_visible(env : Array[(String, HolType)], ty : HolType) -> Array[String] {
  let out : Array[String] = []
  let seen : Array[String] = []
  let mut i = env.length() - 1
  while i >= 0 {
    let (name, bty) = env[i]
    if !seen.contains(name) {
      seen.push(name)
      if ty_eq(bty, ty) {
        out.push(name)
      }
    }
    i = i - 1
  }
  out
}

///|
fn lt_gen_leaf(
  rng : LtRng,
  ty : HolType,
  env : Array[(String, HolType)],
) -> Term {
  let visible = lt_visible(env, ty)
  if visible.length() > 0 && rng.below(3) != 0 {
    return mk_var(visible[rng.below(visible.length())], ty)
  }
  let free = lt_free_names.filter(n => !env.any(b => b.0 == n))
  if free.length() > 0 && rng.below(3) != 0 {
    return mk_var(free[rng.below(free.length())], ty)
  }
  mk_const("c", ty)
}

///|
/// A well-typed term of type `ty`. `env` lists the enclosing binders, innermost
/// last. A free variable never reuses the name of an enclosing binder, which is
/// the condition `to_db_term` places on named terms.
fn lt_gen_term(
  rng : LtRng,
  ty : HolType,
  depth : Int32,
  env : Array[(String, HolType)],
) -> Term {
  let choice = if depth <= 0 { 0 } else { rng.below(8) }
  match (choice, ty) {
    (0, _) => lt_gen_leaf(rng, ty, env)
    (1 | 2 | 3, TyApp("fun", [dom, cod])) => {
      let name = lt_binder_names[rng.below(lt_binder_names.length())]
      let env2 = env.copy()
      env2.push((name, dom))
      mk_abs(mk_var(name, dom), lt_gen_term(rng, cod, depth - 1, env2))
    }
    _ => {
      // Prefer an argument type that a visible binder has, so bound
      // variables occur in argument position.
      let a = if env.length() > 0 && rng.below(2) == 0 {
        env[rng.below(env.length())].1
      } else {
        lt_gen_ty(rng, 1)
      }
      mk_comb(
        lt_gen_term(rng, fun_ty(a, ty), depth - 1, env),
        lt_gen_term(rng, a, depth - 1, env),
      )
    }
  }
}

///|
fn lt_gen_closed_ty_subst(rng : LtRng) -> Array[(String, HolType)] {
  let out : Array[(String, HolType)] = []
  for name in lt_tyvar_names {
    if rng.below(3) != 0 {
      out.push((name, lt_gen_ty(rng, 2)))
    }
  }
  out
}

///|
/// First σ, then θ: Lean `θ.comp σ`.
fn lt_comp(
  sigma : Array[(String, HolType)],
  theta : Array[(String, HolType)],
) -> Array[(String, HolType)] {
  let out = sigma.map(kv => (kv.0, type_subst_unsafe(theta, kv.1)))
  for kv in theta {
    if !sigma.any(s => s.0 == kv.0) {
      out.push(kv)
    }
  }
  out
}

///|
fn lt_db(t : Term) -> DbTerm {
  match to_db_term(t) {
    Some(d) => d
    None => panic()
  }
}

///|
fn[T] lt_some(x : T?) -> T {
  match x {
    Some(v) => v
    None => panic()
  }
}

///|
const LT_CASES : Int32 = 300

///|
/// `n` terms, each of a random type, from a fixed seed.
fn lt_terms(seed : UInt64, n : Int32) -> Array[(Term, HolType)] {
  let rng = LtRng::new(seed)
  Array::makei(n, _ => {
    let ty = if rng.below(2) == 0 {
      fun_ty(lt_gen_ty(rng, 1), lt_gen_ty(rng, 1))
    } else {
      lt_gen_ty(rng, 2)
    }
    (lt_gen_term(rng, ty, 4, []), ty)
  })
}

///|
fn lt_has_bound(d : DbTerm) -> Bool {
  match d {
    DbBound(_, _) => true
    DbComb(f, x) => lt_has_bound(f) || lt_has_bound(x)
    DbAbs(_, body) => lt_has_bound(body)
    _ => false
  }
}

///|
test "lean term laws: the generator yields well-typed named terms" {
  let mut bound = 0
  for case in lt_terms(1, LT_CASES) {
    let (t, ty) = case
    assert_true(type_of(t).map(got => ty_eq(got, ty)).unwrap_or(false))
    if lt_has_bound(lt_db(t)) {
      bound = bound + 1
    }
  }
  // Enough terms have binders with bound occurrences to exercise capture.
  assert_true(bound > LT_CASES / 4)
}

///|
test "Ty.subst_id: the empty substitution is the identity" {
  let rng = LtRng::new(2)
  for _ in 0..<LT_CASES {
    let ty = lt_gen_ty(rng, 3)
    assert_true(ty_eq(lt_some(type_subst([], ty)), ty))
    let ids = lt_tyvar_names.map(n => (n, mk_tyvar(n)))
    assert_true(ty_eq(lt_some(type_subst(ids, ty)), ty))
  }
}

///|
test "Ty.subst_comp: substituting twice is substituting the composite" {
  let rng = LtRng::new(3)
  for _ in 0..<LT_CASES {
    let ty = lt_gen_ty(rng, 3)
    let sigma = lt_gen_closed_ty_subst(rng)
    let theta = lt_gen_closed_ty_subst(rng)
    let twice = lt_some(type_subst(theta, lt_some(type_subst(sigma, ty))))
    let once = lt_some(type_subst(lt_comp(sigma, theta), ty))
    assert_true(ty_eq(twice, once))
  }
}

///|
test "Ty.subst_congr: only the type variables of the type matter" {
  let rng = LtRng::new(4)
  for _ in 0..<LT_CASES {
    let ty = lt_gen_ty(rng, 3)
    let theta = lt_gen_closed_ty_subst(rng)
    let vars = tyvars(ty)
    // Change θ arbitrarily outside the variables of ty.
    let other = theta.filter(kv => vars.contains(kv.0))
    for name in lt_tyvar_names {
      if !vars.contains(name) {
        other.push((name, lt_gen_ty(rng, 2)))
      }
    }
    assert_true(
      ty_eq(lt_some(type_subst(theta, ty)), lt_some(type_subst(other, ty))),
    )
  }
}

///|
test "Ty.IsInst.refl: every type is an instance of itself" {
  let rng = LtRng::new(5)
  for _ in 0..<LT_CASES {
    let ty = lt_gen_ty(rng, 3)
    assert_true(ty_is_instance_of(ty, ty))
  }
}

///|
test "Ty.IsInst.inst: instances stay instances under substitution" {
  let rng = LtRng::new(6)
  for _ in 0..<LT_CASES {
    let schema = lt_gen_ty(rng, 3)
    let sigma = lt_gen_closed_ty_subst(rng)
    let theta = lt_gen_closed_ty_subst(rng)
    let inst = lt_some(type_subst(sigma, schema))
    assert_true(ty_is_instance_of(inst, schema))
    assert_true(ty_is_instance_of(lt_some(type_subst(theta, inst)), schema))
  }
}

///|
test "Ty.IsInst.inst: a non-instance is rejected" {
  let a = mk_tyvar("A")
  let b = mk_tyvar("B")
  // A -> A has no instance bool -> ind.
  assert_false(ty_is_instance_of(fun_ty(bool_ty(), ind_ty()), fun_ty(a, a)))
  // A is not an instance of A -> B.
  assert_false(ty_is_instance_of(a, fun_ty(a, b)))
  assert_true(ty_is_instance_of(fun_ty(b, b), fun_ty(a, a)))
}

///|
test "Term.erase_inj: alpha-equivalence is equality of de Bruijn terms" {
  let terms = lt_terms(7, LT_CASES)
  for i, case in terms {
    let t = case.0
    let d = lt_db(t)
    // The named form of a de Bruijn term reads back to the same term.
    let named = lt_some(from_db_term(d))
    assert_true(db_term_eq(lt_db(named), d))
    assert_true(term_alpha_eq(named, t))
    let u = terms[(i + 1) % terms.length()].0
    assert_eq(term_alpha_eq(t, u), db_term_eq(d, lt_db(u)))
  }
}

///|
test "Term.erase_instType: named type instantiation agrees with de Bruijn" {
  let rng = LtRng::new(8)
  for case in lt_terms(8, LT_CASES) {
    let t = case.0
    let theta = lt_gen_closed_ty_subst(rng)
    let named = lt_some(term_apply_ty_subst(theta, t))
    assert_true(db_term_eq(lt_db(named), db_apply_ty_subst(theta, lt_db(t))))
  }
}

///|
test "Term.instType_var: the empty type substitution is the identity" {
  for case in lt_terms(9, LT_CASES) {
    let d = lt_db(case.0)
    assert_true(db_term_eq(db_apply_ty_subst([], d), d))
  }
}

///|
test "Term.instType_instType: instantiating twice is instantiating the composite" {
  let rng = LtRng::new(10)
  for case in lt_terms(10, LT_CASES) {
    let d = lt_db(case.0)
    let sigma = lt_gen_closed_ty_subst(rng)
    let theta = lt_gen_closed_ty_subst(rng)
    assert_true(
      db_term_eq(
        db_apply_ty_subst(theta, db_apply_ty_subst(sigma, d)),
        db_apply_ty_subst(lt_comp(sigma, theta), d),
      ),
    )
  }
}

///|
test "Term.instType_congr: only the type variables of the term matter" {
  let rng = LtRng::new(11)
  for case in lt_terms(11, LT_CASES) {
    let t = case.0
    let vars = term_tyvars(t)
    let theta = lt_gen_closed_ty_subst(rng)
    let other = theta.filter(kv => vars.contains(kv.0))
    for name in lt_tyvar_names {
      if !vars.contains(name) {
        other.push((name, lt_gen_ty(rng, 2)))
      }
    }
    let d = lt_db(t)
    assert_true(
      db_term_eq(db_apply_ty_subst(theta, d), db_apply_ty_subst(other, d)),
    )
  }
}

///|
test "lean term laws: type instantiation instantiates the type" {
  // Lean `Term.instType` maps `Term S Γ a` to `Term S (Γ.map θ) (a.subst θ)`.
  let rng = LtRng::new(12)
  for case in lt_terms(12, LT_CASES) {
    let (t, ty) = case
    let theta = lt_gen_closed_ty_subst(rng)
    let got = lt_some(db_type_of(db_apply_ty_subst(theta, lt_db(t))))
    assert_true(ty_eq(got, lt_some(type_subst(theta, ty))))
  }
}

///|
/// A substitution for the free variables of `t` with well-typed values.
fn lt_gen_term_subst(rng : LtRng, t : Term) -> Array[(DbTerm, DbTerm)] {
  let out : Array[(DbTerm, DbTerm)] = []
  for v in free_vars(t) {
    if rng.below(3) != 0 {
      out.push((lt_db(mk_var(v.0, v.1)), lt_db(lt_gen_term(rng, v.1, 3, []))))
    }
  }
  out
}

///|
fn lt_subst(t : DbTerm, s : Array[(DbTerm, DbTerm)]) -> DbTerm {
  lt_some(db_subst_free_parallel(t, s))
}

///|
test "Term.substitute_var: substituting variables by themselves is the identity" {
  for case in lt_terms(13, LT_CASES) {
    let t = case.0
    let d = lt_db(t)
    assert_true(db_term_eq(lt_subst(d, []), d))
    let ids = free_vars(t).map(v => {
      (lt_db(mk_var(v.0, v.1)), lt_db(mk_var(v.0, v.1)))
    })
    assert_true(db_term_eq(lt_subst(d, ids), d))
  }
}

///|
test "lean term laws: substitution preserves the type" {
  let rng = LtRng::new(14)
  for case in lt_terms(14, LT_CASES) {
    let (t, ty) = case
    let out = lt_subst(lt_db(t), lt_gen_term_subst(rng, t))
    assert_true(ty_eq(lt_some(db_type_of(out)), ty))
  }
}

///|
test "Term.substitute_substitute: substituting twice is substituting the composite" {
  let rng = LtRng::new(15)
  for case in lt_terms(15, LT_CASES) {
    let t = case.0
    let sigma = lt_gen_term_subst(rng, t)
    // τ acts on the free variables after σ.
    let mid = lt_some(from_db_term(lt_subst(lt_db(t), sigma)))
    let tau = lt_gen_term_subst(rng, mid)
    let composite = sigma.map(kv => (kv.0, lt_subst(kv.1, tau)))
    for kv in tau {
      if !sigma.any(s => db_term_eq(s.0, kv.0)) {
        composite.push(kv)
      }
    }
    assert_true(
      db_term_eq(
        lt_subst(lt_subst(lt_db(t), sigma), tau),
        lt_subst(lt_db(t), composite),
      ),
    )
  }
}

///|
test "Term.substitute_instType: type instantiation commutes with substitution" {
  let rng = LtRng::new(16)
  let mut checked = 0
  for case in lt_terms(16, LT_CASES) {
    let t = case.0
    let sigma = lt_gen_term_subst(rng, t)
    let theta = lt_gen_closed_ty_subst(rng)
    let lhs = db_apply_ty_subst(theta, lt_subst(lt_db(t), sigma))
    let sigma_theta = sigma.map(kv => {
      (db_apply_ty_subst(theta, kv.0), db_apply_ty_subst(theta, kv.1))
    })
    // Distinct variables may collapse under θ; Lean's positions never do, so
    // only compare when θ keeps the substituted variables apart.
    let keys = sigma_theta.map(kv => kv.0)
    let apart = keys.length() ==
      keys
      .mapi((i, k) => keys[:i].iter().all(j => !db_term_eq(j, k)))
      .filter(b => b)
      .length()
    let others = free_vars(t)
      .map(v => lt_db(mk_var(v.0, v.1)))
      .filter(v => !sigma.any(kv => db_term_eq(kv.0, v)))
      .map(v => db_apply_ty_subst(theta, v))
    let no_clash = others.all(o => !keys.any(k => db_term_eq(k, o)))
    if apart && no_clash {
      let rhs = lt_subst(db_apply_ty_subst(theta, lt_db(t)), sigma_theta)
      assert_true(db_term_eq(lhs, rhs))
      checked = checked + 1
    }
  }
  assert_true(checked > LT_CASES / 2)
}

///|
test "Term.instType_single: type instantiation commutes with beta reduction" {
  let rng = LtRng::new(17)
  let mut checked = 0
  for _ in 0..<LT_CASES {
    let a = lt_gen_ty(rng, 2)
    let b = lt_gen_ty(rng, 2)
    let body = lt_gen_term(rng, b, 4, [("x", a)])
    let arg = lt_gen_term(rng, a, 3, [])
    let redex = lt_db(mk_comb(mk_abs(mk_var("x", a), body), arg))
    let theta = lt_gen_closed_ty_subst(rng)
    match db_beta_reduce_once(redex) {
      Some(reduced) => {
        let lhs = db_apply_ty_subst(theta, reduced)
        let rhs = lt_some(db_beta_reduce_once(db_apply_ty_subst(theta, redex)))
        assert_true(db_term_eq(lhs, rhs))
        checked = checked + 1
      }
      None => ()
    }
  }
  assert_true(checked > LT_CASES / 2)
}
