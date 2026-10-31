// A finite-model check of `derivation_sound` (Derivation.lean): every sequent
// the kernel derives is valid.
//
// Theorems are produced by applying the checked primitive rules at random to
// a pool that starts from `ASSUME` and `REFL`. Types are restricted to `bool`
// and functions over it, where Lean's standard model is finite, so `Valid` can
// be decided by enumerating every assignment of the free variables: whenever
// all hypotheses evaluate to true, the conclusion must too.

///|
priv enum SfVal {
  B(Bool)
  F(HolType, (SfVal) -> SfVal)
}

///|
priv struct SfRng {
  mut state : UInt64
}

///|
fn SfRng::below(self : SfRng, n : Int32) -> Int32 {
  self.state = self.state * 6364136223846793005UL + 1442695040888963407UL
  ((self.state >> 33) % n.to_uint64()).to_int()
}

///|
/// The number of values of a type built from bool and `fun`, capped.
fn sf_card(ty : HolType) -> Int32 {
  match ty {
    TyApp("bool", []) => 2
    TyApp("fun", [dom, cod]) => {
      let (d, c) = (sf_card(dom), sf_card(cod).to_int64())
      let mut n = 1L
      for _ in 0..<d {
        n = n * c
        if n > 65536L {
          return 65537
        }
      }
      n.to_int()
    }
    _ => 65537
  }
}

///|
/// Every value of a type built from bool and `fun`.
fn sf_values(ty : HolType) -> Array[SfVal] {
  match ty {
    TyApp("bool", []) => [B(false), B(true)]
    TyApp("fun", [dom, cod]) => {
      let dom_vals = sf_values(dom)
      let cod_vals = sf_values(cod)
      // All functions as tables over the domain.
      let tables : Array[Array[SfVal]] = [[]]
      for _ in dom_vals {
        let next : Array[Array[SfVal]] = []
        for t in tables {
          for v in cod_vals {
            let t2 = t.copy()
            t2.push(v)
            next.push(t2)
          }
        }
        tables.clear()
        tables.push_iter(next.iter())
      }
      tables.map(table => {
        F(dom, x => {
          for i, d in dom_vals {
            if sf_val_eq(d, x) {
              return table[i]
            }
          }
          panic()
        })
      })
    }
    _ => panic()
  }
}

///|
fn sf_val_eq(a : SfVal, b : SfVal) -> Bool {
  match (a, b) {
    (B(x), B(y)) => x == y
    (F(dom, f), F(_, g)) => sf_values(dom).all(v => sf_val_eq(f(v), g(v)))
    _ => false
  }
}

///|
fn sf_eval(t : Term, env : Array[(String, HolType, SfVal)]) -> SfVal {
  match t {
    Var(name, ty) => {
      let mut i = env.length() - 1
      while i >= 0 {
        let (n, vty, v) = env[i]
        if n == name && ty_eq(vty, ty) {
          return v
        }
        i = i - 1
      }
      panic()
    }
    Const("=", TyApp("fun", [dom, _]), _) =>
      F(dom, x => F(dom, y => B(sf_val_eq(x, y))))
    Const(_, _, _) => panic()
    Comb(f, x) =>
      match sf_eval(f, env) {
        F(_, g) => g(sf_eval(x, env))
        B(_) => panic()
      }
    Abs(Var(name, ty), body) =>
      F(ty, v => {
        let env2 = env.copy()
        env2.push((name, ty, v))
        sf_eval(body, env2)
      })
    Abs(_, _) => panic()
  }
}

///|
/// Valid: every assignment of the free variables that makes all hypotheses
/// true makes the conclusion true. `None` when there are too many assignments
/// to enumerate.
fn sf_valid(th : Thm) -> Bool? {
  let hyps = thm_hyps(th).unwrap()
  let concl = thm_concl(th).unwrap()
  let vars : Array[(String, HolType)] = []
  for t in [concl, ..hyps] {
    for v in free_vars(t) {
      if !vars.any(w => w.0 == v.0 && ty_eq(w.1, v.1)) {
        vars.push(v)
      }
    }
  }
  let mut size = 1
  for v in vars {
    size = size * sf_card(v.1)
    if size > 4096 {
      return None
    }
  }
  fn go(i : Int32, env : Array[(String, HolType, SfVal)]) -> Bool {
    if i == vars.length() {
      let holds = t => sf_eval(t, env) is B(true)
      return !hyps.all(holds) || holds(concl)
    }
    let (name, ty) = vars[i]
    sf_values(ty).all(v => {
      let env2 = env.copy()
      env2.push((name, ty, v))
      go(i + 1, env2)
    })
  }

  Some(go(0, []))
}

///|
let sf_bool : HolType = bool_ty()

///|
let sf_types : Array[HolType] = [
  bool_ty(),
  fun_ty(bool_ty(), bool_ty()),
  fun_ty(bool_ty(), fun_ty(bool_ty(), bool_ty())),
]

///|
fn sf_gen_term(rng : SfRng, ty : HolType, depth : Int32) -> Term {
  let choice = if depth <= 0 { 0 } else { rng.below(5) }
  match (choice, ty) {
    (1, TyApp("fun", [dom, cod])) => {
      let name = ["x", "y"][rng.below(2)]
      mk_abs(mk_var(name, dom), sf_gen_term(rng, cod, depth - 1))
    }
    (2, TyApp("bool", [])) => {
      let a = sf_types[rng.below(2)]
      // A binder may capture a same-named variable of another type, which the
      // kernel boundary rejects; fall back to a variable then.
      mk_eq(sf_gen_term(rng, a, depth - 1), sf_gen_term(rng, a, depth - 1)).unwrap_or(
        mk_var("p", sf_bool),
      )
    }
    (3 | 4, _) =>
      // Arguments are boolean, so every type stays small enough to enumerate.
      mk_comb(
        sf_gen_term(rng, fun_ty(sf_bool, ty), depth - 1),
        sf_gen_term(rng, sf_bool, depth - 1),
      )
    _ => {
      let names = ["p", "q", "x", "y", "f"]
      mk_var(names[rng.below(names.length())], ty)
    }
  }
}

///|
fn sf_size(t : Term) -> Int32 {
  match t {
    Var(_, _) | Const(_, _, _) => 1
    Comb(f, x) => 1 + sf_size(f) + sf_size(x)
    Abs(_, body) => 1 + sf_size(body)
  }
}

///|
/// The size of a sequent; derived terms can grow exponentially, so large ones
/// are dropped from the pool.
fn sf_thm_size(th : Thm) -> Int32 {
  thm_hyps(th)
  .unwrap()
  .fold(init=sf_size(thm_concl(th).unwrap()), (n, h) => n + sf_size(h))
}

///|
fn sf_pick(rng : SfRng, pool : Array[Thm]) -> Thm {
  pool[rng.below(pool.length())]
}

///|
/// The free variables of the theorem, for INST and ABS.
fn sf_some_var(rng : SfRng, th : Thm) -> (String, HolType)? {
  let vars = free_vars(thm_concl(th).unwrap())
  if vars.length() == 0 {
    None
  } else {
    Some(vars[rng.below(vars.length())])
  }
}

///|
/// A theorem from the pool whose conclusion matches `want`, if any.
fn sf_find(pool : Array[Thm], want : (Term) -> Bool) -> Thm? {
  for th in pool {
    if want(thm_concl(th).unwrap()) {
      return Some(th)
    }
  }
  None
}

///|
fn sf_step(rng : SfRng, st : KernelState, pool : Array[Thm]) -> (Int32, Thm?) {
  let a = sf_pick(rng, pool)
  let b = sf_pick(rng, pool)
  let rule = rng.below(11)
  let res = match rule {
    0 => assume_checked(st, sf_gen_term(rng, sf_bool, 3))
    1 => refl_checked(st, sf_gen_term(rng, sf_types[rng.below(3)], 3))
    2 =>
      // TRANS needs B.concl = (y = z) for the y of A.concl = (x = y).
      match dest_eq(thm_concl(a).unwrap()) {
        Ok((_, y)) => {
          let next = sf_find(pool, c => {
            match dest_eq(c) {
              Ok((l, _)) =>
                term_alpha_eq(l, y) && !term_alpha_eq(c, thm_concl(a).unwrap())
              Err(_) => false
            }
          })
          match next {
            Some(b2) => trans_checked(st, a, b2)
            None => trans_checked(st, a, b)
          }
        }
        Err(_) => trans_checked(st, a, b)
      }
    3 =>
      // MK_COMB needs a function equation and an argument equation.
      match dest_eq(thm_concl(a).unwrap()) {
        Ok((f, _)) =>
          match type_of(f) {
            Some(TyApp("fun", [dom, _])) => {
              let arg = sf_find(pool, c => {
                match dest_eq(c) {
                  Ok((x, _)) =>
                    type_of(x).map(t => ty_eq(t, dom)).unwrap_or(false)
                  Err(_) => false
                }
              })
              match arg {
                Some(b2) => mk_comb_rule_checked(st, a, b2)
                None => mk_comb_rule_checked(st, a, b)
              }
            }
            _ => mk_comb_rule_checked(st, a, b)
          }
        Err(_) => mk_comb_rule_checked(st, a, b)
      }
    4 =>
      match sf_some_var(rng, a) {
        Some((n, ty)) => abs_rule_checked(st, mk_var(n, ty), a)
        None => abs_rule_checked(st, mk_var("z", sf_bool), a)
      }
    5 =>
      match sf_gen_term(rng, sf_types[rng.below(3)], 3) {
        Comb(Abs(_, _), _) as redex => beta_rule_checked(st, redex)
        _ => {
          let x = mk_var("x", sf_bool)
          beta_rule_checked(
            st,
            mk_comb(
              mk_abs(x, sf_gen_term(rng, sf_bool, 2)),
              sf_gen_term(rng, sf_bool, 2),
            ),
          )
        }
      }
    6 =>
      // EQ_MP needs B.concl = p for A.concl = (p = q).
      match dest_eq(thm_concl(a).unwrap()) {
        Ok((p, _)) if type_of(p).map(is_bool_ty).unwrap_or(false) =>
          match sf_find(pool, c => term_alpha_eq(c, p)) {
            Some(b2) => eq_mp_checked(st, a, b2)
            None =>
              match assume_checked(st, p) {
                Ok(b2) => eq_mp_checked(st, a, b2)
                Err(e) => Err(e)
              }
          }
        _ => eq_mp_checked(st, a, b)
      }
    7 => deduct_antisym_rule_checked(st, a, b)
    8 => add_assum_checked(st, sf_gen_term(rng, sf_bool, 2), a)
    9 =>
      match sf_some_var(rng, a) {
        Some((n, ty)) =>
          inst_checked(st, [(mk_var(n, ty), sf_gen_term(rng, ty, 2))], a)
        None => return (rule, None)
      }
    _ =>
      // Equations from the pool give more chances to TRANS and EQ_MP.
      match dest_eq(thm_concl(a).unwrap()) {
        Ok((l, _)) => refl_checked(st, l)
        Err(_) => assume_checked(st, sf_gen_term(rng, sf_bool, 2))
      }
  }
  (rule, res.to_option())
}

///|
test "derivation_sound: every derived sequent is valid in the finite bool model" {
  let st = empty_kernel_state()
  let rng = SfRng::{ state: 2026UL, }
  let pool : Array[Thm] = []
  for _ in 0..<8 {
    pool.push(assume_checked(st, sf_gen_term(rng, sf_bool, 3)).unwrap())
  }
  let mut derived = 0
  let per_rule = Array::make(11, 0)
  let mut checked = 0
  for _ in 0..<1500 {
    let (rule, out) = sf_step(rng, st, pool)
    match out {
      Some(th) if sf_thm_size(th) <= 80 => {
        per_rule[rule] = per_rule[rule] + 1
        derived = derived + 1
        match sf_valid(th) {
          Some(valid) => {
            assert_true(valid)
            checked = checked + 1
          }
          None => ()
        }
        if pool.length() < 200 {
          pool.push(th)
        } else {
          pool[rng.below(pool.length())] = th
        }
      }
      _ => ()
    }
  }
  // Every rule, including TRANS, MK_COMB and EQ_MP, produced theorems.
  assert_true(per_rule.all(n => n >= 10))
  assert_true(derived > 500)
  assert_true(checked > 300)
}

///|
test "derivation_sound: the finite model rejects an invalid sequent" {
  // A sanity check of the checker itself: {} ⊢ p is not valid.
  let p = mk_var("p", bool_ty())
  let st = empty_kernel_state()
  let th = assume_checked(st, p).unwrap()
  assert_true(sf_valid(th) == Some(true))
  let env = [("p", bool_ty(), B(false))]
  assert_true(sf_eval(p, env) is B(false))
  let q = mk_var("q", bool_ty())
  let pq = mk_eq(p, q).unwrap()
  assert_true(
    sf_eval(pq, [("p", bool_ty(), B(true)), ("q", bool_ty(), B(false))])
    is B(false),
  )
}
