///|
/// Reproducible lineage-cost benchmark for issue #22.
///
/// Toolchain used for the recorded run: moon 0.1.20261012,
/// moonc v0.10.15+943464bfa. Run with:
///
///   moon run src/bench --target native --release
///
/// The first group measures building a state after 0, 100, 300, 500, 2000 and 5000
/// definitions. The second group measures one checked INST call against a
/// theorem admitted at each corresponding lineage length. `Bench::keep` is
/// called inside every timed callback so the optimizer cannot discard the
/// result-producing work.

///|
fn[T, E] expect_ok(result : Result[T, E]) -> T {
  match result {
    Ok(value) => value
    Err(_) => panic()
  }
}

///|
fn definition_name(index : Int32) -> String {
  "lineage_bench_c_" + index.to_string()
}

///|
fn seed_state() -> @kernel.KernelState {
  expect_ok(
    @kernel.ks_add_const(
      @kernel.empty_kernel_state(),
      "lineage_bench_t",
      @kernel.bool_ty(),
    ),
  )
}

///|
fn build_state(definition_count : Int32) -> @kernel.KernelState {
  let mut state = seed_state()
  for index in 0..<definition_count {
    let rhs = @kernel.mk_const("lineage_bench_t", @kernel.bool_ty())
    let (next, _) = expect_ok(
      @kernel.ks_define_const(
        state,
        definition_name(index),
        @kernel.bool_ty(),
        rhs,
      ),
    )
    state = next
  }
  state
}

///|
fn benchmark_term(
  state : @kernel.KernelState,
  definition_count : Int32,
) -> @kernel.Term {
  let name = if definition_count == 0 {
    "lineage_bench_t"
  } else {
    definition_name(definition_count - 1)
  }
  expect_ok(@kernel.ks_mk_const(state, name))
}

///|
fn benchmark_case(
  bencher : @core_bench.Bench,
  definition_count : Int32,
  state : @kernel.KernelState,
) -> Unit {
  let term = benchmark_term(state, definition_count)
  let theorem = expect_ok(@kernel.refl_checked(state, term))
  let suffix = definition_count.to_string()
  bencher.bench(name="inst_after_" + suffix + "_definitions", fn() {
    bencher.keep(@kernel.inst_checked(state, [], theorem))
  })
}

///|
fn main {
  println(
    "kernel_lineage_bench toolchain=moon-0.1.20261012 moonc-0.10.15 target=native release=true",
  )
  let sizes = [0, 100, 300, 500, 2000, 5000]
  let states = sizes.map(fn(size) { (size, build_state(size)) })

  let build_bench = @core_bench.Bench()
  for size in sizes {
    build_bench.bench(name="build_" + size.to_string() + "_definitions", fn() {
      build_bench.keep(build_state(size))
    })
  }
  println("build=" + build_bench.dump_summaries())

  let rule_bench = @core_bench.Bench()
  for item in states {
    let (size, state) = item
    benchmark_case(rule_bench, size, state)
  }
  println("rule=" + rule_bench.dump_summaries())
}
