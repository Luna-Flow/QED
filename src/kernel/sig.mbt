///|
/// Minimal global signature registry for kernel-level constant identities.
pub enum GlobalSig {
  Sig(Array[(String, HolType)])
}

///|
pub fn empty_sig() -> GlobalSig {
  Sig([])
}

///|
pub fn sig_has_const(sig : GlobalSig, name : String) -> Bool {
  match sig {
    Sig(entries) =>
      entries.any(fn(entry) {
        let (n, _) = entry
        n == name
      })
  }
}

///|
pub fn sig_lookup_const(sig : GlobalSig, name : String) -> HolType? {
  match sig {
    Sig(entries) => {
      for entry in entries {
        let (n, ty) = entry
        if n == name {
          return Some(ty)
        }
      }
      None
    }
  }
}

///|
pub fn sig_add_const(
  sig : GlobalSig,
  name : String,
  ty : HolType,
) -> GlobalSig? {
  if sig_has_const(sig, name) {
    None
  } else {
    match sig {
      Sig(entries) => {
        let out = entries.copy()
        out.push((name, ty))
        Some(Sig(out))
      }
    }
  }
}
