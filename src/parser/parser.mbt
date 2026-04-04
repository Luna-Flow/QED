///|
pub enum SynTerm {
  Name(String)
  Prefix(String, SynTerm)
  App(SynTerm, SynTerm)
  Infix(String, SynTerm, SynTerm)
}

///|
pub struct SynGoal {
  hyps : Array[SynTerm]
  concl : SynTerm
}

///|
pub struct ParseEnv {
  locals : Array[(String, HolType)]
}

///|
pub struct NormalizedInput {
  text : String
  raw_offsets : Array[Int]
  raw_length : Int
}

///|
pub enum SynTacticStep {
  Intro(String)
  Exact(String)
  Apply(String)
  Assumption
  Split
  Left
  Right
}

///|
pub struct SynTheoremScript {
  name : String
  goal : SynGoal
  goal_src : String
  steps : Array[SynTacticStep]
}

///|
pub enum ParseErrorCode {
  UnexpectedToken
  UnexpectedEof
  MissingTurnstile
  NonAssocChain
  UnknownOperator
  EmptyConclusion
  EmptyHypothesis
}

///|
pub struct ParseError {
  code : ParseErrorCode
  offset : Int
  detail : String
}

///|
pub enum ParseBridgeError {
  Parse(ParseError)
  Sig(SigError)
  Logic(LogicError)
  Elab(ElabError)
}

///|
pub struct ResolvedGoal {
  hyps : Array[RTerm]
  concl : RTerm
}

///|
priv enum TokKind {
  TkName(String)
  TkLParen
  TkRParen
  TkLBrace
  TkRBrace
  TkComma
  TkSemi
  TkColon
  TkAssign
  TkArrow
  TkTurnstile
  TkAnd
  TkOr
  TkNot
  TkEq
  TkEnd
}

///|
priv struct Token {
  kind : TokKind
  offset : Int
}

///|
priv enum Assoc {
  LeftAssoc
  RightAssoc
  NonAssoc
}

///|
fn mk_parse_error(
  code : ParseErrorCode,
  offset : Int,
  detail : String,
) -> ParseError {
  ParseError::{ code, offset, detail }
}

///|
pub fn empty_parse_env() -> ParseEnv {
  ParseEnv::{ locals: [] }
}

///|
pub fn parse_env_local_count(env : ParseEnv) -> Int {
  env.locals.length()
}

///|
pub fn parse_env_local_at(env : ParseEnv, idx : Int) -> (String, HolType)? {
  if idx < 0 || idx >= env.locals.length() {
    None
  } else {
    Some(env.locals[idx])
  }
}

///|
fn parse_env_lookup(env : ParseEnv, name : String) -> HolType? {
  let mut i = env.locals.length()
  while i > 0 {
    i = i - 1
    let (n, ty) = env.locals[i]
    if n == name {
      return Some(ty)
    }
  }
  None
}

///|
pub fn normalized_input_raw_offset_at(
  input : NormalizedInput,
  idx : Int,
) -> Int {
  if idx < 0 {
    0
  } else if idx >= input.raw_offsets.length() {
    input.raw_length
  } else {
    input.raw_offsets[idx]
  }
}

///|
fn push_normalized_char(
  chars : Array[Char],
  raw_offsets : Array[Int],
  c : Char,
  raw_off : Int,
) -> Unit {
  chars.push(c)
  raw_offsets.push(raw_off)
}

///|
pub fn normalize_parser_input(
  src : String,
) -> Result[NormalizedInput, ParseError] {
  let out_chars : Array[Char] = []
  let raw_offsets : Array[Int] = []
  loop (src.view(), 0, false, 0) {
    ([], off, _, _) =>
      Ok(NormalizedInput::{
        text: String::from_iter(out_chars.iter()),
        raw_offsets,
        raw_length: off,
      })
    ([c, .. rest], off, pending_space, space_off) =>
      if c.is_ascii_whitespace() {
        if out_chars.length() == 0 {
          continue (rest, off + 1, false, 0)
        } else if pending_space {
          continue (rest, off + 1, true, space_off)
        } else {
          continue (rest, off + 1, true, off)
        }
      } else {
        if pending_space && out_chars.length() > 0 {
          push_normalized_char(out_chars, raw_offsets, ' ', space_off)
        }
        if c == '\\' {
          match rest {
            [r, ..] if is_name_start(r) => {
              let (esc_name, rest2, n) = read_name(rest)
              if esc_name == "and" {
                push_normalized_char(out_chars, raw_offsets, '∧', off)
                continue (rest2, off + n + 1, false, 0)
              } else if esc_name == "or" {
                push_normalized_char(out_chars, raw_offsets, '∨', off)
                continue (rest2, off + n + 1, false, 0)
              } else if esc_name == "not" {
                push_normalized_char(out_chars, raw_offsets, '¬', off)
                continue (rest2, off + n + 1, false, 0)
              } else if esc_name == "imp" {
                push_normalized_char(out_chars, raw_offsets, '-', off)
                push_normalized_char(out_chars, raw_offsets, '>', off)
                continue (rest2, off + n + 1, false, 0)
              } else {
                Err(
                  mk_parse_error(
                    UnknownOperator,
                    off,
                    "unknown escaped operator `\\" + esc_name + "`",
                  ),
                )
              }
            }
            _ =>
              Err(
                mk_parse_error(
                  UnknownOperator,
                  off,
                  "unknown operator near `\\`",
                ),
              )
          }
        } else if c == '|' {
          match rest {
            ['-', .. rest2] => {
              push_normalized_char(out_chars, raw_offsets, '⊢', off)
              continue (rest2, off + 2, false, 0)
            }
            _ => {
              push_normalized_char(out_chars, raw_offsets, c, off)
              continue (rest, off + 1, false, 0)
            }
          }
        } else {
          push_normalized_char(out_chars, raw_offsets, c, off)
          continue (rest, off + 1, false, 0)
        }
      }
  }
}

///|
fn map_parse_error_offset(
  input : NormalizedInput,
  err : ParseError,
) -> ParseError {
  ParseError::{
    code: err.code,
    offset: normalized_input_raw_offset_at(input, err.offset),
    detail: err.detail,
  }
}

///|
fn token_label(kind : TokKind) -> String {
  match kind {
    TkName(n) => n
    TkLParen => "("
    TkRParen => ")"
    TkLBrace => "{"
    TkRBrace => "}"
    TkComma => ","
    TkSemi => ";"
    TkColon => ":"
    TkAssign => ":="
    TkArrow => "->"
    TkTurnstile => "⊢"
    TkAnd => "∧"
    TkOr => "∨"
    TkNot => "¬"
    TkEq => "="
    TkEnd => "<eof>"
  }
}

///|
fn is_name_start(c : Char) -> Bool {
  c == '_' || c.is_ascii_alphabetic()
}

///|
fn is_name_continue(c : Char) -> Bool {
  is_name_start(c) || c.is_ascii_digit()
}

///|
fn is_operator_like(c : Char) -> Bool {
  c == '+' ||
  c == '-' ||
  c == '*' ||
  c == '/' ||
  c == '<' ||
  c == '>' ||
  c == '!' ||
  c == '&' ||
  c == '^' ||
  c == '%' ||
  c == ':' ||
  c == '|' ||
  c == '\\' ||
  c == ';' ||
  c == '¬'
}

///|
fn read_name(view : StringView) -> (String, StringView, Int) {
  let chars : Array[Char] = []
  loop (view, 0) {
    ([c, .. rest], n) if is_name_continue(c) => {
      chars.push(c)
      continue (rest, n + 1)
    }
    (rest, n) => (String::from_iter(chars.iter()), rest, n)
  }
}

///|
fn lex_tokens(src : String) -> Result[Array[Token], ParseError] {
  let out : Array[Token] = []
  loop (src.view(), 0) {
    ([], off) => {
      out.push(Token::{ kind: TkEnd, offset: off })
      Ok(out)
    }
    ([c, .. rest], off) =>
      if c.is_ascii_whitespace() {
        continue (rest, off + 1)
      } else if c == '(' {
        out.push(Token::{ kind: TkLParen, offset: off })
        continue (rest, off + 1)
      } else if c == ')' {
        out.push(Token::{ kind: TkRParen, offset: off })
        continue (rest, off + 1)
      } else if c == '{' {
        out.push(Token::{ kind: TkLBrace, offset: off })
        continue (rest, off + 1)
      } else if c == '}' {
        out.push(Token::{ kind: TkRBrace, offset: off })
        continue (rest, off + 1)
      } else if c == '∧' {
        out.push(Token::{ kind: TkAnd, offset: off })
        continue (rest, off + 1)
      } else if c == '∨' {
        out.push(Token::{ kind: TkOr, offset: off })
        continue (rest, off + 1)
      } else if c == ',' {
        out.push(Token::{ kind: TkComma, offset: off })
        continue (rest, off + 1)
      } else if c == ';' {
        out.push(Token::{ kind: TkSemi, offset: off })
        continue (rest, off + 1)
      } else if c == ':' {
        match rest {
          ['=', .. rest2] => {
            out.push(Token::{ kind: TkAssign, offset: off })
            continue (rest2, off + 2)
          }
          _ => {
            out.push(Token::{ kind: TkColon, offset: off })
            continue (rest, off + 1)
          }
        }
      } else if c == '=' {
        out.push(Token::{ kind: TkEq, offset: off })
        continue (rest, off + 1)
      } else if c == '-' {
        match rest {
          ['>', .. rest2] => {
            out.push(Token::{ kind: TkArrow, offset: off })
            continue (rest2, off + 2)
          }
          _ =>
            Err(
              mk_parse_error(UnknownOperator, off, "unknown operator near `-`"),
            )
        }
      } else if c == '|' {
        match rest {
          ['-', .. rest2] => {
            out.push(Token::{ kind: TkTurnstile, offset: off })
            continue (rest2, off + 2)
          }
          _ =>
            Err(
              mk_parse_error(UnknownOperator, off, "unknown operator near `|`"),
            )
        }
      } else if c == '⊢' {
        out.push(Token::{ kind: TkTurnstile, offset: off })
        continue (rest, off + 1)
      } else if c == '¬' {
        out.push(Token::{ kind: TkNot, offset: off })
        continue (rest, off + 1)
      } else if c == '\\' {
        match rest {
          [r, ..] if is_name_start(r) => {
            let (esc_name, rest2, n) = read_name(rest)
            if esc_name == "and" {
              out.push(Token::{ kind: TkAnd, offset: off })
              continue (rest2, off + n + 1)
            } else if esc_name == "or" {
              out.push(Token::{ kind: TkOr, offset: off })
              continue (rest2, off + n + 1)
            } else if esc_name == "not" {
              out.push(Token::{ kind: TkNot, offset: off })
              continue (rest2, off + n + 1)
            } else if esc_name == "imp" {
              out.push(Token::{ kind: TkArrow, offset: off })
              continue (rest2, off + n + 1)
            } else {
              Err(
                mk_parse_error(
                  UnknownOperator,
                  off,
                  "unknown escaped operator `\\" + esc_name + "`",
                ),
              )
            }
          }
          _ =>
            Err(
              mk_parse_error(UnknownOperator, off, "unknown operator near `\\`"),
            )
        }
      } else if is_name_start(c) {
        let (name, rest2, n) = read_name([c, ..rest])
        out.push(Token::{ kind: TkName(name), offset: off })
        continue (rest2, off + n)
      } else if is_operator_like(c) {
        Err(
          mk_parse_error(
            UnknownOperator,
            off,
            "unknown operator near `" + c.to_string() + "`",
          ),
        )
      } else {
        Err(
          mk_parse_error(
            UnexpectedToken,
            off,
            "unexpected character `" + c.to_string() + "`",
          ),
        )
      }
  }
}

///|
fn token_at(tokens : Array[Token], idx : Int) -> Token {
  if idx < 0 || idx >= tokens.length() {
    Token::{ kind: TkEnd, offset: tokens.length() }
  } else {
    tokens[idx]
  }
}

///|
fn is_atom_start(kind : TokKind) -> Bool {
  match kind {
    TkName(_) => true
    TkLParen => true
    _ => false
  }
}

///|
fn name_is_tyvar(name : String) -> Bool {
  match name.view() {
    [c, ..] => c.is_ascii_uppercase() || c == '_'
    _ => false
  }
}

///|
fn type_name_to_hol(name : String) -> HolType {
  if name == "bool" {
    bool_ty()
  } else if name == "ind" {
    ind_ty()
  } else if name_is_tyvar(name) {
    mk_tyvar(name)
  } else {
    mk_tyapp(name, [])
  }
}

///|
fn parse_type_atom(
  tokens : Array[Token],
  idx : Int,
) -> Result[(HolType, Int), ParseError] {
  let tok = token_at(tokens, idx)
  match tok.kind {
    TkName(name) => Ok((type_name_to_hol(name), idx + 1))
    TkLParen =>
      match parse_type(tokens, idx + 1) {
        Ok((ty, j)) =>
          match token_at(tokens, j).kind {
            TkRParen => Ok((ty, j + 1))
            TkEnd =>
              Err(
                mk_parse_error(
                  UnexpectedEof,
                  token_at(tokens, j).offset,
                  "missing right parenthesis in type",
                ),
              )
            _ =>
              Err(
                mk_parse_error(
                  UnexpectedToken,
                  token_at(tokens, j).offset,
                  "expected `)` in type",
                ),
              )
          }
        Err(e) => Err(e)
      }
    TkEnd =>
      Err(mk_parse_error(UnexpectedEof, tok.offset, "unexpected eof in type"))
    _ =>
      Err(
        mk_parse_error(
          UnexpectedToken,
          tok.offset,
          "expected type atom, got `" + token_label(tok.kind) + "`",
        ),
      )
  }
}

///|
fn parse_type(
  tokens : Array[Token],
  idx : Int,
) -> Result[(HolType, Int), ParseError] {
  match parse_type_atom(tokens, idx) {
    Ok((lhs, j)) =>
      match token_at(tokens, j).kind {
        TkArrow =>
          match parse_type(tokens, j + 1) {
            Ok((rhs, k)) => Ok((fun_ty(lhs, rhs), k))
            Err(e) => Err(e)
          }
        _ => Ok((lhs, j))
      }
    Err(e) => Err(e)
  }
}

///|
fn op_fixity(op : String) -> (Int, Assoc)? {
  if op == "=" {
    Some((10, NonAssoc))
  } else if op == "->" {
    Some((15, RightAssoc))
  } else if op == "∨" {
    Some((20, LeftAssoc))
  } else if op == "∧" {
    Some((30, LeftAssoc))
  } else {
    None
  }
}

///|
fn resolve_once(
  terms : Array[SynTerm],
  ops : Array[(String, Int)],
) -> Result[Unit, ParseError] {
  let op = match ops.pop() {
    Some(v) => v
    None =>
      return Err(
        mk_parse_error(
          UnexpectedEof,
          0,
          "internal parser operator stack underflow",
        ),
      )
  }
  let (name, off) = op
  let rhs = match terms.pop() {
    Some(v) => v
    None =>
      return Err(
        mk_parse_error(UnexpectedEof, off, "missing rhs during infix reduction"),
      )
  }
  let lhs = match terms.pop() {
    Some(v) => v
    None =>
      return Err(
        mk_parse_error(UnexpectedEof, off, "missing lhs during infix reduction"),
      )
  }
  terms.push(Infix(name, lhs, rhs))
  Ok(())
}

///|
fn should_reduce(
  top_op : String,
  new_op : String,
  new_off : Int,
) -> Result[Bool, ParseError] {
  let (top_prec, top_assoc) = match op_fixity(top_op) {
    Some(v) => v
    None =>
      return Err(
        mk_parse_error(
          UnknownOperator,
          new_off,
          "unknown operator `" + top_op + "`",
        ),
      )
  }
  let (new_prec, new_assoc) = match op_fixity(new_op) {
    Some(v) => v
    None =>
      return Err(
        mk_parse_error(
          UnknownOperator,
          new_off,
          "unknown operator `" + new_op + "`",
        ),
      )
  }
  if top_prec > new_prec {
    return Ok(true)
  }
  if top_prec < new_prec {
    return Ok(false)
  }
  match (top_assoc, new_assoc) {
    (LeftAssoc, LeftAssoc) => Ok(true)
    (RightAssoc, RightAssoc) => Ok(false)
    (NonAssoc, _) =>
      Err(mk_parse_error(NonAssocChain, new_off, "non-associative chain"))
    (_, NonAssoc) =>
      Err(mk_parse_error(NonAssocChain, new_off, "non-associative chain"))
    _ => Ok(true)
  }
}

///|
fn resolve_infix_chain(
  lhs : SynTerm,
  chain : Array[(String, SynTerm, Int)],
) -> Result[SynTerm, ParseError] {
  if chain.length() == 0 {
    return Ok(lhs)
  }
  let terms : Array[SynTerm] = [lhs]
  let ops : Array[(String, Int)] = []
  for item in chain {
    let (op_name, rhs, off) = item
    while ops.length() > 0 {
      let (top_name, _) = ops[ops.length() - 1]
      match should_reduce(top_name, op_name, off) {
        Ok(true) =>
          match resolve_once(terms, ops) {
            Ok(_) => ()
            Err(e) => return Err(e)
          }
        Ok(false) => break
        Err(e) => return Err(e)
      }
    }
    ops.push((op_name, off))
    terms.push(rhs)
  }
  while ops.length() > 0 {
    match resolve_once(terms, ops) {
      Ok(_) => ()
      Err(e) => return Err(e)
    }
  }
  if terms.length() != 1 {
    Err(
      mk_parse_error(
        UnexpectedEof,
        0,
        "internal parser reduction did not finish with one term",
      ),
    )
  } else {
    Ok(terms[0])
  }
}

///|
fn parse_atom(
  tokens : Array[Token],
  idx : Int,
) -> Result[(SynTerm, Int), ParseError] {
  let tok = token_at(tokens, idx)
  match tok.kind {
    TkName(name) => Ok((Name(name), idx + 1))
    TkLParen =>
      match parse_infix(tokens, idx + 1) {
        Ok((inside, j)) =>
          match token_at(tokens, j).kind {
            TkRParen => Ok((inside, j + 1))
            TkEnd =>
              Err(
                mk_parse_error(
                  UnexpectedEof,
                  token_at(tokens, j).offset,
                  "missing right parenthesis",
                ),
              )
            _ =>
              Err(
                mk_parse_error(
                  UnexpectedToken,
                  token_at(tokens, j).offset,
                  "expected `)`",
                ),
              )
          }
        Err(e) => Err(e)
      }
    TkEnd =>
      Err(
        mk_parse_error(
          UnexpectedEof,
          tok.offset,
          "unexpected end while parsing atom",
        ),
      )
    _ =>
      Err(
        mk_parse_error(
          UnexpectedToken,
          tok.offset,
          "expected atom, got `" + token_label(tok.kind) + "`",
        ),
      )
  }
}

///|
fn parse_app(
  tokens : Array[Token],
  idx : Int,
) -> Result[(SynTerm, Int), ParseError] {
  match parse_atom(tokens, idx) {
    Ok((head, j0)) => {
      let mut out = head
      let mut j = j0
      while is_atom_start(token_at(tokens, j).kind) {
        match parse_atom(tokens, j) {
          Ok((arg, j2)) => {
            out = App(out, arg)
            j = j2
          }
          Err(e) => return Err(e)
        }
      }
      Ok((out, j))
    }
    Err(e) => Err(e)
  }
}

///|
fn parse_prefix(
  tokens : Array[Token],
  idx : Int,
) -> Result[(SynTerm, Int), ParseError] {
  let tok = token_at(tokens, idx)
  match tok.kind {
    TkNot =>
      match parse_prefix(tokens, idx + 1) {
        Ok((inner, j)) => Ok((Prefix("¬", inner), j))
        Err(e) => Err(e)
      }
    _ => parse_app(tokens, idx)
  }
}

///|
fn parse_infix(
  tokens : Array[Token],
  idx : Int,
) -> Result[(SynTerm, Int), ParseError] {
  match parse_prefix(tokens, idx) {
    Ok((lhs0, j0)) => {
      let chain : Array[(String, SynTerm, Int)] = []
      let mut j = j0
      while true {
        let tok = token_at(tokens, j)
        match tok.kind {
          TkAnd =>
            match parse_prefix(tokens, j + 1) {
              Ok((rhs, j2)) => {
                chain.push(("∧", rhs, tok.offset))
                j = j2
              }
              Err(e) => return Err(e)
            }
          TkOr =>
            match parse_prefix(tokens, j + 1) {
              Ok((rhs, j2)) => {
                chain.push(("∨", rhs, tok.offset))
                j = j2
              }
              Err(e) => return Err(e)
            }
          TkArrow =>
            match parse_prefix(tokens, j + 1) {
              Ok((rhs, j2)) => {
                chain.push(("->", rhs, tok.offset))
                j = j2
              }
              Err(e) => return Err(e)
            }
          TkEq =>
            match parse_prefix(tokens, j + 1) {
              Ok((rhs, j2)) => {
                chain.push(("=", rhs, tok.offset))
                j = j2
              }
              Err(e) => return Err(e)
            }
          _ => break
        }
      }
      match resolve_infix_chain(lhs0, chain) {
        Ok(out) => Ok((out, j))
        Err(e) => Err(e)
      }
    }
    Err(e) => Err(e)
  }
}

///|
fn parse_term_tokens(tokens : Array[Token]) -> Result[SynTerm, ParseError] {
  match parse_infix(tokens, 0) {
    Ok((term, idx)) =>
      match token_at(tokens, idx).kind {
        TkEnd => Ok(term)
        _ =>
          Err(
            mk_parse_error(
              UnexpectedToken,
              token_at(tokens, idx).offset,
              "unexpected trailing token `" +
              token_label(token_at(tokens, idx).kind) +
              "`",
            ),
          )
      }
    Err(e) => Err(e)
  }
}

///|
fn parse_goal_tokens(tokens : Array[Token]) -> Result[SynGoal, ParseError] {
  let n = tokens.length()
  let end_idx = n - 1
  let mut depth = 0
  let mut split_idx : Int? = None
  let mut i = 0
  while i < end_idx {
    let tok = tokens[i]
    match tok.kind {
      TkLParen => depth = depth + 1
      TkRParen => {
        depth = depth - 1
        if depth < 0 {
          return Err(
            mk_parse_error(UnexpectedToken, tok.offset, "unmatched `)`"),
          )
        }
      }
      TkTurnstile =>
        if depth == 0 {
          match split_idx {
            Some(_) =>
              return Err(
                mk_parse_error(
                  UnexpectedToken,
                  tok.offset,
                  "multiple top-level turnstiles (`|-` or `⊢`)",
                ),
              )
            None => split_idx = Some(i)
          }
        }
      _ => ()
    }
    i = i + 1
  }
  let k = match split_idx {
    Some(v) => v
    None =>
      return Err(
        mk_parse_error(
          MissingTurnstile,
          tokens[end_idx].offset,
          "missing top-level turnstile (`|-` or `⊢`)",
        ),
      )
  }
  if k + 1 >= end_idx {
    return Err(
      mk_parse_error(
        EmptyConclusion,
        tokens[k].offset,
        "goal conclusion is empty",
      ),
    )
  }

  let hyps : Array[SynTerm] = []
  if k > 0 {
    depth = 0
    let mut seg_start = 0
    let mut j = 0
    while j < k {
      let tok = tokens[j]
      match tok.kind {
        TkLParen => depth = depth + 1
        TkRParen => {
          depth = depth - 1
          if depth < 0 {
            return Err(
              mk_parse_error(UnexpectedToken, tok.offset, "unmatched `)`"),
            )
          }
        }
        TkComma if depth == 0 => {
          if seg_start == j {
            return Err(
              mk_parse_error(
                EmptyHypothesis,
                tok.offset,
                "empty hypothesis slot",
              ),
            )
          }
          let seg = slice_tokens_with_end(tokens, seg_start, j)
          match parse_term_tokens(seg) {
            Ok(t) => hyps.push(t)
            Err(e) => return Err(e)
          }
          seg_start = j + 1
        }
        _ => ()
      }
      j = j + 1
    }
    if seg_start == k {
      return Err(
        mk_parse_error(
          EmptyHypothesis,
          tokens[k - 1].offset,
          "empty hypothesis slot at end",
        ),
      )
    }
    let last_seg = slice_tokens_with_end(tokens, seg_start, k)
    match parse_term_tokens(last_seg) {
      Ok(t) => hyps.push(t)
      Err(e) => return Err(e)
    }
  }

  let concl_tokens = slice_tokens_with_end(tokens, k + 1, end_idx)
  let concl = match parse_term_tokens(concl_tokens) {
    Ok(t) => t
    Err(e) => return Err(e)
  }
  Ok(SynGoal::{ hyps, concl })
}

///|
fn slice_tokens_with_end(
  tokens : Array[Token],
  start : Int,
  end : Int,
) -> Array[Token] {
  let out : Array[Token] = []
  let mut i = start
  while i < end {
    out.push(tokens[i])
    i = i + 1
  }
  let end_offset = if end > start { tokens[end - 1].offset + 1 } else { start }
  out.push(Token::{ kind: TkEnd, offset: end_offset })
  out
}

///|
fn parse_term_raw_normalized(
  input : NormalizedInput,
) -> Result[SynTerm, ParseError] {
  match lex_tokens(input.text) {
    Ok(tokens) =>
      match parse_term_tokens(tokens) {
        Ok(term) => Ok(term)
        Err(e) => Err(map_parse_error_offset(input, e))
      }
    Err(e) => Err(map_parse_error_offset(input, e))
  }
}

///|
pub fn parse_term_raw(src : String) -> Result[SynTerm, ParseError] {
  match normalize_parser_input(src) {
    Ok(input) => parse_term_raw_normalized(input)
    Err(e) => Err(e)
  }
}

///|
fn parse_goal_raw_normalized(
  input : NormalizedInput,
) -> Result[SynGoal, ParseError] {
  let tokens = match lex_tokens(input.text) {
    Ok(v) => v
    Err(e) => return Err(map_parse_error_offset(input, e))
  }
  match parse_goal_tokens(tokens) {
    Ok(goal) => Ok(goal)
    Err(e) => Err(map_parse_error_offset(input, e))
  }
}

///|
pub fn parse_goal_raw(src : String) -> Result[SynGoal, ParseError] {
  match normalize_parser_input(src) {
    Ok(input) => parse_goal_raw_normalized(input)
    Err(e) => Err(e)
  }
}

///|
fn tokens_to_src(tokens : Array[Token], start : Int, end : Int) -> String {
  let out : Array[String] = []
  let mut i = start
  while i < end {
    let label = token_label(tokens[i].kind)
    if label != "<eof>" {
      out.push(label)
    }
    i = i + 1
  }
  out.join(" ")
}

///|
fn parse_script_step_tokens(
  seg : Array[Token],
) -> Result[SynTacticStep, ParseError] {
  if seg.length() == 0 {
    return Err(mk_parse_error(UnexpectedToken, 0, "empty tactic step"))
  }
  if seg.length() == 1 {
    match seg[0].kind {
      TkName("assumption") => Ok(Assumption)
      TkName("split") => Ok(Split)
      TkName("left") => Ok(Left)
      TkName("right") => Ok(Right)
      _ =>
        Err(
          mk_parse_error(
            UnexpectedToken,
            seg[0].offset,
            "unknown tactic step `" + token_label(seg[0].kind) + "`",
          ),
        )
    }
  } else if seg.length() == 2 {
    match (seg[0].kind, seg[1].kind) {
      (TkName("intro"), TkName(n)) => Ok(Intro(n))
      (TkName("exact"), TkName(n)) => Ok(Exact(n))
      (TkName("apply"), TkName(n)) => Ok(Apply(n))
      _ =>
        Err(
          mk_parse_error(
            UnexpectedToken,
            seg[0].offset,
            "malformed tactic step",
          ),
        )
    }
  } else {
    Err(
      mk_parse_error(
        UnexpectedToken,
        seg[0].offset,
        "tactic step has too many tokens",
      ),
    )
  }
}

///|
pub fn parse_theorem_script_raw(
  src : String,
) -> Result[SynTheoremScript, ParseError] {
  let input = match normalize_parser_input(src) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let tokens = match lex_tokens(input.text) {
    Ok(v) => v
    Err(e) => return Err(map_parse_error_offset(input, e))
  }
  let end_idx = tokens.length() - 1
  if end_idx < 5 {
    return Err(mk_parse_error(UnexpectedEof, 0, "incomplete theorem script"))
  }
  match token_at(tokens, 0).kind {
    TkName("theorem") => ()
    _ =>
      return Err(
        map_parse_error_offset(
          input,
          mk_parse_error(
            UnexpectedToken,
            token_at(tokens, 0).offset,
            "expected `theorem`",
          ),
        ),
      )
  }
  let name = match token_at(tokens, 1).kind {
    TkName(n) => n
    _ =>
      return Err(
        map_parse_error_offset(
          input,
          mk_parse_error(
            UnexpectedToken,
            token_at(tokens, 1).offset,
            "expected theorem name",
          ),
        ),
      )
  }
  match token_at(tokens, 2).kind {
    TkColon => ()
    _ =>
      return Err(
        map_parse_error_offset(
          input,
          mk_parse_error(
            UnexpectedToken,
            token_at(tokens, 2).offset,
            "expected `:` after theorem name",
          ),
        ),
      )
  }

  let mut depth = 0
  let mut assign_idx : Int? = None
  let mut i = 3
  while i < end_idx {
    let tk = tokens[i]
    match tk.kind {
      TkLParen => depth = depth + 1
      TkRParen => depth = depth - 1
      TkAssign if depth == 0 => {
        assign_idx = Some(i)
        break
      }
      _ => ()
    }
    i = i + 1
  }
  let k = match assign_idx {
    Some(v) => v
    None =>
      return Err(
        map_parse_error_offset(
          input,
          mk_parse_error(UnexpectedToken, 0, "missing `:=`"),
        ),
      )
  }
  if k <= 3 {
    return Err(
      map_parse_error_offset(
        input,
        mk_parse_error(
          EmptyConclusion,
          token_at(tokens, 2).offset,
          "empty theorem goal",
        ),
      ),
    )
  }
  match token_at(tokens, k + 1).kind {
    TkName("by") => ()
    _ =>
      return Err(
        map_parse_error_offset(
          input,
          mk_parse_error(
            UnexpectedToken,
            token_at(tokens, k + 1).offset,
            "expected `by` after `:=`",
          ),
        ),
      )
  }

  let goal_src = tokens_to_src(tokens, 3, k)
  let goal_tokens = slice_tokens_with_end(tokens, 3, k)
  let goal = match parse_goal_tokens(goal_tokens) {
    Ok(v) => v
    Err(e) => return Err(map_parse_error_offset(input, e))
  }

  let steps : Array[SynTacticStep] = []
  let mut seg_start = k + 2
  let mut j = seg_start
  while j < end_idx {
    match tokens[j].kind {
      TkSemi => {
        if seg_start == j {
          return Err(
            map_parse_error_offset(
              input,
              mk_parse_error(
                UnexpectedToken,
                tokens[j].offset,
                "empty tactic step",
              ),
            ),
          )
        }
        let seg : Array[Token] = []
        let mut s = seg_start
        while s < j {
          seg.push(tokens[s])
          s = s + 1
        }
        match parse_script_step_tokens(seg) {
          Ok(st) => steps.push(st)
          Err(e) => return Err(map_parse_error_offset(input, e))
        }
        seg_start = j + 1
      }
      _ => ()
    }
    j = j + 1
  }
  if seg_start < end_idx {
    let seg : Array[Token] = []
    let mut s = seg_start
    while s < end_idx {
      seg.push(tokens[s])
      s = s + 1
    }
    match parse_script_step_tokens(seg) {
      Ok(st) => steps.push(st)
      Err(e) => return Err(map_parse_error_offset(input, e))
    }
  }
  if steps.length() == 0 {
    return Err(
      map_parse_error_offset(
        input,
        mk_parse_error(
          UnexpectedEof,
          token_at(tokens, k + 1).offset,
          "empty theorem script body",
        ),
      ),
    )
  }

  Ok(SynTheoremScript::{ name, goal, goal_src, steps })
}

///|
fn elab_ctx_of(env : ParseEnv) -> ElabCtx {
  elab_ctx_from_locals(env.locals.copy())
}

///|
fn parser_unknown_const_error() -> SigError {
  match ks_mk_const(empty_kernel_state(), "__parser_missing__") {
    Err(e) => e
    Ok(_) => panic()
  }
}

///|
fn parser_invalid_const_instance_error() -> SigError {
  let a = mk_tyvar("A")
  let st0 = empty_kernel_state()
  let st1 = match ks_add_const(st0, "id", fun_ty(a, a)) {
    Ok(v) => v
    Err(_) => panic()
  }
  match ks_mk_const_instance(st1, "id", fun_ty(bool_ty(), a)) {
    Err(e) => e
    Ok(_) => panic()
  }
}

///|
fn parser_type_mismatch_error() -> LogicError {
  let lhs = mk_var("_parser_tm_lhs", bool_ty())
  let rhs = mk_var("_parser_tm_rhs", mk_tyvar("_PARSER_TM"))
  match mk_eq(lhs, rhs) {
    Err(e) => e
    Ok(_) => panic()
  }
}

///|
fn map_elab_error(err : ElabError) -> ParseBridgeError {
  if elab_err_unknown_name(err) || elab_err_unknown_const(err) {
    Sig(parser_unknown_const_error())
  } else if elab_err_invalid_const_instance(err) {
    match err {
      InvalidConstInstance(_) => Sig(parser_invalid_const_instance_error())
      _ => Elab(err)
    }
  } else if elab_err_core_typing_failure(err) {
    Logic(parser_type_mismatch_error())
  } else if elab_err_scope_resolution_mismatch(err) {
    Elab(err)
  } else {
    Elab(err)
  }
}

///|
fn lower_syn_term_basis(
  state : KernelState,
  env : ParseEnv,
  term : SynTerm,
) -> Result[Term, ParseBridgeError] {
  match term {
    Name(name) =>
      match parse_env_lookup(env, name) {
        Some(ty) => Ok(mk_var(name, ty))
        None =>
          match ks_mk_const(state, name) {
            Ok(t) => Ok(t)
            Err(e) => Err(Sig(e))
          }
      }
    Prefix(op, inner) =>
      if op == "¬" {
        let t = match lower_syn_term_basis(state, env, inner) {
          Ok(v) => v
          Err(e) => return Err(e)
        }
        match prop_mk_not(state, default_prop_prelude(), t) {
          Ok(v) => Ok(v)
          Err(e) => Err(Logic(e))
        }
      } else {
        Err(
          Parse(
            mk_parse_error(
              UnknownOperator,
              0,
              "unsupported prefix `" + op + "`",
            ),
          ),
        )
      }
    App(f, x) => {
      let f2 = match lower_syn_term_basis(state, env, f) {
        Ok(v) => v
        Err(e) => return Err(e)
      }
      let x2 = match lower_syn_term_basis(state, env, x) {
        Ok(v) => v
        Err(e) => return Err(e)
      }
      match elab_app(f2, x2) {
        Ok(v) => Ok(v)
        Err(e) => Err(Logic(e))
      }
    }
    Infix(op, lhs, rhs) =>
      if op == "=" {
        let l = match lower_syn_term_basis(state, env, lhs) {
          Ok(v) => v
          Err(e) => return Err(e)
        }
        let r = match lower_syn_term_basis(state, env, rhs) {
          Ok(v) => v
          Err(e) => return Err(e)
        }
        match elab_eq(l, r) {
          Ok(v) => Ok(v)
          Err(e) => Err(Logic(e))
        }
      } else if op == "->" {
        let l = match lower_syn_term_basis(state, env, lhs) {
          Ok(v) => v
          Err(e) => return Err(e)
        }
        let r = match lower_syn_term_basis(state, env, rhs) {
          Ok(v) => v
          Err(e) => return Err(e)
        }
        match prop_mk_imp(state, default_prop_prelude(), l, r) {
          Ok(v) => Ok(v)
          Err(e) => Err(Logic(e))
        }
      } else if op == "∧" {
        let l = match lower_syn_term_basis(state, env, lhs) {
          Ok(v) => v
          Err(e) => return Err(e)
        }
        let r = match lower_syn_term_basis(state, env, rhs) {
          Ok(v) => v
          Err(e) => return Err(e)
        }
        match prop_mk_and(state, default_prop_prelude(), l, r) {
          Ok(v) => Ok(v)
          Err(e) => Err(Logic(e))
        }
      } else if op == "∨" {
        let l = match lower_syn_term_basis(state, env, lhs) {
          Ok(v) => v
          Err(e) => return Err(e)
        }
        let r = match lower_syn_term_basis(state, env, rhs) {
          Ok(v) => v
          Err(e) => return Err(e)
        }
        match prop_mk_or(state, default_prop_prelude(), l, r) {
          Ok(v) => Ok(v)
          Err(e) => Err(Logic(e))
        }
      } else {
        Err(
          Parse(
            mk_parse_error(UnknownOperator, 0, "unsupported infix `" + op + "`"),
          ),
        )
      }
  }
}

///|
fn resolve_syn_term(
  state : KernelState,
  env : ParseEnv,
  term : SynTerm,
) -> Result[RTerm, ParseBridgeError] {
  match term {
    Prefix(_, _)
    | Infix("->", _, _)
    | Infix("∧", _, _)
    | Infix("∨", _, _) => {
      let named = match lower_syn_term_basis(state, env, term) {
        Ok(v) => v
        Err(e) => return Err(e)
      }
      let ctx = elab_ctx_of(env)
      return match elab_resolve_named_term(state, ctx, named) {
        Ok(v) => Ok(v)
        Err(e) => Err(map_elab_error(e))
      }
    }
    _ => ()
  }
  let ctx = elab_ctx_of(env)
  match term {
    Name(name) =>
      match elab_resolve_name(state, ctx, name) {
        Ok(t) => Ok(t)
        Err(e) => Err(map_elab_error(e))
      }
    Prefix(op, _) =>
      Err(
        Parse(
          mk_parse_error(UnknownOperator, 0, "unsupported prefix `" + op + "`"),
        ),
      )
    App(f, x) =>
      match (resolve_syn_term(state, env, f), resolve_syn_term(state, env, x)) {
        (Ok(f2), Ok(x2)) =>
          match elab_resolve_app(state, ctx, f2, x2) {
            Ok(t) => Ok(t)
            Err(e) => Err(map_elab_error(e))
          }
        (Err(e), _) => Err(e)
        (_, Err(e)) => Err(e)
      }
    Infix(op, lhs, rhs) =>
      if op == "=" {
        match
          (resolve_syn_term(state, env, lhs), resolve_syn_term(state, env, rhs)) {
          (Ok(l), Ok(r)) =>
            match elab_resolve_eq(state, ctx, l, r) {
              Ok(t) => Ok(t)
              Err(e) => Err(map_elab_error(e))
            }
          (Err(e), _) => Err(e)
          (_, Err(e)) => Err(e)
        }
      } else {
        Err(
          Parse(
            mk_parse_error(UnknownOperator, 0, "unsupported infix `" + op + "`"),
          ),
        )
      }
  }
}

///|
pub fn parse_resolved_term_with_env(
  state : KernelState,
  env : ParseEnv,
  src : String,
) -> Result[RTerm, ParseBridgeError] {
  match parse_term_raw(src) {
    Ok(syn) => resolve_syn_term(state, env, syn)
    Err(e) => Err(Parse(e))
  }
}

///|
pub fn parse_resolved_term(
  state : KernelState,
  src : String,
) -> Result[RTerm, ParseBridgeError] {
  parse_resolved_term_with_env(state, empty_parse_env(), src)
}

///|
pub fn lower_syn_term_with_env(
  state : KernelState,
  env : ParseEnv,
  term : SynTerm,
) -> Result[Term, ParseBridgeError] {
  match resolve_syn_term(state, env, term) {
    Ok(rterm) =>
      match elab_lower_to_term(rterm) {
        Ok(out) => Ok(out)
        Err(e) => Err(map_elab_error(e))
      }
    Err(e) => Err(e)
  }
}

///|
pub fn parse_term_with_env(
  state : KernelState,
  env : ParseEnv,
  src : String,
) -> Result[Term, ParseBridgeError] {
  match parse_resolved_term_with_env(state, env, src) {
    Ok(rterm) =>
      match elab_lower_to_term(rterm) {
        Ok(out) => Ok(out)
        Err(e) => Err(map_elab_error(e))
      }
    Err(e) => Err(e)
  }
}

///|
pub fn parse_term(
  state : KernelState,
  src : String,
) -> Result[Term, ParseBridgeError] {
  parse_term_with_env(state, empty_parse_env(), src)
}

///|
pub fn parse_resolved_goal_with_env(
  state : KernelState,
  env : ParseEnv,
  src : String,
) -> Result[ResolvedGoal, ParseBridgeError] {
  let syn_goal = match parse_goal_raw(src) {
    Ok(v) => v
    Err(e) => return Err(Parse(e))
  }
  lower_syn_resolved_goal_with_env(state, env, syn_goal)
}

///|
fn lower_syn_resolved_goal_with_env(
  state : KernelState,
  env : ParseEnv,
  syn_goal : SynGoal,
) -> Result[ResolvedGoal, ParseBridgeError] {
  let hyps : Array[RTerm] = []
  for h in syn_goal.hyps {
    match resolve_syn_term(state, env, h) {
      Ok(t) => hyps.push(t)
      Err(e) => return Err(e)
    }
  }
  match resolve_syn_term(state, env, syn_goal.concl) {
    Ok(concl) => Ok(ResolvedGoal::{ hyps, concl })
    Err(e) => Err(e)
  }
}

///|
pub fn parse_goal_with_env(
  state : KernelState,
  env : ParseEnv,
  src : String,
) -> Result[Goal, ParseBridgeError] {
  match parse_resolved_goal_with_env(state, env, src) {
    Ok(goal) => lower_resolved_goal_with_env(goal)
    Err(e) => Err(e)
  }
}

///|
pub fn lower_syn_goal_with_env(
  state : KernelState,
  env : ParseEnv,
  syn_goal : SynGoal,
) -> Result[Goal, ParseBridgeError] {
  match lower_syn_resolved_goal_with_env(state, env, syn_goal) {
    Ok(goal) => lower_resolved_goal_with_env(goal)
    Err(e) => Err(e)
  }
}

///|
fn lower_resolved_goal_with_env(
  goal : ResolvedGoal,
) -> Result[Goal, ParseBridgeError] {
  let hyps : Array[Term] = []
  for h in goal.hyps {
    match elab_lower_to_term(h) {
      Ok(t) => hyps.push(t)
      Err(e) => return Err(map_elab_error(e))
    }
  }
  match elab_lower_to_term(goal.concl) {
    Ok(concl) => Ok(mk_goal(hyps, concl))
    Err(e) => Err(map_elab_error(e))
  }
}

///|
pub fn parse_goal(
  state : KernelState,
  src : String,
) -> Result[Goal, ParseBridgeError] {
  parse_goal_with_env(state, empty_parse_env(), src)
}

///|
pub fn parse_let(
  env : ParseEnv,
  src : String,
) -> Result[ParseEnv, ParseBridgeError] {
  let input = match normalize_parser_input(src) {
    Ok(v) => v
    Err(e) => return Err(Parse(e))
  }
  let tokens = match lex_tokens(input.text) {
    Ok(v) => v
    Err(e) => return Err(Parse(map_parse_error_offset(input, e)))
  }
  let i = 0
  match token_at(tokens, i).kind {
    TkName("let") => ()
    _ =>
      return Err(
        Parse(
          map_parse_error_offset(
            input,
            mk_parse_error(
              UnexpectedToken,
              token_at(tokens, i).offset,
              "expected `let` declaration",
            ),
          ),
        ),
      )
  }
  let (name, i2) = match token_at(tokens, i + 1).kind {
    TkName(n) => (n, i + 2)
    _ =>
      return Err(
        Parse(
          map_parse_error_offset(
            input,
            mk_parse_error(
              UnexpectedToken,
              token_at(tokens, i + 1).offset,
              "expected local variable name after `let`",
            ),
          ),
        ),
      )
  }
  match token_at(tokens, i2).kind {
    TkColon => ()
    _ =>
      return Err(
        Parse(
          map_parse_error_offset(
            input,
            mk_parse_error(
              UnexpectedToken,
              token_at(tokens, i2).offset,
              "expected `:` in let declaration",
            ),
          ),
        ),
      )
  }
  let (ty, j) = match parse_type(tokens, i2 + 1) {
    Ok(v) => v
    Err(e) => return Err(Parse(map_parse_error_offset(input, e)))
  }
  match token_at(tokens, j).kind {
    TkEnd => ()
    _ =>
      return Err(
        Parse(
          map_parse_error_offset(
            input,
            mk_parse_error(
              UnexpectedToken,
              token_at(tokens, j).offset,
              "unexpected trailing token in let declaration",
            ),
          ),
        ),
      )
  }
  let locals = env.locals.copy()
  locals.push((name, ty))
  Ok(ParseEnv::{ locals, })
}

///|
pub fn parse_def_function(
  state : KernelState,
  env : ParseEnv,
  src : String,
) -> Result[(KernelState, Thm), ParseBridgeError] {
  let input = match normalize_parser_input(src) {
    Ok(v) => v
    Err(e) => return Err(Parse(e))
  }
  let tokens = match lex_tokens(input.text) {
    Ok(v) => v
    Err(e) => return Err(Parse(map_parse_error_offset(input, e)))
  }

  let i0 = 0
  match token_at(tokens, i0).kind {
    TkName("def") => ()
    _ =>
      return Err(
        Parse(
          map_parse_error_offset(
            input,
            mk_parse_error(
              UnexpectedToken,
              token_at(tokens, i0).offset,
              "expected `def` declaration",
            ),
          ),
        ),
      )
  }

  let (fname, i1) = match token_at(tokens, i0 + 1).kind {
    TkName(n) => (n, i0 + 2)
    _ =>
      return Err(
        Parse(
          map_parse_error_offset(
            input,
            mk_parse_error(
              UnexpectedToken,
              token_at(tokens, i0 + 1).offset,
              "expected function name after `def`",
            ),
          ),
        ),
      )
  }

  match token_at(tokens, i1).kind {
    TkLParen => ()
    _ =>
      return Err(
        Parse(
          map_parse_error_offset(
            input,
            mk_parse_error(
              UnexpectedToken,
              token_at(tokens, i1).offset,
              "expected `(` after function name",
            ),
          ),
        ),
      )
  }

  let (param, i2) = match token_at(tokens, i1 + 1).kind {
    TkName(n) => (n, i1 + 2)
    _ =>
      return Err(
        Parse(
          map_parse_error_offset(
            input,
            mk_parse_error(
              UnexpectedToken,
              token_at(tokens, i1 + 1).offset,
              "expected parameter name in `def`",
            ),
          ),
        ),
      )
  }

  match token_at(tokens, i2).kind {
    TkColon => ()
    _ =>
      return Err(
        Parse(
          map_parse_error_offset(
            input,
            mk_parse_error(
              UnexpectedToken,
              token_at(tokens, i2).offset,
              "expected `:` after parameter name",
            ),
          ),
        ),
      )
  }

  let (param_ty, i3) = match parse_type(tokens, i2 + 1) {
    Ok(v) => v
    Err(e) => return Err(Parse(map_parse_error_offset(input, e)))
  }

  match token_at(tokens, i3).kind {
    TkRParen => ()
    _ =>
      return Err(
        Parse(
          map_parse_error_offset(
            input,
            mk_parse_error(
              UnexpectedToken,
              token_at(tokens, i3).offset,
              "expected `)` after parameter type",
            ),
          ),
        ),
      )
  }

  match token_at(tokens, i3 + 1).kind {
    TkColon => ()
    _ =>
      return Err(
        Parse(
          map_parse_error_offset(
            input,
            mk_parse_error(
              UnexpectedToken,
              token_at(tokens, i3 + 1).offset,
              "expected `:` before return type",
            ),
          ),
        ),
      )
  }

  let (ret_ty, i4) = match parse_type(tokens, i3 + 2) {
    Ok(v) => v
    Err(e) => return Err(Parse(map_parse_error_offset(input, e)))
  }

  match token_at(tokens, i4).kind {
    TkLBrace => ()
    _ =>
      return Err(
        Parse(
          map_parse_error_offset(
            input,
            mk_parse_error(
              UnexpectedToken,
              token_at(tokens, i4).offset,
              "expected `{` before function body",
            ),
          ),
        ),
      )
  }

  let mut depth = 1
  let mut j = i4 + 1
  while j < tokens.length() {
    let tk = token_at(tokens, j)
    match tk.kind {
      TkLBrace => depth = depth + 1
      TkRBrace => {
        depth = depth - 1
        if depth == 0 {
          break
        }
      }
      TkEnd => ()
      _ => ()
    }
    j = j + 1
  }
  let missing_rbrace = if j >= tokens.length() {
    true
  } else {
    match token_at(tokens, j).kind {
      TkRBrace => false
      _ => true
    }
  }
  if missing_rbrace {
    return Err(
      Parse(
        map_parse_error_offset(
          input,
          mk_parse_error(
            UnexpectedEof,
            token_at(tokens, i4).offset,
            "missing `}` for function body",
          ),
        ),
      ),
    )
  }

  let body_tokens = slice_tokens_with_end(tokens, i4 + 1, j)
  let body_syn = match parse_term_tokens(body_tokens) {
    Ok(v) => v
    Err(e) => return Err(Parse(map_parse_error_offset(input, e)))
  }

  match token_at(tokens, j + 1).kind {
    TkEnd => ()
    _ =>
      return Err(
        Parse(
          map_parse_error_offset(
            input,
            mk_parse_error(
              UnexpectedToken,
              token_at(tokens, j + 1).offset,
              "unexpected trailing token after function body",
            ),
          ),
        ),
      )
  }

  let locals = env.locals.copy()
  locals.push((param, param_ty))
  let body_env = ParseEnv::{ locals, }
  let body_rterm = match resolve_syn_term(state, body_env, body_syn) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let body_term = match elab_lower_to_term(body_rterm) {
    Ok(v) => v
    Err(e) => return Err(map_elab_error(e))
  }
  let rhs = mk_abs(mk_var(param, param_ty), body_term)
  match type_of(rhs) {
    Some(_) => ()
    None => return Err(Logic(parser_type_mismatch_error()))
  }
  let decl_ty = fun_ty(param_ty, ret_ty)
  match ks_define_const_thm(state, fname, decl_ty, rhs) {
    Ok((st2, th)) => Ok((st2, th))
    Err(e) => Err(Sig(e))
  }
}
