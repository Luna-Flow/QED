///|
pub enum SynTerm {
  Name(String)
  Prefix(String, SynTerm)
  App(SynTerm, SynTerm)
  Infix(String, SynTerm, SynTerm)
  Forall(String, HolType, SynTerm)
}

///|
pub struct SynGoal {
  hyps : Array[SynTerm]
  concl : SynTerm
}

///|
pub struct SynBinder {
  name : String
  ty : HolType
  span : SourceSpan
  src : String
}

///|
pub struct SourceSpan {
  start_offset : Int
  end_offset : Int
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
  Hole(String?)
}

///|
pub struct SynScriptStep {
  step : SynTacticStep
  step_index : Int
  branch_path : Array[Int]
  span : SourceSpan
  src : String
  branches : Array[SynScriptBranch]
}

///|
pub struct SynScriptBranch {
  branch_path : Array[Int]
  body : SynScriptBody
  span : SourceSpan
  src : String
}

///|
pub struct SynScriptBody {
  steps : Array[SynScriptStep]
}

///|
pub struct SynTheoremScript {
  name : String
  binders : Array[SynBinder]
  goal : SynGoal
  goal_src : String
  goal_span : SourceSpan
  body : SynScriptBody
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
pub struct ParsedGoal {
  hyps : Array[Term]
  concl : Term
}

///|
pub fn parsed_goal_hyps(goal : ParsedGoal) -> Array[Term] {
  goal.hyps.copy()
}

///|
pub fn parsed_goal_concl(goal : ParsedGoal) -> Term {
  goal.concl
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
  TkNewline
  TkColon
  TkAssign
  TkArrow
  TkTurnstile
  TkAnd
  TkOr
  TkNot
  TkEq
  TkForall
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
pub fn parse_env_push_local(
  env : ParseEnv,
  name : String,
  ty : HolType,
) -> ParseEnv {
  let locals = env.locals.copy()
  locals.push((name, ty))
  ParseEnv::{ locals, }
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
pub fn source_span(start_offset : Int, end_offset : Int) -> SourceSpan {
  let start = if start_offset < 0 { 0 } else { start_offset }
  let end = if end_offset < start { start } else { end_offset }
  SourceSpan::{ start_offset: start, end_offset: end }
}

///|
fn raw_source_slice(
  src : String,
  start_offset : Int,
  end_offset : Int,
) -> String {
  let start = if start_offset < 0 { 0 } else { start_offset }
  let end = if end_offset < start { start } else { end_offset }
  let chars : Array[Char] = []
  let mut view = src.view()
  let mut off = 0
  while true {
    match view {
      [] => return String::from_iter(chars.iter())
      [c, .. rest] =>
        if off >= end {
          return String::from_iter(chars.iter())
        } else {
          if off >= start {
            chars.push(c)
          }
          view = rest
          off = off + 1
        }
    }
  }
  ""
}

///|
fn normalize_theorem_script_input(
  src : String,
) -> Result[NormalizedInput, ParseError] {
  let out_chars : Array[Char] = []
  let raw_offsets : Array[Int] = []
  let mut view = src.view()
  let mut off = 0
  let mut pending_space = false
  let mut space_off = 0
  while true {
    match view {
      [] =>
        return Ok(NormalizedInput::{
          text: String::from_iter(out_chars.iter()),
          raw_offsets,
          raw_length: off,
        })
      [c, .. rest] =>
        if c.is_ascii_whitespace() {
          if c == '\n' || c == '\r' {
            let (rest2, off2) = if c == '\r' {
              match rest {
                ['\n', .. rest3] => (rest3, off + 2)
                _ => (rest, off + 1)
              }
            } else {
              (rest, off + 1)
            }
            if out_chars.length() != 0 {
              push_normalized_char(out_chars, raw_offsets, '\n', off)
            }
            view = rest2
            off = off2
            pending_space = false
            space_off = 0
          } else if out_chars.length() == 0 ||
            out_chars[out_chars.length() - 1] == '\n' {
            view = rest
            off = off + 1
            pending_space = false
            space_off = 0
          } else {
            if !pending_space {
              space_off = off
            }
            view = rest
            off = off + 1
            pending_space = true
          }
        } else {
          if pending_space && out_chars.length() > 0 {
            push_normalized_char(out_chars, raw_offsets, ' ', space_off)
          }
          pending_space = false
          space_off = 0
          if c == '\\' {
            match rest {
              [r, ..] if is_name_start(r) => {
                let (esc_name, rest2, n) = read_name(rest)
                if esc_name == "and" {
                  push_normalized_char(out_chars, raw_offsets, '∧', off)
                } else if esc_name == "or" {
                  push_normalized_char(out_chars, raw_offsets, '∨', off)
                } else if esc_name == "not" {
                  push_normalized_char(out_chars, raw_offsets, '¬', off)
                } else if esc_name == "imp" {
                  push_normalized_char(out_chars, raw_offsets, '-', off)
                  push_normalized_char(out_chars, raw_offsets, '>', off)
                } else {
                  return Err(
                    mk_parse_error(
                      UnknownOperator,
                      off,
                      "unknown escaped operator `\\" + esc_name + "`",
                    ),
                  )
                }
                view = rest2
                off = off + n + 1
              }
              _ =>
                return Err(
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
                view = rest2
                off = off + 2
              }
              _ => {
                push_normalized_char(out_chars, raw_offsets, c, off)
                view = rest
                off = off + 1
              }
            }
          } else {
            push_normalized_char(out_chars, raw_offsets, c, off)
            view = rest
            off = off + 1
          }
        }
    }
  }
  Err(mk_parse_error(UnexpectedEof, 0, "unreachable"))
}

///|
pub fn normalize_parser_input(
  src : String,
) -> Result[NormalizedInput, ParseError] {
  let out_chars : Array[Char] = []
  let raw_offsets : Array[Int] = []
  let mut view = src.view()
  let mut off = 0
  let mut pending_space = false
  let mut space_off = 0
  while true {
    match view {
      [] =>
        return Ok(NormalizedInput::{
          text: String::from_iter(out_chars.iter()),
          raw_offsets,
          raw_length: off,
        })
      [c, .. rest] =>
        if c.is_ascii_whitespace() {
          if out_chars.length() != 0 {
            if !pending_space {
              space_off = off
            }
            pending_space = true
          }
          view = rest
          off = off + 1
        } else {
          if pending_space && out_chars.length() > 0 {
            push_normalized_char(out_chars, raw_offsets, ' ', space_off)
          }
          pending_space = false
          space_off = 0
          if c == '\\' {
            match rest {
              [r, ..] if is_name_start(r) => {
                let (esc_name, rest2, n) = read_name(rest)
                if esc_name == "and" {
                  push_normalized_char(out_chars, raw_offsets, '∧', off)
                } else if esc_name == "or" {
                  push_normalized_char(out_chars, raw_offsets, '∨', off)
                } else if esc_name == "not" {
                  push_normalized_char(out_chars, raw_offsets, '¬', off)
                } else if esc_name == "imp" {
                  push_normalized_char(out_chars, raw_offsets, '-', off)
                  push_normalized_char(out_chars, raw_offsets, '>', off)
                } else {
                  return Err(
                    mk_parse_error(
                      UnknownOperator,
                      off,
                      "unknown escaped operator `\\" + esc_name + "`",
                    ),
                  )
                }
                view = rest2
                off = off + n + 1
              }
              _ =>
                return Err(
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
                view = rest2
                off = off + 2
              }
              _ => {
                push_normalized_char(out_chars, raw_offsets, c, off)
                view = rest
                off = off + 1
              }
            }
          } else {
            push_normalized_char(out_chars, raw_offsets, c, off)
            view = rest
            off = off + 1
          }
        }
    }
  }
  Err(mk_parse_error(UnexpectedEof, 0, "unreachable"))
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
    TkNewline => "<newline>"
    TkColon => ":"
    TkAssign => ":="
    TkArrow => "->"
    TkTurnstile => "⊢"
    TkAnd => "∧"
    TkOr => "∨"
    TkNot => "¬"
    TkEq => "="
    TkForall => "∀"
    TkEnd => "<eof>"
  }
}

///|
fn token_normalized_width(kind : TokKind) -> Int {
  match kind {
    TkName(name) => name.length()
    TkLParen => 1
    TkRParen => 1
    TkLBrace => 1
    TkRBrace => 1
    TkComma => 1
    TkSemi => 1
    TkNewline => 1
    TkColon => 1
    TkAssign => 2
    TkArrow => 2
    TkTurnstile => 1
    TkAnd => 1
    TkOr => 1
    TkNot => 1
    TkEq => 1
    TkForall => 1
    TkEnd => 0
  }
}

///|
fn token_normalized_end(tok : Token) -> Int {
  tok.offset + token_normalized_width(tok.kind)
}

///|
fn map_source_span(
  input : NormalizedInput,
  start_offset : Int,
  end_offset : Int,
) -> SourceSpan {
  source_span(
    normalized_input_raw_offset_at(input, start_offset),
    normalized_input_raw_offset_at(input, end_offset),
  )
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
  let mut rest = view
  let mut n = 0
  while true {
    match rest {
      [c, .. rest2] if is_name_continue(c) => {
        chars.push(c)
        rest = rest2
        n = n + 1
      }
      _ => return (String::from_iter(chars.iter()), rest, n)
    }
  }
  ("", view, 0)
}

///|
fn lex_tokens_layout(
  src : String,
  keep_newlines : Bool,
) -> Result[Array[Token], ParseError] {
  let out : Array[Token] = []
  let mut view = src.view()
  let mut off = 0
  while true {
    match view {
      [] => {
        out.push(Token::{ kind: TkEnd, offset: off })
        return Ok(out)
      }
      [c, .. rest] =>
        if keep_newlines && c == '\n' {
          out.push(Token::{ kind: TkNewline, offset: off })
          view = rest
          off = off + 1
        } else if c.is_ascii_whitespace() {
          view = rest
          off = off + 1
        } else if c == '(' {
          out.push(Token::{ kind: TkLParen, offset: off })
          view = rest
          off = off + 1
        } else if c == ')' {
          out.push(Token::{ kind: TkRParen, offset: off })
          view = rest
          off = off + 1
        } else if c == '{' {
          out.push(Token::{ kind: TkLBrace, offset: off })
          view = rest
          off = off + 1
        } else if c == '}' {
          out.push(Token::{ kind: TkRBrace, offset: off })
          view = rest
          off = off + 1
        } else if c == '∧' {
          out.push(Token::{ kind: TkAnd, offset: off })
          view = rest
          off = off + 1
        } else if c == '∨' {
          out.push(Token::{ kind: TkOr, offset: off })
          view = rest
          off = off + 1
        } else if c == ',' {
          out.push(Token::{ kind: TkComma, offset: off })
          view = rest
          off = off + 1
        } else if c == ';' {
          out.push(Token::{ kind: TkSemi, offset: off })
          view = rest
          off = off + 1
        } else if c == ':' {
          match rest {
            ['=', .. rest2] => {
              out.push(Token::{ kind: TkAssign, offset: off })
              view = rest2
              off = off + 2
            }
            _ => {
              out.push(Token::{ kind: TkColon, offset: off })
              view = rest
              off = off + 1
            }
          }
        } else if c == '=' {
          out.push(Token::{ kind: TkEq, offset: off })
          view = rest
          off = off + 1
        } else if c == '-' {
          match rest {
            ['>', .. rest2] => {
              out.push(Token::{ kind: TkArrow, offset: off })
              view = rest2
              off = off + 2
            }
            _ =>
              return Err(
                mk_parse_error(
                  UnknownOperator,
                  off,
                  "unknown operator near `-`",
                ),
              )
          }
        } else if c == '|' {
          match rest {
            ['-', .. rest2] => {
              out.push(Token::{ kind: TkTurnstile, offset: off })
              view = rest2
              off = off + 2
            }
            _ =>
              return Err(
                mk_parse_error(
                  UnknownOperator,
                  off,
                  "unknown operator near `|`",
                ),
              )
          }
        } else if c == '⊢' {
          out.push(Token::{ kind: TkTurnstile, offset: off })
          view = rest
          off = off + 1
        } else if c == '¬' {
          out.push(Token::{ kind: TkNot, offset: off })
          view = rest
          off = off + 1
        } else if c == '∀' {
          out.push(Token::{ kind: TkForall, offset: off })
          view = rest
          off = off + 1
        } else if c == '\\' {
          match rest {
            [r, ..] if is_name_start(r) => {
              let (esc_name, rest2, n) = read_name(rest)
              if esc_name == "and" {
                out.push(Token::{ kind: TkAnd, offset: off })
              } else if esc_name == "or" {
                out.push(Token::{ kind: TkOr, offset: off })
              } else if esc_name == "not" {
                out.push(Token::{ kind: TkNot, offset: off })
              } else if esc_name == "imp" {
                out.push(Token::{ kind: TkArrow, offset: off })
              } else {
                return Err(
                  mk_parse_error(
                    UnknownOperator,
                    off,
                    "unknown escaped operator `\\" + esc_name + "`",
                  ),
                )
              }
              view = rest2
              off = off + n + 1
            }
            _ =>
              return Err(
                mk_parse_error(
                  UnknownOperator,
                  off,
                  "unknown operator near `\\`",
                ),
              )
          }
        } else if is_name_start(c) {
          let (name, rest2, n) = read_name([c, ..rest])
          out.push(Token::{ kind: TkName(name), offset: off })
          view = rest2
          off = off + n
        } else if is_operator_like(c) {
          return Err(
            mk_parse_error(
              UnknownOperator,
              off,
              "unknown operator near `" + c.to_string() + "`",
            ),
          )
        } else {
          return Err(
            mk_parse_error(
              UnexpectedToken,
              off,
              "unexpected character `" + c.to_string() + "`",
            ),
          )
        }
    }
  }
  Ok(out)
}

///|
fn lex_tokens(src : String) -> Result[Array[Token], ParseError] {
  lex_tokens_layout(src, false)
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
fn parse_type_tokens(tokens : Array[Token]) -> Result[HolType, ParseError] {
  match parse_type(tokens, 0) {
    Ok((ty, idx)) =>
      match token_at(tokens, idx).kind {
        TkEnd => Ok(ty)
        _ =>
          Err(
            mk_parse_error(
              UnexpectedToken,
              token_at(tokens, idx).offset,
              "unexpected trailing token `" +
              token_label(token_at(tokens, idx).kind) +
              "` in type",
            ),
          )
      }
    Err(e) => Err(e)
  }
}

///|
fn op_fixity(op : String) -> (Int, Assoc)? {
  if op == "=" {
    Some((40, NonAssoc))
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
  allow_forall : Bool,
) -> Result[(SynTerm, Int), ParseError] {
  let tok = token_at(tokens, idx)
  match tok.kind {
    TkName(name) => Ok((Name(name), idx + 1))
    TkLParen =>
      match parse_infix_with_forall(tokens, idx + 1, allow_forall) {
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
  allow_forall : Bool,
) -> Result[(SynTerm, Int), ParseError] {
  match parse_atom(tokens, idx, allow_forall) {
    Ok((head, j0)) => {
      let mut out = head
      let mut j = j0
      while is_atom_start(token_at(tokens, j).kind) {
        match parse_atom(tokens, j, allow_forall) {
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
fn parse_forall_binder(
  tokens : Array[Token],
  idx : Int,
) -> Result[(String, HolType, Int), ParseError] {
  let binder_start = idx + 1
  match token_at(tokens, binder_start).kind {
    TkLParen => ()
    _ =>
      return Err(
        mk_parse_error(
          UnexpectedToken,
          token_at(tokens, binder_start).offset,
          "expected `(name : type)` after `forall`",
        ),
      )
  }
  let name_idx = binder_start + 1
  let name = match token_at(tokens, name_idx).kind {
    TkName(n) => n
    _ =>
      return Err(
        mk_parse_error(
          UnexpectedToken,
          token_at(tokens, name_idx).offset,
          "expected binder name after `forall (`",
        ),
      )
  }
  let colon_idx = name_idx + 1
  match token_at(tokens, colon_idx).kind {
    TkColon => ()
    _ =>
      return Err(
        mk_parse_error(
          UnexpectedToken,
          token_at(tokens, colon_idx).offset,
          "expected `:` in `forall` binder",
        ),
      )
  }
  let mut depth = 0
  let mut close_idx : Int? = None
  let mut i = colon_idx + 1
  while i < tokens.length() {
    match token_at(tokens, i).kind {
      TkLParen => depth = depth + 1
      TkRParen =>
        if depth == 0 {
          close_idx = Some(i)
          break
        } else {
          depth = depth - 1
        }
      TkEnd =>
        return Err(
          mk_parse_error(
            UnexpectedEof,
            token_at(tokens, i).offset,
            "missing `)` in `forall` binder",
          ),
        )
      _ => ()
    }
    i = i + 1
  }
  let close_idx = match close_idx {
    Some(v) => v
    None =>
      return Err(
        mk_parse_error(
          UnexpectedEof,
          token_at(tokens, colon_idx).offset,
          "missing `)` in `forall` binder",
        ),
      )
  }
  let ty = match
    parse_type_tokens(slice_tokens_with_end(tokens, colon_idx + 1, close_idx)) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let comma_idx = close_idx + 1
  match token_at(tokens, comma_idx).kind {
    TkComma => ()
    _ =>
      return Err(
        mk_parse_error(
          UnexpectedToken,
          token_at(tokens, comma_idx).offset,
          "expected `,` after `forall` binder",
        ),
      )
  }
  Ok((name, ty, comma_idx + 1))
}

///|
fn parse_prefix_with_forall(
  tokens : Array[Token],
  idx : Int,
  allow_forall : Bool,
) -> Result[(SynTerm, Int), ParseError] {
  let tok = token_at(tokens, idx)
  match tok.kind {
    TkForall | TkName("forall") if allow_forall => {
      let (name, ty, body_idx) = match parse_forall_binder(tokens, idx) {
        Ok(v) => v
        Err(e) => return Err(e)
      }
      match parse_infix_with_forall(tokens, body_idx, allow_forall) {
        Ok((body, j)) => Ok((Forall(name, ty, body), j))
        Err(e) => Err(e)
      }
    }
    TkForall | TkName("forall") =>
      Err(
        mk_parse_error(
          UnexpectedToken,
          tok.offset,
          "raw `forall` is only supported in goal syntax",
        ),
      )
    TkNot =>
      match parse_prefix_with_forall(tokens, idx + 1, allow_forall) {
        Ok((inner, j)) => Ok((Prefix("¬", inner), j))
        Err(e) => Err(e)
      }
    _ => parse_app(tokens, idx, allow_forall)
  }
}

///|
fn parse_infix_with_forall(
  tokens : Array[Token],
  idx : Int,
  allow_forall : Bool,
) -> Result[(SynTerm, Int), ParseError] {
  match parse_prefix_with_forall(tokens, idx, allow_forall) {
    Ok((lhs0, j0)) => {
      let chain : Array[(String, SynTerm, Int)] = []
      let mut j = j0
      while true {
        let tok = token_at(tokens, j)
        match tok.kind {
          TkAnd =>
            match parse_prefix_with_forall(tokens, j + 1, allow_forall) {
              Ok((rhs, j2)) => {
                chain.push(("∧", rhs, tok.offset))
                j = j2
              }
              Err(e) => return Err(e)
            }
          TkOr =>
            match parse_prefix_with_forall(tokens, j + 1, allow_forall) {
              Ok((rhs, j2)) => {
                chain.push(("∨", rhs, tok.offset))
                j = j2
              }
              Err(e) => return Err(e)
            }
          TkArrow =>
            match parse_prefix_with_forall(tokens, j + 1, allow_forall) {
              Ok((rhs, j2)) => {
                chain.push(("->", rhs, tok.offset))
                j = j2
              }
              Err(e) => return Err(e)
            }
          TkEq =>
            match parse_prefix_with_forall(tokens, j + 1, allow_forall) {
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
  match parse_infix_with_forall(tokens, 0, false) {
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
fn parse_goal_term_tokens(tokens : Array[Token]) -> Result[SynTerm, ParseError] {
  match parse_infix_with_forall(tokens, 0, true) {
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
  let concl = match parse_goal_term_tokens(concl_tokens) {
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
fn slice_tokens_without_newlines_with_end(
  tokens : Array[Token],
  start : Int,
  end : Int,
) -> Array[Token] {
  let out : Array[Token] = []
  let mut i = start
  while i < end {
    match tokens[i].kind {
      TkNewline => ()
      _ => out.push(tokens[i])
    }
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
    match tokens[i].kind {
      TkEnd => ()
      TkNewline => ()
      _ => {
        let label = token_label(tokens[i].kind)
        if label != "<eof>" {
          out.push(label)
        }
      }
    }
    i = i + 1
  }
  out.join(" ")
}

///|
fn child_branch_path(branch_path : Array[Int], branch_idx : Int) -> Array[Int] {
  let out = branch_path.copy()
  out.push(branch_idx)
  out
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
      TkName("hole") => Ok(Hole(None))
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
      (TkName("hole"), TkName(n)) => Ok(Hole(Some(n)))
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
fn next_non_newline_token_index(tokens : Array[Token], idx : Int) -> Int {
  let mut j = idx
  while true {
    match token_at(tokens, j).kind {
      TkNewline => j = j + 1
      _ => return j
    }
  }
  0
}

///|
fn body_remainder_is_only_newlines(
  tokens : Array[Token],
  start : Int,
  end : Int,
) -> Bool {
  let mut i = start
  while i < end {
    match tokens[i].kind {
      TkNewline => i = i + 1
      _ => return false
    }
  }
  true
}

///|
fn last_non_newline_token_index(
  tokens : Array[Token],
  start : Int,
  end : Int,
) -> Int? {
  let mut i = end
  while i > start {
    i = i - 1
    match tokens[i].kind {
      TkNewline => ()
      _ => return Some(i)
    }
  }
  None
}

///|
fn token_is_line_start(tokens : Array[Token], idx : Int) -> Bool {
  if idx <= 0 {
    true
  } else {
    token_at(tokens, idx - 1).kind is TkNewline
  }
}

///|
fn token_line_remainder_is_empty(
  tokens : Array[Token],
  start : Int,
  end : Int,
) -> Bool {
  let i = start + 1
  if i >= end {
    true
  } else {
    match token_at(tokens, i).kind {
      TkNewline => true
      _ => false
    }
  }
}

///|
fn token_is_qed_terminator(tokens : Array[Token], idx : Int, end : Int) -> Bool {
  match token_at(tokens, idx).kind {
    TkName("qed") =>
      token_is_line_start(tokens, idx) &&
      token_line_remainder_is_empty(tokens, idx, end)
    _ => false
  }
}

///|
fn parse_script_step_segment(
  input : NormalizedInput,
  raw_src : String,
  tokens : Array[Token],
  start : Int,
  end : Int,
  step_index : Int,
  branch_path : Array[Int],
) -> Result[SynScriptStep, ParseError] {
  let seg : Array[Token] = []
  let mut i = start
  while i < end {
    seg.push(tokens[i])
    i = i + 1
  }
  let step = match parse_script_step_tokens(seg) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let span = map_source_span(
    input,
    tokens[start].offset,
    token_normalized_end(tokens[end - 1]),
  )
  Ok(SynScriptStep::{
    step,
    step_index,
    branch_path: branch_path.copy(),
    span,
    src: raw_source_slice(raw_src, span.start_offset, span.end_offset),
    branches: [],
  })
}

///|
fn expected_branch_count(step : SynTacticStep) -> Int {
  match step {
    Split => 2
    Left => 1
    Right => 1
    _ => 0
  }
}

///|
fn find_matching_brace(
  tokens : Array[Token],
  start : Int,
  end : Int,
) -> Result[Int, ParseError] {
  let open = token_at(tokens, start)
  match open.kind {
    TkLBrace => ()
    _ =>
      return Err(
        mk_parse_error(
          UnexpectedToken,
          open.offset,
          "expected `{` to start branch block",
        ),
      )
  }
  let mut depth = 0
  let mut i = start + 1
  while i < end {
    match tokens[i].kind {
      TkLBrace => depth = depth + 1
      TkRBrace => if depth == 0 { return Ok(i) } else { depth = depth - 1 }
      _ => ()
    }
    i = i + 1
  }
  Err(
    mk_parse_error(
      UnexpectedEof,
      open.offset,
      "missing `}` to close branch block",
    ),
  )
}

///|
fn parse_script_body_range_with_path(
  input : NormalizedInput,
  raw_src : String,
  tokens : Array[Token],
  start : Int,
  end : Int,
  branch_path : Array[Int],
  next_step_index : Int,
) -> Result[(SynScriptBody, Int), ParseError] {
  let steps : Array[SynScriptStep] = []
  let mut seg_start = start
  let mut step_index = next_step_index
  if seg_start < end && token_at(tokens, seg_start).kind is TkNewline {
    seg_start = seg_start + 1
  }
  if seg_start >= end {
    return Err(
      mk_parse_error(
        UnexpectedEof,
        if start < tokens.length() {
          token_at(tokens, start).offset
        } else {
          0
        },
        "empty theorem script body",
      ),
    )
  }
  if token_at(tokens, seg_start).kind is TkNewline {
    return Err(
      mk_parse_error(
        UnexpectedToken,
        token_at(tokens, seg_start).offset,
        "empty tactic step",
      ),
    )
  }
  while seg_start < end {
    let mut step_end = seg_start
    while step_end < end {
      match tokens[step_end].kind {
        TkSemi | TkNewline | TkLBrace | TkRBrace => break
        _ => step_end = step_end + 1
      }
    }
    if seg_start == step_end {
      let detail = match token_at(tokens, seg_start).kind {
        TkLBrace => "branch block must follow `split`, `left`, or `right`"
        TkRBrace => "unexpected `}`"
        _ => "empty tactic step"
      }
      return Err(
        mk_parse_error(
          UnexpectedToken,
          token_at(tokens, seg_start).offset,
          detail,
        ),
      )
    }
    step_index = step_index + 1
    let mut step = match
      parse_script_step_segment(
        input, raw_src, tokens, seg_start, step_end, step_index, branch_path,
      ) {
      Ok(v) => v
      Err(e) => return Err(e)
    }
    let expected_branches = expected_branch_count(step.step)
    let branches : Array[SynScriptBranch] = []
    let mut cursor = step_end
    while branches.length() < expected_branches {
      let branch_start = next_non_newline_token_index(tokens, cursor)
      if branch_start >= end {
        break
      }
      match tokens[branch_start].kind {
        TkLBrace => {
          let close_idx = match find_matching_brace(tokens, branch_start, end) {
            Ok(v) => v
            Err(e) => return Err(e)
          }
          let branch_idx = branches.length() + 1
          let child_path = child_branch_path(branch_path, branch_idx)
          let (body, next_index) = match
            parse_script_body_range_with_path(
              input,
              raw_src,
              tokens,
              branch_start + 1,
              close_idx,
              child_path,
              step_index,
            ) {
            Ok(v) => v
            Err(e) => return Err(e)
          }
          let span = map_source_span(
            input,
            tokens[branch_start].offset,
            token_normalized_end(tokens[close_idx]),
          )
          branches.push(SynScriptBranch::{
            branch_path: child_path.copy(),
            body,
            span,
            src: raw_source_slice(raw_src, span.start_offset, span.end_offset),
          })
          step_index = next_index
          cursor = close_idx + 1
        }
        _ => break
      }
    }
    if expected_branches == 0 &&
      cursor < end &&
      token_at(tokens, cursor).kind is TkLBrace {
      return Err(
        mk_parse_error(
          UnexpectedToken,
          token_at(tokens, cursor).offset,
          "tactic step does not accept structured branch blocks",
        ),
      )
    }
    if branches.length() != expected_branches &&
      cursor < end &&
      !(token_at(tokens, cursor).kind is TkSemi) &&
      !(token_at(tokens, cursor).kind is TkNewline) {
      if token_at(tokens, cursor).kind is TkRBrace {
        ()
      } else {
        return Err(
          mk_parse_error(
            UnexpectedToken,
            token_at(tokens, cursor).offset,
            "expected tactic separator or branch block",
          ),
        )
      }
    }
    if branches.length() != 0 && branches.length() != expected_branches {
      return Err(
        mk_parse_error(
          UnexpectedToken,
          tokens[seg_start].offset,
          "incorrect number of branch blocks for tactic step",
        ),
      )
    }
    step = SynScriptStep::{
      step: step.step,
      step_index: step.step_index,
      branch_path: step.branch_path,
      span: step.span,
      src: step.src,
      branches,
    }
    steps.push(step)
    if cursor >= end {
      break
    }
    match token_at(tokens, cursor).kind {
      TkSemi => {
        let next_idx = cursor + 1
        let mut seg_after = next_idx
        if seg_after < end && token_at(tokens, seg_after).kind is TkNewline {
          seg_after = seg_after + 1
        }
        if seg_after >= end {
          return Err(
            mk_parse_error(
              UnexpectedEof,
              tokens[cursor].offset,
              "empty theorem script body",
            ),
          )
        }
        if token_at(tokens, seg_after).kind is TkNewline ||
          token_at(tokens, seg_after).kind is TkSemi {
          return Err(
            mk_parse_error(
              UnexpectedToken,
              token_at(tokens, seg_after).offset,
              "empty tactic step",
            ),
          )
        }
        seg_start = seg_after
      }
      TkNewline => {
        if body_remainder_is_only_newlines(tokens, cursor, end) {
          break
        }
        seg_start = cursor + 1
        if seg_start >= end {
          break
        }
        if token_at(tokens, seg_start).kind is TkNewline {
          return Err(
            mk_parse_error(
              UnexpectedToken,
              token_at(tokens, seg_start).offset,
              "empty tactic step",
            ),
          )
        }
        if token_at(tokens, seg_start).kind is TkSemi ||
          token_at(tokens, seg_start).kind is TkRBrace {
          return Err(
            mk_parse_error(
              UnexpectedToken,
              token_at(tokens, seg_start).offset,
              "empty tactic step",
            ),
          )
        }
      }
      TkRBrace =>
        return Err(
          mk_parse_error(
            UnexpectedToken,
            tokens[cursor].offset,
            "expected tactic separator before `}`",
          ),
        )
      _ =>
        return Err(
          mk_parse_error(
            UnexpectedToken,
            tokens[cursor].offset,
            "expected tactic separator",
          ),
        )
    }
  }
  if steps.length() == 0 {
    Err(mk_parse_error(UnexpectedEof, 0, "empty theorem script body"))
  } else {
    Ok((SynScriptBody::{ steps, }, step_index))
  }
}

///|
fn parse_script_body_range(
  input : NormalizedInput,
  raw_src : String,
  tokens : Array[Token],
  start : Int,
  end : Int,
) -> Result[SynScriptBody, ParseError] {
  match
    parse_script_body_range_with_path(input, raw_src, tokens, start, end, [], 0) {
    Ok((body, _)) => Ok(body)
    Err(e) => Err(e)
  }
}

///|
fn parse_theorem_binder_segment(
  input : NormalizedInput,
  raw_src : String,
  tokens : Array[Token],
  start : Int,
  end : Int,
) -> Result[(SynBinder, Int), ParseError] {
  match token_at(tokens, start).kind {
    TkLParen => ()
    _ =>
      return Err(
        mk_parse_error(
          UnexpectedToken,
          token_at(tokens, start).offset,
          "expected `(` to start theorem binder",
        ),
      )
  }
  let name_idx = next_non_newline_token_index(tokens, start + 1)
  let name = match token_at(tokens, name_idx).kind {
    TkName(n) => n
    _ =>
      return Err(
        mk_parse_error(
          UnexpectedToken,
          token_at(tokens, name_idx).offset,
          "expected theorem binder name",
        ),
      )
  }
  let colon_idx = next_non_newline_token_index(tokens, name_idx + 1)
  match token_at(tokens, colon_idx).kind {
    TkColon => ()
    _ =>
      return Err(
        mk_parse_error(
          UnexpectedToken,
          token_at(tokens, colon_idx).offset,
          "expected `:` in theorem binder",
        ),
      )
  }
  let type_start = next_non_newline_token_index(tokens, colon_idx + 1)
  if type_start >= end || token_at(tokens, type_start).kind is TkRParen {
    return Err(
      mk_parse_error(
        UnexpectedToken,
        token_at(tokens, colon_idx).offset,
        "empty theorem binder type",
      ),
    )
  }
  let mut depth = 0
  let mut close_idx : Int? = None
  let mut i = type_start
  while i < end {
    match tokens[i].kind {
      TkLParen => depth = depth + 1
      TkRParen =>
        if depth == 0 {
          close_idx = Some(i)
          break
        } else {
          depth = depth - 1
        }
      _ => ()
    }
    i = i + 1
  }
  let k = match close_idx {
    Some(v) => v
    None =>
      return Err(
        mk_parse_error(
          UnexpectedEof,
          token_at(tokens, end - 1).offset,
          "missing `)` in theorem binder",
        ),
      )
  }
  let ty = match
    parse_type_tokens(
      slice_tokens_without_newlines_with_end(tokens, type_start, k),
    ) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let span = map_source_span(
    input,
    tokens[start].offset,
    token_normalized_end(tokens[k]),
  )
  Ok(
    (
      SynBinder::{
        name,
        ty,
        span,
        src: raw_source_slice(raw_src, span.start_offset, span.end_offset),
      },
      k + 1,
    ),
  )
}

///|
pub fn parse_theorem_script_raw(
  src : String,
) -> Result[SynTheoremScript, ParseError] {
  let input = match normalize_theorem_script_input(src) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let tokens = match lex_tokens_layout(input.text, true) {
    Ok(v) => v
    Err(e) => return Err(map_parse_error_offset(input, e))
  }
  let end_idx = tokens.length() - 1
  if end_idx < 5 {
    return Err(mk_parse_error(UnexpectedEof, 0, "incomplete theorem script"))
  }
  let body_end_idx = match last_non_newline_token_index(tokens, 0, end_idx) {
    Some(last_idx) =>
      if token_is_qed_terminator(tokens, last_idx, end_idx) {
        last_idx
      } else {
        end_idx
      }
    None => end_idx
  }
  match parse_theorem_script_range(input, src, tokens, 0, body_end_idx) {
    Ok(v) => Ok(v)
    Err(e) => Err(map_parse_error_offset(input, e))
  }
}

///|
fn parse_theorem_script_range(
  input : NormalizedInput,
  src : String,
  tokens : Array[Token],
  start_idx : Int,
  end_idx : Int,
) -> Result[SynTheoremScript, ParseError] {
  if end_idx - start_idx < 5 {
    return Err(
      mk_parse_error(
        UnexpectedEof,
        if start_idx < tokens.length() {
          token_at(tokens, start_idx).offset
        } else {
          0
        },
        "incomplete theorem script",
      ),
    )
  }
  let theorem_idx = next_non_newline_token_index(tokens, start_idx)
  match token_at(tokens, theorem_idx).kind {
    TkName("theorem") => ()
    _ =>
      return Err(
        mk_parse_error(
          UnexpectedToken,
          token_at(tokens, theorem_idx).offset,
          "expected `theorem`",
        ),
      )
  }
  let name_idx = next_non_newline_token_index(tokens, theorem_idx + 1)
  let name = match token_at(tokens, name_idx).kind {
    TkName(n) => n
    _ =>
      return Err(
        mk_parse_error(
          UnexpectedToken,
          token_at(tokens, name_idx).offset,
          "expected theorem name",
        ),
      )
  }
  let binders : Array[SynBinder] = []
  let mut colon_idx : Int? = None
  let mut header_idx = next_non_newline_token_index(tokens, name_idx + 1)
  while header_idx < end_idx {
    match token_at(tokens, header_idx).kind {
      TkColon => {
        colon_idx = Some(header_idx)
        break
      }
      TkLParen =>
        match
          parse_theorem_binder_segment(input, src, tokens, header_idx, end_idx) {
          Ok((binder, next_idx)) => {
            binders.push(binder)
            header_idx = next_non_newline_token_index(tokens, next_idx)
          }
          Err(e) => return Err(e)
        }
      _ =>
        return Err(
          mk_parse_error(
            UnexpectedToken,
            token_at(tokens, header_idx).offset,
            if binders.length() == 0 {
              "expected `:` after theorem name"
            } else {
              "expected theorem binder or `:` after theorem name"
            },
          ),
        )
    }
  }
  let colon_idx = match colon_idx {
    Some(v) => v
    None =>
      return Err(
        mk_parse_error(UnexpectedEof, 0, "missing `:` in theorem header"),
      )
  }

  let goal_start = next_non_newline_token_index(tokens, colon_idx + 1)
  let mut depth = 0
  let mut assign_idx : Int? = None
  let mut i = goal_start
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
    None => return Err(mk_parse_error(UnexpectedToken, 0, "missing `:=`"))
  }
  if k <= goal_start {
    return Err(
      mk_parse_error(
        EmptyConclusion,
        token_at(tokens, colon_idx).offset,
        "empty theorem goal",
      ),
    )
  }
  let by_idx = next_non_newline_token_index(tokens, k + 1)
  match token_at(tokens, by_idx).kind {
    TkName("by") => ()
    _ =>
      return Err(
        mk_parse_error(
          UnexpectedToken,
          token_at(tokens, by_idx).offset,
          "expected `by` after `:=`",
        ),
      )
  }

  let goal_src = tokens_to_src(tokens, goal_start, k)
  let goal_tokens = slice_tokens_without_newlines_with_end(
    tokens, goal_start, k,
  )
  let goal_last = match last_non_newline_token_index(tokens, goal_start, k) {
    Some(v) => v
    None =>
      return Err(
        mk_parse_error(
          EmptyConclusion,
          token_at(tokens, colon_idx).offset,
          "empty theorem goal",
        ),
      )
  }
  let goal_span = map_source_span(
    input,
    tokens[goal_start].offset,
    token_normalized_end(tokens[goal_last]),
  )
  let goal = match parse_goal_tokens(goal_tokens) {
    Ok(v) => v
    Err(e) => return Err(e)
  }

  let body = match
    parse_script_body_range(input, src, tokens, by_idx + 1, end_idx) {
    Ok(v) => v
    Err(e) => return Err(e)
  }

  Ok(SynTheoremScript::{ name, binders, goal, goal_src, goal_span, body })
}

///|
pub fn parse_theorem_file_raw(
  src : String,
) -> Result[Array[SynTheoremScript], ParseError] {
  let input = match normalize_theorem_script_input(src) {
    Ok(v) => v
    Err(e) => return Err(e)
  }
  let tokens = match lex_tokens_layout(input.text, true) {
    Ok(v) => v
    Err(e) => return Err(map_parse_error_offset(input, e))
  }
  let end_idx = tokens.length() - 1
  let scripts : Array[SynTheoremScript] = []
  let mut block_start = next_non_newline_token_index(tokens, 0)
  while block_start < end_idx {
    match token_at(tokens, block_start).kind {
      TkName("theorem") => ()
      _ =>
        return Err(
          map_parse_error_offset(
            input,
            mk_parse_error(
              UnexpectedToken,
              token_at(tokens, block_start).offset,
              "expected `theorem`",
            ),
          ),
        )
    }
    let mut depth = 0
    let mut cursor = block_start + 1
    let mut block_end = end_idx
    let mut terminated = false
    while cursor < end_idx {
      if depth == 0 && token_is_line_start(tokens, cursor) {
        match token_at(tokens, cursor).kind {
          TkName("qed") if token_is_qed_terminator(tokens, cursor, end_idx) => {
            block_end = cursor
            terminated = true
            break
          }
          TkName("theorem") =>
            return Err(
              map_parse_error_offset(
                input,
                mk_parse_error(
                  UnexpectedToken,
                  token_at(tokens, cursor).offset,
                  "missing qed before next theorem",
                ),
              ),
            )
          _ => ()
        }
      }
      match token_at(tokens, cursor).kind {
        TkLBrace => depth = depth + 1
        TkRBrace => if depth > 0 { depth = depth - 1 } else { () }
        _ => ()
      }
      cursor = cursor + 1
    }
    match
      parse_theorem_script_range(input, src, tokens, block_start, block_end) {
      Ok(script) => scripts.push(script)
      Err(e) => return Err(map_parse_error_offset(input, e))
    }
    if terminated {
      block_start = next_non_newline_token_index(tokens, cursor + 1)
    } else {
      block_start = end_idx
    }
  }
  if scripts.length() == 0 {
    Err(mk_parse_error(UnexpectedEof, 0, "incomplete theorem script"))
  } else {
    Ok(scripts)
  }
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
    Forall(_, _, _) =>
      Err(
        Parse(
          mk_parse_error(
            UnexpectedToken,
            0,
            "raw `forall` is only supported in goal syntax",
          ),
        ),
      )
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
fn lower_syn_goal_term_with_env(
  state : KernelState,
  env : ParseEnv,
  term : SynTerm,
) -> Result[Term, ParseBridgeError] {
  match term {
    Forall(name, ty, body) => {
      let body_env = parse_env_push_local(env, name, ty)
      lower_syn_goal_term_with_env(state, body_env, body)
    }
    _ => lower_syn_term_with_env(state, env, term)
  }
}

///|
fn lower_syn_term_shipped(
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
fn resolve_syn_goal_term_with_env(
  state : KernelState,
  env : ParseEnv,
  term : SynTerm,
) -> Result[RTerm, ParseBridgeError] {
  match term {
    Forall(name, ty, body) => {
      let body_env = parse_env_push_local(env, name, ty)
      resolve_syn_goal_term_with_env(state, body_env, body)
    }
    _ => resolve_syn_term(state, env, term)
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
    Forall(_, _, _) =>
      Err(
        Parse(
          mk_parse_error(
            UnexpectedToken,
            0,
            "raw `forall` is only supported in goal syntax",
          ),
        ),
      )
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
  lower_syn_term_shipped(state, env, term)
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
  match resolve_syn_goal_term_with_env(state, env, syn_goal.concl) {
    Ok(concl) => Ok(ResolvedGoal::{ hyps, concl })
    Err(e) => Err(e)
  }
}

///|
pub fn parse_goal_with_env(
  state : KernelState,
  env : ParseEnv,
  src : String,
) -> Result[ParsedGoal, ParseBridgeError] {
  match parse_goal_raw(src) {
    Ok(goal) => lower_syn_goal_with_env(state, env, goal)
    Err(e) => Err(Parse(e))
  }
}

///|
pub fn lower_syn_goal_with_env(
  state : KernelState,
  env : ParseEnv,
  syn_goal : SynGoal,
) -> Result[ParsedGoal, ParseBridgeError] {
  let hyps : Array[Term] = []
  for h in syn_goal.hyps {
    match lower_syn_term_with_env(state, env, h) {
      Ok(t) => hyps.push(t)
      Err(e) => return Err(e)
    }
  }
  match lower_syn_goal_term_with_env(state, env, syn_goal.concl) {
    Ok(concl) => Ok(ParsedGoal::{ hyps, concl })
    Err(e) => Err(e)
  }
}

///|
pub fn parse_goal(
  state : KernelState,
  src : String,
) -> Result[ParsedGoal, ParseBridgeError] {
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
  Ok(parse_env_push_local(env, name, ty))
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
