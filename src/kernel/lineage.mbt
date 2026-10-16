///|
/// Declaration lineage as a persistent, hash-consed chain.
///
/// A kernel state records the events that produced it (root, push_scope,
/// add_const, definition, ...). A theorem records the lineage of the state in
/// which it was first admitted and stays admissible only in states whose lineage
/// extends it. The lineage used to be an array copied on every event and on every
/// theorem, and compared element by element, which made building a state
/// quadratic and every rule step linear in the length of the development.
///
/// Here every node is interned by `(parent id, event)`, so two histories that
/// perform the same events from the same parent share the node: structural
/// equality of lineages is node identity. Each node also keeps a skew-binary
/// jump pointer, so "is this node an ancestor of that one" is answered in
/// O(log depth). Appending an event and storing a lineage in a theorem are O(1).
///
/// The intern table is private to the kernel and only grows; it holds one small
/// node per distinct lineage event.
priv struct LineageNode {
  id : Int32
  depth : Int32
  parent : LineageNode?
  jump : LineageNode?
}

///|
let lineage_table : Map[(Int32, String), LineageNode] = Map([])

///|
let lineage_next_id : Ref[Int32] = Ref(0)

///|
/// The root of every lineage; its parent and jump pointer are itself.
fn lineage_root() -> LineageNode {
  let key = (-1, "root")
  match lineage_table.get(key) {
    Some(node) => node
    None => {
      let node = LineageNode::{
        id: lineage_next_id.val,
        depth: 1,
        parent: None,
        jump: None,
      }
      lineage_next_id.val = lineage_next_id.val + 1
      lineage_table[key] = node
      node
    }
  }
}

///|
fn lineage_jump_of(node : LineageNode) -> LineageNode {
  match node.jump {
    Some(j) => j
    None => node
  }
}

///|
/// Append `event` to `parent`, reusing the interned node when the same event was
/// already appended to the same parent.
fn lineage_append(parent : LineageNode, event : String) -> LineageNode {
  let key = (parent.id, event)
  match lineage_table.get(key) {
    Some(node) => node
    None => {
      // Skew-binary jump pointer: jump over a block as long as the two previous
      // jumps have the same length, otherwise point at the parent.
      let pj = lineage_jump_of(parent)
      let pjj = lineage_jump_of(pj)
      let jump = if parent.depth - pj.depth == pj.depth - pjj.depth {
        pjj
      } else {
        parent
      }
      let node = LineageNode::{
        id: lineage_next_id.val,
        depth: parent.depth + 1,
        parent: Some(parent),
        jump: Some(jump),
      }
      lineage_next_id.val = lineage_next_id.val + 1
      lineage_table[key] = node
      node
    }
  }
}

///|
/// The ancestor of `node` at depth `depth` (`depth <= node.depth`) and the number
/// of pointer hops it took. The skew-binary jump pointers bound the hops by
/// O(log depth).
fn lineage_ancestor_counted(
  node : LineageNode,
  depth : Int32,
) -> (LineageNode, Int32) {
  let mut cur = node
  let mut hops = 0
  while cur.depth > depth {
    let j = lineage_jump_of(cur)
    if j.depth >= depth {
      cur = j
    } else {
      match cur.parent {
        Some(p) => cur = p
        None => break
      }
    }
    hops += 1
  }
  (cur, hops)
}

///|
fn lineage_ancestor_at(node : LineageNode, depth : Int32) -> LineageNode {
  let (ancestor, _) = lineage_ancestor_counted(node, depth)
  ancestor
}

///|
/// Whether `origin` is `current` or one of its ancestors.
fn lineage_is_prefix(origin : LineageNode, current : LineageNode) -> Bool {
  if origin.depth > current.depth {
    return false
  }
  lineage_ancestor_at(current, origin.depth).id == origin.id
}
