/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Sync.CancellationToken
public import Init.Data.Ord.UInt

public section

/-!
This module provides a tree-structured cancellation context called `CancellationToken` where cancelling a parent
automatically cancels all child contexts.
-/

namespace Std
open Std.Async

structure CancellationContext.State where
  /--
  Map of token IDs to optional tokens and their children.
  -/
  tokens : TreeMap UInt64 (CancellationToken × Array UInt64) := .empty

  /--
  Next available ID
  -/
  id : UInt64 := 1

/--
A cancellation context that allows multiple consumers to wait until cancellation is requested. Forms
a tree structure where cancelling a parent cancels all children.
-/
structure CancellationContext where
  state : Std.Mutex CancellationContext.State
  token : CancellationToken
  id : UInt64

namespace CancellationContext

/--
Creates a new root cancellation context.
-/
def new : BaseIO CancellationContext := do
  let token ← Std.CancellationToken.new
  return {
    state := ← Std.Mutex.new { tokens := .empty |>.insert 0 (token, #[]) },
    token,
    id := 0
  }

/--
Forks a child context from a parent. If the parent is already cancelled, returns the parent context.
Otherwise, creates a new child that will be cancelled when the parent is cancelled.
-/
def fork (root : CancellationContext) : BaseIO CancellationContext := do
  root.state.atomically do
    if ← root.token.isCancelled then
      return root

    let token ← Std.CancellationToken.new

    let st ← get
    let newId := st.id
    -- The live map bounds the number of live direct children. At this threshold at least
    -- half of the stored IDs are stale, so scans are charged to the IDs they remove.
    let tokens := st.tokens.modify root.id fun (token, children) =>
      let children := if children.size ≥ 2 * st.tokens.size then
          children.filter fun id => st.tokens.contains id
        else
          children
      (token, children.push newId)

    set { st with
      id := newId + 1,
      tokens := tokens.insert newId (token, #[])
    }

    return { state := root.state, token, id := newId }

/--
Recursively cancels a context and all its children with the given reason.
-/
private partial def cancelChildren (state : CancellationContext.State) (id : UInt64) (reason : CancellationReason) : BaseIO CancellationContext.State := do
  let mut state := state

  let some (token, children) := state.tokens.get? id
    | return state

  for tokenId in children do
    state ← cancelChildren state tokenId reason

  token.cancel reason

  pure { state with tokens := state.tokens.erase id }

/--
Cancels this context and all child contexts with the given reason.
-/
def cancel (x : CancellationContext) (reason : CancellationReason) : BaseIO Unit := do
  if ← x.token.isCancelled then
    return

  x.state.atomically do
    let st ← get
    let st ← cancelChildren st x.id reason
    set st

/--
Checks if the context is cancelled.
-/
@[inline]
def isCancelled (x : CancellationContext) : BaseIO Bool := do
  x.token.isCancelled

/--
Returns the cancellation reason if the context is cancelled.
-/
@[inline]
def getCancellationReason (x : CancellationContext) : BaseIO (Option CancellationReason) := do
  x.token.getCancellationReason

/--
Waits for cancellation. Returns a task that completes when the context is cancelled.
-/
@[inline]
def done (x : CancellationContext) : IO (AsyncTask Unit) :=
  x.token.wait

/--
Creates a selector that waits for cancellation.
-/
@[inline]
def doneSelector (x : CancellationContext) : Selector Unit :=
  x.token.selector

private partial def countAliveTokensRec (state : CancellationContext.State) (id : UInt64) :
    CancellationContext.State × Nat := Id.run do
  let some (token, children) := state.tokens.get? id
    | return (state, 0)
  let mut state := state
  let mut count := 1
  let mut hasDeadChildren := false
  for childId in children do
    let (nextState, childCount) := countAliveTokensRec state childId
    state := nextState
    count := count + childCount
    if childCount == 0 then hasDeadChildren := true
  if hasDeadChildren then
    let children := children.filter fun childId => state.tokens.contains childId
    state := { state with tokens := state.tokens.insert id (token, children) }
  return (state, count)

/--
Counts the number of alive (non-cancelled) tokens in the context tree, including
this context and all its descendants. Also removes stale child IDs in the visited subtree,
so later counts do not repeatedly traverse already-cancelled children.
-/
def countAliveTokens (x : CancellationContext) : BaseIO Nat := do
  x.state.atomically do
    let (st, count) := countAliveTokensRec (← get) x.id
    set st
    return count

end CancellationContext
end Std
