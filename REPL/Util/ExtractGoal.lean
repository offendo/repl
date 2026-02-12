/-
Copyright (c) 2024 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean
--import REPL.Util.Cleanup

open Lean Lean.Meta

section Inaccessible
/-!
These come from `Std.Lean.Meta.Inaccessible`
-/

/--
Obtain the inaccessible fvars from the given local context. An fvar is
inaccessible if (a) its user name is inaccessible or (b) it is shadowed by a
later fvar with the same user name.
-/
def Lean.LocalContext.inaccessibleFVars (lctx : LocalContext) :
    Array LocalDecl :=
  let (result, _) :=
    lctx.foldr (β := Array LocalDecl × Std.HashSet Name)
      (init := (Array.mkEmpty lctx.numIndices, {}))
      λ ldecl (result, seen) =>
        if ldecl.isImplementationDetail then
          (result, seen)
        else
          let result :=
            if ldecl.userName.hasMacroScopes || seen.contains ldecl.userName then
              result.push ldecl
            else
              result
          (result, seen.insert ldecl.userName)
  result.reverse

/--
Obtain the inaccessible fvars from the current local context. An fvar is
inaccessible if (a) its user name is inaccessible or (b) it is shadowed by a
later fvar with the same user name.
-/
def Lean.Meta.getInaccessibleFVars [Monad m] [MonadLCtx m] :
    m (Array LocalDecl) :=
  return (← getLCtx).inaccessibleFVars

/--
Rename all inaccessible fvars. An fvar is inaccessible if (a) its user name is
inaccessible or (b) it is shadowed by a later fvar with the same user name. This
function gives all inaccessible fvars a unique, accessible user name. It returns
the new goal and the fvars that were renamed.
-/
def Lean.MVarId.renameInaccessibleFVars (mvarId : MVarId) :
    MetaM (MVarId × Array FVarId) := do
  let mdecl ← mvarId.getDecl
  let mut lctx := mdecl.lctx
  let inaccessibleFVars := lctx.inaccessibleFVars
  if inaccessibleFVars.isEmpty then
    return (mvarId, #[])
  let mut renamedFVars := Array.mkEmpty lctx.decls.size
  for ldecl in inaccessibleFVars do
    -- Edit(kmill): made it only do non-inst-implicits
    if ldecl.binderInfo != .instImplicit then
      let newName := lctx.getUnusedName ldecl.userName
      lctx := lctx.setUserName ldecl.fvarId newName
      renamedFVars := renamedFVars.push ldecl.fvarId
  let newMVar ← mkFreshExprMVarAt lctx mdecl.localInstances mdecl.type
  mvarId.assign newMVar
  return (newMVar.mvarId!, renamedFVars)

end Inaccessible

namespace REPL.Util

open Lean Elab Tactic

open PrettyPrinter Delaborator SubExpr
open Lean.Parser.Term

open TSyntax.Compat in
partial def delabSignature' (idStx : Ident)  : Delab := do
  let e ← getExpr
  descend (← inferType e) 1 <|
    delabParams {} #[]
where
  /--
  For types in the signature, we want to be sure pi binder types are pretty printed.
  -/
  delabTy : DelabM Term := withOptions (pp.piBinderTypes.set · true) delab
  /-
  Similar to `delabBinders`, but does not uniquify binder names (since for named arguments we want to know the name),
  and it always merges binder groups when possible.
  Once it reaches a binder with an inaccessible name, or a name that has already been used,
  the remaining binders appear in pi types after the `:` of the declaration.
  -/
  delabParams (bindingNames : NameSet) (groups : TSyntaxArray ``bracketedBinder) := do
    let e ← getExpr
    if e.isForall && e.binderInfo.isInstImplicit && e.bindingName!.hasMacroScopes then
      -- Assumption: this instance can be found by instance search, so it does not need to be named.
      -- The oversight here is that this inaccessible name can appear in the pretty printed expression.
      -- We could check to see whether the instance appears in the type and avoid omitting the instance name,
      -- but this would be the usual case.
      let group ← withBindingDomain do `(bracketedBinderF|[$(← delabTy)])
      withBindingBody e.bindingName! <| delabParams bindingNames (groups.push group)
    else if e.isForall && !e.bindingName!.hasMacroScopes && !bindingNames.contains e.bindingName! then
      delabParamsAux bindingNames groups #[]
    else
      let type ← delabTy
      `(declSigWithId| $idStx:ident $groups* : $type)
  /--
  Inner loop for `delabParams`, collecting binders.
  Invariants:
  - The current expression is a forall.
  - It has a name that's not inaccessible.
  - It has a name that hasn't been used yet.
  -/
  delabParamsAux (bindingNames : NameSet) (groups : TSyntaxArray ``bracketedBinder) (curIds : Array Ident) := do
    let e@(.forallE n d e' i) ← getExpr | unreachable!
    let bindingNames := bindingNames.insert n
    let stxN := mkIdent n
    let curIds := curIds.push ⟨stxN⟩
    if shouldGroupWithNext bindingNames e e' then
      withBindingBody n <| delabParamsAux bindingNames groups curIds
    else
      let group ← withBindingDomain do
        match i with
        | .implicit       => `(bracketedBinderF|{$curIds* : $(← delabTy)})
        | .strictImplicit => `(bracketedBinderF|⦃$curIds* : $(← delabTy)⦄)
        | .instImplicit   => `(bracketedBinderF|[$stxN : $(← delabTy)])
        | _ =>
          if d.isOptParam then
            `(bracketedBinderF|($curIds* : $(← withAppFn <| withAppArg delabTy) := $(← withAppArg delabTy)))
          else if let some (.const tacticDecl _) := d.getAutoParamTactic? then
            let tacticSyntax ← ofExcept <| evalSyntaxConstant (← getEnv) (← getOptions) tacticDecl
            `(bracketedBinderF|($curIds* : $(← withAppFn <| withAppArg delabTy) := by $tacticSyntax))
          else
            `(bracketedBinderF|($curIds* : $(← delabTy)))
      withBindingBody n <| delabParams bindingNames (groups.push group)
  /-
  Given the forall `e` with body `e'`, determines if the binder from `e'` (if it is a forall) should be grouped with `e`'s binder.
  -/
  shouldGroupWithNext (bindingNames : NameSet) (e e' : Expr) : Bool :=
    e'.isForall &&
    -- At the first sign of an inaccessible name, stop merging binders:
    !e'.bindingName!.hasMacroScopes &&
    -- If it's a name that has already been used, stop merging binders:
    !bindingNames.contains e'.bindingName! &&
    e.binderInfo == e'.binderInfo &&
    e.bindingDomain! == e'.bindingDomain! &&
    -- Inst implicits can't be grouped:
    e'.binderInfo != BinderInfo.instImplicit

/-- Pretty-prints type of `e` as a signature `idStx <params> : <type>`. -/
def ppSignature' (idStx : Ident) (e : Expr) : MetaM FormatWithInfos := do
  let (stx, infos) ← delabCore e (delab := delabSignature' idStx )
  return ⟨← ppTerm ⟨stx⟩, infos⟩  -- HACK: not a term

/--
`extract_goal` formats the current goal as a stand-alone theorem or definition,
and `extract_goal name` uses the name `name` instead of an autogenerated one.

It tries to produce an output that can be copy-pasted and just work,
but its success depends on whether the expressions are amenable
to being unambiguously pretty printed.

By default it cleans up the local context. To use the full local context, use `extract_goal*`.

The tactic responds to pretty printing options.
For example, `set_option pp.all true in extract_goal` gives the `pp.all` form.
-/
def extractGoal (g : MVarId) (cleanup := false) (name? : Option Name := none) : MetaM MessageData := do
  let name ←
    match name? with
    | some name => pure name
    | none => mkAuxDeclName ((← getCurrNamespace) ++ `extracted)
  withoutModifyingEnv <| withoutModifyingState <| do
    let g ← if cleanup then g.cleanup else pure g
    let (g, _) ← g.renameInaccessibleFVars
    g.withContext do
      let fvarIds ← (← g.getDecl).lctx.getFVarIds.filterM fun fvarId => return !(← fvarId.getDecl).isAuxDecl
      let (_, g) ← g.revert (clearAuxDeclsInsteadOfRevert := true) fvarIds
      let ty ← instantiateMVars (← g.getType)
      let initLevels := (collectLevelParams {} ty).params
      let ty ← Term.TermElabM.run' (s := {levelNames := initLevels.reverse.toList}) do Term.levelMVarToParam ty
      let e ← mkFreshExprMVar ty
      let sig ← addMessageContext <|
        MessageData.ofFormatWithInfosM do
          ppSignature' (mkIdent name) e

      -- let sig ← addMessageContext <| MessageData.lazy fun ctx => MessageData.ofFormatWithInfosM <$> (ctx.runMetaM <| ppSignature' (mkIdent name) e)
      -- let sig ← addMessageContext <| MessageData.ofFormatWithInfos { pp := fun
      --             | some ctx => ctx.runMetaM <| ppSignature' (mkIdent name) e
      --             | none     => unreachable!
      --           }
      let cmd := if ← Meta.isProp ty then "theorem" else "def"
      addMessageContext m!"{cmd} {sig} := sorry"
