/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr
import Lean.Environment
import Lean.Util.FoldConsts

namespace Lean
namespace Expr

/-- Like `Expr.getUsedConstants`, but produce a `NameSet`. -/
def getUsedConstantsAsSet (e : Expr) : NameSet :=
  e.foldConsts {} fun c cs => cs.insert c

end Expr

/-- The union of two `NameSet`s. -/
def NameSet.append (s t : NameSet) : NameSet :=
  s.mergeBy (fun _ _ _ => .unit) t

instance : Append NameSet where
  append := NameSet.append

namespace ConstantInfo

/-- Return all names appearing in the type or value of a `ConstantInfo`. -/
def getUsedConstantsAsSet (c : ConstantInfo) : NameSet :=
  c.type.getUsedConstantsAsSet ++ match c.value? with
  | some v => v.getUsedConstantsAsSet
  | none => match c with
    | .inductInfo val => .ofList val.ctors
    | .opaqueInfo val => val.value.getUsedConstantsAsSet
    | .ctorInfo val => ({} : NameSet).insert val.name
    | .recInfo val => .ofList val.all
    | _ => {}

end ConstantInfo


end Lean
