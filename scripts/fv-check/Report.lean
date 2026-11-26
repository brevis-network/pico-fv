import PicoFV64

/-! Prints, for each theorem named in `theorems.d/*.txt`, the axioms it depends on and its
statement, in a line-oriented form that `check.sh` compares against the whitelist and
the committed signature snapshot.

It also prints a `DEFINITION <name> <fingerprint>` line for every constant of this repository
that the statements reach, following definition bodies (and theorem statements, but not their
proofs). The walk stops at constants from other packages (Lean, Mathlib, the Sail model, the
constraint framework): `lake-manifest.json` pins those. Constructors and recursors are folded
into their inductive type.

A fingerprint hashes the constant's type and value with every reference to another reached
constant replaced by that constant's fingerprint, and with binder names left out. It does not
depend on any name from this repository, so a rename changes only the line's name, and a change
anywhere below a definition changes the fingerprints of the definitions above it. The only
cycles are the members of one (mutual) inductive type: they are hashed together, each reference
inside the group standing for the member's position. -/

open Lean Elab Command Meta

namespace FVReport

/-- Whether `n` was declared in this repository, rather than in a pinned dependency. -/
def isLocal (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i =>
    let root := env.header.moduleNames[i.toNat]!.getRoot
    root == `PicoFV || root == `PicoFV64
  | none => false

/-- The node a local constant is hashed under: an inductive group by its first member, and a
constructor or recursor by its inductive's group; otherwise the constant itself. -/
def node (env : Environment) (n : Name) : Name :=
  match env.find? n with
  | some (.inductInfo i) => i.all.head!
  | some (.ctorInfo c) =>
    match env.find? c.induct with
    | some (.inductInfo i) => i.all.head!
    | _ => c.induct
  | some (.recInfo r) => r.all.head!
  | _ => n

def mix (h : UInt64) (xs : List UInt64) : UInt64 := xs.foldl mixHash h

def str (s : String) : UInt64 := hash s

/-- The expressions a node's fingerprint covers, after its kind. -/
def nodeExprs (env : Environment) (n : Name) : Except String (List Expr) :=
  match env.find? n with
  | some (.defnInfo d) => .ok [d.type, d.value]
  | some (.thmInfo t) => .ok [t.type]
  | some (.inductInfo i) => .ok <| i.all.flatMap fun m =>
      match env.find? m with
      | some (.inductInfo j) => j.type :: j.ctors.filterMap fun c => (env.find? c).map (·.type)
      | _ => []
  | some (.opaqueInfo _) => .error s!"{n} is opaque: it cannot be fingerprinted"
  | some (.axiomInfo _) => .error s!"{n} is an axiom"
  | some (.quotInfo _) => .error s!"{n} is a quotient primitive"
  | some _ => .error s!"{n} is a constructor or recursor, not a node"
  | none => .error s!"{n} is not in the environment"

/-- The local nodes a node refers to, itself excluded. -/
def deps (env : Environment) (n : Name) : Except String (Array Name) := do
  let mut out : NameSet := {}
  for e in ← nodeExprs env n do
    for c in e.getUsedConstants do
      if isLocal env c then
        let m := node env c
        if m != n then out := out.insert m
  return out.toArray

/-- Hashes a universe level; a parameter stands for its position in the declaration. -/
partial def hashLevel (ps : List Name) : Level → UInt64
  | .zero => 11
  | .succ l => mix 12 [hashLevel ps l]
  | .max a b => mix 13 [hashLevel ps a, hashLevel ps b]
  | .imax a b => mix 14 [hashLevel ps a, hashLevel ps b]
  | .param p => mix 15 [(ps.idxOf p).toUInt64]
  | .mvar _ => 16

structure Ctx where
  env : Environment
  /-- Fingerprints of the nodes already hashed. -/
  fps : NameMap UInt64
  /-- The members of the inductive group being hashed, in declaration order. -/
  group : List Name
  /-- The universe parameters of the declaration being hashed. -/
  params : List Name

/-- What a reference to the constant `c` contributes to a hash. -/
def refHash (ctx : Ctx) (c : Name) : Except String UInt64 := do
  let env := ctx.env
  if !isLocal env c then return mix 21 [str c.toString]
  let base (m : Name) : Except String UInt64 :=
    match ctx.group.idxOf? m with
    | some i => .ok (mix 22 [i.toUInt64])
    | none => match ctx.fps.find? m with
      | some h => .ok h
      | none => .error s!"{m} is referenced before it is fingerprinted"
  match env.find? c with
  | some (.ctorInfo k) => return mix 23 [← base k.induct, k.cidx.toUInt64]
  | some (.recInfo _) => return mix 24 [← base c.getPrefix, str (c.componentsRev.head!.toString)]
  | _ => base c

abbrev HashM := StateT (Std.HashMap Expr UInt64) (Except String)

/-- Hashes an expression, caching shared subterms. Binder names and metadata are left out. -/
partial def hashExpr (ctx : Ctx) (e : Expr) : HashM UInt64 := do
  if let some h := (← get).get? e then return h
  let ps := ctx.params
  let h ← match e with
    | .bvar i => pure (mix 31 [i.toUInt64])
    | .sort l => pure (mix 32 [hashLevel ps l])
    | .const c ls => do
      let r ← liftExcept (refHash ctx c)
      pure (mix 33 (r :: ls.map (hashLevel ps)))
    | .app f a => return mix 34 [← hashExpr ctx f, ← hashExpr ctx a]
    | .lam _ t b bi => return mix 35 [← hashExpr ctx t, ← hashExpr ctx b, hash bi]
    | .forallE _ t b bi => return mix 36 [← hashExpr ctx t, ← hashExpr ctx b, hash bi]
    | .letE _ t v b _ => return mix 37 [← hashExpr ctx t, ← hashExpr ctx v, ← hashExpr ctx b]
    | .lit (.natVal n) => pure (mix 38 [str (toString n)])
    | .lit (.strVal s) => pure (mix 39 [str s])
    | .mdata _ b => hashExpr ctx b
    | .proj s i b => return mix 40 [← liftExcept (refHash ctx s), i.toUInt64, ← hashExpr ctx b]
    | .fvar _ | .mvar _ => throw s!"free or meta variable in a declaration"
  modify (·.insert e h)
  return h

/-- The fingerprints of a node's members: one for a definition or theorem, one per member for an
inductive group. -/
def hashNode (env : Environment) (fps : NameMap UInt64) (n : Name) :
    Except String (List (Name × UInt64)) := do
  match env.find? n with
  | some (.inductInfo i) =>
    let ctx : Ctx := { env, fps, group := i.all, params := i.levelParams }
    let mut acc : List UInt64 := [str "inductive", i.all.length.toUInt64]
    for m in i.all do
      let some (.inductInfo j) := env.find? m | throw s!"{m} is not an inductive"
      acc := acc ++ [j.numParams.toUInt64, j.numIndices.toUInt64, j.ctors.length.toUInt64]
      let (h, _) ← (hashExpr ctx j.type).run {}
      acc := acc ++ [h]
      for c in j.ctors do
        let some (.ctorInfo k) := env.find? c | throw s!"{c} is not a constructor"
        let (h, _) ← (hashExpr ctx k.type).run {}
        acc := acc ++ [k.numFields.toUInt64, h]
    let g := mix 0 acc
    return i.all.zipIdx.map fun (m, k) => (m, mix 41 [g, k.toUInt64])
  | some ci =>
    let ctx : Ctx := { env, fps, group := [], params := ci.levelParams }
    let tag := match ci with
      | .defnInfo _ => "definition" | .thmInfo _ => "theorem" | _ => "other"
    let mut acc : List UInt64 := [str tag]
    for e in ← nodeExprs env n do
      let (h, _) ← (hashExpr ctx e).run {}
      acc := acc ++ [h]
    return [(n, mix 0 acc)]
  | none => throw s!"{n} is not in the environment"

/-- Fingerprints every local node reached from `roots`, dependencies first (an iterative
depth-first walk, so a long chain of definitions cannot overflow the stack). -/
def fingerprints (env : Environment) (roots : Array Name) : Except String (NameMap UInt64) := do
  let mut fps : NameMap UInt64 := {}
  let mut done : NameSet := {}
  let mut onPath : NameSet := {}
  -- each frame: a node and the dependencies it has still to visit
  let mut stack : Array (Name × Array Name) := #[]
  for r in roots do
    if done.contains r then continue
    stack := stack.push (r, ← deps env r)
    onPath := onPath.insert r
    while stack.size > 0 do
      let (n, ds) := stack.back!
      if ds.size > 0 then
        let d := ds.back!
        stack := stack.set! (stack.size - 1) (n, ds.pop)
        if done.contains d then continue
        if onPath.contains d then throw s!"cycle through {d} and {n}: not one inductive group"
        stack := stack.push (d, ← deps env d)
        onPath := onPath.insert d
      else
        for (m, fp) in ← hashNode env fps n do fps := fps.insert m fp
        done := done.insert n
        onPath := onPath.erase n
        stack := stack.pop
  return fps

/-- A fingerprint as 16 hexadecimal digits. -/
def hex (h : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 h.toNat)
  "".pushn '0' (16 - s.length) ++ s

end FVReport

elab "#fv_report " dir:str : command => do
  let files := (← System.FilePath.readDir dir.getString).map (·.path)
    |>.filter (·.extension == some "txt") |>.qsort (·.toString < ·.toString)
  let mut names := #[]
  for file in files do
    names := names ++ (← IO.FS.lines file).filter (·.trim ≠ "")
  let env ← getEnv
  let mut roots : NameSet := {}
  for line in names do
    let n := line.trim.toName
    match env.find? n with
    | none => IO.println s!"MISSING {n}"
    | some ci =>
      let axs ← collectAxioms n
      let axs := axs.map toString |>.qsort (· < ·)
      IO.println s!"AXIOMS {n} {String.intercalate "," axs.toList}"
      let ty ← liftTermElabM do return (← ppExpr ci.type).pretty 100000
      IO.println s!"SIGNATURE {n} {ty.replace "\n" " "}"
      for c in ci.type.getUsedConstants do
        if FVReport.isLocal env c then roots := roots.insert (FVReport.node env c)
  match FVReport.fingerprints env roots.toArray with
  | .error msg => IO.println s!"DEFINITION-ERROR {msg}"
  | .ok fps =>
    for (n, fp) in fps do
      let key := n.toString
      if key.any (·.isWhitespace) then
        IO.println s!"DEFINITION-ERROR the name {key} contains a space"
      else IO.println s!"DEFINITION {key} {FVReport.hex fp}"

#fv_report "scripts/fv-check/theorems.d"
