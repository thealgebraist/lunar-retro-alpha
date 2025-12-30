(* Simplified Zig AST in Coq *)
Require Import String.
Require Import List.
Import ListNotations.

Inductive TypeExpr : Type :=
| TInt (bits : nat) (signed : bool)
| TFloat (bits : nat)
| TBool
| TVoid
| TUsize
| TPtr (t : TypeExpr) (const : bool)
| TArray (t : TypeExpr) (len : option nat)
| TStruct (name : string)
| TEnum (name : string)
| TOptional (t : TypeExpr)
| TFn (args : list TypeExpr) (ret : TypeExpr).

Inductive BinOp : Type :=
| Add | Sub | Mul | Div | Mod
| Eq | Ne | Lt | Gt | Le | Ge
| And | Or.

Inductive Expr : Type :=
| ELitInt (v : nat)
| ELitFloat (v : string)
| ELitNull
| ELitEnum (enum_name : string) (member : string)
| EVar (name : string)
| EField (obj : Expr) (field : string)
| EMember (enum_val : Expr) (field : string) (* for accessing enum fields if any, or just EField *)
| EBinOp (op : BinOp) (e1 e2 : Expr)
| ECall (func : string) (args : list Expr)
| EStructLiteral (struct_name : string) (fields : list (string * Expr))
| EArrayLiteral (elems : list Expr)
| ECast (t : TypeExpr) (e : Expr)
| EOptionalCheck (e : Expr) (is_null : bool)
| EImport (path : string)
| EEmbedFile (path : string)
| EAddrOf (e : Expr)
| EDeref (e : Expr)
| ETry (e : Expr)
| EOrelse (e1 e2 : Expr)
| EMethodCall (obj : Expr) (method : string) (args : list Expr).

Inductive Stmt : Type :=
| SVarDecl (export : bool) (const : bool) (name : string) (t : option TypeExpr) (init : Expr)
| SAssign (lhs : Expr) (rhs : Expr)
| SIf (cond : Expr) (then_b : list Stmt) (else_b : option (list Stmt))
| SWhile (cond : Expr) (body : list Stmt)
| SReturn (e : option Expr)
| SExpr (e : Expr)
| SSwitch (e : Expr) (cases : list (list Expr * list Stmt)) (default : option (list Stmt))
| SInlineFor (iter : string) (list_expr : Expr) (body : list Stmt)
| SFor (iter : string) (list_expr : Expr) (body : list Stmt)
| SBreak
| SContinue.

Inductive Decl : Type :=
| DExternFn (name : string) (args : list (string * TypeExpr)) (ret : TypeExpr)
| DFn (export : bool) (name : string) (args : list (string * TypeExpr)) (ret : TypeExpr) (body : list Stmt)
| DStruct (name : string) (fields : list (string * TypeExpr))
| DEnum (name : string) (members : list string)
| DGlobal (export : bool) (const : bool) (name : string) (t : TypeExpr) (init : Expr).

Definition Program := list Decl.
