Require Export String.
Require Export ch2o.abstract_c.frontend.

Local Open Scope string_scope.

Definition decls: list (string * decl) :=
  [("main",
    FunDecl [] (CTFun [] (CTInt (CIntType None CIntRank)))
      (CSReturn (Some (CEConst (CIntType (Some Signed) CIntRank) 42))))].


