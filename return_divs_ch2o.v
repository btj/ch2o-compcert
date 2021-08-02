Require Export String.
Require Export ch2o.abstract_c.frontend.

Local Open Scope string_scope.

Definition decls: list (string * decl) :=
  [("main",
    FunDecl [] (CTFun [] (CTInt (CIntType None CIntRank)))
      (CSReturn
        (Some
          (CEBinOp (ArithOp DivOp)
            (CEBinOp (ArithOp DivOp)
              (CEConst (CIntType (Some Signed) CIntRank) 17)
              (CEConst (CIntType (Some Signed) CIntRank) 2))
            (CEBinOp (ArithOp DivOp)
              (CEConst (CIntType (Some Signed) CIntRank) 15)
              (CEConst (CIntType (Some Signed) CIntRank) 5))))))].
