Require Export String.
Require Export ch2o.abstract_c.frontend.

Local Open Scope string_scope.

Definition decls: list (string * decl) :=
  [("main",
    FunDecl [] (CTFun [] (CTInt (CIntType None CIntRank)))
      (CSLocal [] "x" (CTInt (CIntType None CIntRank)) None
        (CSLocal [] "y" (CTInt (CIntType None CIntRank)) None
          (CSLocal [] "z" (CTInt (CIntType None CIntRank)) None
            (CSComp
              (CSDo
                (CEAssign Assign (CEVar "x")
                  (CEBinOp (ArithOp DivOp)
                    (CEConst (CIntType (Some Signed) CIntRank) 17)
                    (CEConst (CIntType (Some Signed) CIntRank) 2))))
              (CSComp
                (CSDo
                  (CEAssign Assign (CEVar "y")
                    (CEBinOp (ArithOp DivOp)
                      (CEConst (CIntType (Some Signed) CIntRank) 15)
                      (CEConst (CIntType (Some Signed) CIntRank) 5))))
                (CSComp
                  (CSDo
                    (CEAssign Assign (CEVar "z")
                      (CEBinOp (ArithOp DivOp) (CEVar "x") (CEVar "y"))))
                  (CSReturn (Some (CEVar "z"))))))))))].
