import Freigen

/-! Golden serialized ASTs for every reflector-backed example in `Freigen.Examples`.
Each guard deliberately records the complete serialized tree. -/

namespace Freigen.Ast.SerializedExamples

/--
info: (program nat
  (def def0 (env1 unit) (x2 nat) nat
    (block
      (source Freigen.Examples.Circuit.Basic 112 0 115 8
        (block
          (let v3 nat (mul x2 x2))
          (let v4 bool (le x2 v3))
          (let v5 unit
            (op assert v4)
          )
          (let v6 nat (mul x2 x2))
          (ret v6)
        )
      )
    )
  )
  (def def7 (env8 unit) (x9 nat) nat
    (block
      (source Freigen.Examples.Circuit.Basic 117 0 122 18
        (block
          (let v10 nat (lit 0))
          (let v11 bool (eq x9 v10))
          (let v12 nat (if v11
            (block
              (let v13 nat (lit 0))
              (ret v13)
            )
            (block
              (let v14 nat (lit 1))
              (let v15 nat (sub x9 v14))
              (let v16 unit (lit unit))
              (let f17 (fn nat nat) (closure def7 v16))
              (let v18 nat (app f17 v15))
              (let v19 nat (lit 1))
              (let v20 nat (add v15 v19))
              (let v21 unit (lit unit))
              (let f22 (fn nat nat) (closure def0 v21))
              (let v23 nat (app f22 v20))
              (let v24 nat (add v18 v23))
              (ret v24)
            )
          ))
          (ret v12)
        )
      )
    )
  )
  (main ()
    (block
      (source Freigen.Examples.Circuit.Basic 132 35 132 42
        (block
          (source Freigen.Examples.Circuit.Basic 124 0 128 8
            (block
              (let v25 nat (lit 3))
              (let v26 unit (lit unit))
              (let f27 (fn nat nat) (closure def7 v26))
              (let v28 nat (app f27 v25))
              (let v29 unit (lit unit))
              (let v31 nat
                (op hint v29
                  (branch b30
                    (block
                      (ret v28)
                    )
                  )
                )
              )
              (let v32 bool (eq v31 v28))
              (let v33 unit
                (op assert v32)
              )
              (ret v31)
            )
          )
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Example.circRender Example.mainMacroReflected.1

/--
info: (program nat
  (def def0 (env1 unit) (x2 nat) nat
    (block
      (source Freigen.Examples.Circuit.Basic 112 0 115 8
        (block
          (let v3 nat (mul x2 x2))
          (let v4 bool (le x2 v3))
          (let v5 unit
            (op assert v4)
          )
          (let v6 nat (mul x2 x2))
          (ret v6)
        )
      )
    )
  )
  (main ()
    (block
      (source Freigen.Examples.Circuit.Basic 144 40 144 58
        (block
          (source Freigen.Examples.Circuit.Basic 138 0 140 15
            (block
              (let v7 unit (lit unit))
              (let v10 nat
                (op hint v7
                  (branch b8
                    (block
                      (let v9 nat (lit 4))
                      (ret v9)
                    )
                  )
                )
              )
              (let v11 unit (lit unit))
              (let f12 (fn nat nat) (closure def0 v11))
              (let v13 nat (app f12 v10))
              (ret v13)
            )
          )
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Example.circRender Example.symbolicHelperReflected.1

/--
info: (program nat
  (def def0 (env1 unit) (x2 nat) nat
    (block
      (source Freigen.Examples.Circuit.Basic 112 0 115 8
        (block
          (let v3 nat (mul x2 x2))
          (let v4 bool (le x2 v3))
          (let v5 unit
            (op assert v4)
          )
          (let v6 nat (mul x2 x2))
          (ret v6)
        )
      )
    )
  )
  (main ()
    (block
      (source Freigen.Examples.Circuit.Basic 146 35 146 53
        (block
          (source Freigen.Examples.Circuit.Basic 138 0 140 15
            (block
              (let v7 unit (lit unit))
              (let v10 nat
                (op hint v7
                  (branch b8
                    (block
                      (let v9 nat (lit 4))
                      (ret v9)
                    )
                  )
                )
              )
              (let v11 unit (lit unit))
              (let f12 (fn nat nat) (closure def0 v11))
              (let v13 nat (app f12 v10))
              (ret v13)
            )
          )
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Example.circRender Example.symbolicHelperNamed

/--
info: (program nat
  (def def0 (env1 unit) (x2 nat) nat
    (block
      (source Freigen.Examples.Circuit.Basic 148 0 152 29
        (block
          (let v3 nat (lit 0))
          (let v4 bool (eq x2 v3))
          (let v5 nat (if v4
            (block
              (let v6 nat (lit 0))
              (ret v6)
            )
            (block
              (let v7 nat (lit 1))
              (let v8 nat (sub x2 v7))
              (let v9 unit (lit unit))
              (let f10 (fn nat nat) (closure def0 v9))
              (let v11 nat (app f10 v8))
              (let v12 nat (add v11 v8))
              (let v13 nat (lit 1))
              (let v14 nat (add v12 v13))
              (ret v14)
            )
          ))
          (ret v5)
        )
      )
    )
  )
  (main ()
    (block
      (source Freigen.Examples.Circuit.Basic 160 42 160 63
        (block
          (source Freigen.Examples.Circuit.Basic 154 0 156 17
            (block
              (let v15 unit (lit unit))
              (let v18 nat
                (op hint v15
                  (branch b16
                    (block
                      (let v17 nat (lit 5))
                      (ret v17)
                    )
                  )
                )
              )
              (let v19 unit (lit unit))
              (let f20 (fn nat nat) (closure def0 v19))
              (let v21 nat (app f20 v18))
              (ret v21)
            )
          )
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Example.circRender Example.symbolicRecursiveReflected

/--
info: (program nat
  (def def0 (env1 unit) (x2 nat) nat
    (block
      (source Freigen.Examples.Circuit.Basic 112 0 115 8
        (block
          (let v3 nat (mul x2 x2))
          (let v4 bool (le x2 v3))
          (let v5 unit
            (op assert v4)
          )
          (let v6 nat (mul x2 x2))
          (ret v6)
        )
      )
    )
  )
  (def def7 (env8 unit) (x9 nat) nat
    (block
      (source Freigen.Examples.Circuit.Basic 178 0 180 15
        (block
          (let v10 unit (lit unit))
          (let f11 (fn nat nat) (closure def0 v10))
          (let v12 nat (app f11 x9))
          (let v13 unit (lit unit))
          (let f14 (fn nat nat) (closure def0 v13))
          (let v15 nat (app f14 v12))
          (ret v15)
        )
      )
    )
  )
  (main ()
    (block
      (source Freigen.Examples.Circuit.Basic 188 37 188 53
        (block
          (source Freigen.Examples.Circuit.Basic 182 0 184 20
            (block
              (let v16 unit (lit unit))
              (let v19 nat
                (op hint v16
                  (branch b17
                    (block
                      (let v18 nat (lit 2))
                      (ret v18)
                    )
                  )
                )
              )
              (let v20 unit (lit unit))
              (let f21 (fn nat nat) (closure def7 v20))
              (let v22 nat (app f21 v19))
              (ret v22)
            )
          )
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Example.circRender Example.nestedHelperReflected

/--
info: (program nat
  (def def0 (env1 unit) (x2 (prod nat nat)) nat
    (block
      (source Freigen.Examples.Circuit.Basic 190 0 191 14
        (block
          (let v3 nat (fst x2))
          (let v4 nat (snd x2))
          (let v5 nat (add v3 v4))
          (ret v5)
        )
      )
    )
  )
  (main ()
    (block
      (source Freigen.Examples.Circuit.Basic 200 37 200 53
        (block
          (source Freigen.Examples.Circuit.Basic 193 0 196 15
            (block
              (let v6 unit (lit unit))
              (let v9 nat
                (op hint v6
                  (branch b7
                    (block
                      (let v8 nat (lit 8))
                      (ret v8)
                    )
                  )
                )
              )
              (let v10 unit (lit unit))
              (let v13 nat
                (op hint v10
                  (branch b11
                    (block
                      (let v12 nat (lit 13))
                      (ret v12)
                    )
                  )
                )
              )
              (let v14 (prod nat nat) (pair v9 v13))
              (let v15 unit (lit unit))
              (let f16 (fn (prod nat nat) nat) (closure def0 v15))
              (let v17 nat (app f16 v14))
              (ret v17)
            )
          )
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Example.circRender Example.tupledHelperReflected

/--
info: (program unit
  (def def0 (env1 unit) (x2 nat) unit
    (block
      (source Freigen.Examples.Circuit.Basic 211 0 213 9
        (block
          (let v3 unit (lit unit))
          (let v5 nat
            (op hint v3
              (branch b4
                (block
                  (ret x2)
                )
              )
            )
          )
          (let v6 unit (lit unit))
          (ret v6)
        )
      )
    )
  )
  (def def7 (env8 unit) (x9 bool) unit
    (block
      (source Freigen.Examples.Circuit.Basic 211 0 213 9
        (block
          (let v10 unit (lit unit))
          (let v12 bool
            (op hint v10
              (branch b11
                (block
                  (ret x9)
                )
              )
            )
          )
          (let v13 unit (lit unit))
          (ret v13)
        )
      )
    )
  )
  (main ()
    (block
      (source Freigen.Examples.Circuit.Basic 221 45 221 69
        (block
          (source Freigen.Examples.Circuit.Basic 215 0 217 18
            (block
              (let v14 nat (lit 5))
              (let v15 unit (lit unit))
              (let f16 (fn nat unit) (closure def0 v15))
              (let v17 unit (app f16 v14))
              (let v18 bool (lit true))
              (let v19 unit (lit unit))
              (let f20 (fn bool unit) (closure def7 v19))
              (let v21 unit (app f20 v18))
              (ret v21)
            )
          )
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Example.circRender Example.staticSpecializationReflected

/--
info: (program nat
  (main ()
    (block
      (source Freigen.Examples.Circuit.Basic 228 30 228 52
        (block
          (source Init.Prelude 3722 2 3722 6
            (block
              (let v0 nat (lit 7))
              (ret v0)
            )
          )
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Example.circRender Example.pureReflected.1

/--
info: (program nat
  (main ()
    (block
      (source Freigen.Examples.Circuit.Basic 235 35 235 72
        (block
          (source Freigen.Examples.Circuit.Basic 104 0 105 43
            (block
              (let v0 unit (lit unit))
              (let v3 nat
                (op hint v0
                  (branch b1
                    (block
                      (let v2 nat (lit 7))
                      (ret v2)
                    )
                  )
                )
              )
              (ret v3)
            )
          )
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Example.circRender Example.hintMacroReflected.1

/--
info: (program unit
  (main ()
    (block
      (source Freigen.Examples.Circuit.Basic 237 37 237 58
        (block
          (source Freigen.Examples.Circuit.Basic 101 0 102 58
            (block
              (let v0 bool (lit true))
              (let v1 unit
                (op assert v0)
              )
              (ret v1)
            )
          )
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Example.circRender Example.assertMacroReflected.1

/--
info: (program nat
  (main ()
    (block
      (source Freigen.Examples.Storage 102 25 102 35
        (block
          (source Freigen.Examples.Storage 100 0 100 35
            (block
              (let v0 nat (lit 0))
              (let v1 nat
                (op get v0)
              )
              (ret v1)
            )
          )
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize StorageExample.render StorageExample.reflected

/--
info: (program nat
  (def def0 (env1 unit) (x2 nat) nat
    (block
      (source Freigen.Examples.Recursion 13 0 17 25
        (block
          (let v3 nat (lit 0))
          (let v4 bool (eq x2 v3))
          (let v5 nat (if v4
            (block
              (let v6 nat (lit 0))
              (ret v6)
            )
            (block
              (let v7 nat (lit 1))
              (let v8 nat (sub x2 v7))
              (let v9 unit (lit unit))
              (let f10 (fn nat nat) (closure def0 v9))
              (let v11 nat (app f10 v8))
              (let v12 nat (add v11 v8))
              (let v13 nat (lit 1))
              (let v14 nat (add v12 v13))
              (ret v14)
            )
          ))
          (ret v5)
        )
      )
    )
  )
  (main ()
    (block
      (source Freigen.Examples.Recursion 37 28 37 35
        (block
          (source Freigen.Examples.Recursion 29 0 31 7
            (block
              (let v15 unit (lit unit))
              (let v18 nat
                (op hint v15
                  (branch b16
                    (block
                      (let v17 nat (lit 5))
                      (ret v17)
                    )
                  )
                )
              )
              (let v19 unit (lit unit))
              (let f20 (fn nat nat) (closure def0 v19))
              (let v21 nat (app f20 v18))
              (ret v21)
            )
          )
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Example.circRender RecursionExample.sumReflected

/--
info: (program nat
  (main ((arg0 nat))
    (block
      (ret arg0)
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Example.circRender Example.argumentMain

end Freigen.Ast.SerializedExamples
