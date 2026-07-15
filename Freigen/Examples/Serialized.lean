import Freigen

/-! Golden serialized ASTs for every reflector-backed example in `Freigen.Examples`.
Each guard deliberately records the complete serialized tree. -/

namespace Freigen.Ast.SerializedExamples

/--
info: (program nat
  (source Freigen.Examples.Circuit.Basic 132 35 132 42
    (block
      (source Freigen.Examples.Circuit.Basic 124 0 128 8
        (block
          (let f5 (fn nat nat) (lam (x0 nat)
            (block
              (source Freigen.Examples.Circuit.Basic 112 0 115 8
                (block
                  (let v1 nat (mul x0 x0))
                  (let v2 bool (le x0 v1))
                  (let v3 unit
                    (op assert v2)
                  )
                  (let v4 nat (mul x0 x0))
                  (ret v4)
                )
              )
            )
          ))
          (letrec rec18 (x6 nat) nat
            (block
              (source Freigen.Examples.Circuit.Basic 117 0 122 18
                (block
                  (let v7 nat (lit 0))
                  (let v8 bool (eq x6 v7))
                  (let v9 nat (if v8
                    (block
                      (let v10 nat (lit 0))
                      (ret v10)
                    )
                    (block
                      (let v11 nat (lit 1))
                      (let v12 nat (sub x6 v11))
                      (let v13 nat (self v12))
                      (let v14 nat (lit 1))
                      (let v15 nat (add v12 v14))
                      (let v16 nat (app f5 v15))
                      (let v17 nat (add v13 v16))
                      (ret v17)
                    )
                  ))
                  (ret v9)
                )
              )
            )
          )
          (let v19 nat (lit 3))
          (let v20 nat (app rec18 v19))
          (let v21 unit (lit unit))
          (let v23 nat
            (op hint v21
              (branch b22
                (block
                  (ret v20)
                )
              )
            )
          )
          (let v24 bool (eq v23 v20))
          (let v25 unit
            (op assert v24)
          )
          (ret v23)
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
  (source Freigen.Examples.Circuit.Basic 150 40 150 58
    (block
      (source Freigen.Examples.Circuit.Basic 144 0 146 15
        (block
          (let f5 (fn nat nat) (lam (x0 nat)
            (block
              (source Freigen.Examples.Circuit.Basic 112 0 115 8
                (block
                  (let v1 nat (mul x0 x0))
                  (let v2 bool (le x0 v1))
                  (let v3 unit
                    (op assert v2)
                  )
                  (let v4 nat (mul x0 x0))
                  (ret v4)
                )
              )
            )
          ))
          (let v6 unit (lit unit))
          (let v9 nat
            (op hint v6
              (branch b7
                (block
                  (let v8 nat (lit 4))
                  (ret v8)
                )
              )
            )
          )
          (let v10 nat (app f5 v9))
          (ret v10)
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
  (source Freigen.Examples.Circuit.Basic 152 35 152 53
    (block
      (source Freigen.Examples.Circuit.Basic 144 0 146 15
        (block
          (let f5 (fn nat nat) (lam (x0 nat)
            (block
              (source Freigen.Examples.Circuit.Basic 112 0 115 8
                (block
                  (let v1 nat (mul x0 x0))
                  (let v2 bool (le x0 v1))
                  (let v3 unit
                    (op assert v2)
                  )
                  (let v4 nat (mul x0 x0))
                  (ret v4)
                )
              )
            )
          ))
          (let v6 unit (lit unit))
          (let v9 nat
            (op hint v6
              (branch b7
                (block
                  (let v8 nat (lit 4))
                  (ret v8)
                )
              )
            )
          )
          (let v10 nat (app f5 v9))
          (ret v10)
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
  (source Freigen.Examples.Circuit.Basic 166 42 166 63
    (block
      (source Freigen.Examples.Circuit.Basic 160 0 162 17
        (block
          (letrec rec11 (x0 nat) nat
            (block
              (source Freigen.Examples.Circuit.Basic 154 0 158 29
                (block
                  (let v1 nat (lit 0))
                  (let v2 bool (eq x0 v1))
                  (let v3 nat (if v2
                    (block
                      (let v4 nat (lit 0))
                      (ret v4)
                    )
                    (block
                      (let v5 nat (lit 1))
                      (let v6 nat (sub x0 v5))
                      (let v7 nat (self v6))
                      (let v8 nat (add v7 v6))
                      (let v9 nat (lit 1))
                      (let v10 nat (add v8 v9))
                      (ret v10)
                    )
                  ))
                  (ret v3)
                )
              )
            )
          )
          (let v12 unit (lit unit))
          (let v15 nat
            (op hint v12
              (branch b13
                (block
                  (let v14 nat (lit 5))
                  (ret v14)
                )
              )
            )
          )
          (let v16 nat (app rec11 v15))
          (ret v16)
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
  (source Freigen.Examples.Circuit.Basic 203 37 203 53
    (block
      (source Freigen.Examples.Circuit.Basic 197 0 199 20
        (block
          (let f5 (fn nat nat) (lam (x0 nat)
            (block
              (source Freigen.Examples.Circuit.Basic 112 0 115 8
                (block
                  (let v1 nat (mul x0 x0))
                  (let v2 bool (le x0 v1))
                  (let v3 unit
                    (op assert v2)
                  )
                  (let v4 nat (mul x0 x0))
                  (ret v4)
                )
              )
            )
          ))
          (let f9 (fn nat nat) (lam (x6 nat)
            (block
              (source Freigen.Examples.Circuit.Basic 193 0 195 15
                (block
                  (let v7 nat (app f5 x6))
                  (let v8 nat (app f5 v7))
                  (ret v8)
                )
              )
            )
          ))
          (let v10 unit (lit unit))
          (let v13 nat
            (op hint v10
              (branch b11
                (block
                  (let v12 nat (lit 2))
                  (ret v12)
                )
              )
            )
          )
          (let v14 nat (app f9 v13))
          (ret v14)
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
  (source Freigen.Examples.Circuit.Basic 215 37 215 53
    (block
      (source Freigen.Examples.Circuit.Basic 208 0 211 15
        (block
          (let f4 (fn (prod nat nat) nat) (lam (x0 (prod nat nat))
            (block
              (source Freigen.Examples.Circuit.Basic 205 0 206 14
                (block
                  (let v1 nat (fst x0))
                  (let v2 nat (snd x0))
                  (let v3 nat (add v1 v2))
                  (ret v3)
                )
              )
            )
          ))
          (let v5 unit (lit unit))
          (let v8 nat
            (op hint v5
              (branch b6
                (block
                  (let v7 nat (lit 8))
                  (ret v7)
                )
              )
            )
          )
          (let v9 unit (lit unit))
          (let v12 nat
            (op hint v9
              (branch b10
                (block
                  (let v11 nat (lit 13))
                  (ret v11)
                )
              )
            )
          )
          (let v13 (prod nat nat) (pair v8 v12))
          (let v14 nat (app f4 v13))
          (ret v14)
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
  (source Freigen.Examples.Circuit.Basic 238 45 238 69
    (block
      (source Freigen.Examples.Circuit.Basic 232 0 234 18
        (block
          (let f5 (fn nat unit) (lam (x0 nat)
            (block
              (source Freigen.Examples.Circuit.Basic 228 0 230 9
                (block
                  (let v1 unit (lit unit))
                  (let v3 nat
                    (op hint v1
                      (branch b2
                        (block
                          (ret x0)
                        )
                      )
                    )
                  )
                  (let v4 unit (lit unit))
                  (ret v4)
                )
              )
            )
          ))
          (let f11 (fn bool unit) (lam (x6 bool)
            (block
              (source Freigen.Examples.Circuit.Basic 228 0 230 9
                (block
                  (let v7 unit (lit unit))
                  (let v9 bool
                    (op hint v7
                      (branch b8
                        (block
                          (ret x6)
                        )
                      )
                    )
                  )
                  (let v10 unit (lit unit))
                  (ret v10)
                )
              )
            )
          ))
          (let v12 nat (lit 5))
          (let v13 unit (app f5 v12))
          (let v14 bool (lit true))
          (let v15 unit (app f11 v14))
          (ret v15)
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
  (source Freigen.Examples.Circuit.Basic 245 30 245 52
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
-/
#guard_msgs in
#eval IO.println <| serialize Example.circRender Example.pureReflected.1

/--
info: (program nat
  (source Freigen.Examples.Circuit.Basic 257 35 257 72
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
-/
#guard_msgs in
#eval IO.println <| serialize Example.circRender Example.hintMacroReflected.1

/--
info: (program unit
  (source Freigen.Examples.Circuit.Basic 259 37 259 58
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
-/
#guard_msgs in
#eval IO.println <| serialize Example.circRender Example.assertMacroReflected.1

/--
info: (program nat
  (source Freigen.Examples.Storage 101 25 101 35
    (block
      (source Freigen.Examples.Storage 99 0 99 35
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
-/
#guard_msgs in
#eval IO.println <| serialize StorageExample.render StorageExample.reflected

/--
info: (program nat
  (source Freigen.Examples.Recursion 37 28 37 35
    (block
      (source Freigen.Examples.Recursion 29 0 31 7
        (block
          (letrec rec11 (x0 nat) nat
            (block
              (source Freigen.Examples.Recursion 13 0 17 25
                (block
                  (let v1 nat (lit 0))
                  (let v2 bool (eq x0 v1))
                  (let v3 nat (if v2
                    (block
                      (let v4 nat (lit 0))
                      (ret v4)
                    )
                    (block
                      (let v5 nat (lit 1))
                      (let v6 nat (sub x0 v5))
                      (let v7 nat (self v6))
                      (let v8 nat (add v7 v6))
                      (let v9 nat (lit 1))
                      (let v10 nat (add v8 v9))
                      (ret v10)
                    )
                  ))
                  (ret v3)
                )
              )
            )
          )
          (let v12 unit (lit unit))
          (let v15 nat
            (op hint v12
              (branch b13
                (block
                  (let v14 nat (lit 5))
                  (ret v14)
                )
              )
            )
          )
          (let v16 nat (app rec11 v15))
          (ret v16)
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Example.circRender RecursionExample.sumReflected

end Freigen.Ast.SerializedExamples
