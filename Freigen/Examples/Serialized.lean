import Freigen
import Freigen.Examples.FiniteTypes

/-! Golden serialized ASTs for every reflector-backed example in `Freigen.Examples`.
Each guard deliberately records the complete serialized tree. -/

namespace Freigen.Ast.SerializedExamples

/--
info: (program nat
  (source Freigen.Examples.Circuit.Basic 141 35 141 42
    (block
      (source Freigen.Examples.Circuit.Basic 133 0 137 8
        (block
          (let f5 (fn nat nat) (lam (x0 nat)
            (block
              (source Freigen.Examples.Circuit.Basic 121 0 124 8
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
              (source Freigen.Examples.Circuit.Basic 126 0 131 18
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
  (source Freigen.Examples.Circuit.Basic 159 40 159 58
    (block
      (source Freigen.Examples.Circuit.Basic 153 0 155 15
        (block
          (let f5 (fn nat nat) (lam (x0 nat)
            (block
              (source Freigen.Examples.Circuit.Basic 121 0 124 8
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
  (source Freigen.Examples.Circuit.Basic 161 35 161 53
    (block
      (source Freigen.Examples.Circuit.Basic 153 0 155 15
        (block
          (let f5 (fn nat nat) (lam (x0 nat)
            (block
              (source Freigen.Examples.Circuit.Basic 121 0 124 8
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
  (source Freigen.Examples.Circuit.Basic 175 42 175 63
    (block
      (source Freigen.Examples.Circuit.Basic 169 0 171 17
        (block
          (letrec rec11 (x0 nat) nat
            (block
              (source Freigen.Examples.Circuit.Basic 163 0 167 29
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
  (source Freigen.Examples.Circuit.Basic 212 37 212 53
    (block
      (source Freigen.Examples.Circuit.Basic 206 0 208 20
        (block
          (let f5 (fn nat nat) (lam (x0 nat)
            (block
              (source Freigen.Examples.Circuit.Basic 121 0 124 8
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
              (source Freigen.Examples.Circuit.Basic 202 0 204 15
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
  (source Freigen.Examples.Circuit.Basic 224 37 224 53
    (block
      (source Freigen.Examples.Circuit.Basic 217 0 220 15
        (block
          (let f4 (fn (prod nat nat) nat) (lam (x0 (prod nat nat))
            (block
              (source Freigen.Examples.Circuit.Basic 214 0 215 14
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
  (source Freigen.Examples.Circuit.Basic 247 45 247 69
    (block
      (source Freigen.Examples.Circuit.Basic 241 0 243 18
        (block
          (let f5 (fn nat unit) (lam (x0 nat)
            (block
              (source Freigen.Examples.Circuit.Basic 237 0 239 9
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
              (source Freigen.Examples.Circuit.Basic 237 0 239 9
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
  (source Freigen.Examples.Circuit.Basic 254 30 254 52
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
  (source Freigen.Examples.Circuit.Basic 266 35 266 72
    (block
      (source Freigen.Examples.Circuit.Basic 113 0 114 43
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
  (source Freigen.Examples.Circuit.Basic 268 37 268 58
    (block
      (source Freigen.Examples.Circuit.Basic 110 0 111 58
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
info: (program (fin 5)
  (source Freigen.Examples.Circuit.Basic 283 38 283 51
    (block
      (source Freigen.Examples.Circuit.Basic 280 0 281 36
        (block
          (let v0 unit (lit unit))
          (let v4 (fin 5)
            (op hint v0
              (branch b1
                (block
                  (let v2 nat (lit 3))
                  (let v3 (fin 5) (fin-tag-5 v2))
                  (ret v3)
                )
              )
            )
          )
          (ret v4)
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Example.circRender Example.finHintMacroReflected.1

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

/--
info: (program (fin 5)
  (source Freigen.Examples.FiniteTypes 45 36 45 52
    (block
      (source Freigen.Examples.FiniteTypes 42 0 43 21
        (block
          (let v0 nat (lit 3))
          (let v1 (fin 5) (fin-tag-5 v0))
          (ret v1)
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Freigen.Examples.FiniteTypes.noOpRender
  Freigen.Examples.FiniteTypes.finLiteralReflected.1

/--
info: (program (zmod 7)
  (source Freigen.Examples.FiniteTypes 52 37 52 54
    (block
      (source Freigen.Examples.FiniteTypes 49 0 50 8
        (block
          (let v0 int (lit 3))
          (let v1 (zmod 7) (zmod-tag-7 v0))
          (ret v1)
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Freigen.Examples.FiniteTypes.noOpRender
  Freigen.Examples.FiniteTypes.zmodLiteralReflected.1

/--
info: (program (fin 5)
  (source Freigen.Examples.FiniteTypes 62 32 62 44
    (block
      (source Freigen.Examples.FiniteTypes 59 0 60 23
        (block
          (let f4 (fn (fin 5) (fin 5)) (lam (x0 (fin 5))
            (block
              (source Freigen.Examples.FiniteTypes 56 0 57 14
                (block
                  (let v1 nat (lit 1))
                  (let v2 (fin 5) (fin-tag-5 v1))
                  (let v3 (fin 5) (add x0 v2))
                  (ret v3)
                )
              )
            )
          ))
          (let v5 nat (lit 2))
          (let v6 (fin 5) (fin-tag-5 v5))
          (let v7 (fin 5) (app f4 v6))
          (ret v7)
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Freigen.Examples.FiniteTypes.noOpRender
  Freigen.Examples.FiniteTypes.addFinReflected.1

/--
info: (program nat
  (source Freigen.Examples.FiniteTypes 72 34 72 48
    (block
      (source Freigen.Examples.FiniteTypes 69 0 70 25
        (block
          (let f2 (fn (fin 5) nat) (lam (x0 (fin 5))
            (block
              (source Freigen.Examples.FiniteTypes 66 0 67 12
                (block
                  (let v1 nat (fin-erase-5 x0))
                  (ret v1)
                )
              )
            )
          ))
          (let v3 nat (lit 2))
          (let v4 (fin 5) (fin-tag-5 v3))
          (let v5 nat (app f2 v4))
          (ret v5)
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Freigen.Examples.FiniteTypes.noOpRender
  Freigen.Examples.FiniteTypes.finValueReflected.1

/--
info: (program nat
  (source Freigen.Examples.FiniteTypes 88 37 88 54
    (block
      (source Freigen.Examples.FiniteTypes 85 0 86 21
        (block
          (let f2 (fn (fin 5) nat) (lam (x0 (fin 5))
            (block
              (source Freigen.Examples.FiniteTypes 76 0 80 12
                (block
                  (let v1 nat (fin-erase-5 x0))
                  (ret v1)
                )
              )
            )
          ))
          (let f5 (fn nat nat) (lam (x3 nat)
            (block
              (source Freigen.Examples.FiniteTypes 82 0 83 44
                (block
                  (let v4 nat (lit 0))
                  (ret v4)
                )
              )
            )
          ))
          (let v6 nat (lit 4))
          (let v7 nat (app f5 v6))
          (ret v7)
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Freigen.Examples.FiniteTypes.noOpRender
  Freigen.Examples.FiniteTypes.symbolicFinReflected.1

/--
info: (program (zmod 7)
  (source Freigen.Examples.FiniteTypes 98 33 98 46
    (block
      (source Freigen.Examples.FiniteTypes 95 0 96 11
        (block
          (let f4 (fn (zmod 7) (zmod 7)) (lam (x0 (zmod 7))
            (block
              (source Freigen.Examples.FiniteTypes 92 0 93 14
                (block
                  (let v1 int (lit 1))
                  (let v2 (zmod 7) (zmod-tag-7 v1))
                  (let v3 (zmod 7) (add x0 v2))
                  (ret v3)
                )
              )
            )
          ))
          (let v5 int (lit 2))
          (let v6 (zmod 7) (zmod-tag-7 v5))
          (let v7 (zmod 7) (app f4 v6))
          (ret v7)
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Freigen.Examples.FiniteTypes.noOpRender
  Freigen.Examples.FiniteTypes.addZModReflected.1

/--
info: (program int
  (source Freigen.Examples.FiniteTypes 108 35 108 50
    (block
      (source Freigen.Examples.FiniteTypes 105 0 106 13
        (block
          (let f2 (fn (zmod 7) int) (lam (x0 (zmod 7))
            (block
              (source Freigen.Examples.FiniteTypes 102 0 103 30
                (block
                  (let v1 int (zmod-erase-7 x0))
                  (ret v1)
                )
              )
            )
          ))
          (let v3 int (lit 3))
          (let v4 (zmod 7) (zmod-tag-7 v3))
          (let v5 int (app f2 v4))
          (ret v5)
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Freigen.Examples.FiniteTypes.noOpRender
  Freigen.Examples.FiniteTypes.zmodValueReflected.1

/--
info: (program int
  (source Freigen.Examples.FiniteTypes 114 39 114 58
    (block
      (source Freigen.Examples.FiniteTypes 111 0 112 27
        (block
          (let v0 int (lit -10))
          (ret v0)
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Freigen.Examples.FiniteTypes.noOpRender
  Freigen.Examples.FiniteTypes.intArithmeticReflected.1

/--
info: (program (zmod 0)
  (source Freigen.Examples.FiniteTypes 121 44 121 68
    (block
      (source Freigen.Examples.FiniteTypes 118 0 119 33
        (block
          (let v0 int (lit -2))
          (let v1 (zmod 0) (zmod-tag-0 v0))
          (ret v1)
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Freigen.Examples.FiniteTypes.noOpRender
  Freigen.Examples.FiniteTypes.zmodZeroArithmeticReflected.1

/--
info: (program (fin 5)
  (source Freigen.Examples.FiniteTypes 133 38 133 56
    (block
      (source Freigen.Examples.FiniteTypes 130 0 131 38
        (block
          (let f1 (fn (fin 5) (fin 5)) (lam (x0 (fin 5))
            (block
              (source Freigen.Examples.FiniteTypes 125 0 128 8
                (block
                  (ret x0)
                )
              )
            )
          ))
          (let v2 nat (lit 4))
          (let v3 (fin 5) (fin-tag-5 v2))
          (let v4 (fin 5) (app f1 v3))
          (ret v4)
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Freigen.Examples.FiniteTypes.noOpRender
  Freigen.Examples.FiniteTypes.dependentFinReflected.1

/--
info: (program (zmod 7)
  (source Freigen.Examples.FiniteTypes 143 39 143 58
    (block
      (source Freigen.Examples.FiniteTypes 140 0 141 26
        (block
          (let f1 (fn (zmod 7) (zmod 7)) (lam (x0 (zmod 7))
            (block
              (source Freigen.Examples.FiniteTypes 137 0 138 8
                (block
                  (ret x0)
                )
              )
            )
          ))
          (let v2 int (lit 6))
          (let v3 (zmod 7) (zmod-tag-7 v2))
          (let v4 (zmod 7) (app f1 v3))
          (ret v4)
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Freigen.Examples.FiniteTypes.noOpRender
  Freigen.Examples.FiniteTypes.dependentZModReflected.1

/--
info: (program nat
  (source Freigen.Examples.FiniteTypes 165 47 165 74
    (block
      (source Freigen.Examples.FiniteTypes 153 0 156 21
        (block
          (let f2 (fn (fin 5) nat) (lam (x0 (fin 5))
            (block
              (source Freigen.Examples.FiniteTypes 147 0 151 12
                (block
                  (let v1 nat (fin-erase-5 x0))
                  (ret v1)
                )
              )
            )
          ))
          (let f5 (fn (fin 7) nat) (lam (x3 (fin 7))
            (block
              (source Freigen.Examples.FiniteTypes 147 0 151 12
                (block
                  (let v4 nat (fin-erase-7 x3))
                  (ret v4)
                )
              )
            )
          ))
          (let v6 nat (lit 3))
          (let v7 (fin 5) (fin-tag-5 v6))
          (let v8 nat (app f2 v7))
          (let v9 nat (lit 4))
          (let v10 (fin 7) (fin-tag-7 v9))
          (let v11 nat (app f5 v10))
          (let v12 nat (add v8 v11))
          (ret v12)
        )
      )
    )
  )
)
-/
#guard_msgs in
#eval IO.println <| serialize Freigen.Examples.FiniteTypes.noOpRender
  Freigen.Examples.FiniteTypes.twoFinSpecializationsReflected.1

end Freigen.Ast.SerializedExamples
