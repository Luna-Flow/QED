namespace QEDFV

structure RuleMappingEntry where
  ruleName : String
  modulePath : String
  declaration : String
deriving Repr

def ruleToImplementationMapping : List RuleMappingEntry :=
  [ { ruleName := "REFL", modulePath := "QEDFV.Kernel.PrimitiveRules", declaration := "Derivable.refl" }
  , { ruleName := "ASSUME", modulePath := "QEDFV.Kernel.PrimitiveRules", declaration := "Derivable.assume" }
  , { ruleName := "TRANS", modulePath := "QEDFV.Kernel.PrimitiveRules", declaration := "Derivable.trans" }
  , { ruleName := "MK_COMB", modulePath := "QEDFV.Kernel.PrimitiveRules", declaration := "Derivable.mkComb" }
  , { ruleName := "ABS", modulePath := "QEDFV.Kernel.PrimitiveRules", declaration := "Derivable.abs" }
  , { ruleName := "BETA", modulePath := "QEDFV.Kernel.PrimitiveRules", declaration := "Derivable.beta" }
  , { ruleName := "EQ_MP", modulePath := "QEDFV.Kernel.PrimitiveRules", declaration := "Derivable.eqMp" }
  , { ruleName := "DEDUCT_ANTISYM_RULE", modulePath := "QEDFV.Kernel.PrimitiveRules", declaration := "Derivable.deductAntisym" }
  , { ruleName := "INST_TYPE", modulePath := "QEDFV.Kernel.PrimitiveRules", declaration := "Derivable.instType" }
  , { ruleName := "INST", modulePath := "QEDFV.Kernel.PrimitiveRules", declaration := "Derivable.inst" }
  ]

end QEDFV
