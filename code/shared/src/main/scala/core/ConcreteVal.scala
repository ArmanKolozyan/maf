package scalaam.core

trait ConcreteVal

object ConcreteVal {
  case class ConcreteNumber(x: Int)                                             extends ConcreteVal
  case class ConcreteReal(x: Double)                                            extends ConcreteVal
  case class ConcreteString(x: String)                                          extends ConcreteVal
  case class ConcreteBool(x: Boolean)                                           extends ConcreteVal
  case class ConcreteChar(x: Char)                                              extends ConcreteVal
  case class ConcreteSymbol(x: String)                                          extends ConcreteVal
  case class ConcretePrim[P <: Primitive](p: P)                                 extends ConcreteVal
  case class ConcreteClosure[E <: Expression, A <: Address, Env]
    (e: E, env: Env, name: Option[String])                                      extends ConcreteVal
  case object ConcreteNil                                                       extends ConcreteVal
  case class ConcretePointer[A <: Address](ptr: A)                              extends ConcreteVal
}
