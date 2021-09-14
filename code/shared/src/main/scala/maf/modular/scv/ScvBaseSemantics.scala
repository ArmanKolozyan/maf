package maf.modular.scv

import maf.modular.scheme.modf._
import maf.modular.scheme.SchemeDomain
import maf.language.scheme._
import maf.util.TaggedSet
import maf.core._
import maf.language.scheme.primitives.SchemePrimM
import maf.lattice.interfaces.BoolLattice

/**
 * Provides the base Scheme semantics for soft contract verification.
 *
 * The actual contract semantics are implemented in traits extending from this base trait
 */
trait ScvBaseSemantics extends BigStepModFSemanticsT { outer =>
  import TaggedSet._
  import MonadStateT._
  import Monad.MonadSyntaxOps

  case class State(env: Environment[Address], store: StoreCache, lstore: BasicStore[Addr, Value], pc: List[Symbolic], freshVar: Int):
      def extendPc(addition: Symbolic) = this.copy(pc = addition :: pc)

  object State:
      def empty: State = State(env = BasicEnvironment(Map()), store = Map(), new BasicStore(content = Map()), pc = List(), freshVar = 0)

  case class PostValue(symbolic: Option[Symbolic], value: Value)

  override type EvalM[X] = ScvEvalM[X]
  type Symbolic = SchemeExp
  type SymbolicSet[X] = TaggedSet[Symbolic, X]
  type ScvEvalM[X] = MonadStateT[State, SymbolicSet, X]
  type StoreCache = Map[Addr, Symbolic]

  final lazy val scvMonadInstance: StateOps[State, ScvEvalM] = MonadStateT.stateInstance[State, SymbolicSet]
  implicit val evalM = new TEvalM:
      import scvMonadInstance.{get, put, withState}
      export scvMonadInstance._
      def getEnv: EvalM[Environment[Address]] = get.map(_.env)
      def withEnv[X](f: Environment[Address] => Environment[Address])(ev: => EvalM[X]): EvalM[X] =
        withState(s => s.copy(env = f(s.env)))(ev)
      def guard(bln: Boolean): EvalM[Unit] =
        if bln then unit(()) else mzero
      def mzero[X]: EvalM[X] = MonadStateT.lift(TaggedSet.empty)
      def merge[X: Lattice](x: EvalM[X], y: EvalM[X]): EvalM[X] =
        throw new Exception("Merging not supported in ScvEvalM")
  /* MonadStateT((state) => {
          val xRes = x.run(state)
          val yRes = y.run(state)
          val xs = xRes.vs.map(_._2._1)
          val ys = xRes.vs.map(_._2._1)
          val newValue = (xs ++ ys).foldLeft(Lattice[X].bottom)((acc, el) => Lattice[X].join(acc, el))
        }) */

  //////////////////////////////////////////////////
  // Other useful operations on the ScvEvalM monad
  // ///////////////////////////////////////////////

  /** Lookup the given address in the store cache and return the associated symbolic information */
  protected def lookupCache(addr: Addr): ScvEvalM[Option[Symbolic]] =
    scvMonadInstance.get.map(_.store.get(addr))

  protected def flatten[X](ms: ScvEvalM[TaggedSet[Symbolic, X]]): ScvEvalM[(Option[Symbolic], X)] =
    ms.flatMap(ts => MonadStateT.lift(TaggedSet.extract(ts)))

  /** Returns a computation that, when composed with other computions results in no computation at all ie. void >>= m == void */
  protected def void[X]: ScvEvalM[X] = MonadStateT.lift(TaggedSet.empty)

  /** Extracts the tag along with the value from a computation returning such a tagged value */
  protected def extract(computation: EvalM[Value]): EvalM[PostValue] =
    flatten(unlift(computation)).map(v => PostValue(v._1, v._2))

  /**
   * Extend the path condition in the current state, and propogate it.
   *
   * @param symb
   *   the symbolic expression to add to the path condition (as a conjunction)
   */
  protected def extendPc(symb: Symbolic): EvalM[Unit] =
    for
        st <- scvMonadInstance.get
        _ <- scvMonadInstance.put(st.extendPc(symb))
    yield ()

  /** Generates a fresh symbolic variable */
  protected def fresh: EvalM[Symbolic] =
    for
        st <- scvMonadInstance.get
        _ <- scvMonadInstance.put(st.copy(freshVar = st.freshVar + 1))
    yield SchemeVar(Identifier(s"#x${st.freshVar}", Identity.none))

  /** Executes both computations non-determinstically */
  protected def nondet[X](tru: EvalM[X], fls: EvalM[X]): EvalM[X] =
    nondets(Set(tru, fls))

  protected def nondets[X](branches: Set[EvalM[X]]): EvalM[X] =
    MonadStateT((state) => TaggedSet.flatten(branches.map(_.run(state))))

  /** Executes the given computation with the current store */
  protected def usingStore[X](m: (BasicStore[Address, Value], StoreCache) => EvalM[X]): EvalM[X] =
    scvMonadInstance.get.map(st => (st.lstore, st.store)).flatMap(p => m(p._1, p._2))

  /** Converts a Scheme expression to a compatible Symbolic representation */
  protected def symbolic(e: SchemeExp | Symbolic): Symbolic = e match {
    case e: SchemeExp => e
  }

  /** Tags the given value with the given Scheme expression */
  protected def tag(e: SchemeExp | Symbolic)(v: Value): EvalM[Value] =
    scvMonadInstance.unit(v).flatMap(result => lift(TaggedSet.tag(symbolic(e), result)))

  override def intraAnalysis(cmp: Component): BaseIntraAnalysis

  trait BaseIntraAnalysis extends BigStepModFIntraT:
      given SchemePrimM[EvalM, Address, Value] with
          export scvMonadInstance._
          def fail[X](err: Error): EvalM[X] = void // TODO: register error
          def mbottom[X]: EvalM[X] = void
          def mjoin[X: Lattice](x: EvalM[X], y: EvalM[X]): EvalM[X] = evalM.merge(x, y)
          def allocVar(idn: Identifier): EvalM[Address] =
            throw new Exception("not supported")

          def allocPtr(exp: SchemeExp): EvalM[Address] = scvMonadInstance.unit(interpreterBridge.pointer(exp))

          /**
           * Two addresses are potentially equal when their `equals` implementation says so. However, they can point to multiple concrete addresses
           * (since they are abstract), so the result is top, otherwise it is defintely not the same address
           */
          def addrEq: EvalM[MaybeEq[Address]] = scvMonadInstance.unit(
            new MaybeEq[Address]:
                def apply[B: BoolLattice](a1: Address, a2: Address): B =
                  if a1 == a2 then BoolLattice[B].top else BoolLattice[B].inject(false)
          )

          /** Extending the store means that we need to extend both the local and global store */
          def extendSto(a: Address, v: Value): EvalM[Unit] =
            for
                st <- scvMonadInstance.get
                _ <- scvMonadInstance.put(st.copy(lstore = st.lstore.extend(a, v)))
                _ <- scvMonadInstance.impure(writeAddr(a, v))
            yield ()

          /**
           * Store lookup will return the value from the local store (if available) and otherwise the value from the global store.
           *
           * The value fro the local store can be more precise than the value in the local store, since the local store is flow sensitive while the
           * global one is not. However, since the local store in this analysis is not threaded through the entire analysis, in the fixed point the
           * local store does not result in a flow sensitive analysis, but instead in a flow insentive one.
           */
          def lookupSto(a: Address): EvalM[Value] = usingStore { (store, cache) =>
              val value = store.lookup(a).getOrElse(readAddr(a))
              // also return the symbolic representation if one is available
              cache.get(a) match
                  case Some(symbolic) => tag(symbolic)(value)
                  case _              => scvMonadInstance.unit(value)
          }

          def updateSto(a: Address, v: Value): EvalM[Unit] = extendSto(a, v)
}