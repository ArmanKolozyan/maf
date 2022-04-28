package maf.modular.scv

import maf.core.*
import maf.core.Position.*
import maf.util.datastructures.ListOps.*
import maf.language.scheme.*
import maf.language.symbolic.*
import maf.modular.scheme.modf.*
import maf.core.IdentityMonad

/*
 * Soft contract verification uses the following forms of
 * context:
 *
 * - Contract call: if a function that is beinig monitored by a particular
 *   contract is called, the pre-condition and post-condition contracts
 *   are part of the context, and can be used during the analysis such
 *   that the preconditions can be assumed, and the post-condition
 *   can be checked, after the analysis of a particular component
 * - k-path conditions: during the analysis, the path conditions
 *    from the previous "k" components are added to the context
 *    to enable more precise symbolic information to be available during the
 *    analysis.
 */
sealed trait ScvContext[L]

/** Used when the function call is originating from applying a monitor */
case class ContractCallContext[L](domains: List[L], rangeContract: L, args: List[SchemeExp], idn: Identity) extends ScvContext[L]

trait ScvContextSensitivity extends SchemeModFSensitivity:
    type ComponentContext = ScvContext[Value]

    /**
     * An address to represent the nth argument of a function call in the store cache.
     *
     * To be replaced with the actual address when inserting the store cache in the context of the callee
     */
    case class ArgAddr(n: Int) extends Address:
        override def printable: Boolean = false
        override def idn: Identity = Identity.none

    /**
     * Keeps track of the path conditions from the last k components
     *
     * @param pc
     *   a list of path conditions from the last k components
     * @param vars
     *   a list of variables used in the path conditions from the last k components
     * @param symbolic
     *   a mapping between names of variables and symbolic values that should be passed between components (also from the last k components)
     * @param changes
     *   a list of changes applied to obtain the current path condition
     * @param symArgs
     *   a list of (symbolic) arguments of the called function (TODO: this might not be a great place to add this)
     */

    object CPathCondition:
        def unapply(a: Component): Option[(KPathCondition[Value], Component)] = context(a) match
            case Some(k: KPathCondition[Value]) => Some((k, a))
            case _                              => None

    // TODO: factor out rangeContract, because it is required for a sound implementation of scv, and cannot be disabled/enabled
    // for certain experiments.As such it is not part of a variable context.
    case class KPathCondition[L](
        pc: PathCondition,
        rangeContract: Option[L],
        callers: List[Position],
        changes: List[SymChange],
        symArgs: Map[String, SchemeExp],
        stoCache: Map[Addr, SchemeExp],
        widened: Boolean)
        extends ScvContext[L]:
        override def toString: String = s"KPathCondition($pc, $rangeContract, $stoCache, $changes)"

        /** Computes the set of symbolic arguments of the function call */
        def args: Set[SchemeExp] =
            stoCache.collect { case (ArgAddr(_), sym) => sym }.toSet ++ symArgs.values.toSet

        def reindexed: KPathCondition[L] =
            val thisChanges = Reindexer.computeRenaming(this.pc, this.stoCache, this.changes)
            val thisReindexedPc = this.pc.applyChanges(thisChanges)
            val thisStoCacheReindex = this.stoCache.mapValues(SymChange.applyAll(thisChanges, _)).toMap
            val thisChangesReindex = this.changes.map(_.applyChanges(thisChanges))
            this.copy(pc = thisReindexedPc, stoCache = thisStoCacheReindex, changes = thisChangesReindex)

        /** KPath condition contexts are equal modulo alpha renaming */
        override def equals(other: Any): Boolean = other match
            case other: KPathCondition[_] if this.callers == other.callers && this.symArgs == other.symArgs && this.widened == other.widened =>
                val thisR = this.reindexed
                val otherR = other.reindexed

                (thisR.pc == otherR.pc) && (thisR.stoCache == otherR.stoCache) && (thisR.changes == otherR.changes)
            case _ => false

        override def hashCode: Int =
            val r = this.reindexed
            (r.pc, rangeContract, callers, r.changes, symArgs, r.stoCache, widened).##

    //s"KPathCondition(rangeContract = $rangeContract, pc = ${pc}, sstore = ${stoCache}, changes = ${changes}, symARgs = ${symArgs})"
    case class NoContext[L]() extends ScvContext[L]

    def contractContext(cmp: Component): Option[ContractCallContext[Value]] = context(cmp).flatMap {
        case c: ContractCallContext[_] =>
            // safety: the ComponentContext is constrained to ScvContext[Value] (where
            // the type paremeter is invariant) which
            // means that ContractCallContext is always in L = Value otherwise
            // it does not type check. But unfortunately type parameters are erased
            // at runtime, and the isInstanceOf check cannot garuantee the type
            //  of the type parameter at runtime.
            Some(c.asInstanceOf[ContractCallContext[Value]])

        case _ => None
    }

    override def allocCtx(
        clo: (SchemeLambdaExp, Environment[Address]),
        args: List[Value],
        call: Position,
        caller: Component
      ): ComponentContext = NoContext() // contexts will be created by overriding them in the semantics

trait ScvKContextSensitivity extends ScvContextSensitivity with ScvModAnalysis with ScvUpdateCount:
    import evalM.*
    import maf.core.Monad.MonadSyntaxOps

    protected def k: Int
    protected def m: Int

    protected def usingContract[X](cmp: Component)(f: Option[(List[Value], Value, List[SchemeExp], Identity)] => X): X = contractContext(cmp) match
        case Some(context) => f(Some(context.domains, context.rangeContract, context.args, context.idn))
        case _             => f(None)

    protected def usingRangeContract[X](cmp: Component)(f: Option[Value] => X): X = context(cmp) match
        case Some(KPathCondition(_, rangeContractOpt, _, _, _, _, _)) => f(rangeContractOpt)
        case _                                                        => f(None)

    override def fromContext(cmp: Component): FromContext = context(cmp) match
        case Some(k @ KPathCondition(pc, _, _, _, symArgs, lcache, _)) => // KPathCondition(ps, sstore, _, cmps, _, _, lcache)
            new FromContext:
                def pathCondition: PathCondition = pc
                def vars: List[String] =
                    k.args
                        .flatMap(PathCondition.visit[IdentityMonad.Id, List[String]](_) {
                            case SchemeVar(name)       => Some(List(name.name))
                            case SchemeVarLex(name, _) => Some(List(name.name))
                            case _                     => None
                        })
                        .toList ++ k.pc.vars
                def symbolic: Map[String, Option[SchemeExp]] = symArgs.mapValues(Some(_)).toMap
                def lexStoCache: Map[Address, SchemeExp] = lcache
        case _ => EmptyContext

    override def buildCtx(symArgs: List[Option[SchemeExp]], rangeContract: Option[Value] = None): ContextBuilder =
        new ContextBuilder:
            def allocM(
                clo: (SchemeLambdaExp, Environment[Address]),
                args: List[Value],
                call: Position,
                caller: Component
              ): EvalM[ComponentContext] =
                unit(KPathCondition(PathCondition.empty, rangeContract, List(), List(), Map(), Map(), false))

trait ScvOneContextSensitivity(protected val m: Int) extends ScvKContextSensitivity:
    protected val k: Int = 1
