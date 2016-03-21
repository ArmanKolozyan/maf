import org.scalatest._
import org.scalatest.prop._

abstract class Benchmarks[Exp : Expression, Addr : Address, Time : Timestamp](val lattice: Lattice)
    extends FlatSpec with Matchers {
  type Abs = lattice.L
  implicit val abs = lattice.isAbstractValue
  val sem: Semantics[Exp, lattice.L, Addr, Time]
  val machine: AbstractMachine[Exp, lattice.L, Addr, Time]

  def checkResult(file: String, expected: Abs): Unit = {
    val result = machine.eval(sem.parse(Main.fileContent(s"test/$file")), sem, false, None)
    assert(result.containsFinalValue(expected))
    println(s"${machine.name}, $file: ${result.numberOfStates}, ${result.time}")
  }
  def check(file: String, expected: Abs): Unit =
    file should s"eval to $expected" in { checkResult(file, expected) }

  val concrete = abs.name.contains("Concrete")

  check("blur.scm", abs.inject(true))
  check("count.scm", abs.inject("done"))
  if (!concrete) { check("cpstak.scm", abs.inject(6)) }
  check("fib.scm", abs.inject(3))
  check("eta.scm", abs.inject(false))
  check("fact.scm", abs.inject(120))
  check("gcipd.scm", abs.inject(36))
  check("inc.scm", abs.inject(4))
  check("kcfa2.scm", abs.inject(false))
  check("kcfa3.scm", abs.inject(false))
  check("mj09.scm", abs.inject(2))
  check("mut-rec.scm", abs.inject(true))
  check("rotate.scm", abs.inject("hallo"))
  check("sq.scm", abs.inject(9))
  check("sym.scm", abs.injectSymbol("foo"))
  check("ack.scm", abs.inject(4))
  check("collatz.scm", abs.inject(5))
  check("widen.scm", abs.inject(10))
  if (scala.util.Properties.envOrElse("SLOW_BENCHMARKS", "no") == "yes") {
    check("loop2.scm", abs.inject(550))
    check("rsa.scm", abs.inject(true))
    check("sat.scm", abs.inject(true))
    check("primtest.scm", abs.inject(1))
    if (!concrete) {
      // check("nqueens.scm", abs.inject(92)) // doesn't terminate in AAC !
      check("church.scm", abs.inject(true))
      check("boyer.scm", abs.inject(true))
      check("dderiv.scm", abs.inject(true))
      check("takl.scm", abs.inject(true))
    }
  }
}

abstract class OneResultTests[Exp : Expression, Addr : Address, Time : Timestamp](val lattice: Lattice)
    extends FlatSpec with Matchers {
  type Abs = lattice.L
  implicit val abs = lattice.isAbstractValue
  val sem: Semantics[Exp, lattice.L, Addr, Time]
  val machine: AbstractMachine[Exp, lattice.L, Addr, Time]

  def check(file: String, expected: Abs): Unit =
    file should s"have only one final state in concrete mode and return $expected" in {
      val result = machine.eval(sem.parse(Main.fileContent(s"test/$file")), sem, false, None)
      result.finalValues.size should equal (1)
      result.finalValues.head should equal (expected)
    }

  check("blur.scm", abs.inject(true))
  check("count.scm", abs.inject("done"))
  // check("cpstak.scm", abs.inject(6)) disabled due to the time it takes
  check("fib.scm", abs.inject(3))
  check("eta.scm", abs.inject(false))
  check("fact.scm", abs.inject(120))
  check("gcipd.scm", abs.inject(36))
  check("inc.scm", abs.inject(4))
  check("kcfa2.scm", abs.inject(false))
  check("kcfa3.scm", abs.inject(false))
  check("mj09.scm", abs.inject(2))
  check("mut-rec.scm", abs.inject(true))
  check("rotate.scm", abs.inject("hallo"))
  check("sq.scm", abs.inject(9))
  check("sym.scm", abs.injectSymbol("foo"))
  check("ack.scm", abs.inject(4))
  check("collatz.scm", abs.inject(5))
  check("widen.scm", abs.inject(10))
  if (scala.util.Properties.envOrElse("SLOW_BENCHMARKS", "no") == "yes") {
    check("loop2.scm", abs.inject(550))
    check("rsa.scm", abs.inject(true))
    // check("sat.scm", abs.inject(true)) // doesn't terminate in AAC !
    check("primtest.scm", abs.inject(1))
    // check("nqueens.scm", abs.inject(92)) // doesn't terminate in AAC !
    check("church.scm", abs.inject(true))
    check("boyer.scm", abs.inject(true))
    check("dderiv.scm", abs.inject(true))
    check("takl.scm", abs.inject(true))
  }
}

abstract class AACBenchmarks[Addr : Address, Time : Timestamp](override val lattice: Lattice)
    extends Benchmarks[SchemeExp, Addr, Time](lattice) {
  val sem = new SchemeSemantics[lattice.L, Addr, Time]
  val machine = new AAC[SchemeExp, lattice.L, Addr, Time]
}

abstract class AAMBenchmarks[Addr : Address, Time : Timestamp](override val lattice: Lattice)
    extends Benchmarks[SchemeExp, Addr, Time](lattice) {
  val sem = new SchemeSemantics[lattice.L, Addr, Time]
  val machine = new AAM[SchemeExp, lattice.L, Addr, Time]
}

abstract class FreeBenchmarks[Addr : Address, Time : Timestamp](override val lattice: Lattice)
    extends Benchmarks[SchemeExp, Addr, Time](lattice) {
  val sem = new SchemeSemantics[lattice.L, Addr, Time]
  val machine = new Free[SchemeExp, lattice.L, Addr, Time]
}

abstract class ConcurrentAAMBenchmarks[Addr : Address, Time : Timestamp, TID : ThreadIdentifier](override val lattice: Lattice)
    extends Benchmarks[SchemeExp, Addr, Time](lattice) {
  val sem = new SchemeSemantics[lattice.L, Addr, Time]
  val machine = new ConcurrentAAM[SchemeExp, lattice.L, Addr, Time, TID](AllInterleavings)
}

class AACConcreteBenchmarks extends AACBenchmarks[ClassicalAddress.A, ConcreteTimestamp.T](ConcreteLattice)
class AACConcreteNewBenchmarks extends AACBenchmarks[ClassicalAddress.A, ConcreteTimestamp.T](new ConcreteLatticeNew(true))
class AACTypeSetBenchmarks extends AACBenchmarks[ClassicalAddress.A, ZeroCFA.T](new TypeSetLattice(false))
// Compilation doesn't terminate?!
//class AACBoundedIntBenchmarks extends AACBenchmarks[ClassicalAddress.A, ZeroCFA.T](BoundedIntLattice)

class AAMConcreteBenchmarks extends AAMBenchmarks[ClassicalAddress.A, ConcreteTimestamp.T](ConcreteLattice)
class AAMConcreteNewBenchmarks extends AAMBenchmarks[ClassicalAddress.A, ConcreteTimestamp.T](new ConcreteLatticeNew(true))
class AAMTypeSetBenchmarks extends AAMBenchmarks[ClassicalAddress.A, ZeroCFA.T](new TypeSetLattice(false))
//class AAMBoundedIntBenchmarks extends AACBenchmarks[ClassicalAddress.A, ZeroCFA.T](BoundedIntLattice)

class FreeConcreteBenchmarks extends FreeBenchmarks[ClassicalAddress.A, ConcreteTimestamp.T](ConcreteLattice)
class FreeConcreteNewBenchmarks extends FreeBenchmarks[ClassicalAddress.A, ConcreteTimestamp.T](new ConcreteLatticeNew(true))
class FreeTypeSetBenchmarks extends FreeBenchmarks[ClassicalAddress.A, ZeroCFA.T](new TypeSetLattice(false))
//class FreeBoundedIntBenchmarks extends FreeBenchmarks[ClassicalAddress.A, ZeroCFA.T](BoundedIntLattice)

class ConcurrentAAMConcreteBenchmarks extends ConcurrentAAMBenchmarks[ClassicalAddress.A, ConcreteTimestamp.T, ContextSensitiveTID](ConcreteLattice)
class ConcurrentAAMConcreteNewBenchmarks extends ConcurrentAAMBenchmarks[ClassicalAddress.A, ConcreteTimestamp.T, ContextSensitiveTID](new ConcreteLatticeNew(true))
class ConcurrentAAMTypeSetBenchmarks extends ConcurrentAAMBenchmarks[ClassicalAddress.A, ZeroCFA.T, ContextSensitiveTID](new TypeSetLattice(false))
//class ConcurrentAAMBoundedIntBenchmarks extends ConcurrentAAMBenchmarks[ClassicalAddress.A, ZeroCFA.T, ContextSensitiveTID](BoundedIntLattice)

class AACOneResultTests extends OneResultTests[SchemeExp, ClassicalAddress.A, ConcreteTimestamp.T](ConcreteLattice) {
  val sem = new SchemeSemantics[lattice.L, ClassicalAddress.A, ConcreteTimestamp.T]
  val machine = new AAC[SchemeExp, lattice.L, ClassicalAddress.A, ConcreteTimestamp.T]
}

class AACOneResultTestsNew extends OneResultTests[SchemeExp, ClassicalAddress.A, ConcreteTimestamp.T](new ConcreteLatticeNew(true)) {
  val sem = new SchemeSemantics[lattice.L, ClassicalAddress.A, ConcreteTimestamp.T]
  val machine = new AAC[SchemeExp, lattice.L, ClassicalAddress.A, ConcreteTimestamp.T]
}

class AAMOneResultTests extends OneResultTests[SchemeExp, ClassicalAddress.A, ConcreteTimestamp.T](ConcreteLattice) {
  val sem = new SchemeSemantics[lattice.L, ClassicalAddress.A, ConcreteTimestamp.T]
  val machine = new AAM[SchemeExp, lattice.L, ClassicalAddress.A, ConcreteTimestamp.T]
}

class AAMOneResultTestsNew extends OneResultTests[SchemeExp, ClassicalAddress.A, ConcreteTimestamp.T](new ConcreteLatticeNew(true)) {
  val sem = new SchemeSemantics[lattice.L, ClassicalAddress.A, ConcreteTimestamp.T]
  val machine = new AAM[SchemeExp, lattice.L, ClassicalAddress.A, ConcreteTimestamp.T]
}

class FreeOneResultTests extends OneResultTests[SchemeExp, ClassicalAddress.A, ConcreteTimestamp.T](ConcreteLattice) {
  val sem = new SchemeSemantics[lattice.L, ClassicalAddress.A, ConcreteTimestamp.T]
  val machine = new Free[SchemeExp, lattice.L, ClassicalAddress.A, ConcreteTimestamp.T]
}

class FreeOneResultTestsNew extends OneResultTests[SchemeExp, ClassicalAddress.A, ConcreteTimestamp.T](new ConcreteLatticeNew(true)) {
  val sem = new SchemeSemantics[lattice.L, ClassicalAddress.A, ConcreteTimestamp.T]
  val machine = new Free[SchemeExp, lattice.L, ClassicalAddress.A, ConcreteTimestamp.T]
}

class ConcurrentAAMOneResultTests extends OneResultTests[SchemeExp, ClassicalAddress.A, ConcreteTimestamp.T](ConcreteLattice) {
  val sem = new SchemeSemantics[lattice.L, ClassicalAddress.A, ConcreteTimestamp.T]
  val machine = new ConcurrentAAM[SchemeExp, lattice.L, ClassicalAddress.A, ConcreteTimestamp.T, ContextSensitiveTID](AllInterleavings)
}

class ConcurrentAAMOneResultTestsNew extends OneResultTests[SchemeExp, ClassicalAddress.A, ConcreteTimestamp.T](new ConcreteLatticeNew(true)) {
  val sem = new SchemeSemantics[lattice.L, ClassicalAddress.A, ConcreteTimestamp.T]
  val machine = new ConcurrentAAM[SchemeExp, lattice.L, ClassicalAddress.A, ConcreteTimestamp.T, ContextSensitiveTID](AllInterleavings)
}
