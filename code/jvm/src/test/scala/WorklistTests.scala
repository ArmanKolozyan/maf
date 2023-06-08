import maf.cli.runnables.AnalyzeWorklistAlgorithms.{FIFOanalysis, LIFOanalysis, biggerEnvironmentFirstAnalysis, callDepthAnalysis, deepExpressionFirstAnalysis, depAnalysis, leastDependenciesFirstAnalysis, leastVisitedAnalysis, mostDependenciesFirstAnalysis, mostVisitedAnalysis, shallowExpressionsFirstAnalysis, smallerEnvironmentFirstAnalysis}
import maf.cli.runnables.DynamicWorklistAlgorithms.{SchemeAnalysisWithDeps, call_dependencies_only, least_dependencies_first, liveAnalysis, liveAnalysis_CallsOnly_With_Check, liveAnalysis_CallsOnly_Without_Check, most_dependencies_first, randomAnalysis}
import maf.core.Address
import maf.language.scheme.{SchemeExp, SchemeParser}
import maf.util.Reader
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import maf.modular.*

class WorklistTests extends AnyFlatSpec with Matchers {

  def analyzeProgram[A <: SchemeAnalysisWithDeps](program: SchemeExp, analysis: SchemeExp => A, name: String) = {
    val a: A = analysis(program)
    println("-------------------------")
    println(name)
    a.analyze()
    println("-------------------------")
    a.store
  }

  trait Fixture:
    val benchmark = ("test/R5RS/gambit/sboyer.scm", "sboyer")
    val program = SchemeParser.parseProgram(Reader.loadFile(benchmark._1))



  "The results of the live_dependencies and the random worklist heuristics" should "be equal" in new Fixture {
    analyzeProgram(program, liveAnalysis, "liveAnalysis") should equal(analyzeProgram(program, randomAnalysis, "randomAnalysis"))
  }

  "The results of the least_dependencies_first and the random worklist heuristics" should "be equal" in new Fixture {
    analyzeProgram(program, least_dependencies_first, "depAnalysis") should equal(analyzeProgram(program, randomAnalysis, "randomAnalysis"))
  }

  "The results of the most_dependencies_first and the random worklist heuristics" should "be equal" in new Fixture {
    analyzeProgram(program, most_dependencies_first, "most_dependencies_first") should equal(analyzeProgram(program, randomAnalysis, "randomAnalysis"))
  }

  "The results of the call_dependencies_only and the random worklist heuristics" should "be equal" in new Fixture {
    analyzeProgram(program, call_dependencies_only, "call_dependencies_only") should equal(analyzeProgram(program, randomAnalysis, "randomAnalysis"))
  }

  "The results of the FIFOanalysis and the random worklist heuristics" should "be equal" in new Fixture {
    analyzeProgram(program, FIFOanalysis, "FIFOanalysis") should equal(analyzeProgram(program, randomAnalysis, "randomAnalysis"))
  }

  "The results of the LIFOanalysis and the random worklist heuristics" should "be equal" in new Fixture {
    analyzeProgram(program, LIFOanalysis, "LIFOanalysis") should equal(analyzeProgram(program, randomAnalysis, "randomAnalysis"))
  }

  "The results of the callDepthAnalysis and the random worklist heuristics" should "be equal" in new Fixture {
    analyzeProgram(program, callDepthAnalysis, "callDepthAnalysis") should equal(analyzeProgram(program, randomAnalysis, "randomAnalysis"))
  }

  "The results of the leastVisitedAnalysis and the random worklist heuristics" should "be equal" in new Fixture {
    analyzeProgram(program, leastVisitedAnalysis, "leastVisitedAnalysis") should equal(analyzeProgram(program, randomAnalysis, "randomAnalysis"))
  }

  "The results of the mostVisitedAnalysis and the random worklist heuristics" should "be equal" in new Fixture {
    analyzeProgram(program, mostVisitedAnalysis, "mostVisitedAnalysis") should equal(analyzeProgram(program, randomAnalysis, "randomAnalysis"))
  }

  "The results of the deepExpressionFirstAnalysis and the random worklist heuristics" should "be equal" in new Fixture {
    analyzeProgram(program, deepExpressionFirstAnalysis, "deepExpressionFirstAnalysis") should equal(analyzeProgram(program, randomAnalysis, "randomAnalysis"))
  }

  "The results of the shallowExpressionsFirstAnalysis and the random worklist heuristics" should "be equal" in new Fixture {
    analyzeProgram(program, shallowExpressionsFirstAnalysis, "shallowExpressionsFirstAnalysis") should equal(analyzeProgram(program, randomAnalysis, "randomAnalysis"))
  }

  "The results of the mostDependenciesFirstAnalysis and the random worklist heuristics" should "be equal" in new Fixture {
    analyzeProgram(program, mostDependenciesFirstAnalysis, "mostDependenciesFirstAnalysis") should equal(analyzeProgram(program, randomAnalysis, "randomAnalysis"))
  }

  "The results of the leastDependenciesFirstAnalysis and the random worklist heuristics" should "be equal" in new Fixture {
    analyzeProgram(program, leastDependenciesFirstAnalysis, "leastDependenciesFirstAnalysis") should equal(analyzeProgram(program, randomAnalysis, "randomAnalysis"))
  }

  "The results of the biggerEnvironmentFirstAnalysis and the random worklist heuristics" should "be equal" in new Fixture {
    analyzeProgram(program, biggerEnvironmentFirstAnalysis, "biggerEnvironmentFirstAnalysis") should equal(analyzeProgram(program, randomAnalysis, "randomAnalysis"))
  }

  "The results of the smallerEnvironmentFirstAnalysis and the random worklist heuristics" should "be equal" in new Fixture {
    analyzeProgram(program, smallerEnvironmentFirstAnalysis, "smallerEnvironmentFirstAnalysis") should equal(analyzeProgram(program, randomAnalysis, "randomAnalysis"))
  }

  "The results of the liveAnalysis_CaliveAnalysis_CallsOnly_Without_CheckllsOnly and the random worklist heuristics" should "be equal" in new Fixture {
    analyzeProgram(program, liveAnalysis_CallsOnly_Without_Check, "liveAnalysis_CallsOnly_Without_Check") should equal(analyzeProgram(program, randomAnalysis, "randomAnalysis"))
  }

  "The results of the liveAnalysis_CallsOnly_With_Check and the random worklist heuristics" should "be equal" in new Fixture {
    analyzeProgram(program, liveAnalysis_CallsOnly_With_Check, "liveAnalysis_CallsOnly_With_Check") should equal(analyzeProgram(program, randomAnalysis, "randomAnalysis"))
  }
}
