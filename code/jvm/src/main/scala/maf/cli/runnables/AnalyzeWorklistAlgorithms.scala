package maf.cli.runnables

import maf.bench.scheme.SchemeBenchmarkPrograms
import maf.cli.experiments.SchemeAnalyses
import maf.cli.runnables.DynamicWorklistAlgorithms.{
    LeastDependenciesFirstWorklistAlgorithmPOC,
    LiveLeastDependenciesFirstWorklistAlgorithm_CallsOnly_With_Check
}
import maf.core.{Address, Identifier, Monad}
import maf.language.CScheme.CSchemeParser
import maf.language.scheme.*
import maf.modular.*
import maf.modular.incremental.ProgramVersionExtracter.*
import maf.modular.incremental.scheme.lattice.IncrementalSchemeTypeDomain
import maf.modular.scheme.*
import maf.modular.scheme.modf.*
import maf.modular.worklist.*
import maf.util.Reader
import maf.util.benchmarks.{Timeout, Timer}

import scala.concurrent.duration.*

import scala.collection.immutable.Set
import scala.collection.mutable

// null values are used here due to Java interop
import scala.language.unsafeNulls

object AnalyzeWorklistAlgorithms extends App:
    val analyses = List((randomAnalysis, "RandomWorklistAlgorithm"), (depAnalysis, "DepAnalysis"))
    val bench: Map[String, String] = List(
      ("test/R5RS/icp/icp_1c_prime-sum-pair.scm", "prime-sum-pair"),
    ).toMap
    val warmup = 5
    val numIterations = 10

    def timeAnalysis[A <: ModAnalysis[SchemeExp]](bench: (String, SchemeExp), analysis: A, worklist: String): (mutable.Map[String, Int], Double) =
        var time: Long = -1
        //  println(s"Analysis of ${bench._1} with heuristic $worklist")
        try {
            time = Timer.timeOnly {
                analysis.analyze()
            }
            //   println(s"terminated in ${time / 1000000} ms.")
        } catch {
            case t: Throwable =>
                println(s"raised exception.")
                System.err.println(t.getMessage)
                t.printStackTrace()
                System.err.flush()
        }
        (analysis.analysis_stats_map, time)

    def randomAnalysis(program: SchemeExp) = new BasicAnalysis(program) with RandomWorklistAlgorithm[SchemeExp]

    def FIFOanalysis(program: SchemeExp) = new BasicAnalysis(program) with FIFOWorklistAlgorithm[SchemeExp]

    def LIFOanalysis(program: SchemeExp) = new BasicAnalysis(program) with LIFOWorklistAlgorithm[SchemeExp]

    def callDepthAnalysis(program: SchemeExp) = new BasicAnalysis(program) with CallDepthFirstWorklistAlgorithm[SchemeExp]

    def leastVisitedAnalysis(program: SchemeExp) = new BasicAnalysis(program) with LeastVisitedFirstWorklistAlgorithm[SchemeExp]

    def mostVisitedAnalysis(program: SchemeExp) = new BasicAnalysis(program) with MostVisitedFirstWorklistAlgorithm[SchemeExp]

    def deepExpressionFirstAnalysis(program: SchemeExp) = new BasicAnalysis(program) with DeepExpressionsFirstWorklistAlgorithm[SchemeExp]

    def shallowExpressionsFirstAnalysis(program: SchemeExp) = new BasicAnalysis(program) with ShallowExpressionsFirstWorklistAlgorithm[SchemeExp]

    def mostDependenciesFirstAnalysis(program: SchemeExp) = new BasicAnalysis(program) with MostDependenciesFirstWorklistAlgorithm[SchemeExp]

    def leastDependenciesFirstAnalysis(program: SchemeExp) = new BasicAnalysis(program) with LeastDependenciesFirstWorklistAlgorithm[SchemeExp]

    def biggerEnvironmentFirstAnalysis(program: SchemeExp) = new BasicAnalysis(program) with BiggerEnvironmentFirstWorklistAlgorithm.ModF

    def smallerEnvironmentFirstAnalysis(program: SchemeExp) = new BasicAnalysis(program) with SmallerEnvironmentFirstWorklistAlgorithm.ModF

    def liveAnalysis_CallsOnly_With_Check(program: SchemeExp) =
        new SimpleSchemeModFAnalysis(program)
            with SchemeModFNoSensitivity
            with SchemeConstantPropagationDomain
            with DependencyTracking[SchemeExp]
            with GlobalStore[SchemeExp]
            with LiveLeastDependenciesFirstWorklistAlgorithm_CallsOnly_With_Check[SchemeExp] {
            override def intraAnalysis(cmp: SchemeModFComponent) =
                new IntraAnalysis(cmp) with BigStepModFIntra with LiveDependencyTrackingIntra
        }

    def depAnalysis(program: SchemeExp) = new BasicAnalysis(program) with LeastDependenciesFirstWorklistAlgorithmPOC[SchemeExp]

    abstract class BasicAnalysis(program: SchemeExp)
        extends SimpleSchemeModFAnalysis(program)
        with SchemeConstantPropagationDomain
        with DependencyTracking[SchemeExp]
        with SchemeModFNoSensitivity {
        override def intraAnalysis(cmp: SchemeModFComponent) =
            new IntraAnalysis(cmp) with BigStepModFIntra with DependencyTrackingIntra
    }
