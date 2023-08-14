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
import maf.core.Lattice
import scala.util.Try
import java.util.concurrent.TimeoutException

object AnalyzeWorklistAlgorithms extends App:
    // val analyses = List((randomAnalysis, "RandomWorklistAlgorithm"), (depAnalysis, "DepAnalysis"))
    val warmup = 5
    val numIterations = 3

    case class AnalysisStats(
        /** Contains information about the number of intra-analysis iterations for each component */
        iterationsPerComponent: Map[String, Int],
        /** Contains the "size" of the incoming flows from variables and function parameters */
        varAddrSize: Map[String, Int],
        /** Contains the "size" fo the incoming flows from return values */
        retAddrSize: Map[String, Int]):
        def totalIterations: Int = iterationsPerComponent.values.foldLeft(0)(_ + _)
        def totalVarSize: Int = varAddrSize.values.foldLeft(0)(_ + _)
        def totalRetSize: Int = retAddrSize.values.foldLeft(0)(_ + _)

    def computeSize[Adr, Vlu](store: Map[Adr, Vlu])(adr: Adr)(using lat: Lattice[Vlu]): Int =
        lat.level(store.get(adr).getOrElse(lat.bottom))

    def timeAnalysis[A <: ModAnalysis[SchemeExp] & DependencyTracking[SchemeExp] & GlobalStore[SchemeExp]](
        bench: (String, SchemeExp),
        analysis: A,
        worklist: String
      ): Option[(AnalysisStats, Double)] =
        for
            time <- Try(Timer.timeOnly {
                try analysis.analyzeWithTimeout(Timeout.start(5.minutes))
                catch
                    case e: Exception =>
                        e.printStackTrace()
                        throw e
                if !analysis.finished then throw TimeoutException()
            }).toOption
            // compute the "size" for each variable address in the program
            varAdrSize = analysis.readDependencies.map { case (cmp, adrs) =>
                (cmp.toString -> adrs
                    .collect { case v @ VarAddr(_, _) => v }
                    .map(computeSize[analysis.Addr, analysis.Value](analysis.store))
                    .foldLeft(0)(_ + _))
            }.toMap
            retAddrSize = analysis.readDependencies.map { case (cmp, adrs) =>
                (cmp.toString -> adrs
                    .collect { case v @ ReturnAddr(_, _) => v }
                    .map(computeSize[analysis.Addr, analysis.Value](analysis.store))
                    .foldLeft(0)(_ + _))
            }.toMap
            stats = AnalysisStats(analysis.analysis_stats_map.toMap, varAdrSize, retAddrSize)
        yield (stats, time.toDouble)

    // def randomAnalysis(program: SchemeExp) = new BasicAnalysis(program) with RandomWorklistAlgorithm[SchemeExp]

    def FIFOanalysis(theK: Int)(program: SchemeExp) = new BasicAnalysis(program) with FIFOWorklistAlgorithm[SchemeExp]:
        val k = theK

    def LIFOanalysis(theK: Int)(program: SchemeExp) = new BasicAnalysis(program) with LIFOWorklistAlgorithm[SchemeExp]:
        val k = theK

    //def callDepthAnalysis(program: SchemeExp) = new BasicAnalysis(program) with CallDepthFirstWorklistAlgorithm[SchemeExp]

    //def leastVisitedAnalysis(program: SchemeExp) = new BasicAnalysis(program) with LeastVisitedFirstWorklistAlgorithm[SchemeExp]

    //def mostVisitedAnalysis(program: SchemeExp) = new BasicAnalysis(program) with MostVisitedFirstWorklistAlgorithm[SchemeExp]

    //def deepExpressionFirstAnalysis(program: SchemeExp) = new BasicAnalysis(program) with DeepExpressionsFirstWorklistAlgorithm[SchemeExp]

    //def shallowExpressionsFirstAnalysis(program: SchemeExp) = new BasicAnalysis(program) with ShallowExpressionsFirstWorklistAlgorithm[SchemeExp]

    //def mostDependenciesFirstAnalysis(program: SchemeExp) = new BasicAnalysis(program) with MostDependenciesFirstWorklistAlgorithm[SchemeExp]

    //def leastDependenciesFirstAnalysis(program: SchemeExp) = new BasicAnalysis(program) with LeastDependenciesFirstWorklistAlgorithm[SchemeExp]

    //def biggerEnvironmentFirstAnalysis(program: SchemeExp) = new BasicAnalysis(program) with BiggerEnvironmentFirstWorklistAlgorithm.ModF

    //def smallerEnvironmentFirstAnalysis(program: SchemeExp) = new BasicAnalysis(program) with SmallerEnvironmentFirstWorklistAlgorithm.ModF

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

    //def depAnalysis(program: SchemeExp) = new BasicAnalysis(program) with LeastDependenciesFirstWorklistAlgorithmPOC[SchemeExp]

    abstract class BasicAnalysis(program: SchemeExp)
        extends SimpleSchemeModFAnalysis(program)
        with SchemeConstantPropagationDomain
        with DependencyTracking[SchemeExp]
        with SchemeModFKCallSiteSensitivity {
        override def intraAnalysis(cmp: SchemeModFComponent) =
            new IntraAnalysis(cmp) with BigStepModFIntra with DependencyTrackingIntra
    }
